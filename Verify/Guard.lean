import Lean

/-!
# Verifier metaprograms

Trusted, harness-owned commands used by the generated check files. Nothing here is
importable by a submission (the verifier rejects submissions that import `Verify.*`).

Four commands:

* `#conject_refutation refuted target` — kernel-check that `refuted` is the literal negation
  of `target` at shared universe parameters. `example : R ↔ ¬ T := Iff.rfl` generalizes the
  two sides' universes independently, so it rejects every universe-polymorphic refutation.
* `#conject_provenance d "Mod"` — fail unless constant `d` was declared in module `Mod`.
  This is what stops a submission from shadowing the canonical statement.
* `#conject_no_new_axioms "Mod"` — fail if module `Mod` declares any `axiom`.
* `#conject_audit d "Mod" "out/prefix"` — write the axiom set and a normalized
  serialization of `d`'s elaborated proof term to `out/prefix.json` / `out/prefix.term`.

Every command writes a `CONJECT_ERROR: <code>` line and throws on failure, so the shell
driver can distinguish a policy failure from a Lean crash.
-/

open Lean Elab Command Meta

namespace Conject.Guard

/-! ## Normalized serialization of elaborated terms

The goal is a byte string that is identical for two proofs that are the same proof, and
different for two proofs that are not. So we drop everything the kernel does not care
about — binder names, binder info, `mdata`, the spelling of universe parameters — and we
inline the submitter's own auxiliary definitions, since `alice.helper_1` and
`bob.aux` being spelled differently is not a mathematical difference.

Constants from Mathlib, core, and `Commons` stay opaque: shared vocabulary is exactly
what *should* make two proofs compare equal.
-/

/-- Serializer state. `fuel` bounds the output for pathological terms. -/
structure SState where
  out : Array String := #[]
  fuel : Nat := 4000000
  truncated : Bool := false
  deriving Inhabited

abbrev SM := StateM SState

private def emit (s : String) : SM Unit :=
  modify fun st => { st with out := st.out.push s }

/-- Universe levels, with parameter names replaced by their index in the declaration's
`levelParams`, so `u`/`u_1`/`v` renamings do not change the hash. -/
private partial def levelStr (pm : NameMap Nat) : Level → String
  | .zero      => "0"
  | .succ u    => "s(" ++ levelStr pm u ++ ")"
  | .max a b   => "M(" ++ levelStr pm a ++ "," ++ levelStr pm b ++ ")"
  | .imax a b  => "I(" ++ levelStr pm a ++ "," ++ levelStr pm b ++ ")"
  | .param n   => match pm.find? n with
                  | some i => "p" ++ toString i
                  | none   => "P" ++ n.toString
  | .mvar _    => "?u"

private def litStr : Literal → String
  | .natVal n => "n" ++ toString n
  | .strVal s => "s" ++ toString s.length ++ ":" ++ s

private def constStr (pm : NameMap Nat) (c : Name) (us : List Level) : String :=
  "C" ++ c.toString ++ "{" ++ String.intercalate "," (us.map (levelStr pm)) ++ "}"

/-- Serialize `e`, inlining any constant in `inl` (the submission's own declarations).
`active` breaks cycles from recursive helpers. -/
private partial def ser (env : Environment) (inl : NameSet) (pm : NameMap Nat)
    (active : NameSet) (e : Expr) : SM Unit := do
  if (← get).fuel == 0 then
    modify fun st => { st with truncated := true }
    emit "!"
    return
  modify fun st => { st with fuel := st.fuel - 1 }
  let go := ser env inl pm active
  match e with
  | .bvar i => emit s!"b{i}"
  | .fvar _ => emit "!fvar"
  | .mvar _ => emit "!mvar"
  | .sort u => emit ("S" ++ levelStr pm u)
  | .lit l => emit ("#" ++ litStr l)
  | .mdata _ b => go b
  | .app f a => do
    emit "("
    go f
    emit " "
    go a
    emit ")"
  | .lam _ t b _ => do
    emit "L["
    go t
    emit "]"
    go b
  | .forallE _ t b _ => do
    emit "A["
    go t
    emit "]"
    go b
  | .letE _ t v b _ => do
    emit "T["
    go t
    emit "="
    go v
    emit "]"
    go b
  | .proj s i b => do
    emit s!"J{s}/{i}("
    go b
    emit ")"
  | .const c us => do
    match (if inl.contains c && !active.contains c then env.find? c else none) with
    | some ci =>
      match ci.value? (allowOpaque := true) with
      | some v => do
        emit "<"
        ser env inl pm (active.insert c) (v.instantiateLevelParams ci.levelParams us)
        emit ">"
      | none => emit (constStr pm c us)
    | none => emit (constStr pm c us)

/-- Transitive closure of the constants `root` depends on that were declared in `mod`.
These are the submitter's own auxiliary definitions. -/
private partial def ownDeps (mod : Name) (visited : NameSet) (todo : List Name) :
    CommandElabM NameSet := do
  match todo with
  | [] => return visited
  | c :: rest =>
    if visited.contains c then
      ownDeps mod visited rest
    else
      let env ← getEnv
      let some ci := env.find? c | ownDeps mod visited rest
      let inMod := match env.getModuleIdxFor? c with
        | some idx => env.allImportedModuleNames[idx.toNat]! == mod
        | none     => false
      if !inMod then
        ownDeps mod visited rest
      else
        let more := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
        ownDeps mod (visited.insert c) (more.toList ++ rest)

/-- Serialize a constant's elaborated value (or its type, if it has no value). -/
def normalize (declName : Name) (mod : Name) : CommandElabM (String × Bool) := do
  let env ← getEnv
  let some ci := env.find? declName
    | throwError "conject: unknown constant '{declName}'"
  let inl ← ownDeps mod {} (((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]).toList
  let pm : NameMap Nat := ci.levelParams.foldl (init := ({}, 0))
      (fun (m, i) n => (m.insert n i, i + 1)) |>.1
  let body := (ci.value? (allowOpaque := true)).getD ci.type
  let st := (ser env inl pm {} body).run {} |>.2
  return (String.join st.out.toList, st.truncated)

/-! ## Commands -/

private def jsonStr (s : String) : String := Json.str s |>.compress

private def fail (code : String) (msg : String) : CommandElabM α := do
  logInfo s!"CONJECT_ERROR: {code}"
  IO.println s!"CONJECT_ERROR: {code}"
  throwError "conject [{code}]: {msg}"

/-- `#conject_provenance Foo.bar "Foo"` — the constant must live in exactly that module. -/
syntax (name := conjectProvenance) "#conject_provenance " ident ppSpace str : command

@[command_elab conjectProvenance]
def elabProvenance : CommandElab := fun stx => do
  let declName := stx[1].getId
  let expected := stx[2].isStrLit?.getD ""
  let env ← getEnv
  unless (env.find? declName).isSome do
    fail "provenance_missing" s!"constant '{declName}' does not exist"
  let actual := match env.getModuleIdxFor? declName with
    | some idx => (env.allImportedModuleNames[idx.toNat]!).toString
    | none     => "<current>"
  unless actual == expected do
    fail "provenance_mismatch"
      s!"'{declName}' is declared in '{actual}', expected '{expected}'"
  IO.println s!"CONJECT_PROVENANCE_OK: {declName} @ {actual}"

/-- `#conject_no_new_axioms "Mod"` — module `Mod` must not declare any `axiom`. -/
syntax (name := conjectNoNewAxioms) "#conject_no_new_axioms " str : command

@[command_elab conjectNoNewAxioms]
def elabNoNewAxioms : CommandElab := fun stx => do
  let modName := (stx[1].isStrLit?.getD "").toName
  let env ← getEnv
  let names := env.allImportedModuleNames
  let some idx := names.findIdx? (· == modName)
    | fail "module_not_imported" s!"module '{modName}' is not imported"
  let data := env.header.moduleData[idx]!
  let bad := data.constants.filterMap fun ci =>
    match ci with
    | .axiomInfo v => some v.name
    | _            => none
  unless bad.isEmpty do
    fail "declares_axiom" s!"module '{modName}' declares axioms: {bad.toList}"
  IO.println s!"CONJECT_NO_NEW_AXIOMS_OK: {modName}"

/-- `#conject_audit Foo.bar "Foo" "path/prefix"` — emit axioms + normalized term. -/
syntax (name := conjectAudit) "#conject_audit " ident ppSpace str ppSpace str : command

@[command_elab conjectAudit]
def elabAudit : CommandElab := fun stx => do
  let declName := stx[1].getId
  let modName := (stx[2].isStrLit?.getD "").toName
  let prefixPath := stx[3].isStrLit?.getD ""
  let env ← getEnv
  unless (env.find? declName).isSome do
    fail "audit_missing_decl" s!"constant '{declName}' does not exist"
  let axs ← liftCoreM <| Lean.collectAxioms declName
  let (term, truncated) ← normalize declName modName
  let termPath := prefixPath ++ ".term"
  IO.FS.writeFile termPath term
  let axJson := String.intercalate "," (axs.toList.map (fun a => jsonStr a.toString))
  let json := "{\"decl\":" ++ jsonStr declName.toString
    ++ ",\"module\":" ++ jsonStr modName.toString
    ++ ",\"axioms\":[" ++ axJson ++ "]"
    ++ ",\"term_file\":" ++ jsonStr termPath
    ++ ",\"term_bytes\":" ++ toString term.utf8ByteSize
    ++ ",\"term_truncated\":" ++ (if truncated then "true" else "false")
    ++ "}"
  IO.FS.writeFile (prefixPath ++ ".json") json
  IO.println s!"CONJECT_AUDIT_OK: {declName}"

/-- `#conject_refutation R T` — `R` must be definitionally `¬ T`, at the same universe
parameters on both sides. The kernel does the check, via `addDecl`. -/
syntax (name := conjectRefutation) "#conject_refutation " ident ppSpace ident : command

@[command_elab conjectRefutation]
def elabRefutation : CommandElab := fun stx => do
  let refutedName := stx[1].getId
  let targetName := stx[2].getId
  let env ← getEnv
  let some refuted := env.find? refutedName
    | fail "refutation_missing_decl" s!"constant '{refutedName}' does not exist"
  let some target := env.find? targetName
    | fail "refutation_missing_decl" s!"constant '{targetName}' does not exist"
  unless refuted.levelParams.length == target.levelParams.length do
    fail "not_a_refutation"
      s!"'{refutedName}' has {refuted.levelParams.length} universe parameter(s) but '{targetName}' has {target.levelParams.length}"
  let levels := refuted.levelParams.map Level.param
  let lhs := mkConst refutedName levels
  let rhs := mkApp (mkConst ``Not) (mkConst targetName levels)
  let decl : Declaration := .thmDecl {
    name := `Conject.Refutation.bridge
    levelParams := refuted.levelParams
    type := mkApp2 (mkConst ``Iff) lhs rhs
    value := mkApp (mkConst ``Iff.rfl) lhs }
  -- Synchronous: the elaborator's `addDecl` defers kernel checking, and a deferred
  -- failure would land after the OK line below.
  let opts ← getOptions
  match env.toKernelEnv.addDecl opts decl with
  | .error ex =>
    fail "not_a_refutation"
      s!"'{refutedName}' is not definitionally '¬ {targetName}': {← (ex.toMessageData opts).toString}"
  | .ok _ => pure ()
  IO.println s!"CONJECT_REFUTATION_OK: {refutedName} ↔ ¬ {targetName}"

end Conject.Guard
