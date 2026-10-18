"""Galactic kinematics for Jig's stellar certificates.

A witness gives one star's ICRS astrometry and radial velocity with errors. This
module turns that into a galactocentric position and velocity, decides bound or
unbound against a named Milky Way potential, and integrates the orbit backward
under it. Every quantity is sampled over the quoted errors, so a checker's
predicate is a probability rather than a point estimate.

The potential is MWPotential2014 (Bovy 2015): a power-law bulge with an
exponential cutoff, a Miyamoto-Nagai disk and an NFW halo, normalised so the
three contribute 5%, 60% and 35% of the circular speed squared at R0 = 8 kpc with
v_c = 220 km/s. The halo may be scaled by `halo_scale`; the spec says which
value a problem uses, since that is what sets the escape speed.

Solar position and motion default to the astropy v4.0 values: R0 = 8.122 kpc,
z_sun = 20.8 pc, v_sun = (12.9, 245.6, 7.78) km/s.
"""

from __future__ import annotations

import math

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import gammainc, gamma

KPC_KM = 3.0856775814913673e16
KM_S_TO_KPC_MYR = 1.0227121650537077e-3  # km/s -> kpc/Myr
G_KPC_KMS2_MSUN = 4.30091727e-6  # kpc (km/s)^2 / Msun
MAS_YR_KM_S_PC = 4.740470463533348  # km/s per (mas/yr * kpc)

# ICRS -> Galactic (Hipparcos definition).
ICRS_TO_GAL = np.array([
    [-0.0548755604162154, -0.8734370902348850, -0.4838350155487132],
    [0.4941094278755837, -0.4448296299600112, 0.7469822444972189],
    [-0.8676661490190047, -0.1980763734312015, 0.4559837761750669],
])


class WitnessError(ValueError):
    pass


# ----------------------------------------------------------------- frames

def _rx(a):
    c, s = math.cos(a), math.sin(a)
    return np.array([[1, 0, 0], [0, c, s], [0, -s, c]])


def _ry(a):
    c, s = math.cos(a), math.sin(a)
    return np.array([[c, 0, -s], [0, 1, 0], [s, 0, c]])


def _rz(a):
    c, s = math.cos(a), math.sin(a)
    return np.array([[c, s, 0], [-s, c, 0], [0, 0, 1]])


# Sgr A* in ICRS, and the roll that puts the frame's z on the north Galactic
# pole: astropy's Galactocentric definition, reproduced so the numbers here are
# the numbers anyone with astropy gets.
GALCEN_RA_DEG = 266.4051
GALCEN_DEC_DEG = -28.936175
ROLL0_DEG = 58.5986320306


def galactocentric(ra_deg, dec_deg, dist_kpc, pmra, pmdec, rv, sun):
    """ICRS observables -> galactocentric Cartesian (kpc, km/s), vectorised over
    samples. The Sun sits at (-R0 cos(theta), 0, z_sun) with theta = asin(z_sun/R0),
    x points from the Sun through Sgr A*, y along Galactic rotation at the Sun,
    z toward the north Galactic pole."""
    ra = np.radians(ra_deg)
    dec = np.radians(dec_deg)
    cd, sd, cr, sr = np.cos(dec), np.sin(dec), np.cos(ra), np.sin(ra)
    unit = np.stack([cd * cr, cd * sr, sd], axis=-1)
    e_ra = np.stack([-sr, cr, np.zeros_like(sr)], axis=-1)
    e_dec = np.stack([-sd * cr, -sd * sr, cd], axis=-1)
    pos_icrs = unit * dist_kpc[..., None]
    vt_ra = MAS_YR_KM_S_PC * pmra * dist_kpc
    vt_dec = MAS_YR_KM_S_PC * pmdec * dist_kpc
    vel_icrs = unit * rv[..., None] + e_ra * vt_ra[..., None] + e_dec * vt_dec[..., None]
    R0, z0 = sun["R0_kpc"], sun["z_sun_kpc"]
    R = _rx(math.radians(ROLL0_DEG)) @ _ry(-math.radians(GALCEN_DEC_DEG)) @ _rz(math.radians(GALCEN_RA_DEG))
    H = _ry(-math.asin(z0 / R0))
    A = H @ R
    offset = -(H @ np.array([R0, 0.0, 0.0]))
    pos = pos_icrs @ A.T + offset
    vel = vel_icrs @ A.T + np.array(sun["v_sun_kms"])
    return pos, vel


# ----------------------------------------------------------------- potential

class MWPotential2014:
    def __init__(self, halo_scale: float = 1.0, R0: float = 8.0, vc: float = 220.0):
        self.R0, self.vc = R0, vc
        # Bulge: rho ~ (r1/r)^alpha exp(-(r/rc)^2), alpha = 1.8, rc = 1.9 kpc.
        self.alpha, self.rc = 1.8, 1.9
        # Disk: Miyamoto-Nagai a = 3 kpc, b = 0.28 kpc. Halo: NFW a = 16 kpc.
        self.a_d, self.b_d, self.a_h = 3.0, 0.28, 16.0
        vb2 = self._bulge_vc2(R0, 1.0)
        vd2 = self._disk_vc2(R0, 0.0, 1.0)
        vh2 = self._halo_vc2(R0, 1.0)
        self.amp_b = 0.05 * vc * vc / vb2
        self.amp_d = 0.60 * vc * vc / vd2
        self.amp_h = 0.35 * vc * vc / vh2 * halo_scale
        self.halo_scale = halo_scale

    # bulge, as enclosed mass and the outer integral, both via incomplete gamma.
    def _bulge_mass_terms(self, r):
        a, rc = self.alpha, self.rc
        k = (3 - a) / 2
        x = (r / rc) ** 2
        m_in = 0.5 * rc ** (3 - a) * gamma(k) * gammainc(k, x)  # ∫0^r r'^(2-a) e^{-x} dr'
        k2 = (2 - a) / 2
        m_out = 0.5 * rc ** (2 - a) * gamma(k2) * (1 - gammainc(k2, x))  # ∫r^∞ r'^(1-a) e^{-x} dr'
        return m_in, m_out

    def _bulge_vc2(self, r, amp):
        m_in, _ = self._bulge_mass_terms(r)
        return amp * m_in / r

    def _bulge_phi(self, r, amp):
        m_in, m_out = self._bulge_mass_terms(r)
        return -amp * (m_in / r + m_out)

    def _disk_phi(self, R, z, amp):
        return -amp / np.sqrt(R * R + (self.a_d + np.sqrt(z * z + self.b_d ** 2)) ** 2)

    def _disk_vc2(self, R, z, amp):
        s = self.a_d + np.sqrt(z * z + self.b_d ** 2)
        return amp * R * R / (R * R + s * s) ** 1.5

    def _halo_phi(self, r, amp):
        return -amp * np.log(1 + r / self.a_h) / r

    def _halo_vc2(self, r, amp):
        x = r / self.a_h
        return amp * (np.log(1 + x) - x / (1 + x)) / r

    def phi(self, pos):
        pos = np.asarray(pos, dtype=float)
        R = np.hypot(pos[..., 0], pos[..., 1])
        z = pos[..., 2]
        r = np.sqrt(R * R + z * z)
        return (self._bulge_phi(r, self.amp_b) + self._disk_phi(R, z, self.amp_d)
                + self._halo_phi(r, self.amp_h))

    def accel(self, pos):
        pos = np.asarray(pos, dtype=float)
        h = 1e-5
        g = np.zeros_like(pos)
        for k in range(3):
            dp = pos.copy(); dp[..., k] += h
            dm = pos.copy(); dm[..., k] -= h
            g[..., k] = -(self.phi(dp) - self.phi(dm)) / (2 * h)
        return g

    def v_esc(self, pos):
        return np.sqrt(np.maximum(-2 * self.phi(pos), 0.0))

    def v_circ(self, R):
        return math.sqrt(self._bulge_vc2(R, self.amp_b) + self._disk_vc2(R, 0.0, self.amp_d)
                         + self._halo_vc2(R, self.amp_h))


def integrate_back(pot: MWPotential2014, pos, vel, t_myr: float, n_out: int = 400):
    """Orbit backward for `t_myr`. Positions in kpc, velocities in km/s."""
    y0 = np.concatenate([pos, vel * KM_S_TO_KPC_MYR])

    def rhs(t, y):
        a = pot.accel(y[:3]) * KM_S_TO_KPC_MYR * KM_S_TO_KPC_MYR  # (km/s)^2/kpc -> kpc/Myr^2
        return np.concatenate([y[3:], a])

    ts = np.linspace(0, -t_myr, n_out)
    sol = solve_ivp(rhs, (0.0, -t_myr), y0, method="DOP853", rtol=1e-9, atol=1e-11, t_eval=ts)
    if not sol.success:
        raise RuntimeError(sol.message)
    return sol.t, sol.y[:3].T, sol.y[3:].T / KM_S_TO_KPC_MYR


# ----------------------------------------------------------------- witness

def read_star(doc: dict, spec: dict) -> dict:
    """The astrometry and spectroscopy of one star, with errors. Distance comes
    from a parallax only when it is measured well enough to invert; otherwise
    the witness states a distance and its error and says where it came from."""
    p = spec.get("params", {})
    out = {}

    def need(key, lo=None, hi=None):
        v = doc.get(key)
        if v is None or isinstance(v, bool) or not isinstance(v, (int, float)) or not math.isfinite(v):
            raise WitnessError(f"{key} must be a finite number")
        v = float(v)
        if lo is not None and v < lo or hi is not None and v > hi:
            raise WitnessError(f"{key} out of range")
        return v

    out["ra"] = need("ra_deg", 0, 360)
    out["dec"] = need("dec_deg", -90, 90)
    out["pmra"] = need("pmra_mas_yr", -5000, 5000)
    out["pmra_err"] = need("pmra_error_mas_yr", 0)
    out["pmdec"] = need("pmdec_mas_yr", -5000, 5000)
    out["pmdec_err"] = need("pmdec_error_mas_yr", 0)
    out["rv"] = need("rv_km_s", -5000, 5000)
    out["rv_err"] = need("rv_error_km_s", 0)
    rv_src = doc.get("rv_source")
    if not isinstance(rv_src, str) or not rv_src.strip():
        raise WitnessError("rv_source must say where the radial velocity comes from")
    out["rv_source"] = rv_src.strip()[:200]
    min_snr = float(p.get("min_parallax_snr", 5.0))
    if doc.get("distance_kpc") is not None:
        out["dist"] = need("distance_kpc", 0.001, 1000)
        out["dist_err"] = need("distance_error_kpc", 0)
        src = doc.get("distance_source")
        if not isinstance(src, str) or not src.strip():
            raise WitnessError("distance_source must say where the distance comes from")
        out["dist_source"] = src.strip()[:200]
        out["dist_kind"] = "stated"
    else:
        plx = need("parallax_mas")
        plx_err = need("parallax_error_mas", 0)
        if plx <= 0 or plx / max(plx_err, 1e-9) < min_snr:
            raise WitnessError(
                f"parallax is not measured well enough to invert (needs S/N >= {min_snr}); "
                "state distance_kpc, distance_error_kpc and distance_source instead"
            )
        out["plx"], out["plx_err"] = plx, plx_err
        out["dist_kind"] = "parallax"
    out["source_id"] = str(doc.get("source_id", "")).strip()
    return out


def sample(star: dict, n: int, rng: np.random.Generator):
    pmra = rng.normal(star["pmra"], star["pmra_err"], n)
    pmdec = rng.normal(star["pmdec"], star["pmdec_err"], n)
    rv = rng.normal(star["rv"], star["rv_err"], n)
    if star["dist_kind"] == "parallax":
        plx = rng.normal(star["plx"], star["plx_err"], n)
        plx = np.where(plx > 1e-3, plx, 1e-3)
        dist = 1.0 / plx
    else:
        dist = rng.normal(star["dist"], star["dist_err"], n)
        dist = np.where(dist > 1e-3, dist, 1e-3)
    ra = np.full(n, star["ra"])
    dec = np.full(n, star["dec"])
    return ra, dec, dist, pmra, pmdec, rv


def kinematics(star: dict, spec: dict, n: int | None = None, seed: int = 0) -> dict:
    """Monte Carlo over the errors: galactocentric state, escape speed, and the
    fraction of samples that are unbound, inbound, outbound."""
    p = spec.get("params", {})
    sun = p.get("sun", {"R0_kpc": 8.122, "z_sun_kpc": 0.0208, "v_sun_kms": [12.9, 245.6, 7.78]})
    pot = MWPotential2014(float(p.get("halo_scale", 1.5)))
    n = n or int(p.get("samples", 20000))
    rng = np.random.default_rng(seed)
    ra, dec, dist, pmra, pmdec, rv = sample(star, n, rng)
    pos, vel = galactocentric(ra, dec, dist, pmra, pmdec, rv, sun)
    r = np.linalg.norm(pos, axis=-1)
    speed = np.linalg.norm(vel, axis=-1)
    vesc = pot.v_esc(pos)
    v_r = np.einsum("ij,ij->i", pos, vel) / r
    unbound = speed > vesc
    inbound = v_r < 0
    # The median sample, as the point estimate a reader sees.
    med = np.argsort(speed - vesc)[n // 2]
    return {
        "potential": {"name": "MWPotential2014", "halo_scale": pot.halo_scale,
                      "v_esc_at_sun_km_s": float(pot.v_esc(np.array([-sun["R0_kpc"], 0.0, sun["z_sun_kpc"]]))),
                      "v_circ_at_R0_km_s": pot.v_circ(sun["R0_kpc"])},
        "sun": sun,
        "samples": n,
        "r_kpc": {"median": float(np.median(r)), "p16": float(np.percentile(r, 16)), "p84": float(np.percentile(r, 84))},
        "speed_km_s": {"median": float(np.median(speed)), "p16": float(np.percentile(speed, 16)), "p84": float(np.percentile(speed, 84))},
        "v_esc_km_s": {"median": float(np.median(vesc)), "p16": float(np.percentile(vesc, 16)), "p84": float(np.percentile(vesc, 84))},
        "v_r_km_s": {"median": float(np.median(v_r)), "p16": float(np.percentile(v_r, 16)), "p84": float(np.percentile(v_r, 84))},
        "p_unbound": float(unbound.mean()),
        "p_inbound": float(inbound.mean()),
        "p_outbound": float((~inbound).mean()),
        "p_unbound_and_inbound": float((unbound & inbound).mean()),
        "p_unbound_and_outbound": float((unbound & ~inbound).mean()),
        "_samples": {"pos": pos, "vel": vel, "unbound": unbound, "inbound": inbound, "median_index": int(med)},
        "_pot": pot,
    }


def origin_backward(kin: dict, spec: dict, n_orbits: int = 300, seed: int = 1) -> dict:
    """Integrate a subset of samples backward and ask where the star came from:
    did its path cross the disk away from the Galactic centre, and how close did
    it pass to the centre? Both as fractions over the subset."""
    p = spec.get("params", {})
    t_back = float(p.get("backtrack_myr", 150))
    z_disk = float(p.get("disk_half_thickness_kpc", 0.3))
    r_disk_max = float(p.get("disk_radius_max_kpc", 30.0))
    gc_min = float(p.get("gc_exclusion_kpc", 1.0))
    pot = kin["_pot"]
    S = kin["_samples"]
    rng = np.random.default_rng(seed)
    idx = rng.choice(len(S["pos"]), size=min(n_orbits, len(S["pos"])), replace=False)
    crossed = []
    gc_dist = []
    cross_t = []
    for i in idx:
        t, pos, _ = integrate_back(pot, S["pos"][i], S["vel"][i], t_back)
        R = np.hypot(pos[:, 0], pos[:, 1])
        in_disk = (np.abs(pos[:, 2]) < z_disk) & (R < r_disk_max)
        rmin = float(np.min(np.linalg.norm(pos, axis=1)))
        gc_dist.append(rmin)
        if in_disk.any():
            k = int(np.argmax(in_disk))
            crossed.append(True)
            cross_t.append(float(-t[k]))
        else:
            crossed.append(False)
    crossed = np.array(crossed)
    gc_dist = np.array(gc_dist)
    return {
        "backtrack_myr": t_back,
        "orbits": int(len(idx)),
        "p_disk_crossing": float(crossed.mean()),
        "p_avoids_gc": float((gc_dist > gc_min).mean()),
        "p_disk_crossing_and_avoids_gc": float((crossed & (gc_dist > gc_min)).mean()),
        "gc_closest_kpc": {"median": float(np.median(gc_dist)), "p16": float(np.percentile(gc_dist, 16)), "p84": float(np.percentile(gc_dist, 84))},
        "disk_crossing_myr_ago": (
            {"median": float(np.median(cross_t)), "p16": float(np.percentile(cross_t, 16)), "p84": float(np.percentile(cross_t, 84))}
            if cross_t else None
        ),
    }


def check_against_gaia(star: dict, gaia_path: str, spec: dict) -> dict:
    """The witness has to be the catalog row it names: position to the arcsecond,
    proper motions and parallax within tolerance of Gaia DR3. The radial velocity
    is Gaia's when Gaia has one; otherwise the witness's own, with its source."""
    import json
    p = spec.get("params", {})
    try:
        tab = json.load(open(gaia_path))
    except FileNotFoundError:
        raise WitnessError("source_id must name a Gaia DR3 source") from None
    names = [m["name"] for m in tab.get("metadata", [])]
    rows = tab.get("data", [])
    if not rows:
        raise WitnessError(f"Gaia DR3 has no source {star['source_id']}")
    row = dict(zip(names, rows[0]))
    sep = 3600 * math.hypot((row["ra"] - star["ra"]) * math.cos(math.radians(star["dec"])), row["dec"] - star["dec"])
    if sep > float(p.get("max_position_sep_arcsec", 2.0)):
        raise WitnessError(f"ra/dec are {sep:.1f} arcsec from Gaia DR3 source {star['source_id']}")
    tol = float(p.get("catalog_tolerance_sigma", 3.0))
    for key, gk in (("pmra", "pmra"), ("pmdec", "pmdec")):
        gv, ge = row.get(gk), row.get(gk + "_error")
        if gv is None:
            raise WitnessError(f"Gaia DR3 source {star['source_id']} has no {gk}")
        if abs(star[key] - gv) > tol * max(ge or 0.0, star[key + "_err"], 1e-6):
            raise WitnessError(f"{key} disagrees with Gaia DR3 ({gv} ± {ge})")
    if star["dist_kind"] == "parallax":
        gv, ge = row.get("parallax"), row.get("parallax_error")
        if gv is None or abs(star["plx"] - gv) > tol * max(ge or 0.0, star["plx_err"], 1e-6):
            raise WitnessError(f"parallax disagrees with Gaia DR3 ({gv} ± {ge})")
    rv_note = "witness"
    if row.get("radial_velocity") is not None:
        grv, gerr = row["radial_velocity"], row.get("radial_velocity_error") or 0.0
        if abs(star["rv"] - grv) > tol * max(gerr, star["rv_err"], 1e-6):
            raise WitnessError(f"rv disagrees with Gaia DR3 ({grv} ± {gerr})")
        rv_note = "gaia_dr3_consistent"
    return {"source_id": str(row["source_id"]), "g_mag": row.get("phot_g_mean_mag"), "ruwe": row.get("ruwe"),
            "position_sep_arcsec": sep, "rv_check": rv_note}
