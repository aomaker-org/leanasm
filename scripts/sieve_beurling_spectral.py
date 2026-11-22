# Path: leanasm/scripts/sieve_beurling_spectral.py
# Generalized Prime and Lucky-like Sieve Sequences and Beurling Spectral Operators
# End-to-end reference implementation for forward synthesis and inverse Landau/VarPro estimation.
# Max Column: 120 Columns

import fractions
import numpy as np
from scipy.optimize import least_squares
from scipy.signal import find_peaks


# -----------------------------------------------------------------------------
# 1. Sequence Generators (dropping 1 so l_1 > 1 for Beurling Euler products)
# -----------------------------------------------------------------------------

def generate_primes(limit: int) -> np.ndarray:
    """Generate prime generators <= limit using value-based congruence sieve."""
    if limit < 2:
        return np.array([], dtype=np.int64)
    sieve = np.ones(limit + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    return np.nonzero(sieve)[0]


def generate_lucky(limit: int) -> np.ndarray:
    """Generate Lucky number generators <= limit (A000959, dropping 1)."""
    arr = np.arange(1, limit + 1, 2, dtype=np.int64)
    idx = 1
    while idx < len(arr) and arr[idx] <= len(arr):
        step = arr[idx]
        keep = np.ones(len(arr), dtype=bool)
        keep[step - 1 :: step] = False
        arr = arr[keep]
        idx += 1
    return arr[arr > 1]


def generate_ludic(limit: int) -> np.ndarray:
    """Generate Ludic number generators <= limit (A003309)."""
    pool = list(range(2, limit + 1))
    ludics = []
    while pool:
        step = pool[0]
        ludics.append(step)
        pool = [x for i, x in enumerate(pool[1:], 1) if i % step != 0]
    return np.array(ludics, dtype=np.int64)


def generate_josephus(limit: int) -> np.ndarray:
    """Generate Josephus sieve generators <= limit (A000960, dropping 1)."""
    arr = np.arange(1, limit + 1, dtype=np.int64)
    k = 2
    while k <= len(arr):
        keep = np.ones(len(arr), dtype=bool)
        keep[k - 1 :: k] = False
        arr = arr[keep]
        k += 1
    return arr[arr > 1]


def generate_hawkins(limit: int, seed: int = 42) -> np.ndarray:
    """Generate Hawkins random sieve generators <= limit.

    Stochastic sieve where survivor x eliminates subsequent y > x with probability 1/x.
    """
    if limit < 2:
        return np.array([], dtype=np.int64)
    rng = np.random.default_rng(seed)
    seq = list(range(2, limit + 1))
    idx = 0
    while idx < len(seq):
        x = seq[idx]
        prob = 1.0 / float(x)
        survivors = seq[: idx + 1]
        for y in seq[idx + 1 :]:
            if rng.random() >= prob:
                survivors.append(y)
        seq = survivors
        idx += 1
    return np.array(seq, dtype=np.int64)


def generate_ulam(limit: int) -> np.ndarray:
    """Generate Ulam numbers <= limit (A002858, dropping 1).

    Smallest integer > U_{n-1} with unique representation as sum of two earlier elements.
    """
    if limit < 2:
        return np.array([], dtype=np.int64)
    ulam = [1, 2]
    cand = 3
    while cand <= limit:
        count = 0
        for i in range(len(ulam)):
            if ulam[i] * 2 >= cand:
                break
            for j in range(i + 1, len(ulam)):
                if ulam[i] + ulam[j] == cand:
                    count += 1
                    if count > 1:
                        break
            if count > 1:
                break
        if count == 1:
            ulam.append(cand)
        cand += 1
    return np.array([x for x in ulam if x > 1], dtype=np.int64)


# -----------------------------------------------------------------------------
# 2. Exact Generalized Chebyshev Step Function psi_P(x) and Prime Powers
# -----------------------------------------------------------------------------

def build_von_mangoldt_jumps(seq: np.ndarray, x_max: int) -> tuple[np.ndarray, np.ndarray]:
    """Return sorted jump positions n = l^m <= x_max and weights Lambda_P(n) = ln(l)."""
    positions = []
    weights = []
    for l in seq:
        ln_l = np.log(float(l))
        val = int(l)
        while val <= x_max:
            positions.append(val)
            weights.append(ln_l)
            val *= int(l)
    order = np.argsort(positions)
    return np.array(positions, dtype=np.float64)[order], np.array(weights, dtype=np.float64)[order]


def evaluate_chebyshev_step(x_grid: np.ndarray, jump_pos: np.ndarray, jump_weights: np.ndarray) -> np.ndarray:
    """Evaluate exact stepwise psi_P(x) = sum_{l^m <= x} ln(l) on x_grid."""
    idx = np.searchsorted(jump_pos, x_grid, side="right")
    cum_weights = np.concatenate(([0.0], np.cumsum(jump_weights)))
    return cum_weights[idx]


# -----------------------------------------------------------------------------
# 3. Partial Euler Product Z_X(s) and Log-Derivative Dirichlet Polynomial F_X(s)
# -----------------------------------------------------------------------------

def partial_euler_product_Z(s: complex, seq: np.ndarray, cutoff: int) -> complex:
    """Evaluate partial Euler product Z_X(s) = prod_{l <= X} (1 - l^{-s})^{-1}."""
    gens = seq[seq <= cutoff]
    if len(gens) == 0:
        return 1.0 + 0.0j
    terms = 1.0 / (1.0 - gens.astype(np.complex128) ** (-s))
    return np.prod(terms)


def log_derivative_dirichlet_F(s: complex, seq: np.ndarray, cutoff: int) -> complex:
    """Evaluate log-derivative Dirichlet polynomial F_X(s) = -Z_X'(s)/Z_X(s) = sum_{l^m <= X} ln(l)/l^{ms}."""
    gens = seq[seq <= cutoff]
    val = 0.0 + 0.0j
    for l in gens:
        ln_l = np.log(float(l))
        lm = float(l)
        while lm <= cutoff:
            val += ln_l / (lm**s)
            lm *= float(l)
    return val


def log_derivative_euler_Z(s: complex, seq: np.ndarray, cutoff: int) -> complex:
    """Evaluate exact logarithmic derivative Z_X'(s)/Z_X(s) = - sum_{l <= X} ln(l) / (l^s - 1)."""
    gens = seq[seq <= cutoff].astype(np.complex128)
    if len(gens) == 0:
        return 0.0 + 0.0j
    ln_l = np.log(gens.real)
    return -np.sum(ln_l / (gens**s - 1.0))


def contour_winding_integration(
    seq: np.ndarray,
    cutoff: int,
    sigma_min: float,
    sigma_max: float,
    T1: float,
    T2: float,
    n_pts: int = 400,
) -> complex:
    """Compute (1 / 2pi i) oint_{dR} (Z_X'(s) / Z_X(s)) ds over rectangle [sigma_min, sigma_max] x [T1, T2]."""
    def integrate_segment(s_start: complex, s_end: complex) -> complex:
        ts = np.linspace(0.0, 1.0, n_pts)
        pts = s_start + ts * (s_end - s_start)
        vals = np.array([log_derivative_euler_Z(s, seq, cutoff) for s in pts])
        dt = (s_end - s_start) / (n_pts - 1)
        return (0.5 * (vals[0] + vals[-1]) + np.sum(vals[1:-1])) * dt

    c1 = integrate_segment(sigma_min + 1j * T1, sigma_max + 1j * T1)
    c2 = integrate_segment(sigma_max + 1j * T1, sigma_max + 1j * T2)
    c3 = integrate_segment(sigma_max + 1j * T2, sigma_min + 1j * T2)
    c4 = integrate_segment(sigma_min + 1j * T2, sigma_min + 1j * T1)
    return (c1 + c2 + c3 + c4) / (2.0 * np.pi * 1j)


def newton_polish_inv_F(
    s_init: complex,
    seq: np.ndarray,
    cutoff: int,
    max_iter: int = 50,
    tol: float = 1e-10,
) -> complex:
    """Polish root of 1 / F_X(s) = 0 using Newton-Raphson iterations."""
    gens = seq[seq <= cutoff]
    s = s_init
    for _ in range(max_iter):
        F = 0.0 + 0.0j
        F_prime = 0.0 + 0.0j
        for l in gens:
            ln_l = np.log(float(l))
            lm = float(l)
            while lm <= cutoff:
                term = ln_l / (lm**s)
                F += term
                F_prime += -ln_l * np.log(lm) / (lm**s)
                lm *= float(l)
        if abs(F) == 0.0:
            break
        g = 1.0 / F
        if abs(g) < tol:
            break
        step = F / F_prime
        s = s + step
        if abs(step) < tol:
            break
    return s


# -----------------------------------------------------------------------------
# 4. Forward Synthesis: Reconstruct Stepwise Curve from Beurling Zeros
# -----------------------------------------------------------------------------

def synthesize_chebyshev_from_zeros(
    x_grid: np.ndarray,
    rhos: np.ndarray,
    s0: float = 1.0,
    a0: float = 1.0,
    c0: float = 0.0,
) -> np.ndarray:
    """Compute psi_{P, K}(x) = a0 * x^s0 - sum_k 2 * Re(x^rho_k / rho_k) - c0."""
    u = np.log(x_grid)
    baseline = a0 * np.exp(s0 * u) - c0
    oscillations = np.sum(2.0 * np.real(np.exp(np.outer(u, rhos)) / rhos[None, :]), axis=1)
    return baseline - oscillations


# -----------------------------------------------------------------------------
# 5. Inverse Transform: Landau Spectral Scan + Iterative VarPro Refinement
# -----------------------------------------------------------------------------

def landau_inverse_spectrum(
    jump_pos: np.ndarray,
    jump_weights: np.ndarray,
    sigma: float,
    omegas: np.ndarray,
) -> np.ndarray:
    """Compute -sum_{n <= X} Lambda_P(n) * n^(-sigma - i*omega)."""
    u_jumps = np.log(jump_pos)
    amps = jump_weights * np.exp(-sigma * u_jumps)
    return -(np.exp(-1j * np.outer(omegas, u_jumps)) @ amps)


def extract_and_refine_zeros(
    jump_pos: np.ndarray,
    jump_weights: np.ndarray,
    x_max: int,
    num_zeros: int = 12,
    s0: float = 1.0,
    sigma_init: float = 0.5,
) -> tuple[np.ndarray, float]:
    """Estimate initial zeros via Landau scan, fit baseline a0, and refine via VarPro."""
    u_grid = np.linspace(np.log(2.0), np.log(float(x_max)), 2000)
    x_grid = np.exp(u_grid)
    psi_true = evaluate_chebyshev_step(x_grid, jump_pos, jump_weights)

    # Fit smooth baseline amplitude a0 * x^s0
    basis = np.exp(s0 * u_grid)
    a0 = float(np.dot(psi_true, basis) / np.dot(basis, basis))
    residual_target = a0 * basis - psi_true

    # Seed frequencies via Landau spectrum peaks
    omegas = np.linspace(1.0, 60.0, 6000)
    spec = np.abs(landau_inverse_spectrum(jump_pos, jump_weights, sigma_init, omegas))
    peaks, _ = find_peaks(spec, distance=15)
    top_peaks = peaks[np.argsort(spec[peaks])[::-1][:num_zeros]]
    gamma_init = np.sort(omegas[top_peaks])
    rhos_init = sigma_init + 1j * gamma_init

    # Iterative nonlinear least-squares polish on (beta_k, gamma_k)
    def residual_fn(params: np.ndarray) -> np.ndarray:
        half = len(params) // 2
        rhos = params[:half] + 1j * params[half:]
        pred = np.sum(2.0 * np.real(np.exp(np.outer(u_grid, rhos)) / rhos[None, :]), axis=1)
        return pred - residual_target

    p0 = np.concatenate([rhos_init.real, rhos_init.imag])
    bounds_low = np.concatenate([np.full(num_zeros, 0.05), np.full(num_zeros, 0.5)])
    bounds_high = np.concatenate([np.full(num_zeros, s0 - 0.01), np.full(num_zeros, 80.0)])
    sol = least_squares(residual_fn, p0, bounds=(bounds_low, bounds_high), xtol=1e-10, ftol=1e-10)
    half = len(sol.x) // 2
    refined_rhos = sol.x[:half] + 1j * sol.x[half:]
    return refined_rhos[np.argsort(refined_rhos.imag)], a0


def main():
    print("Testing Sieve Sequences and Beurling Operators...")
    limit = 200
    p = generate_primes(limit)
    lucky = generate_lucky(limit)
    ludic = generate_ludic(limit)
    josephus = generate_josephus(limit)
    hawkins = generate_hawkins(limit, seed=42)
    ulam = generate_ulam(limit)

    print(f"Primes <= {limit}: count = {len(p)}")
    print(f"Lucky <= {limit}: count = {len(lucky)}")
    print(f"Ludic <= {limit}: count = {len(ludic)}")
    print(f"Josephus <= {limit}: count = {len(josephus)}")
    print(f"Hawkins (seed=42) <= {limit}: count = {len(hawkins)}, expected ~ {limit / np.log(limit):.1f}")
    print(f"Ulam <= {limit}: count = {len(ulam)}, expected ~ {limit / 13.517:.1f}")

    # Partial Euler Product and Log-Derivative Dirichlet Polynomial
    cutoff = 50
    s_test = 2.0 + 0.0j
    z_val = partial_euler_product_Z(s_test, ulam, cutoff)
    f_val = log_derivative_dirichlet_F(s_test, ulam, cutoff)
    print(f"Ulam Z_{cutoff}(2.0) = {z_val:.6f}")
    print(f"Ulam F_{cutoff}(2.0) = {f_val:.6f}")

    # Argument Principle Contour Winding Integration
    winding = contour_winding_integration(ulam, cutoff, 0.2, 0.8, 10.0, 20.0)
    print(f"Contour winding in [0.2, 0.8] x [10, 20]: {winding.real:.4f} + {winding.imag:.4f}i")

    # Newton Root Polishing on 1 / F_X(s) = 0
    s_root = newton_polish_inv_F(0.5 + 14.0j, ulam, cutoff)
    inv_f_val = 1.0 / log_derivative_dirichlet_F(s_root, ulam, cutoff)
    print(f"Newton polished root: s = {s_root.real:.4f} + {s_root.imag:.4f}i, |1/F(s)| = {abs(inv_f_val):.2e}")

    jumps, weights = build_von_mangoldt_jumps(lucky, 100)
    print(f"Lucky von Mangoldt jumps <= 100: count = {len(jumps)}")
    rhos, a0 = extract_and_refine_zeros(jumps, weights, 100, num_zeros=6, s0=1.0)
    print(f"Fitted baseline a0 = {a0:.4f}")
    print("Top refined Beurling pseudo-zeros:")
    for i, r in enumerate(rhos):
        print(f"  rho_{i+1} = {r.real:.4f} + {r.imag:.4f}i")


if __name__ == "__main__":
    main()

# end of file: leanasm/scripts/sieve_beurling_spectral.py
