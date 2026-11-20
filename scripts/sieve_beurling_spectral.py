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


# -----------------------------------------------------------------------------
# 2. Exact Generalized Chebyshev Step Function psi_P(x)
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
# 3. Forward Synthesis: Reconstruct Stepwise Curve from Beurling Zeros
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
# 4. Inverse Transform: Landau Spectral Scan + Iterative VarPro Refinement
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

    print(f"Primes <= {limit}: count = {len(p)}")
    print(f"Lucky <= {limit}: count = {len(lucky)}")
    print(f"Ludic <= {limit}: count = {len(ludic)}")
    print(f"Josephus <= {limit}: count = {len(josephus)}")

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
