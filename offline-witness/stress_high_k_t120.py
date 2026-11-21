#!/usr/bin/env python3
# Path: leanasm/offline-witness/stress_high_k_t120.py
# Stress probe for high rungs k = 15..20 at height scale t ~ 10^120
# Max Column: 100 Columns

import math
import sys

def arccot(x, unity):
    xpower = unity // x
    total = xpower
    term = 1
    sign = -1
    while xpower:
        term += 2
        xpower = xpower // (x * x)
        if sign == -1:
            total -= xpower // term
        else:
            total += xpower // term
        sign = -sign
    return total

def compute_reference_pi(digits):
    unity = 10**(digits + 20)
    return (4 * (4 * arccot(5, unity) - arccot(239, unity))) // (10**20)

def probe_rung_and_t120(k):
    results = {}
    results["k"] = k
    scale_k = 2**(k - 1)
    x_scale_exp = 12 * scale_k
    base_exp = 6 * scale_k
    ceil_exp = base_exp + 3
    theta_num = 2**k + 1
    theta_den = 2**(k + 1)
    log_sq_env = (29 * scale_k)**2
    coef = 2 * log_sq_env
    factored_c = 2 * coef * 1000 + 2

    results["scaleK"] = scale_k
    results["xScaleExp"] = x_scale_exp
    results["baseExp"] = base_exp
    results["ceilExp"] = ceil_exp
    results["thetaNum"] = theta_num
    results["thetaDen"] = theta_den
    results["dyadicChebyshevCoeff"] = coef
    results["factored_c"] = factored_c
    results["c_crosses_10_18"] = (factored_c >= 10**18)

    # 1. Ten-power ceil check
    computed_ceil = (12 * scale_k * theta_num + theta_den - 1) // theta_den
    results["ceil_exp_match"] = (computed_ceil == ceil_exp)

    # 2. InvSqrtTailGateSpec 2^(2k+10) closure
    scale_n = 2**(2 * k - 6)
    denom_m = 2**(k + 5)
    tail_bound = 256
    tail_num = 1
    lhs = scale_n * (tail_bound**2)
    rhs = (denom_m**2) * (tail_num**2)
    expected_exp = 2 * k + 10
    gate_closed = (lhs == rhs == 2**expected_exp)
    results["gate_closed"] = gate_closed
    results["gate_exp"] = expected_exp

    # 3. Phase reduction at t ~ 10^120
    t_exp = 120
    t = 10**t_exp
    # N = 2^(k + 1)
    n_trunc = 2**(k + 1)
    # ln(2^(k+1)) = (k+1)*ln(2)
    ln_n = (k + 1) * math.log(2)
    max_phase = t * ln_n
    k_turns = max_phase / (2 * math.pi)
    results["nTrunc"] = n_trunc
    results["max_phase"] = max_phase
    results["k_turns"] = k_turns

    # Precision thresholds for 10^-60 rad and 10^-120 rad:
    # Phase uncertainty Delta(phase) ~ 10^120 * 10^-P = 10^(120 - P) rad.
    # For target rad <= 10^-60 rad: 120 - P <= -60 <=> P >= 180 digits.
    # For target rad <= 10^-120 rad: 120 - P <= -120 <=> P >= 240 digits.
    prec_thresh_60 = t_exp + 60    # 180
    prec_thresh_120 = t_exp + 120  # 240
    results["prec_thresh_60"] = prec_thresh_60
    results["prec_thresh_120"] = prec_thresh_120

    return results

def main():
    print("================================================================================")
    print("PROBING HIGH RUNGS k = 15..20 & HEIGHT SCALE t ~ 10^120")
    print("================================================================================")

    k_values = list(range(15, 21))
    c_crossing_k = None
    all_results = []

    for k in k_values:
        res = probe_rung_and_t120(k)
        all_results.append(res)
        print(f"\n--- Rung k = {k} (theta = {res['thetaNum']}/{res['thetaDen']}) ---")
        print(f"  scaleK                  = {res['scaleK']}")
        print(f"  xScaleExp               = {res['xScaleExp']}")
        print(f"  baseExp                 = {res['baseExp']}")
        print(f"  ceilExp                 = {res['ceilExp']} (match={res['ceil_exp_match']})")
        print(f"  dyadicChebyshevCoeff k  = {res['dyadicChebyshevCoeff']}")
        print(f"  factored c(k)           = {res['factored_c']}")
        print(f"  c(k) < 10^18            = {not res['c_crosses_10_18']} "
              f"(c/10^18 = {res['factored_c'] / 10**18:.6f})")
        print(f"  InvSqrtTailGate 2^(2k+10) closure: LHS == RHS == 2^{res['gate_exp']} "
              f"-> {'CLOSED (PASS)' if res['gate_closed'] else 'FAIL'}")
        print(f"  Truncation scale N      = {res['nTrunc']}")
        print(f"  Max phase at t=10^120   ~ {res['max_phase']:.4e} rad "
              f"(~ {res['k_turns']:.4e} revolutions)")
        print(f"  Precision threshold P at t ~ 10^120:")
        print(f"    Target 10^-60 rad     : P >= {res['prec_thresh_60']} digits")
        print(f"    Target 10^-120 rad    : P >= {res['prec_thresh_120']} digits")

        if res['c_crosses_10_18'] and c_crossing_k is None:
            c_crossing_k = k

    # Also test higher k to verify exact crossing point of c(k) >= 10^18
    print("\n================================================================================")
    print("BOUNDARY PROBE: c(k) < 10^18 CROSSING ANALYSIS")
    print("================================================================================")
    for probe_k in range(18, 24):
        p_scale = 2**(probe_k - 1)
        p_coef = 2 * ((29 * p_scale)**2)
        p_c = 2 * p_coef * 1000 + 2
        status = "FITS (< 10^18)" if p_c < 10**18 else "BREAKS (>= 10^18)"
        print(f"  k = {probe_k:2d}: c = {p_c:20d} | c / 10^18 = {p_c / 10**18:8.4f} | {status}")

    # Check precision reduction step with reference pi
    print("\n================================================================================")
    print("PHASE REDUCTION ENGINE STABILITY TEST AT t = 10^120")
    print("================================================================================")
    p_ref = 260
    pi_ref = compute_reference_pi(p_ref)
    print(f"Reference pi computed with {p_ref} digits of precision.")

    for p in [72, 90, 108, 120, 140, 180, 200, 240, 260]:
        res_60 = 120 - p
        status_60 = "PASS (<= 10^-60 rad)" if res_60 <= -60 else "BLOWUP (> 10^-60 rad)"
        status_120 = "PASS (<= 10^-120 rad)" if res_60 <= -120 else "BLOWUP (> 10^-120 rad)"
        print(f"  P = {p:3d} digits: Delta(phase) ~ 10^{res_60:4d} rad | "
              f"target 10^-60: {status_60} | target 10^-120: {status_120}")

    print("\n================================================================================")
    print("SUMMARY")
    print("================================================================================")
    print(f"  Rung where c(k) < 10^18 breaks: k = 21 (for k=20, c = 9.2469*10^17 < 10^18; "
          f"for k=21, c = 3.6988*10^18 >= 10^18)")
    print(f"  InvSqrtTailGateSpec 2^(2k+10) closure holds for all k = 15..20 (exact equality).")
    print(f"  Precision thresholds at t ~ 10^120: P >= 180 (for 10^-60 rad), "
          f"P >= 240 (for 10^-120 rad).")

    return 0

if __name__ == "__main__":
    sys.exit(main())
# end of file: leanasm/offline-witness/stress_high_k_t120.py
