#!/usr/bin/env python3
# Path: leanasm/offline-witness/check_rung10.py
# Verify candidate rung k = 10 (1025/2048) parameters for QuasiRiemann
# Max Column: 100 Columns

import sys

def main():
    k = 10
    print(f"=== QuasiRiemann Ladder Rung k = {k} Verification ===")

    # 1. Candidate Exponent: θ(k) = (2^k + 1) / 2^(k + 1)
    theta_num = 2**k + 1
    theta_den = 2**(k + 1)
    print(f"Exponent θ({k}): {theta_num}/{theta_den}")
    assert theta_num == 1025
    assert theta_den == 2048
    assert theta_num < theta_den

    # Strict monotonicity against k = 9 (513/1024) and k = 7 (129/256)
    # θ(10) < θ(9): 1025/2048 < 513/1024 <=> 1025 < 1026
    assert theta_num * 1024 < 513 * theta_den
    # θ(10) > 1/2: 1025/2048 > 1/2 <=> 1025 * 2 > 2048 <=> 2050 > 2048
    assert theta_num * 2 > theta_den

    # 2. Scale and Log-Square Envelope
    scale_k = 2**(k - 1)  # 512
    x_scale_exp = 12 * scale_k  # 6144
    assert scale_k == 512
    assert x_scale_exp == 6144

    # tenPowThetaCeilExp scaleK θ = ⌈(12 * scaleK * thetaNum) / thetaDen⌉
    # (12 * 512 * 1025 + 2048 - 1) // 2048 = (6297600 + 2047) // 2048 = 3075
    ceil_exp = (12 * scale_k * theta_num + theta_den - 1) // theta_den
    print(f"scaleK: {scale_k}, xScaleExp: {x_scale_exp}, tenPowThetaCeilExp: {ceil_exp}")
    assert ceil_exp == 3075

    # chebyshevLogSqEnv scaleK = (29 * scaleK)^2
    # 29 * 512 = 14848, 14848^2 = 220463104
    # coef = 2 * prefactor * (29 * scaleK)^2 = 2 * 1 * 220463104 = 440926208
    log_sq_env = (29 * scale_k)**2
    coef = 2 * 1 * log_sq_env
    assert log_sq_env == 220463104
    assert coef == 440926208
    print(f"chebyshevLogSqEnv: {log_sq_env}, coef (errUpper factor): {coef}")

    # Prime-power correction: 2 * 10^(xScaleExp / 2) = 2 * 10^3072
    base_exp = x_scale_exp // 2  # 3072
    assert base_exp == 3072
    print(f"Base exponent (primePowerCorr / factored 10^a): {base_exp}")

    # 3. Factored 10^a Short-Interval Verification
    # errUpper = coef * 10^ceil_exp = 440926208 * 10^3075
    # primePowerCorr = 2 * 10^3072
    # Notice: 10^3075 = 10^(3 + 3072) = 10^3 * 10^3072 = 1000 * 10^3072
    # 2 * errUpper + primePowerCorr = (2 * coef * 1000 + 2) * 10^3072
    # 2 * 440926208 * 1000 + 2 = 881852416000 + 2 = 881852416002
    factored_c = 2 * coef * 1000 + 2
    assert factored_c == 881852416002
    print(f"Factored coefficient c for 2 * errUpper + primePowerCorr: {factored_c}")

    # Factored gap exponent eGap:
    # We require c < 10^eGap.
    # Since 881852416002 < 10^12 = 1000000000000:
    # eGap = 12 suffices! (Or eGap = 18 as used in k=7, 8).
    # With eGap = 18, hScaleExp = eGap + baseExp = 18 + 3072 = 3090.
    # Notice: 3090 < 6144 (hScaleExp <= xScaleExp).
    e_gap_12 = 12
    e_gap_18 = 18
    assert factored_c < 10**e_gap_12
    assert factored_c < 10**e_gap_18

    h_scale_exp = e_gap_18 + base_exp
    assert h_scale_exp == 3090
    print(f"With eGap = 18, hScaleExp = {h_scale_exp} (xScaleExp = {x_scale_exp})")
    assert h_scale_exp <= x_scale_exp

    # ShortIntervalChebyshevSpec.HasGuaranteedPrime:
    # 2 * errUpper + primePowerCorr < 10^hScaleExp
    # By pow_ten_factor_lt_mvb: factored_c * 10^3072 < 10^(18 + 3072)
    # The decide tactic in Lean evaluates `factored_c < 10^18`,
    # which is purely bounded on small integers without materializing 10^3072!
    print("ShortIntervalChebyshevSpec.HasGuaranteedPrime check PASSED (factored)")

    # 4. Cleared-Denominator InvSqrtTailGateSpec Bounds
    # At k = 10: denomM = 32768, scaleN = 16384, tailBound = 256, tailNum = 1
    # Condition: scaleN * tailBound^2 <= denomM^2 * tailNum^2
    # 16384 * 256^2 = 16384 * 65536 = 1073741824
    # 32768^2 * 1^2 = 1073741824
    # Equality holds exactly!
    scale_n = 16384
    denom_m = 32768
    tail_bound = 256
    tail_num = 1
    lhs = scale_n * (tail_bound**2)
    rhs = (denom_m**2) * (tail_num**2)
    assert lhs == rhs == 1073741824
    assert scale_n > 0 and denom_m > 0
    print(f"InvSqrtTailGateSpec: scaleN={scale_n}, denomM={denom_m}, lhs={lhs}, rhs={rhs}")
    print("InvSqrtTailGateSpec check PASSED")

    # Dyadic preservation step check:
    # (4 * scaleN) * tailBound^2 <= ((2 * denomM)^2) * tailNum^2
    lhs_step = (4 * scale_n) * (tail_bound**2)
    rhs_step = ((2 * denom_m)**2) * (tail_num**2)
    assert lhs_step == rhs_step == 4 * 1073741824
    print("inv_sqrt_tail_gate_dyadic_step check PASSED")

    print("\nAll candidate rung k = 10 offline checks successfully verified!")
    return 0

if __name__ == "__main__":
    sys.exit(main())
# end of file: leanasm/offline-witness/check_rung10.py
