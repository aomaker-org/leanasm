-- Path: leanasm/src/LeanAsm/EulerFactorNonVanishing.lean
-- Local prime-tower Euler factor non-vanishing bounds for RNS moduli {7, 11, 13}.
-- Bridges RnsArithmetic and QuasiRiemann with ZERO axioms.
-- Max Column: 100 Columns

import LeanAsm.RnsArithmetic

namespace EulerFactorNonVanishing

open RnsArithmetic

/--
Exact margin numerator for local Euler factor at rational real part σ = num / den:
Since 1 - p^(-num/den) > 0 ↔ p^(num/den) > 1 ↔ p^num > 1,
the margin quantity is p^num - 1.
-/
def eulerFactorMargin (p num : Nat) : Nat :=
  p ^ num - 1

/--
Joint margin numerator for partial Euler product over the RNS prime tower {7, 11, 13}.
-/
def partialEulerProductMargin (num : Nat) : Nat :=
  (eulerFactorMargin m1 num) * (eulerFactorMargin m2 num) * (eulerFactorMargin m3 num)

/--
Theorem (Prime Power Strictly Greater Than One):
For any prime or base p ≥ 2 and exponent num ≥ 1, p^num > 1.
Proved constructively with ZERO axioms.
-/
theorem prime_power_gt_one (p num : Nat) (hp : 2 ≤ p) (hnum : 1 ≤ num) :
    1 < p ^ num := by
  induction num with
  | zero => contradiction
  | succ n ih =>
    cases n with
    | zero =>
      change 1 < 1 * p
      cases p with
      | zero => contradiction
      | succ p =>
        cases p with
        | zero => contradiction
        | succ p =>
          exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
    | succ n =>
      have ih' := ih (Nat.succ_le_succ (Nat.zero_le _))
      have hsucc : p ^ (n + 1 + 1) = p ^ (n + 1) * p := rfl
      show 1 < p ^ (n + 1 + 1)
      have hmul : 1 < p ^ (n + 1) * p :=
        Nat.lt_of_lt_of_le ih' (Nat.le_mul_of_pos_right _ (Nat.lt_of_lt_of_le (Nat.succ_le_succ (Nat.zero_le _)) hp))
      exact hmul

/--
Theorem (Local Euler Factor Non-Vanishing):
For any base p ≥ 2 and exponent num ≥ 1, the local Euler factor margin is strictly positive.
Proved constructively with ZERO axioms.
-/
theorem local_euler_factor_nonvanishing (p num : Nat) (hp : 2 ≤ p) (hnum : 1 ≤ num) :
    0 < eulerFactorMargin p num := by
  dsimp [eulerFactorMargin]
  have hgt := prime_power_gt_one p num hp hnum
  cases h : p ^ num with
  | zero =>
    have : 1 < 0 := by rw [h] at hgt; exact hgt
    contradiction
  | succ val =>
    cases val with
    | zero =>
      have : 1 < 1 := by rw [h] at hgt; exact hgt
      contradiction
    | succ val' =>
      change 0 < val' + 1
      exact Nat.succ_le_succ (Nat.zero_le _)

/--
Theorem (RNS Prime Tower Euler Factors Non-Vanishing):
All local Euler factors for the RNS prime tower {7, 11, 13} are strictly positive for σ > 0.
Proved constructively with ZERO axioms.
-/
theorem rns_prime_tower_euler_nonvanishing (num : Nat) (hnum : 1 ≤ num) :
    0 < eulerFactorMargin 7 num ∧
    0 < eulerFactorMargin 11 num ∧
    0 < eulerFactorMargin 13 num := by
  refine ⟨local_euler_factor_nonvanishing 7 num (by decide) hnum,
          local_euler_factor_nonvanishing 11 num (by decide) hnum,
          local_euler_factor_nonvanishing 13 num (by decide) hnum⟩

/--
Theorem (Partial Euler Product Non-Vanishing):
The partial Euler product margin ∏_{p ∈ {7,11,13}} (p^num - 1) is strictly positive for any num ≥ 1.
Shows that zeros of ζ(s) cannot arise from the finite RNS prime tower.
Proved constructively with ZERO axioms.
-/
theorem partial_euler_product_nonvanishing (num : Nat) (hnum : 1 ≤ num) :
    0 < partialEulerProductMargin num := by
  dsimp [partialEulerProductMargin]
  have ⟨h7, h11, h13⟩ := rns_prime_tower_euler_nonvanishing num hnum
  have h7_11 : 0 < eulerFactorMargin 7 num * eulerFactorMargin 11 num := Nat.mul_pos h7 h11
  exact Nat.mul_pos h7_11 h13

/--
Theorem (QRH 7/8 Euler Factor Margins):
At the QRH threshold σ = 7/8 (represented by num = 7), the concrete margins are strictly positive:
  7^7 - 1 = 823542 > 0
  11^7 - 1 = 19487170 > 0
  13^7 - 1 = 62748516 > 0
Proved constructively with ZERO axioms.
-/
theorem qrh_seven_eighths_euler_margins :
    eulerFactorMargin 7 7 = 823542 ∧
    0 < eulerFactorMargin 7 7 ∧
    eulerFactorMargin 11 7 = 19487170 ∧
    0 < eulerFactorMargin 11 7 ∧
    eulerFactorMargin 13 7 = 62748516 ∧
    0 < eulerFactorMargin 13 7 ∧
    0 < partialEulerProductMargin 7 := by
  decide

-- =============================================================================
-- Parametric List-Based Euler Product Non-Vanishing (gemweb018)
-- =============================================================================

/-- Margin for an arbitrary prime-tower list ps: ∏_{p ∈ ps} (p^num - 1). -/
def listEulerProductMargin (ps : List Nat) (num : Nat) : Nat :=
  match ps with
  | [] => 1
  | p :: rest => (eulerFactorMargin p num) * (listEulerProductMargin rest num)

/--
Theorem: For any prime-tower list ps where every element p ≥ 2,
the generalized partial Euler product margin is strictly positive for num ≥ 1.
Proved constructively with ZERO axioms via structural induction on ps.
-/
theorem list_euler_product_nonvanishing (ps : List Nat) (num : Nat)
    (hps : ∀ p ∈ ps, 2 ≤ p) (hnum : 1 ≤ num) :
    0 < listEulerProductMargin ps num := by
  induction ps with
  | nil =>
    dsimp [listEulerProductMargin]
    exact Nat.succ_le_succ (Nat.zero_le _)
  | cons p rest ih =>
    dsimp [listEulerProductMargin]
    have hp_in : p ∈ p :: rest := List.Mem.head _
    have hp : 2 ≤ p := hps p hp_in
    have hp_margin : 0 < eulerFactorMargin p num :=
      local_euler_factor_nonvanishing p num hp hnum
    have hrest_ps : ∀ q ∈ rest, 2 ≤ q := by
      intro q hq
      exact hps q (List.Mem.tail p hq)
    have hrest_margin : 0 < listEulerProductMargin rest num := ih hrest_ps
    exact Nat.mul_pos hp_margin hrest_margin

/-- Concrete check for Fermat prime tower [3, 5, 17, 257, 65537] at σ = 1/2 (num = 1). -/
theorem fermat_tower_euler_nonvanishing_concrete :
    0 < listEulerProductMargin [3, 5, 17, 257, 65537] 1 := by
  decide

-- =============================================================================
-- Fermat-Prime Tower {5, 17, 257, 65537} Critical-Strip Non-Vanishing (Issue #28)
-- =============================================================================

/-- Fermat number `F_k = 2^(2^k) + 1`. -/
def fermatNumber (k : Nat) : Nat :=
  2 ^ (2 ^ k) + 1

/-- Prefix product `∏_{k=0}^{n-1} F_k` of Fermat numbers. -/
def fermatPrefixProd : Nat → Nat
  | 0 => 1
  | n + 1 => fermatPrefixProd n * fermatNumber n

/-- Constructive Fermat-prime CRT-NTT tower `{5, 17, 257, 65537}` (`F_1..F_4`),
matching `{5, 17}` in `CrtNtt` and `{17, 257, 65537}` in `CrtNttUniversal`. -/
def fermatTowerPrimes : List Nat :=
  [5, 17, 257, 65537]

/-- Full 32-bit Fermat-prime factorization `[3, 5, 17, 257, 65537]` (`F_0..F_4`). -/
def fermatAllPrimes : List Nat :=
  [3, 5, 17, 257, 65537]

private theorem pred_mul_succ_eq_sq_sub_one (a : Nat) (ha : 1 ≤ a) :
    (a - 1) * (a + 1) = a * a - 1 := by
  cases a with
  | zero => contradiction
  | succ b =>
    have h1 : b + 1 - 1 = b := by omega
    have h2 : b + 1 + 1 = b + 2 := by omega
    have h3 : (b + 1) * (b + 1) = b * b + 2 * b + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    have h4 : b * (b + 2) = b * b + 2 * b := by
      rw [Nat.mul_add, Nat.mul_comm b 2]
    rw [h1, h2, h3, h4]
    omega

/-- Constructive telescoping Fermat product identity:
`∏_{k=0}^{n-1} (2^(2^k) + 1) = 2^(2^n) - 1`. -/
theorem fermat_prefix_prod_eq (n : Nat) :
    fermatPrefixProd n = 2 ^ (2 ^ n) - 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    dsimp [fermatPrefixProd, fermatNumber]
    rw [ih]
    have ha : 1 ≤ 2 ^ (2 ^ k) := Nat.one_le_two_pow
    rw [pred_mul_succ_eq_sq_sub_one (2 ^ (2 ^ k)) ha]
    have hsq : 2 ^ (2 ^ k) * 2 ^ (2 ^ k) = 2 ^ (2 ^ (k + 1)) := by
      rw [← Nat.pow_add, ← Nat.two_mul, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
    rw [hsq]

/-- Fermat-prime tower product and Euler totient product identities:
`fermatTowerPrimes.prod = 1431655765`, `3 * fermatTowerPrimes.prod = 2^32 - 1 = 4294967295`,
`fermatAllPrimes.prod = 2^32 - 1`, and `∏_{p ∈ fermatTowerPrimes} (p - 1) = 2^30 = 1073741824`. -/
theorem fermat_tower_product_eq_2pow32_sub_1 :
    fermatTowerPrimes = [fermatNumber 1, fermatNumber 2, fermatNumber 3, fermatNumber 4] ∧
    fermatTowerPrimes.prod = 1431655765 ∧
    3 * fermatTowerPrimes.prod = 2 ^ 32 - 1 ∧
    2 ^ 32 - 1 = 4294967295 ∧
    fermatAllPrimes.prod = fermatPrefixProd 5 ∧
    fermatAllPrimes.prod = 2 ^ 32 - 1 ∧
    (fermatTowerPrimes.map (· - 1)).prod = 2 ^ 30 ∧
    2 ^ 30 = 1073741824 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, fermat_prefix_prod_eq 5, rfl, rfl⟩

private theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  if hx : 0 ≤ x then
    exact Int.mul_nonneg hx hx
  else
    have hnx : 0 ≤ -x := by omega
    have hmul : 0 ≤ (-x) * (-x) := Int.mul_nonneg hnx hnx
    have heq : (-x) * (-x) = x * x := by
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    omega

private theorem sq_le_sq_of_nonneg (a b : Int) (ha : 0 ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b :=
  Int.mul_le_mul hab hab ha (Int.le_trans ha hab)

private theorem le_of_sq_le_sq_nonneg (x r : Int) (hr : 0 ≤ r) (h : x * x ≤ r * r) :
    x ≤ r := by
  if hxr : x ≤ r then
    exact hxr
  else
    have hrx : r < x := by omega
    have hr1 : r + 1 ≤ x := hrx
    have hsq : (r + 1) * (r + 1) ≤ x * x :=
      sq_le_sq_of_nonneg (r + 1) x (by omega) hr1
    have hexp : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add]
      omega
    omega

private theorem int_reverse_triangle_disk_sq (d zx zy r : Int)
    (hr : 0 ≤ r) (hrd : r ≤ d) (hnorm : zx * zx + zy * zy ≤ r * r) :
    (d - r) * (d - r) ≤ (d - zx) * (d - zx) + zy * zy := by
  have hy : 0 ≤ zy * zy := int_sq_nonneg zy
  have hx2 : zx * zx ≤ r * r := by omega
  have hxr : zx ≤ r := le_of_sq_le_sq_nonneg zx r hr hx2
  have hdiff :
      ((d - zx) * (d - zx) + zy * zy) - (d - r) * (d - r) =
        2 * ((d - r) * (r - zx)) + (r - zx) * (r - zx) + zy * zy := by
    have e1 : (d - zx) * (d - zx) = d * d - 2 * (d * zx) + zx * zx := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      have c := Int.mul_comm zx d
      omega
    have e2 : (d - r) * (d - r) = d * d - 2 * (d * r) + r * r := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      have c := Int.mul_comm r d
      omega
    have e3 : (r - zx) * (r - zx) = r * r - 2 * (r * zx) + zx * zx := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      have c := Int.mul_comm zx r
      omega
    have e4 : (d - r) * (r - zx) = d * r - d * zx - r * r + r * zx := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
      omega
    rw [e1, e2, e3, e4]
    omega
  have h1 : 0 ≤ (d - r) * (r - zx) := Int.mul_nonneg (by omega) (by omega)
  have h2 : 0 ≤ (r - zx) * (r - zx) := int_sq_nonneg (r - zx)
  omega

/-- Cleared-denominator integer specification for a local Euler factor `1 - z_p` where
`z_p = (zx + i zy) / d` lies inside the closed disk `|z_p| ≤ rNum / d < 1`. -/
structure EulerLocalFactorSpec where
  p : Nat
  d : Int
  rNum : Int
  zx : Int
  zy : Int
  deriving DecidableEq, Repr

/-- Admissibility of a local Euler factor specification: `p ≥ 2`, `0 < rNum < d`, and
`(zx / d)^2 + (zy / d)^2 ≤ (rNum / d)^2`. -/
def ValidEulerLocalFactorSpec (f : EulerLocalFactorSpec) : Prop :=
  2 ≤ f.p ∧ 0 < f.d ∧ 0 < f.rNum ∧ f.rNum < f.d ∧
    f.zx * f.zx + f.zy * f.zy ≤ f.rNum * f.rNum

instance (f : EulerLocalFactorSpec) : Decidable (ValidEulerLocalFactorSpec f) := by
  dsimp [ValidEulerLocalFactorSpec]
  infer_instance

/-- Cleared-denominator lower envelope product `∏ (d_p - rNum_p)^2`. -/
def eulerProdMarginSq : List EulerLocalFactorSpec → Int
  | [] => 1
  | f :: rest => (f.d - f.rNum) * (f.d - f.rNum) * eulerProdMarginSq rest

/-- Cleared-denominator local Euler product squared modulus `∏ ((d_p - zx_p)^2 + zy_p^2)`. -/
def eulerProdNormSq : List EulerLocalFactorSpec → Int
  | [] => 1
  | f :: rest => ((f.d - f.zx) * (f.d - f.zx) + f.zy * f.zy) * eulerProdNormSq rest

/-- Cleared-denominator square scale `∏ d_p^2`. -/
def eulerProdDenSq : List EulerLocalFactorSpec → Int
  | [] => 1
  | f :: rest => (f.d * f.d) * eulerProdDenSq rest

/-- Single-factor reverse-triangle disk lower bound:
`0 < (d - rNum)^2 ≤ (d - zx)^2 + zy^2`. -/
theorem local_euler_disk_nonvanishing (f : EulerLocalFactorSpec)
    (hf : ValidEulerLocalFactorSpec f) :
    0 < (f.d - f.rNum) * (f.d - f.rNum) ∧
    (f.d - f.rNum) * (f.d - f.rNum) ≤ (f.d - f.zx) * (f.d - f.zx) + f.zy * f.zy ∧
    0 < f.d * f.d := by
  rcases hf with ⟨_, hd, hr, hrd, hnorm⟩
  refine ⟨Int.mul_pos (by omega) (by omega), ?_, Int.mul_pos hd hd⟩
  exact int_reverse_triangle_disk_sq f.d f.zx f.zy f.rNum (by omega) (by omega) hnorm

/-- Theorem (Inductive Finite Euler Product Norm Lower Bound):
For any finite list `fs` of admissible local Euler factors `1 - z_p` (`|z_p| ≤ r_p < 1`),
the cleared-denominator Euler product squared modulus is strictly bounded below by
`0 < ∏ (d_p - rNum_p)^2 ≤ ∏ ((d_p - zx_p)^2 + zy_p^2)`. -/
theorem euler_product_finite_norm_lower_bound (fs : List EulerLocalFactorSpec)
    (hfs : ∀ f ∈ fs, ValidEulerLocalFactorSpec f) :
    0 < eulerProdMarginSq fs ∧
    eulerProdMarginSq fs ≤ eulerProdNormSq fs ∧
    0 < eulerProdDenSq fs := by
  induction fs with
  | nil =>
    dsimp [eulerProdMarginSq, eulerProdNormSq, eulerProdDenSq]
    exact ⟨by decide, by decide, by decide⟩
  | cons f rest ih =>
    dsimp [eulerProdMarginSq, eulerProdNormSq, eulerProdDenSq]
    have hf : ValidEulerLocalFactorSpec f := hfs f (List.Mem.head _)
    have hrest : ∀ g ∈ rest, ValidEulerLocalFactorSpec g :=
      fun g hg => hfs g (List.Mem.tail f hg)
    obtain ⟨hm1, hle1, hd1⟩ := local_euler_disk_nonvanishing f hf
    obtain ⟨hm2, hle2, hd2⟩ := ih hrest
    refine ⟨Int.mul_pos hm1 hm2, ?_, Int.mul_pos hd1 hd2⟩
    exact Int.mul_le_mul hle1 hle2 (by omega) (by omega)

/-- Predicate asserting `fs` instantiates the 4-prime Fermat tower `[5, 17, 257, 65537]`
with admissible local Euler factor bounds. -/
def IsFermatTowerFactors (fs : List EulerLocalFactorSpec) : Prop :=
  fs.map (·.p) = fermatTowerPrimes ∧ ∀ f ∈ fs, ValidEulerLocalFactorSpec f

/-- Theorem (Fermat-Tower Euler Product Non-Vanishing):
For any valid complex factors over the Fermat-prime tower `{5, 17, 257, 65537}`
with `0 < rNum_p < d_p`, the finite Euler product squared modulus is strictly positive
and bounded below by `∏ (d_p - rNum_p)^2 > 0`. -/
theorem fermat_tower_euler_product_nonvanishing (fs : List EulerLocalFactorSpec)
    (hfs : IsFermatTowerFactors fs) :
    fs.length = 4 ∧
    fs.map (·.p) = [5, 17, 257, 65537] ∧
    0 < eulerProdMarginSq fs ∧
    eulerProdMarginSq fs ≤ eulerProdNormSq fs ∧
    0 < eulerProdDenSq fs := by
  rcases hfs with ⟨hp, hvalid⟩
  obtain ⟨hm, hle, hd⟩ := euler_product_finite_norm_lower_bound fs hvalid
  have hlen : fs.length = 4 := by
    have hmapLen : (fs.map (·.p)).length = 4 := by rw [hp]; rfl
    simpa [List.length_map] using hmapLen
  exact ⟨hlen, hp, hm, hle, hd⟩

private theorem strip_half_admissible :
    1 ^ 2 * 5 ≥ 2 ^ 2 ∧ 1 ^ 2 * 17 ≥ 4 ^ 2 ∧
    1 ^ 2 * 257 ≥ 16 ^ 2 ∧ 1 ^ 2 * 65537 ≥ 256 ^ 2 ∧
    (2 - 1) * (4 - 1) * (16 - 1) * (256 - 1) = 11475 ∧
    2 * 4 * 16 * 256 = 32768 ∧
    32768 ^ 2 < 9 * 11475 ^ 2 := by
  decide

private theorem strip_three_quarters_admissible :
    3 ^ 4 * 5 ^ 3 ≥ 10 ^ 4 ∧ 1 ^ 4 * 17 ^ 3 ≥ 8 ^ 4 ∧
    1 ^ 4 * 257 ^ 3 ≥ 64 ^ 4 ∧ 1 ^ 4 * 65537 ^ 3 ≥ 4096 ^ 4 ∧
    (10 - 3) * (8 - 1) * (64 - 1) * (4096 - 1) = 12641265 ∧
    10 * 8 * 64 * 4096 = 20971520 ∧
    12641265 = 5 * 2528253 ∧
    20971520 = 5 * 4194304 ∧
    4194304 ^ 2 < 3 * 2528253 ^ 2 ∧
    20971520 ^ 2 < 3 * 12641265 ^ 2 := by
  decide

private theorem strip_one_admissible :
    (5 - 1) * (17 - 1) * (257 - 1) * (65537 - 1) = 2 ^ 30 ∧
    (5 - 1) * (17 - 1) * (257 - 1) * (65537 - 1) = 1073741824 ∧
    5 * 17 * 257 * 65537 = 1431655765 ∧
    9 * 1431655765 ^ 2 < 16 * 1073741824 ^ 2 ∧
    1431655765 ^ 2 < 16 * 1073741824 ^ 2 ∧
    4294967295 ^ 2 < 4 * (2 * 1073741824) ^ 2 := by
  decide

/-- Theorem (Critical-Strip Certified Rational Lower Bounds for `{5, 17, 257, 65537}`):
Certifies cleared-denominator envelope admissibility (`r_p ≥ p^{-σ}`) and strict rational
lower bounds across `σ = 1/2` (`> 1/9`), `σ = 3/4` (`> 1/3`), and `σ = 1` (`> 9/16 > 1/16`,
and `> 1/4 > 1/16` when including `F_0 = 3`). -/
theorem fermat_tower_euler_product_strip_certs :
    (1 ^ 2 * 5 ≥ 2 ^ 2 ∧ 1 ^ 2 * 17 ≥ 4 ^ 2 ∧
     1 ^ 2 * 257 ≥ 16 ^ 2 ∧ 1 ^ 2 * 65537 ≥ 256 ^ 2 ∧
     (2 - 1) * (4 - 1) * (16 - 1) * (256 - 1) = 11475 ∧
     2 * 4 * 16 * 256 = 32768 ∧
     32768 ^ 2 < 9 * 11475 ^ 2) ∧
    (3 ^ 4 * 5 ^ 3 ≥ 10 ^ 4 ∧ 1 ^ 4 * 17 ^ 3 ≥ 8 ^ 4 ∧
     1 ^ 4 * 257 ^ 3 ≥ 64 ^ 4 ∧ 1 ^ 4 * 65537 ^ 3 ≥ 4096 ^ 4 ∧
     (10 - 3) * (8 - 1) * (64 - 1) * (4096 - 1) = 12641265 ∧
     10 * 8 * 64 * 4096 = 20971520 ∧
     4194304 ^ 2 < 3 * 2528253 ^ 2 ∧
     20971520 ^ 2 < 3 * 12641265 ^ 2) ∧
    ((5 - 1) * (17 - 1) * (257 - 1) * (65537 - 1) = 1073741824 ∧
     5 * 17 * 257 * 65537 = 1431655765 ∧
     9 * 1431655765 ^ 2 < 16 * 1073741824 ^ 2 ∧
     1431655765 ^ 2 < 16 * 1073741824 ^ 2 ∧
     4294967295 ^ 2 < 4 * 2147483648 ^ 2) := by
  refine ⟨strip_half_admissible, ?_, ?_⟩
  · have h := strip_three_quarters_admissible
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩
  · have h := strip_one_admissible
    refine ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
    simp [h.2.2.2.2.2]

private theorem fermat_tower_four_factors_bound
    (d5 r5 zx5 zy5 d17 r17 zx17 zy17
     d257 r257 zx257 zy257 d65537 r65537 zx65537 zy65537 : Int)
    (hd5 : 0 < d5) (hr5 : 0 < r5) (hrd5 : r5 < d5) (hn5 : zx5 * zx5 + zy5 * zy5 ≤ r5 * r5)
    (hd17 : 0 < d17) (hr17 : 0 < r17) (hrd17 : r17 < d17)
    (hn17 : zx17 * zx17 + zy17 * zy17 ≤ r17 * r17)
    (hd257 : 0 < d257) (hr257 : 0 < r257) (hrd257 : r257 < d257)
    (hn257 : zx257 * zx257 + zy257 * zy257 ≤ r257 * r257)
    (hd65537 : 0 < d65537) (hr65537 : 0 < r65537) (hrd65537 : r65537 < d65537)
    (hn65537 : zx65537 * zx65537 + zy65537 * zy65537 ≤ r65537 * r65537) :
    eulerProdMarginSq
      [ ⟨5, d5, r5, zx5, zy5⟩, ⟨17, d17, r17, zx17, zy17⟩,
        ⟨257, d257, r257, zx257, zy257⟩, ⟨65537, d65537, r65537, zx65537, zy65537⟩ ] ≤
    eulerProdNormSq
      [ ⟨5, d5, r5, zx5, zy5⟩, ⟨17, d17, r17, zx17, zy17⟩,
        ⟨257, d257, r257, zx257, zy257⟩, ⟨65537, d65537, r65537, zx65537, zy65537⟩ ] := by
  let fs : List EulerLocalFactorSpec :=
    [ ⟨5, d5, r5, zx5, zy5⟩, ⟨17, d17, r17, zx17, zy17⟩,
      ⟨257, d257, r257, zx257, zy257⟩, ⟨65537, d65537, r65537, zx65537, zy65537⟩ ]
  have hvalid : IsFermatTowerFactors fs := by
    refine ⟨rfl, ?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨by dsimp; decide, hd5, hr5, hrd5, hn5⟩
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨by dsimp; decide, hd17, hr17, hrd17, hn17⟩
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact ⟨by dsimp; decide, hd257, hr257, hrd257, hn257⟩
        · rcases List.mem_cons.mp hf with rfl | hf
          · exact ⟨by dsimp; decide, hd65537, hr65537, hrd65537, hn65537⟩
          · cases hf
  exact (fermat_tower_euler_product_nonvanishing fs hvalid).2.2.2.1

/-- Cleared-denominator `σ = 1/2` lower bound for ANY local factors `(zx_p, zy_p)` over
`{5, 17, 257, 65537}` inside the rational radii `(1/2, 1/4, 1/16, 1/256)`:
`|∏ (1 - z_p)|^2 > 1 / 9`. -/
theorem fermat_tower_sigma_half_lower_bound
    (zx5 zy5 zx17 zy17 zx257 zy257 zx65537 zy65537 : Int)
    (h5 : zx5 * zx5 + zy5 * zy5 ≤ 1)
    (h17 : zx17 * zx17 + zy17 * zy17 ≤ 1)
    (h257 : zx257 * zx257 + zy257 * zy257 ≤ 1)
    (h65537 : zx65537 * zx65537 + zy65537 * zy65537 ≤ 1) :
    let fs : List EulerLocalFactorSpec :=
      [ ⟨5, 2, 1, zx5, zy5⟩,
        ⟨17, 4, 1, zx17, zy17⟩,
        ⟨257, 16, 1, zx257, zy257⟩,
        ⟨65537, 256, 1, zx65537, zy65537⟩ ]
    eulerProdDenSq fs < 9 * eulerProdNormSq fs := by
  intro fs
  have hle := fermat_tower_four_factors_bound
    2 1 zx5 zy5 4 1 zx17 zy17 16 1 zx257 zy257 256 1 zx65537 zy65537
    (by decide) (by decide) (by decide) h5
    (by decide) (by decide) (by decide) h17
    (by decide) (by decide) (by decide) h257
    (by decide) (by decide) (by decide) h65537
  change eulerProdMarginSq fs ≤ eulerProdNormSq fs at hle
  have hm : eulerProdDenSq fs < 9 * eulerProdMarginSq fs := by
    dsimp [fs, eulerProdDenSq, eulerProdMarginSq]
    decide
  have hmul : 9 * eulerProdMarginSq fs ≤ 9 * eulerProdNormSq fs :=
    Int.mul_le_mul_of_nonneg_left hle (by decide)
  exact Int.lt_of_lt_of_le hm hmul

/-- Cleared-denominator `σ = 3/4` lower bound for ANY local factors `(zx_p, zy_p)` over
`{5, 17, 257, 65537}` inside the rational radii `(3/10, 1/8, 1/64, 1/4096)`:
`|∏ (1 - z_p)|^2 > 1 / 3`. -/
theorem fermat_tower_sigma_three_quarters_lower_bound
    (zx5 zy5 zx17 zy17 zx257 zy257 zx65537 zy65537 : Int)
    (h5 : zx5 * zx5 + zy5 * zy5 ≤ 9)
    (h17 : zx17 * zx17 + zy17 * zy17 ≤ 1)
    (h257 : zx257 * zx257 + zy257 * zy257 ≤ 1)
    (h65537 : zx65537 * zx65537 + zy65537 * zy65537 ≤ 1) :
    let fs : List EulerLocalFactorSpec :=
      [ ⟨5, 10, 3, zx5, zy5⟩,
        ⟨17, 8, 1, zx17, zy17⟩,
        ⟨257, 64, 1, zx257, zy257⟩,
        ⟨65537, 4096, 1, zx65537, zy65537⟩ ]
    eulerProdDenSq fs < 3 * eulerProdNormSq fs := by
  intro fs
  have hle := fermat_tower_four_factors_bound
    10 3 zx5 zy5 8 1 zx17 zy17 64 1 zx257 zy257 4096 1 zx65537 zy65537
    (by decide) (by decide) (by decide) h5
    (by decide) (by decide) (by decide) h17
    (by decide) (by decide) (by decide) h257
    (by decide) (by decide) (by decide) h65537
  change eulerProdMarginSq fs ≤ eulerProdNormSq fs at hle
  have hm : eulerProdDenSq fs < 3 * eulerProdMarginSq fs := by
    dsimp [fs, eulerProdDenSq, eulerProdMarginSq]
    decide
  have hmul : 3 * eulerProdMarginSq fs ≤ 3 * eulerProdNormSq fs :=
    Int.mul_le_mul_of_nonneg_left hle (by decide)
  exact Int.lt_of_lt_of_le hm hmul

/-- Cleared-denominator `σ = 1` lower bound for ANY local factors `(zx_p, zy_p)` over
`{5, 17, 257, 65537}` inside the rational radii `1 / p`:
`|∏ (1 - z_p)|^2 > 9 / 16 > 1 / 16`. -/
theorem fermat_tower_sigma_one_lower_bound
    (zx5 zy5 zx17 zy17 zx257 zy257 zx65537 zy65537 : Int)
    (h5 : zx5 * zx5 + zy5 * zy5 ≤ 1)
    (h17 : zx17 * zx17 + zy17 * zy17 ≤ 1)
    (h257 : zx257 * zx257 + zy257 * zy257 ≤ 1)
    (h65537 : zx65537 * zx65537 + zy65537 * zy65537 ≤ 1) :
    let fs : List EulerLocalFactorSpec :=
      [ ⟨5, 5, 1, zx5, zy5⟩,
        ⟨17, 17, 1, zx17, zy17⟩,
        ⟨257, 257, 1, zx257, zy257⟩,
        ⟨65537, 65537, 1, zx65537, zy65537⟩ ]
    9 * eulerProdDenSq fs < 16 * eulerProdNormSq fs ∧
    eulerProdDenSq fs < 16 * eulerProdNormSq fs := by
  intro fs
  have hle := fermat_tower_four_factors_bound
    5 1 zx5 zy5 17 1 zx17 zy17 257 1 zx257 zy257 65537 1 zx65537 zy65537
    (by decide) (by decide) (by decide) h5
    (by decide) (by decide) (by decide) h17
    (by decide) (by decide) (by decide) h257
    (by decide) (by decide) (by decide) h65537
  change eulerProdMarginSq fs ≤ eulerProdNormSq fs at hle
  have hm9 : 9 * eulerProdDenSq fs < 16 * eulerProdMarginSq fs := by
    dsimp [fs, eulerProdDenSq, eulerProdMarginSq]
    decide
  have hm1 : eulerProdDenSq fs < 16 * eulerProdMarginSq fs := by
    dsimp [fs, eulerProdDenSq, eulerProdMarginSq]
    decide
  have hmul : 16 * eulerProdMarginSq fs ≤ 16 * eulerProdNormSq fs :=
    Int.mul_le_mul_of_nonneg_left hle (by decide)
  exact ⟨Int.lt_of_lt_of_le hm9 hmul, Int.lt_of_lt_of_le hm1 hmul⟩

end EulerFactorNonVanishing

-- end of file: leanasm/src/LeanAsm/EulerFactorNonVanishing.lean
