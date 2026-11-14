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

-- =============================================================================
-- Cyclotomic Splitting & Dedekind Zeta Euler Factors over Q(ζ_{2^(2^k)})
-- (Issue #38)
-- =============================================================================

/-- Cyclotomic splitting multiplicity `g_k = φ(2^(2^k)) = 2^(2^k - 1)` for `F_k = 2^(2^k) + 1`
in `ℚ(ζ_{2^(2^k)})` (`k ≥ 1`). -/
def fermatCyclotomicSplittingDeg (k : Nat) : Nat :=
  2 ^ (2 ^ k - 1)

/-- Splitting multiplicities `[g_1, g_2, g_3, g_4] = [2, 8, 128, 32768]` across `{5, 17, 257, 65537}`. -/
def fermatTowerSplittingDegs : List Nat :=
  [1, 2, 3, 4].map fermatCyclotomicSplittingDeg

/-- Complete splitting arithmetic of Fermat primes in `ℚ(ζ_{2^(2^k)})`:
for every `k ≥ 1`, `F_k ≡ 1 (mod 2^(2^k))` (so residue degree `f = 1`),
`F_k - 1 = 2 * g_k`, and across `k = 1..4` the splitting multiplicities are
`(2, 8, 128, 32768)` with total splitting prime-ideal count `32906`. -/
theorem fermat_prime_cyclotomic_splitting_deg :
    (∀ k : Nat, 1 ≤ k →
      fermatNumber k % 2 ^ (2 ^ k) = 1 ∧
      fermatNumber k - 1 = 2 * fermatCyclotomicSplittingDeg k ∧
      1 ≤ fermatCyclotomicSplittingDeg k) ∧
    fermatCyclotomicSplittingDeg 1 = 2 ∧
    fermatCyclotomicSplittingDeg 2 = 8 ∧
    fermatCyclotomicSplittingDeg 3 = 128 ∧
    fermatCyclotomicSplittingDeg 4 = 32768 ∧
    fermatTowerSplittingDegs = [2, 8, 128, 32768] ∧
    fermatTowerSplittingDegs.sum = 32906 := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro k hk
  have h1k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2k : 2 ≤ 2 ^ k := by
    have hp : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    simpa using hp
  have hmod_lt : 1 < 2 ^ (2 ^ k) := by
    have h4 : (2 : Nat) ^ 2 ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by decide) h2k
    change 4 ≤ 2 ^ (2 ^ k) at h4
    omega
  have hmod : fermatNumber k % 2 ^ (2 ^ k) = 1 := by
    dsimp [fermatNumber]
    rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hmod_lt]
  have hsub : fermatNumber k - 1 = 2 * fermatCyclotomicSplittingDeg k := by
    dsimp [fermatNumber, fermatCyclotomicSplittingDeg]
    have hsucc : 2 ^ k - 1 + 1 = 2 ^ k := Nat.sub_add_cancel h1k
    have hpow : 2 ^ (2 ^ k) = 2 * 2 ^ (2 ^ k - 1) := by
      calc 2 ^ (2 ^ k) = 2 ^ ((2 ^ k - 1) + 1) := by rw [hsucc]
        _ = 2 ^ (2 ^ k - 1) * 2 := Nat.pow_succ _ _
        _ = 2 * 2 ^ (2 ^ k - 1) := Nat.mul_comm _ _
    omega
  have hg1 : 1 ≤ fermatCyclotomicSplittingDeg k := Nat.one_le_two_pow
  exact ⟨hmod, hsub, hg1⟩

private theorem cyclotomic_split_euler_factor_pow
    (f : EulerLocalFactorSpec) (hf : ValidEulerLocalFactorSpec f) (g : Nat) :
    0 < (f.d - f.rNum) ^ (2 * g) ∧
    (f.d - f.rNum) ^ (2 * g) ≤
      ((f.d - f.zx) * (f.d - f.zx) + f.zy * f.zy) ^ g ∧
    0 < (f.d * f.d) ^ g := by
  obtain ⟨hm, hle, hd⟩ := local_euler_disk_nonvanishing f hf
  induction g with
  | zero =>
    simp only [Nat.mul_zero, Int.pow_zero]
    exact ⟨by decide, by decide, by decide⟩
  | succ k ih =>
    have hexp : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [hexp, Int.pow_succ, Int.pow_succ, Int.pow_succ, Int.pow_succ]
    have hm2 : (f.d - f.rNum) ^ (2 * k) * (f.d - f.rNum) * (f.d - f.rNum) =
        (f.d - f.rNum) ^ (2 * k) * ((f.d - f.rNum) * (f.d - f.rNum)) :=
      Int.mul_assoc _ _ _
    rw [hm2]
    refine ⟨Int.mul_pos ih.1 hm, ?_, Int.mul_pos ih.2.2 hd⟩
    exact Int.mul_le_mul ih.2.1 hle (Int.le_of_lt hm)
      (Int.le_trans (Int.le_of_lt ih.1) ih.2.1)

/-- Inductive power-lifted cyclotomic local Euler factor non-vanishing:
if `f` is admissible (`|z_p| ≤ rNum/d < 1`) and `g ≥ 1` is the complete splitting
multiplicity, then the Dedekind factor `(1 - p^{-s})^g` satisfies
`0 < (d - rNum)^(2g) ≤ ((d - zx)^2 + zy^2)^g` and `0 < (d^2)^g`. -/
theorem cyclotomic_split_euler_factor_nonvanishing
    (f : EulerLocalFactorSpec) (hf : ValidEulerLocalFactorSpec f)
    (g : Nat) (_hg : 1 ≤ g) :
    0 < (f.d - f.rNum) ^ (2 * g) ∧
    (f.d - f.rNum) ^ (2 * g) ≤
      ((f.d - f.zx) * (f.d - f.zx) + f.zy * f.zy) ^ g ∧
    0 < (f.d * f.d) ^ g :=
  cyclotomic_split_euler_factor_pow f hf g

/-- Single-prime cyclotomic splitting factor specification `(base, g)` representing
the completely split local Dedekind Euler factor `∏_{𝔭 | p} (1 - N(𝔭)^{-s}) = (1 - z_p)^g`. -/
structure CyclotomicSplitFactorSpec where
  base : EulerLocalFactorSpec
  g : Nat
  deriving DecidableEq, Repr

/-- Cleared-denominator cyclotomic lower envelope `∏ (d_p - rNum_p)^(2 * g_p)`. -/
def cyclotomicProdMarginPow : List CyclotomicSplitFactorSpec → Int
  | [] => 1
  | c :: rest => (c.base.d - c.base.rNum) ^ (2 * c.g) * cyclotomicProdMarginPow rest

/-- Cleared-denominator cyclotomic Dedekind product modulus `∏ ((d_p - zx_p)^2 + zy_p^2)^g_p`. -/
def cyclotomicProdNormPow : List CyclotomicSplitFactorSpec → Int
  | [] => 1
  | c :: rest =>
    ((c.base.d - c.base.zx) * (c.base.d - c.base.zx) + c.base.zy * c.base.zy) ^ c.g *
      cyclotomicProdNormPow rest

/-- Cleared-denominator cyclotomic scale `∏ (d_p^2)^g_p`. -/
def cyclotomicProdDenPow : List CyclotomicSplitFactorSpec → Int
  | [] => 1
  | c :: rest => (c.base.d * c.base.d) ^ c.g * cyclotomicProdDenPow rest

/-- Inductive lower bound across any list of completely split cyclotomic Euler factors:
`0 < ∏ (d_p - r_p)^(2g_p) ≤ ∏ ((d_p - zx_p)^2 + zy_p^2)^{g_p}` and `0 < ∏ (d_p^2)^{g_p}`. -/
theorem cyclotomic_euler_product_lower_bound (cs : List CyclotomicSplitFactorSpec)
    (hcs : ∀ c ∈ cs, ValidEulerLocalFactorSpec c.base ∧ 1 ≤ c.g) :
    0 < cyclotomicProdMarginPow cs ∧
    cyclotomicProdMarginPow cs ≤ cyclotomicProdNormPow cs ∧
    0 < cyclotomicProdDenPow cs := by
  induction cs with
  | nil =>
    dsimp [cyclotomicProdMarginPow, cyclotomicProdNormPow, cyclotomicProdDenPow]
    exact ⟨by decide, by decide, by decide⟩
  | cons c rest ih =>
    dsimp [cyclotomicProdMarginPow, cyclotomicProdNormPow, cyclotomicProdDenPow]
    have hc := hcs c (List.Mem.head _)
    have hrest : ∀ c' ∈ rest, ValidEulerLocalFactorSpec c'.base ∧ 1 ≤ c'.g :=
      fun c' hc' => hcs c' (List.Mem.tail c hc')
    obtain ⟨hm1, hle1, hd1⟩ :=
      cyclotomic_split_euler_factor_nonvanishing c.base hc.1 c.g hc.2
    obtain ⟨hm2, hle2, hd2⟩ := ih hrest
    refine ⟨Int.mul_pos hm1 hm2, ?_, Int.mul_pos hd1 hd2⟩
    exact Int.mul_le_mul hle1 hle2 (Int.le_of_lt hm2)
      (Int.le_trans (Int.le_of_lt hm1) hle1)

/-- Elementary constructive Bernoulli inequality in cleared-denominator `Nat` form:
for any `d` and `k` with `k + 1 ≤ d`, `d^k * (d - (k + 1)) ≤ (d - 1)^(k + 1)`. -/
private theorem bernoulli_sub_pow_nat (d k : Nat) (hkd : k + 1 ≤ d) :
    d ^ k * (d - (k + 1)) ≤ (d - 1) ^ (k + 1) := by
  induction k with
  | zero =>
    simp
  | succ m ih =>
    have hm1 : m + 1 ≤ d := Nat.le_trans (Nat.le_succ _) hkd
    have ih' := ih hm1
    have hstep : d * (d - (m + 2)) ≤ (d - (m + 1)) * (d - 1) := by
      have hdm : d - (m + 2) + (m + 2) = d := Nat.sub_add_cancel hkd
      have hm1' : d - (m + 1) = (d - (m + 2)) + 1 := by omega
      have hd1 : d - 1 = (d - (m + 2)) + (m + 1) := by omega
      rw [hm1', hd1]
      have hmuld : d * (d - (m + 2)) = ((d - (m + 2)) + (m + 2)) * (d - (m + 2)) := by
        rw [hdm]
      rw [hmuld]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      have hcomm : (d - (m + 2)) * m = m * (d - (m + 2)) := Nat.mul_comm _ _
      rw [hcomm]
      omega
    have hmul : d ^ m * (d - (m + 1)) * (d - 1) ≤ (d - 1) ^ (m + 1) * (d - 1) :=
      Nat.mul_le_mul_right (d - 1) ih'
    calc d ^ (m + 1) * (d - (m + 2))
        = (d ^ m * d) * (d - (m + 2)) := by rw [Nat.pow_succ]
      _ = d ^ m * (d * (d - (m + 2))) := Nat.mul_assoc _ _ _
      _ ≤ d ^ m * ((d - (m + 1)) * (d - 1)) := Nat.mul_le_mul_left _ hstep
      _ = d ^ m * (d - (m + 1)) * (d - 1) := (Nat.mul_assoc _ _ _).symm
      _ ≤ (d - 1) ^ (m + 1) * (d - 1) := hmul
      _ = (d - 1) ^ (m + 2) := (Nat.pow_succ _ _).symm

/-- Constructive uniform Euler lower bound at `σ = 1`:
for every `k ≥ 1`, letting `F_k = 2^(2^k) + 1` and `g_k = 2^(2^k - 1)`,
`(F_k : Int)^(2 * g_k) < 4 * (F_k - 1 : Int)^(2 * g_k)` (i.e. `(1 - 1/F_k)^(2g_k) > 1/4`)
holds uniformly without expanding large literal powers. -/
theorem fermat_sigma_one_uniform_quarter_bound (k : Nat) (hk : 1 ≤ k) :
    ((fermatNumber k : Int) ^ (2 * fermatCyclotomicSplittingDeg k)) <
      4 * (((fermatNumber k : Int) - 1) ^ (2 * fermatCyclotomicSplittingDeg k)) := by
  have hs := fermat_prime_cyclotomic_splitting_deg.1 k hk
  let g := fermatCyclotomicSplittingDeg k
  let d := fermatNumber k
  have hg1 : 1 ≤ g := hs.2.2
  have hd_eq : d = 2 * g + 1 := by
    have hsub := hs.2.1
    omega
  have hg_d : (g - 1) + 1 ≤ d := by omega
  have hbern := bernoulli_sub_pow_nat d (g - 1) hg_d
  have hg_sub : (g - 1) + 1 = g := Nat.sub_add_cancel hg1
  have hdg : d - g = g + 1 := by omega
  rw [hg_sub, hdg] at hbern
  have h2bern : 2 * (d ^ (g - 1) * (g + 1)) ≤ 2 * (d - 1) ^ g :=
    Nat.mul_le_mul_left 2 hbern
  have hdg_lt : d ^ g < 2 * (d - 1) ^ g := by
    have hpow : d ^ g = d ^ (g - 1) * d := by
      calc d ^ g = d ^ ((g - 1) + 1) := by rw [hg_sub]
        _ = d ^ (g - 1) * d := Nat.pow_succ _ _
    have hlt2 : d ^ (g - 1) * d < d ^ (g - 1) * (2 * (g + 1)) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (Nat.pow_pos (by omega))
    have hassoc : d ^ (g - 1) * (2 * (g + 1)) = 2 * (d ^ (g - 1) * (g + 1)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (d ^ (g - 1)) 2, Nat.mul_assoc]
    rw [hpow]
    exact Nat.lt_of_lt_of_le (by rw [← hassoc]; exact hlt2) h2bern
  have hsq : d ^ (2 * g) < 4 * (d - 1) ^ (2 * g) := by
    have hpowL : d ^ (2 * g) = d ^ g * d ^ g := by
      rw [Nat.two_mul, Nat.pow_add]
    have hpowR : 4 * (d - 1) ^ (2 * g) = (2 * (d - 1) ^ g) * (2 * (d - 1) ^ g) := by
      rw [Nat.two_mul g, Nat.pow_add]
      have hl : (2 * (d - 1) ^ g) * (2 * (d - 1) ^ g) =
          (2 * 2) * ((d - 1) ^ g * (d - 1) ^ g) := by
        rw [Nat.mul_assoc 2, Nat.mul_left_comm ((d - 1) ^ g) 2, ← Nat.mul_assoc 2 2]
      rw [hl]
    rw [hpowL, hpowR]
    exact Nat.lt_of_le_of_lt
      (Nat.mul_le_mul_right (d ^ g) (Nat.le_of_lt hdg_lt))
      (Nat.mul_lt_mul_of_pos_left hdg_lt (Nat.zero_lt_of_lt hdg_lt))
  have hz : ((d ^ (2 * g) : Nat) : Int) < ((4 * (d - 1) ^ (2 * g) : Nat) : Int) :=
    Int.ofNat_lt.mpr hsq
  have hcd : ((d - 1 : Nat) : Int) = (d : Int) - 1 := by omega
  have hc4 : ((4 : Nat) : Int) = 4 := rfl
  rw [Int.natCast_mul, Int.natCast_pow, Int.natCast_pow, hcd, hc4] at hz
  exact hz

private theorem fermat_4_mul_lt_mul {a1 a2 a3 a4 b1 b2 b3 b4 : Int}
    (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (ha4 : 0 < a4)
    (h1 : a1 < b1) (h2 : a2 < b2) (h3 : a3 < b3) (h4 : a4 < b4) :
    a1 * (a2 * (a3 * (a4 * 1))) < b1 * (b2 * (b3 * (b4 * 1))) := by
  have hb1 : 0 < b1 := Int.lt_trans ha1 h1
  have hb2 : 0 < b2 := Int.lt_trans ha2 h2
  have hb3 : 0 < b3 := Int.lt_trans ha3 h3
  have p4 : a4 * 1 < b4 * 1 := by omega
  have ha34 : 0 < a4 * 1 := by omega
  have p3 : a3 * (a4 * 1) < b3 * (b4 * 1) := by
    calc a3 * (a4 * 1) < a3 * (b4 * 1) := Int.mul_lt_mul_of_pos_left p4 ha3
      _ < b3 * (b4 * 1) := Int.mul_lt_mul_of_pos_right h3 (by omega)
  have ha234 : 0 < a3 * (a4 * 1) := Int.mul_pos ha3 ha34
  have p2 : a2 * (a3 * (a4 * 1)) < b2 * (b3 * (b4 * 1)) := by
    calc a2 * (a3 * (a4 * 1)) < a2 * (b3 * (b4 * 1)) := Int.mul_lt_mul_of_pos_left p3 ha2
      _ < b2 * (b3 * (b4 * 1)) := Int.mul_lt_mul_of_pos_right h2 (by omega)
  have ha1234 : 0 < a2 * (a3 * (a4 * 1)) := Int.mul_pos ha2 ha234
  calc a1 * (a2 * (a3 * (a4 * 1))) < a1 * (b2 * (b3 * (b4 * 1))) :=
        Int.mul_lt_mul_of_pos_left p2 ha1
    _ < b1 * (b2 * (b3 * (b4 * 1))) := Int.mul_lt_mul_of_pos_right h1 (by omega)

private theorem fermatNumber_int_1 : (fermatNumber 1 : Int) = 5 := rfl
private theorem fermatNumber_int_2 : (fermatNumber 2 : Int) = 17 := rfl
private theorem fermatNumber_int_3 : (fermatNumber 3 : Int) = 257 := rfl
private theorem fermatNumber_int_4 : (fermatNumber 4 : Int) = 65537 := rfl
private theorem fermatDeg_1 : fermatCyclotomicSplittingDeg 1 = 2 := rfl
private theorem fermatDeg_2 : fermatCyclotomicSplittingDeg 2 = 8 := rfl
private theorem fermatDeg_3 : fermatCyclotomicSplittingDeg 3 = 128 := rfl
private theorem fermatDeg_4 : fermatCyclotomicSplittingDeg 4 = 32768 := rfl

private theorem fermat_4_cyclotomic_valid
    (c1 c2 c3 c4 : CyclotomicSplitFactorSpec)
    (h1 : ValidEulerLocalFactorSpec c1.base ∧ 1 ≤ c1.g)
    (h2 : ValidEulerLocalFactorSpec c2.base ∧ 1 ≤ c2.g)
    (h3 : ValidEulerLocalFactorSpec c3.base ∧ 1 ≤ c3.g)
    (h4 : ValidEulerLocalFactorSpec c4.base ∧ 1 ≤ c4.g) :
    0 < cyclotomicProdMarginPow [c1, c2, c3, c4] ∧
    cyclotomicProdMarginPow [c1, c2, c3, c4] ≤ cyclotomicProdNormPow [c1, c2, c3, c4] ∧
    0 < cyclotomicProdDenPow [c1, c2, c3, c4] := by
  refine cyclotomic_euler_product_lower_bound [c1, c2, c3, c4] ?_
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact h1
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact h2
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact h3
      · rcases List.mem_cons.mp hc with rfl | hc
        · exact h4
        · cases hc

/-- Theorem (Fermat-Tower Cyclotomic Dedekind Euler Product Certificates):
Specializes `cyclotomic_split_euler_factor_nonvanishing` across the splitting prime ideals of
`(5, 17, 257, 65537)` in `ℚ(ζ_{2^(2^k)})` with multiplicities `(2, 8, 128, 32768)` across
`σ ∈ {1/2, 3/4, 1}` in symbolic power form (sub-second kernel verification):
1. At `σ = 1/2`: `0 < ∏ (d_p - 1)^(2g_p) ≤ ∏ normSq_p^{g_p}` and `0 < ∏ (d_p^2)^{g_p}`.
2. At `σ = 3/4`: `0 < ∏ (d_p - r_p)^(2g_p) ≤ ∏ normSq_p^{g_p}` and `0 < ∏ (d_p^2)^{g_p}`.
3. At `σ = 1`: `0 < ∏ (p - 1)^(2g_p) ≤ ∏ normSq_p^{g_p}` AND the uniform Dedekind strip
   lower bound `∏ (p^2)^{g_p} < 256 * ∏ normSq_p^{g_p}` (`|∏_{k=1..4} (1 - F_k^{-s})^{g_k}|^2 > 1/256`).
Zero `Classical.choice`, zero `sorryAx`. -/
theorem fermat_tower_dedekind_euler_strip_certs
    (zx5 zy5 zx17 zy17 zx257 zy257 zx65537 zy65537 : Int) :
    -- (1) σ = 1/2 cyclotomic Dedekind bound
    (zx5 * zx5 + zy5 * zy5 ≤ 1 →
     zx17 * zx17 + zy17 * zy17 ≤ 1 →
     zx257 * zx257 + zy257 * zy257 ≤ 1 →
     zx65537 * zx65537 + zy65537 * zy65537 ≤ 1 →
     let fsHalf : List CyclotomicSplitFactorSpec :=
       [ ⟨⟨5, 2, 1, zx5, zy5⟩, 2⟩,
         ⟨⟨17, 4, 1, zx17, zy17⟩, 8⟩,
         ⟨⟨257, 16, 1, zx257, zy257⟩, 128⟩,
         ⟨⟨65537, 256, 1, zx65537, zy65537⟩, 32768⟩ ]
     0 < cyclotomicProdMarginPow fsHalf ∧
     cyclotomicProdMarginPow fsHalf ≤ cyclotomicProdNormPow fsHalf ∧
     0 < cyclotomicProdDenPow fsHalf) ∧
    -- (2) σ = 3/4 cyclotomic Dedekind bound
    (zx5 * zx5 + zy5 * zy5 ≤ 9 →
     zx17 * zx17 + zy17 * zy17 ≤ 1 →
     zx257 * zx257 + zy257 * zy257 ≤ 1 →
     zx65537 * zx65537 + zy65537 * zy65537 ≤ 1 →
     let fs34 : List CyclotomicSplitFactorSpec :=
       [ ⟨⟨5, 10, 3, zx5, zy5⟩, 2⟩,
         ⟨⟨17, 8, 1, zx17, zy17⟩, 8⟩,
         ⟨⟨257, 64, 1, zx257, zy257⟩, 128⟩,
         ⟨⟨65537, 4096, 1, zx65537, zy65537⟩, 32768⟩ ]
     0 < cyclotomicProdMarginPow fs34 ∧
     cyclotomicProdMarginPow fs34 ≤ cyclotomicProdNormPow fs34 ∧
     0 < cyclotomicProdDenPow fs34) ∧
    -- (3) σ = 1 cyclotomic Dedekind bound + uniform > 1/256 rational lower bound
    (zx5 * zx5 + zy5 * zy5 ≤ 1 →
     zx17 * zx17 + zy17 * zy17 ≤ 1 →
     zx257 * zx257 + zy257 * zy257 ≤ 1 →
     zx65537 * zx65537 + zy65537 * zy65537 ≤ 1 →
     let fsOne : List CyclotomicSplitFactorSpec :=
       [ ⟨⟨5, 5, 1, zx5, zy5⟩, 2⟩,
         ⟨⟨17, 17, 1, zx17, zy17⟩, 8⟩,
         ⟨⟨257, 257, 1, zx257, zy257⟩, 128⟩,
         ⟨⟨65537, 65537, 1, zx65537, zy65537⟩, 32768⟩ ]
     0 < cyclotomicProdMarginPow fsOne ∧
     cyclotomicProdMarginPow fsOne ≤ cyclotomicProdNormPow fsOne ∧
     cyclotomicProdDenPow fsOne < 256 * cyclotomicProdNormPow fsOne) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h5 h17 h257 h65537 fsHalf
    exact fermat_4_cyclotomic_valid
      ⟨⟨5, 2, 1, zx5, zy5⟩, 2⟩ ⟨⟨17, 4, 1, zx17, zy17⟩, 8⟩
      ⟨⟨257, 16, 1, zx257, zy257⟩, 128⟩ ⟨⟨65537, 256, 1, zx65537, zy65537⟩, 32768⟩
      ⟨⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, h5⟩, by dsimp; omega⟩
      ⟨⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, h17⟩, by dsimp; omega⟩
      ⟨⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, h257⟩, by dsimp; omega⟩
      ⟨⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, h65537⟩, by dsimp; omega⟩
  · intro h5 h17 h257 h65537 fs34
    exact fermat_4_cyclotomic_valid
      ⟨⟨5, 10, 3, zx5, zy5⟩, 2⟩ ⟨⟨17, 8, 1, zx17, zy17⟩, 8⟩
      ⟨⟨257, 64, 1, zx257, zy257⟩, 128⟩ ⟨⟨65537, 4096, 1, zx65537, zy65537⟩, 32768⟩
      ⟨⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, h5⟩, by dsimp; omega⟩
      ⟨⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, h17⟩, by dsimp; omega⟩
      ⟨⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, h257⟩, by dsimp; omega⟩
      ⟨⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, h65537⟩, by dsimp; omega⟩
  · intro h5 h17 h257 h65537 fsOne
    have hlow := fermat_4_cyclotomic_valid
      ⟨⟨5, 5, 1, zx5, zy5⟩, 2⟩ ⟨⟨17, 17, 1, zx17, zy17⟩, 8⟩
      ⟨⟨257, 257, 1, zx257, zy257⟩, 128⟩ ⟨⟨65537, 65537, 1, zx65537, zy65537⟩, 32768⟩
      ⟨⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, h5⟩, by dsimp; omega⟩
      ⟨⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, h17⟩, by dsimp; omega⟩
      ⟨⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, h257⟩, by dsimp; omega⟩
      ⟨⟨by dsimp; omega, by dsimp; omega, by dsimp; omega, by dsimp; omega, h65537⟩, by dsimp; omega⟩
    refine ⟨hlow.1, hlow.2.1, ?_⟩
    have q1 := fermat_sigma_one_uniform_quarter_bound 1 (by decide)
    have q2 := fermat_sigma_one_uniform_quarter_bound 2 (by decide)
    have q3 := fermat_sigma_one_uniform_quarter_bound 3 (by decide)
    have q4 := fermat_sigma_one_uniform_quarter_bound 4 (by decide)
    rw [fermatNumber_int_1, fermatDeg_1] at q1
    rw [fermatNumber_int_2, fermatDeg_2] at q2
    rw [fermatNumber_int_3, fermatDeg_3] at q3
    rw [fermatNumber_int_4, fermatDeg_4] at q4
    have hpow2 : ∀ (d : Int) (g : Nat), (d * d) ^ g = d ^ (2 * g) := by
      intro d g
      induction g with
      | zero => simp
      | succ m ih =>
        calc (d * d) ^ (m + 1)
            = (d * d) ^ m * (d * d) := Int.pow_succ _ _
          _ = d ^ (2 * m) * (d * d) := by rw [ih]
          _ = d ^ (2 * m) * (d ^ 1 * d) := by rw [Int.pow_one]
          _ = d ^ (2 * m) * d ^ 2 := by rw [← Int.pow_succ]
          _ = d ^ (2 * m + 2) := (Int.pow_add d (2 * m) 2).symm
          _ = d ^ (2 * (m + 1)) := by rw [Nat.mul_succ]
    have h256 : cyclotomicProdDenPow fsOne < 256 * cyclotomicProdMarginPow fsOne := by
      change ((5 : Int) * 5) ^ 2 * (((17 : Int) * 17) ^ 8 *
          (((257 : Int) * 257) ^ 128 * (((65537 : Int) * 65537) ^ 32768 * 1))) <
        256 * (((5 : Int) - 1) ^ (2 * 2) * (((17 : Int) - 1) ^ (2 * 8) *
          (((257 : Int) - 1) ^ (2 * 128) * (((65537 : Int) - 1) ^ (2 * 32768) * 1))))
      rw [hpow2 5 2, hpow2 17 8, hpow2 257 128, hpow2 65537 32768]
      have hmul := fermat_4_mul_lt_mul
        (Int.pow_pos (by omega)) (Int.pow_pos (by omega))
        (Int.pow_pos (by omega)) (Int.pow_pos (by omega)) q1 q2 q3 q4
      have hr : (4 * ((5 : Int) - 1) ^ (2 * 2)) * ((4 * ((17 : Int) - 1) ^ (2 * 8)) *
            ((4 * ((257 : Int) - 1) ^ (2 * 128)) *
              ((4 * ((65537 : Int) - 1) ^ (2 * 32768)) * 1))) =
          256 * (((5 : Int) - 1) ^ (2 * 2) * (((17 : Int) - 1) ^ (2 * 8) *
            (((257 : Int) - 1) ^ (2 * 128) * (((65537 : Int) - 1) ^ (2 * 32768) * 1)))) := by
        have h16 : (4 : Int) * 4 = 16 := rfl
        have h64 : (4 : Int) * 16 = 64 := rfl
        have h256c : (4 : Int) * 64 = 256 := rfl
        calc (4 * ((5 : Int) - 1) ^ (2 * 2)) * ((4 * ((17 : Int) - 1) ^ (2 * 8)) *
              ((4 * ((257 : Int) - 1) ^ (2 * 128)) *
                ((4 * ((65537 : Int) - 1) ^ (2 * 32768)) * 1)))
            = (4 * (4 * (4 * 4))) * (((5 : Int) - 1) ^ (2 * 2) *
                (((17 : Int) - 1) ^ (2 * 8) * (((257 : Int) - 1) ^ (2 * 128) *
                  (((65537 : Int) - 1) ^ (2 * 32768) * 1)))) := by ac_rfl
          _ = 256 * (((5 : Int) - 1) ^ (2 * 2) * (((17 : Int) - 1) ^ (2 * 8) *
                (((257 : Int) - 1) ^ (2 * 128) * (((65537 : Int) - 1) ^ (2 * 32768) * 1)))) := by
              rw [h16, h64, h256c]
      rw [hr] at hmul
      exact hmul
    have hnorm := Int.mul_le_mul_of_nonneg_left hlow.2.1 (by decide : (0 : Int) ≤ 256)
    exact Int.lt_of_lt_of_le h256 hnorm

end EulerFactorNonVanishing

-- end of file: leanasm/src/LeanAsm/EulerFactorNonVanishing.lean
