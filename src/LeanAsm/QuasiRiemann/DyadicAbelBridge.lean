-- Path: leanasm/src/LeanAsm/QuasiRiemann/DyadicAbelBridge.lean
-- Constructive [M, M * 2^k) dyadic-shell foliation and discrete Abel summation-by-parts.
-- Max Column: 120 Columns

import LeanAsm.ConstructiveOpenaiBridge
import LeanAsm.QuasiRiemann.ShortIntervalPrimes
import LeanAsm.QuasiRiemann.ParametricQrhLadder

namespace QuasiRiemann

open ConstructiveOpenaiBridge

-- =============================================================================
-- Part 1: Constructive Half-Open Range Sums & [M, M * 2^k) Dyadic Foliation
-- =============================================================================

/-- Constructive half-open integer index list `[a, b) = [a, a + 1, ..., b - 1]`. -/
def halfOpenRange (a b : Nat) : List Nat :=
  (List.range (b - a)).map (fun i => a + i)

/-- Half-open list sum over `[a, b)` using `ConstructiveOpenaiBridge.listSum`. -/
def rangeSumInt (f : Nat → Int) (a b : Nat) : Int :=
  listSum (halfOpenRange a b) f

/-- Cumulative partial sum `∑_{0 ≤ i ≤ k} a i`. -/
def partialSumInt (a : Nat → Int) (k : Nat) : Int :=
  rangeSumInt a 0 (k + 1)

/-- `j`-th dyadic shell `[M * 2^j, M * 2^(j + 1))`. -/
def dyadicShell (M j : Nat) : List Nat :=
  halfOpenRange (M * 2 ^ j) (M * 2 ^ (j + 1))

/-- Partition of `[M, M * 2^k)` into `k` disjoint dyadic shells `[M * 2^j, M * 2^(j + 1))`. -/
def dyadicShellPartition (M k : Nat) : List (List Nat) :=
  (List.range k).map (dyadicShell M)

theorem halfOpenRange_self (a : Nat) : halfOpenRange a a = [] := by
  simp [halfOpenRange]

theorem halfOpenRange_empty {a b : Nat} (hba : b ≤ a) : halfOpenRange a b = [] := by
  have hzero : b - a = 0 := Nat.sub_eq_zero_of_le hba
  simp [halfOpenRange, hzero]

theorem halfOpenRange_succ_right {a b : Nat} (hab : a ≤ b) :
    halfOpenRange a (b + 1) = halfOpenRange a b ++ [b] := by
  have hsub : b + 1 - a = (b - a) + 1 := by omega
  dsimp [halfOpenRange]
  rw [hsub, List.range_succ, List.map_append]
  have hpt : a + (b - a) = b := by omega
  simp [hpt]

theorem halfOpenRange_succ_left {a b : Nat} (hab : a < b) :
    halfOpenRange a b = a :: halfOpenRange (a + 1) b := by
  induction b with
  | zero => exact absurd hab (Nat.not_lt_zero a)
  | succ b ih =>
    by_cases hlt : a < b
    · have hab' : a ≤ b := Nat.le_of_lt hlt
      have ha1 : a + 1 ≤ b := hlt
      rw [halfOpenRange_succ_right hab', ih hlt, halfOpenRange_succ_right ha1, List.cons_append]
    · have heq : b = a := by omega
      subst heq
      rw [halfOpenRange_succ_right (Nat.le_refl b), halfOpenRange_self b, halfOpenRange_self (b + 1)]
      rfl

theorem halfOpenRange_append {a m b : Nat} (ham : a ≤ m) (hmb : m ≤ b) :
    halfOpenRange a m ++ halfOpenRange m b = halfOpenRange a b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmb
  induction d with
  | zero =>
    rw [Nat.add_zero, halfOpenRange_self m, List.append_nil]
  | succ d ih =>
    have hmd : m ≤ m + d := Nat.le_add_right m d
    have hamd : a ≤ m + d := Nat.le_trans ham hmd
    have ih' := ih hmd
    rw [← Nat.add_assoc, halfOpenRange_succ_right hmd, halfOpenRange_succ_right hamd,
        ← List.append_assoc, ih']

theorem mem_halfOpenRange {a b n : Nat} :
    n ∈ halfOpenRange a b ↔ a ≤ n ∧ n < b := by
  dsimp [halfOpenRange]
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.mem_range] at hi
    exact ⟨Nat.le_add_right a i, by omega⟩
  · rintro ⟨han, hnb⟩
    refine ⟨n - a, List.mem_range.mpr (by omega), ?_⟩
    exact Nat.add_sub_cancel' han

private theorem nodup_map_inj {α β : Type} (f : α → β)
    (hinj : ∀ a b, f a = f b → a = b) : ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    rcases List.nodup_cons.mp h with ⟨hnx, hxs⟩
    apply List.nodup_cons.mpr
    refine ⟨?_, nodup_map_inj f hinj hxs⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
    exact hnx (hinj y x hfy ▸ hy)

theorem halfOpenRange_nodup (a b : Nat) : (halfOpenRange a b).Nodup := by
  dsimp [halfOpenRange]
  exact nodup_map_inj (fun i => a + i) (fun _ _ h => Nat.add_left_cancel h) List.nodup_range

theorem dyadicShell_nodup (M j : Nat) : (dyadicShell M j).Nodup :=
  halfOpenRange_nodup (M * 2 ^ j) (M * 2 ^ (j + 1))

theorem rangeSumInt_self (f : Nat → Int) (a : Nat) : rangeSumInt f a a = 0 := by
  simp [rangeSumInt, halfOpenRange_self, listSum]

theorem rangeSumInt_empty (f : Nat → Int) {a b : Nat} (hba : b ≤ a) :
    rangeSumInt f a b = 0 := by
  simp [rangeSumInt, halfOpenRange_empty hba, listSum]

theorem rangeSumInt_succ_right (f : Nat → Int) {a b : Nat} (hab : a ≤ b) :
    rangeSumInt f a (b + 1) = rangeSumInt f a b + f b := by
  dsimp [rangeSumInt]
  rw [halfOpenRange_succ_right hab, listSum_append]
  simp [listSum]

theorem rangeSumInt_succ_left (f : Nat → Int) {a b : Nat} (hab : a < b) :
    rangeSumInt f a b = f a + rangeSumInt f (a + 1) b := by
  dsimp [rangeSumInt]
  rw [halfOpenRange_succ_left hab]
  simp [listSum]

theorem rangeSumInt_singleton (f : Nat → Int) (a : Nat) :
    rangeSumInt f a (a + 1) = f a := by
  rw [rangeSumInt_succ_right f (Nat.le_refl a), rangeSumInt_self, Int.zero_add]

theorem rangeSumInt_append (f : Nat → Int) {a m b : Nat} (ham : a ≤ m) (hmb : m ≤ b) :
    rangeSumInt f a b = rangeSumInt f a m + rangeSumInt f m b := by
  dsimp [rangeSumInt]
  rw [← halfOpenRange_append ham hmb, listSum_append]

theorem rangeSumInt_congr {f g : Nat → Int} {a b : Nat}
    (h : ∀ n, a ≤ n → n < b → f n = g n) :
    rangeSumInt f a b = rangeSumInt g a b := by
  by_cases hab : a ≤ b
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    clear hab
    induction d with
    | zero => rw [Nat.add_zero, rangeSumInt_self, rangeSumInt_self]
    | succ d ih =>
      have had : a ≤ a + d := Nat.le_add_right a d
      rw [← Nat.add_assoc, rangeSumInt_succ_right f had, rangeSumInt_succ_right g had]
      have hcongr : ∀ n, a ≤ n → n < a + d → f n = g n :=
        fun n hn1 hn2 => h n hn1 (Nat.lt_trans hn2 (Nat.lt_succ_self (a + d)))
      have hlast : f (a + d) = g (a + d) := h (a + d) had (Nat.lt_succ_self (a + d))
      rw [ih hcongr, hlast]
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    rw [rangeSumInt_empty f hba, rangeSumInt_empty g hba]

theorem rangeSumInt_add (f g : Nat → Int) (a b : Nat) :
    rangeSumInt (fun n => f n + g n) a b = rangeSumInt f a b + rangeSumInt g a b := by
  by_cases hab : a ≤ b
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    clear hab
    induction d with
    | zero => simp [rangeSumInt_self]
    | succ d ih =>
      have had : a ≤ a + d := Nat.le_add_right a d
      rw [← Nat.add_assoc, rangeSumInt_succ_right _ had, rangeSumInt_succ_right _ had,
          rangeSumInt_succ_right _ had, ih]
      omega
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    rw [rangeSumInt_empty _ hba, rangeSumInt_empty _ hba, rangeSumInt_empty _ hba, Int.add_zero]

theorem rangeSumInt_sub (f g : Nat → Int) (a b : Nat) :
    rangeSumInt (fun n => f n - g n) a b = rangeSumInt f a b - rangeSumInt g a b := by
  by_cases hab : a ≤ b
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    clear hab
    induction d with
    | zero => simp [rangeSumInt_self]
    | succ d ih =>
      have had : a ≤ a + d := Nat.le_add_right a d
      rw [← Nat.add_assoc, rangeSumInt_succ_right _ had, rangeSumInt_succ_right _ had,
          rangeSumInt_succ_right _ had, ih]
      omega
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    rw [rangeSumInt_empty _ hba, rangeSumInt_empty _ hba, rangeSumInt_empty _ hba, Int.sub_zero]

theorem partialSumInt_zero (a : Nat → Int) : partialSumInt a 0 = a 0 :=
  rangeSumInt_singleton a 0

theorem partialSumInt_succ (a : Nat → Int) (k : Nat) :
    partialSumInt a (k + 1) = partialSumInt a k + a (k + 1) := by
  dsimp [partialSumInt]
  exact rangeSumInt_succ_right a (Nat.zero_le (k + 1))

theorem partialSumInt_sub (a : Nat → Int) {M k : Nat} (hMk : M ≤ k) :
    partialSumInt a k - partialSumInt a M = rangeSumInt a (M + 1) (k + 1) := by
  dsimp [partialSumInt]
  have h1 : 0 ≤ M + 1 := Nat.zero_le (M + 1)
  have h2 : M + 1 ≤ k + 1 := Nat.succ_le_succ hMk
  rw [rangeSumInt_append a h1 h2]
  omega

theorem partialSumInt_ones (k : Nat) :
    partialSumInt (fun _ => (1 : Int)) k = ((k + 1 : Nat) : Int) := by
  induction k with
  | zero => simp [partialSumInt_zero]
  | succ k ih =>
    rw [partialSumInt_succ, ih]
    omega

private theorem mul_one_le_mul_two_pow (M k : Nat) : M ≤ M * 2 ^ k := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  calc
    M = M * 1 := (Nat.mul_one M).symm
    _ ≤ M * 2 ^ k := Nat.mul_le_mul_left M h1

private theorem mul_two_pow_le_succ (M k : Nat) : M * 2 ^ k ≤ M * 2 ^ (k + 1) := by
  have hpow : 2 ^ k ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ k)
  exact Nat.mul_le_mul_left M hpow

theorem dyadicShellPartition_flatten (M k : Nat) :
    (dyadicShellPartition M k).flatten = halfOpenRange M (M * 2 ^ k) := by
  induction k with
  | zero =>
    simp [dyadicShellPartition, halfOpenRange_self]
  | succ k ih =>
    dsimp [dyadicShellPartition]
    rw [List.range_succ, List.map_append, List.flatten_append, List.map_singleton]
    have hcons : ([dyadicShell M k] : List (List Nat)).flatten = dyadicShell M k := by
      simp [List.flatten]
    rw [hcons]
    dsimp [dyadicShellPartition] at ih
    rw [ih]
    exact halfOpenRange_append (mul_one_le_mul_two_pow M k) (mul_two_pow_le_succ M k)

/-- Theorem (Constructive `[M, M * 2^k)` Dyadic Shell Partition):
Summing an integer observable over the half-open interval `[M, M * 2^k)` equals
summing across the `k` disjoint dyadic shells `[M * 2^j, M * 2^(j + 1))` (`j < k`).
Zero `Classical.choice`, zero `sorryAx`. -/
theorem dyadic_shell_sum_partition (M k : Nat) (f : Nat → Int) :
    rangeSumInt f M (M * 2 ^ k) =
      listSum (List.range k) (fun j => listSum (dyadicShell M j) f) := by
  induction k with
  | zero =>
    simp [rangeSumInt, listSum, halfOpenRange_self]
  | succ k ih =>
    rw [rangeSumInt_append f (mul_one_le_mul_two_pow M k) (mul_two_pow_le_succ M k), ih]
    rw [List.range_succ, listSum_append]
    have hlast : listSum [k] (fun j => listSum (dyadicShell M j) f) =
        rangeSumInt f (M * 2 ^ k) (M * 2 ^ (k + 1)) := by
      simp [listSum, dyadicShell, rangeSumInt]
    rw [hlast]

/-- Theorem (Dyadic-Shell & Lattice Slab Foliation):
Combines `ConstructiveOpenaiBridge.slab_sum_foliation` over pinned 4D lattice slabs
`slabSites r o (l ++ [i])` with `dyadic_shell_sum_partition` over `[M, M * 2^k)`,
foliating any separable slab-by-dyadic observable `fun x z => f x * g z` into
coordinate layers `z0 ∈ layerRange r` and dyadic magnitude shells `j ∈ List.range k`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem dyadic_shell_sum_foliation (r : Nat) (o : Cover4) {i : Axis} {l : List Axis}
    (hi : i ∉ l) (M k : Nat) (f : Cover4 → Int) (g : Nat → Int) :
    listSum (slabSites r o (l ++ [i])) (fun x => f x * rangeSumInt g M (M * 2 ^ k)) =
      listSum (layerRange r) (fun z0 =>
        listSum (slabSites r (o.update i z0) l) f) *
      listSum (List.range k) (fun j => listSum (dyadicShell M j) g) := by
  have hFactor : ∀ (xs : List Cover4) (c : Int),
      listSum xs (fun x => f x * c) = listSum xs f * c := by
    intro xs c
    induction xs with
    | nil => simp [listSum]
    | cons x xs ih =>
      simp only [listSum, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, Int.add_mul]
  rw [hFactor, slab_sum_foliation r o hi f, dyadic_shell_sum_partition M k g]

-- =============================================================================
-- Part 2: Discrete Abel Summation-by-Parts & Monotone-Weight Envelopes
-- =============================================================================

/-- Theorem (Discrete Abel Summation-by-Parts on `[a, b]`):
For all integers `a ≤ b` and sequences `f, g : Nat → Int`,
`∑_{n=a}^{b} f(n) g(n) = (∑_{n=a}^{b} f(n)) * g(b) + ∑_{k=a}^{b-1} (∑_{n=a}^{k} f(n)) * (g(k) - g(k + 1))`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem discrete_abel_summation_by_parts (f g : Nat → Int) (a b : Nat) (hab : a ≤ b) :
    rangeSumInt (fun n => f n * g n) a (b + 1) =
      rangeSumInt f a (b + 1) * g b +
        rangeSumInt (fun k => rangeSumInt f a (k + 1) * (g k - g (k + 1))) a b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero =>
    simp only [Nat.add_zero]
    rw [rangeSumInt_singleton, rangeSumInt_singleton, rangeSumInt_self, Int.add_zero]
  | succ d ih =>
    have had : a ≤ a + d := Nat.le_add_right a d
    have ih' := ih
    have hStepFG : rangeSumInt (fun n => f n * g n) a (a + (d + 1) + 1) =
        rangeSumInt (fun n => f n * g n) a (a + d + 1) + f (a + d + 1) * g (a + d + 1) := by
      have hle : a ≤ a + d + 1 := by omega
      have h := rangeSumInt_succ_right (fun n => f n * g n) hle
      simpa [Nat.add_assoc] using h
    have hStepF : rangeSumInt f a (a + (d + 1) + 1) =
        rangeSumInt f a (a + d + 1) + f (a + d + 1) := by
      have hle : a ≤ a + d + 1 := by omega
      have h := rangeSumInt_succ_right f hle
      simpa [Nat.add_assoc] using h
    have hStepDiff :
        rangeSumInt (fun k => rangeSumInt f a (k + 1) * (g k - g (k + 1))) a (a + (d + 1)) =
        rangeSumInt (fun k => rangeSumInt f a (k + 1) * (g k - g (k + 1))) a (a + d) +
          rangeSumInt f a (a + d + 1) * (g (a + d) - g (a + d + 1)) := by
      have h := rangeSumInt_succ_right
        (fun k => rangeSumInt f a (k + 1) * (g k - g (k + 1))) had
      simpa [Nat.add_assoc] using h
    rw [hStepFG, ih', hStepF, hStepDiff]
    let S : Int := rangeSumInt f a (a + d + 1)
    let x : Int := f (a + d + 1)
    let g0 : Int := g (a + d)
    let g1 : Int := g (a + d + 1)
    change S * g0 + rangeSumInt (fun k => rangeSumInt f a (k + 1) * (g k - g (k + 1))) a (a + d) +
        x * g1 =
      (S + x) * g1 +
        (rangeSumInt (fun k => rangeSumInt f a (k + 1) * (g k - g (k + 1))) a (a + d) +
          S * (g0 - g1))
    have hAlg : S * g0 + x * g1 = (S + x) * g1 + S * (g0 - g1) := by
      rw [Int.add_mul, Int.mul_sub]
      omega
    omega

/-- Theorem (List-Backed Abel Summation-by-Parts with Offset `M`):
For all `M ≤ N` and sequences `a, w : Nat → Int`, with `A(k) = ∑_{0 ≤ i ≤ k} a i`:
`∑_{n=M+1}^{N} a(n) w(n) = (A(N) - A(M)) w(N) + ∑_{k=M+1}^{N-1} (A(k) - A(M)) (w(k) - w(k + 1))`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem abel_summation_by_parts_list (a w : Nat → Int) (M N : Nat) (hMN : M ≤ N) :
    rangeSumInt (fun n => a n * w n) (M + 1) (N + 1) =
      (partialSumInt a N - partialSumInt a M) * w N +
        rangeSumInt (fun k => (partialSumInt a k - partialSumInt a M) * (w k - w (k + 1)))
          (M + 1) N := by
  by_cases hEq : M = N
  · subst hEq
    rw [rangeSumInt_self, Int.sub_self, Int.zero_mul, rangeSumInt_empty _ (Nat.le_succ M),
        Int.add_zero]
  · have hLt : M + 1 ≤ N := by omega
    rw [discrete_abel_summation_by_parts a w (M + 1) N hLt]
    rw [partialSumInt_sub a hMN]
    have hCong :
        rangeSumInt (fun k => rangeSumInt a (M + 1) (k + 1) * (w k - w (k + 1))) (M + 1) N =
        rangeSumInt (fun k => (partialSumInt a k - partialSumInt a M) * (w k - w (k + 1)))
          (M + 1) N := by
      apply rangeSumInt_congr
      intro k hk1 _
      have hMk : M ≤ k := by omega
      rw [partialSumInt_sub a hMk]
    rw [hCong]

private theorem telescope_diff_sum (w : Nat → Int) {a b : Nat} (hab : a ≤ b) :
    rangeSumInt (fun k => w k - w (k + 1)) a b = w a - w b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => simp [rangeSumInt_self]
  | succ d ih =>
    have had : a ≤ a + d := Nat.le_add_right a d
    rw [← Nat.add_assoc, rangeSumInt_succ_right _ had, ih had]
    omega

private theorem bounds_of_natAbs_le {z : Int} {n : Nat}
    (h : Int.natAbs z ≤ n) :
    -(n : Int) ≤ z ∧ z ≤ (n : Int) := by
  cases z with
  | ofNat m =>
    change m ≤ n at h
    exact ⟨Int.le_trans (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg n))
      (Int.natCast_nonneg m), Int.ofNat_le.mpr h⟩
  | negSucc m =>
    change m + 1 ≤ n at h
    exact ⟨Int.neg_le_neg (Int.ofNat_le.mpr h),
      Int.le_trans (Int.le_of_lt (Int.negSucc_lt_zero m)) (Int.natCast_nonneg n)⟩

private theorem int_neg_le_of_add_nonneg {x y : Int} (h : 0 ≤ y + x) : -x ≤ y := by
  have h1 : 0 + -x ≤ y + x + -x := Int.add_le_add_right h (-x)
  rwa [Int.zero_add, Int.add_assoc, Int.add_right_neg, Int.add_zero] at h1

private theorem int_add_nonneg_of_neg_le {x y : Int} (h : -x ≤ y) : 0 ≤ y + x := by
  have h1 : -x + x ≤ y + x := Int.add_le_add_right h x
  rwa [Int.add_left_neg] at h1

private theorem rangeSumInt_abs_weighted_bounds (u c : Nat → Int) (a b : Nat) (B : Nat)
    (hab : a ≤ b)
    (hu : ∀ k, a ≤ k → k < b → Int.natAbs (u k) ≤ B)
    (hc : ∀ k, a ≤ k → k < b → 0 ≤ c k) :
    -((B : Int) * rangeSumInt c a b) ≤ rangeSumInt (fun k => u k * c k) a b ∧
    rangeSumInt (fun k => u k * c k) a b ≤ (B : Int) * rangeSumInt c a b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero =>
    rw [Nat.add_zero, rangeSumInt_self, rangeSumInt_self, Int.mul_zero, Int.neg_zero]
    exact ⟨Int.le_refl 0, Int.le_refl 0⟩
  | succ d ih =>
    have had : a ≤ a + d := Nat.le_add_right a d
    have hu' : ∀ k, a ≤ k → k < a + d → Int.natAbs (u k) ≤ B :=
      fun k h1 h2 => hu k h1 (Nat.lt_trans h2 (Nat.lt_succ_self (a + d)))
    have hc' : ∀ k, a ≤ k → k < a + d → 0 ≤ c k :=
      fun k h1 h2 => hc k h1 (Nat.lt_trans h2 (Nat.lt_succ_self (a + d)))
    have ih' := ih hu' hc'
    have hLastU : Int.natAbs (u (a + d)) ≤ B := hu (a + d) had (Nat.lt_succ_self (a + d))
    have hLastC : 0 ≤ c (a + d) := hc (a + d) had (Nat.lt_succ_self (a + d))
    have hBd := bounds_of_natAbs_le hLastU
    have hMulLo : -((B : Int) * c (a + d)) ≤ u (a + d) * c (a + d) := by
      have h0 : 0 ≤ u (a + d) + (B : Int) := int_add_nonneg_of_neg_le hBd.1
      have h1 : 0 ≤ (u (a + d) + (B : Int)) * c (a + d) := Int.mul_nonneg h0 hLastC
      rw [Int.add_mul] at h1
      exact int_neg_le_of_add_nonneg h1
    have hMulHi : u (a + d) * c (a + d) ≤ (B : Int) * c (a + d) := by
      have h0 : 0 ≤ (B : Int) - u (a + d) := Int.sub_nonneg.mpr hBd.2
      have h1 : 0 ≤ ((B : Int) - u (a + d)) * c (a + d) := Int.mul_nonneg h0 hLastC
      rw [Int.sub_mul] at h1
      exact Int.sub_nonneg.mp h1
    rw [← Nat.add_assoc, rangeSumInt_succ_right (fun k => u k * c k) had,
        rangeSumInt_succ_right c had, Int.mul_add, Int.neg_add]
    exact ⟨Int.add_le_add ih'.1 hMulLo, Int.add_le_add ih'.2 hMulHi⟩

private theorem natAbs_le_of_int_bounds {z : Int} {n : Nat}
    (hLo : -(n : Int) ≤ z) (hHi : z ≤ (n : Int)) :
    Int.natAbs z ≤ n := by
  cases z with
  | ofNat m =>
    change m ≤ n
    exact Int.ofNat_le.mp hHi
  | negSucc m =>
    change m + 1 ≤ n
    have hNeg : -((m + 1 : Nat) : Int) = Int.negSucc m := rfl
    have h1 : -(n : Int) ≤ -((m + 1 : Nat) : Int) := hNeg ▸ hLo
    exact Int.ofNat_le.mp (Int.neg_le_neg_iff.mp h1)

/-- Theorem (Monotone-Weight Abel Summation Remainder Envelope):
Given `a w : Nat → Int`, interval `M < N`, non-negative non-increasing weights
(`0 ≤ w N`, `w (k + 1) ≤ w k` for `M + 1 ≤ k < N`), and uniform Chebyshev partial-sum
remainder `|partialSumInt a k - k| ≤ E` (`M ≤ k ≤ N`), discrete Abel summation-by-parts
contracts the weighted remainder `∑_{n=M+1}^{N} a(n) w(n) - ∑_{n=M+1}^{N} w(n)` to at
most `2 * E * w (M + 1)`, independent of the interval length `N - M`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem abel_monotone_weight_envelope (a w : Nat → Int) (M N E : Nat) (hMN : M < N)
    (hw_nonneg : 0 ≤ w N)
    (hw_anti : ∀ k, M + 1 ≤ k → k < N → w (k + 1) ≤ w k)
    (hRem : ∀ k, M ≤ k → k ≤ N → Int.natAbs (partialSumInt a k - (k : Int)) ≤ E) :
    rangeSumInt w (M + 1) (N + 1) - (2 * E : Int) * w (M + 1) ≤
      rangeSumInt (fun n => a n * w n) (M + 1) (N + 1) ∧
    rangeSumInt (fun n => a n * w n) (M + 1) (N + 1) ≤
      rangeSumInt w (M + 1) (N + 1) + (2 * E : Int) * w (M + 1) ∧
    Int.natAbs (rangeSumInt (fun n => a n * w n) (M + 1) (N + 1) -
        rangeSumInt w (M + 1) (N + 1)) ≤
      2 * E * Int.natAbs (w (M + 1)) := by
  let ones : Nat → Int := fun _ => 1
  have hMNle : M ≤ N := Nat.le_of_lt hMN
  have hAbA := abel_summation_by_parts_list a w M N hMNle
  have hAbOne := abel_summation_by_parts_list ones w M N hMNle
  have hOneSum : rangeSumInt (fun n => ones n * w n) (M + 1) (N + 1) =
      rangeSumInt w (M + 1) (N + 1) := by
    apply rangeSumInt_congr
    intro n _ _
    simp [ones]
  have hDiffSum :
      rangeSumInt (fun n => a n * w n) (M + 1) (N + 1) - rangeSumInt w (M + 1) (N + 1) =
      ((partialSumInt a N - (N : Int)) - (partialSumInt a M - (M : Int))) * w N +
        rangeSumInt (fun k =>
          ((partialSumInt a k - (k : Int)) - (partialSumInt a M - (M : Int))) *
            (w k - w (k + 1))) (M + 1) N := by
    rw [hAbA, ← hOneSum, hAbOne]
    have hTermN :
        ((partialSumInt a N - partialSumInt a M) -
          (partialSumInt ones N - partialSumInt ones M)) * w N =
        ((partialSumInt a N - (N : Int)) - (partialSumInt a M - (M : Int))) * w N := by
      rw [partialSumInt_ones N, partialSumInt_ones M]
      have hZ : (partialSumInt a N - partialSumInt a M) -
          (((N + 1 : Nat) : Int) - ((M + 1 : Nat) : Int)) =
          (partialSumInt a N - (N : Int)) - (partialSumInt a M - (M : Int)) := by omega
      rw [hZ]
    have hDiffTail :
        rangeSumInt (fun k => (partialSumInt a k - partialSumInt a M) * (w k - w (k + 1)))
            (M + 1) N -
          rangeSumInt (fun k => (partialSumInt ones k - partialSumInt ones M) * (w k - w (k + 1)))
            (M + 1) N =
        rangeSumInt (fun k =>
          ((partialSumInt a k - (k : Int)) - (partialSumInt a M - (M : Int))) *
            (w k - w (k + 1))) (M + 1) N := by
      rw [← rangeSumInt_sub]
      apply rangeSumInt_congr
      intro k _ _
      rw [partialSumInt_ones k, partialSumInt_ones M]
      have hSub : ((partialSumInt a k - partialSumInt a M) * (w k - w (k + 1))) -
          ((((k + 1 : Nat) : Int) - ((M + 1 : Nat) : Int)) * (w k - w (k + 1))) =
          ((partialSumInt a k - (k : Int)) - (partialSumInt a M - (M : Int))) *
            (w k - w (k + 1)) := by
        rw [← Int.sub_mul]
        have hZ : (partialSumInt a k - partialSumInt a M) -
            (((k + 1 : Nat) : Int) - ((M + 1 : Nat) : Int)) =
            (partialSumInt a k - (k : Int)) - (partialSumInt a M - (M : Int)) := by omega
        rw [hZ]
      exact hSub
    rw [← hTermN, ← hDiffTail]
    have hAlg (A B T1 T2 wd : Int) : (A * wd + T1) - (B * wd + T2) = (A - B) * wd + (T1 - T2) := by
      rw [Int.sub_mul]
      omega
    exact hAlg _ _ _ _ _
  have hDiffBound : ∀ k, M ≤ k → k ≤ N →
      Int.natAbs ((partialSumInt a k - (k : Int)) - (partialSumInt a M - (M : Int))) ≤ 2 * E := by
    intro k hk1 hk2
    have hBk := bounds_of_natAbs_le (hRem k hk1 hk2)
    have hBm := bounds_of_natAbs_le (hRem M (Nat.le_refl M) hMNle)
    exact natAbs_le_of_int_bounds (by omega) (by omega)
  have hTailBounds :=
    rangeSumInt_abs_weighted_bounds
      (fun k => (partialSumInt a k - (k : Int)) - (partialSumInt a M - (M : Int)))
      (fun k => w k - w (k + 1)) (M + 1) N (2 * E) hMN
      (fun k hk1 hk2 => hDiffBound k (by omega) (Nat.le_of_lt hk2))
      (fun k hk1 hk2 => by
        have ha := hw_anti k hk1 hk2
        omega)
  have hTele : rangeSumInt (fun k => w k - w (k + 1)) (M + 1) N = w (M + 1) - w N :=
    telescope_diff_sum w hMN
  rw [hTele] at hTailBounds
  have hNabs := bounds_of_natAbs_le (hRem N hMNle (Nat.le_refl N))
  have hMabs := bounds_of_natAbs_le (hRem M (Nat.le_refl M) hMNle)
  have hNdiffLo : -((2 * E : Nat) : Int) ≤
      (partialSumInt a N - (N : Int)) - (partialSumInt a M - (M : Int)) := by omega
  have hNdiffHi :
      (partialSumInt a N - (N : Int)) - (partialSumInt a M - (M : Int)) ≤
      ((2 * E : Nat) : Int) := by omega
  have hMulNLo : -((2 * E : Int) * w N) ≤
      ((partialSumInt a N - (N : Int)) - (partialSumInt a M - (M : Int))) * w N := by
    have h1 : 0 ≤ (((partialSumInt a N - (N : Int)) - (partialSumInt a M - (M : Int))) +
        (2 * E : Int)) * w N :=
      Int.mul_nonneg (int_add_nonneg_of_neg_le (by omega : -((2 * E : Int)) ≤ _)) hw_nonneg
    rw [Int.add_mul] at h1
    exact int_neg_le_of_add_nonneg h1
  have hMulNHi :
      ((partialSumInt a N - (N : Int)) - (partialSumInt a M - (M : Int))) * w N ≤
      (2 * E : Int) * w N := by
    have h1 : 0 ≤ ((2 * E : Int) -
        ((partialSumInt a N - (N : Int)) - (partialSumInt a M - (M : Int)))) * w N :=
      Int.mul_nonneg (Int.sub_nonneg.mpr (by omega)) hw_nonneg
    rw [Int.sub_mul] at h1
    exact Int.sub_nonneg.mp h1
  have hCast2E : ((2 * E : Nat) : Int) = (2 * E : Int) := by omega
  have hLo : -((2 * E : Int) * w (M + 1)) ≤
      rangeSumInt (fun n => a n * w n) (M + 1) (N + 1) - rangeSumInt w (M + 1) (N + 1) := by
    rw [hDiffSum]
    rw [hCast2E, Int.mul_sub] at hTailBounds
    omega
  have hHi :
      rangeSumInt (fun n => a n * w n) (M + 1) (N + 1) - rangeSumInt w (M + 1) (N + 1) ≤
      (2 * E : Int) * w (M + 1) := by
    rw [hDiffSum]
    rw [hCast2E, Int.mul_sub] at hTailBounds
    omega
  have hwStartNonneg : 0 ≤ w (M + 1) := by
    have hSumNonneg : 0 ≤ w (M + 1) - w N := by
      have hTailPos : 0 ≤ rangeSumInt (fun k => w k - w (k + 1)) (M + 1) N := by
        have h0 := rangeSumInt_abs_weighted_bounds
          (fun _ => (1 : Int)) (fun k => w k - w (k + 1)) (M + 1) N 1 hMN
          (fun _ _ _ => by decide)
          (fun k hk1 hk2 => by
            have ha := hw_anti k hk1 hk2
            omega)
        have h1 : rangeSumInt (fun k => 1 * (w k - w (k + 1))) (M + 1) N =
            rangeSumInt (fun k => w k - w (k + 1)) (M + 1) N := by
          apply rangeSumInt_congr
          intro k _ _
          exact Int.one_mul _
        rw [h1] at h0
        omega
      rw [hTele] at hTailPos
      exact hTailPos
    omega
  have hwStartNatAbs : (Int.natAbs (w (M + 1)) : Int) = w (M + 1) :=
    Int.natAbs_of_nonneg hwStartNonneg
  have hAbsBound :
      Int.natAbs (rangeSumInt (fun n => a n * w n) (M + 1) (N + 1) -
        rangeSumInt w (M + 1) (N + 1)) ≤
      2 * E * Int.natAbs (w (M + 1)) := by
    apply natAbs_le_of_int_bounds
    · rw [Int.natCast_mul, hwStartNatAbs]
      exact hLo
    · rw [Int.natCast_mul, hwStartNatAbs]
      exact hHi
  exact ⟨by omega, by omega, hAbsBound⟩

/-- Cleared-denominator `QRat` version of `abel_monotone_weight_envelope` for positive
rational weights `w(n) = wNum(n) / D` (`0 < D`). Zero `Classical.choice`, zero `sorryAx`. -/
theorem abel_monotone_weight_envelope_qrat (a wNum : Nat → Int) (M N E D : Nat)
    (hMN : M < N) (hD : 0 < D) (hw_nonneg : 0 ≤ wNum N)
    (hw_anti : ∀ k, M + 1 ≤ k → k < N → wNum (k + 1) ≤ wNum k)
    (hRem : ∀ k, M ≤ k → k ≤ N → Int.natAbs (partialSumInt a k - (k : Int)) ≤ E) :
    QRat.mk' (Int.natAbs (rangeSumInt (fun n => a n * wNum n) (M + 1) (N + 1) -
        rangeSumInt wNum (M + 1) (N + 1)) : Int) D hD ≤
      QRat.mk' ((2 * E * Int.natAbs (wNum (M + 1)) : Nat) : Int) D hD := by
  have hEnv := (abel_monotone_weight_envelope a wNum M N E hMN hw_nonneg hw_anti hRem).2.2
  change _ * (D : Int) ≤ _ * (D : Int)
  exact Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hEnv) (Int.natCast_nonneg D)

-- =============================================================================
-- Part 3: Cleared-Denominator Quadratic 1 / sqrt(N) Tail Gates
-- =============================================================================

/-- Cleared-denominator quadratic tail gate encoding `m * bound ≤ num * sqrt(N)` via
`m^2 * bound^2 ≤ N * num^2`, avoiding `Real.sqrt` and `Classical.choice`. -/
structure SqrtTailGateSpec where
  denomM : Nat
  tailBound : Nat
  scaleN : Nat
  tailNum : Nat
  denomM_pos : 0 < denomM
  scaleN_pos : 0 < scaleN
  gate_le : denomM * denomM * (tailBound * tailBound) ≤ scaleN * (tailNum * tailNum)

/-- Cleared-denominator inverse square-root tail gate encoding `bound / m ≤ num / sqrt(N)`
via `N * bound^2 ≤ m^2 * num^2`, matching `1 / sqrt(N)` contraction budgets. -/
structure InvSqrtTailGateSpec where
  denomM : Nat
  tailBound : Nat
  scaleN : Nat
  tailNum : Nat
  denomM_pos : 0 < denomM
  scaleN_pos : 0 < scaleN
  gate_le : scaleN * (tailBound * tailBound) ≤ denomM * denomM * (tailNum * tailNum)

/-- Construct a `SqrtTailGateSpec` from a linear certificate `m * bound ≤ num * q` and
integer square witness `q^2 ≤ N`. Zero `Classical.choice`, zero `sorryAx`. -/
theorem sqrt_tail_gate_of_sq_le (m bound N num q : Nat)
    (_hm : 0 < m) (_hN : 0 < N)
    (hLin : m * bound ≤ num * q) (hSq : q * q ≤ N) :
    m * m * (bound * bound) ≤ N * (num * num) := by
  have h1 : (m * bound) * (m * bound) ≤ (num * q) * (num * q) := Nat.mul_le_mul hLin hLin
  have hL : (m * bound) * (m * bound) = m * m * (bound * bound) := by ac_rfl
  have hR : (num * q) * (num * q) = (q * q) * (num * num) := by ac_rfl
  have h2 : (q * q) * (num * num) ≤ N * (num * num) := Nat.mul_le_mul_right _ hSq
  rw [hL, hR] at h1
  exact Nat.le_trans h1 h2

/-- Dyadic-scale preservation on `InvSqrtTailGateSpec`: passing from scale `N` to `4 * N`
tightens the denominator from `m` to `2 * m` (`bound / (2 * m) ≤ num / sqrt(4 * N)`).
Zero `Classical.choice`, zero `sorryAx`. -/
theorem inv_sqrt_tail_gate_dyadic_step (g : InvSqrtTailGateSpec) :
    (4 * g.scaleN) * (g.tailBound * g.tailBound) ≤
      ((2 * g.denomM) * (2 * g.denomM)) * (g.tailNum * g.tailNum) := by
  have hL : (4 * g.scaleN) * (g.tailBound * g.tailBound) =
      4 * (g.scaleN * (g.tailBound * g.tailBound)) := by ac_rfl
  have hR : ((2 * g.denomM) * (2 * g.denomM)) * (g.tailNum * g.tailNum) =
      4 * (g.denomM * g.denomM * (g.tailNum * g.tailNum)) := by ac_rfl
  rw [hL, hR]
  exact Nat.mul_le_mul_left 4 g.gate_le

/-- Dyadic-scale doubling on `SqrtTailGateSpec`: passing from `(N, num)` to `(4 * N, 2 * num)`
allows doubling the numerator budget `bound ↦ 2 * bound` or keeping strict headroom.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem sqrt_tail_gate_dyadic_step (g : SqrtTailGateSpec) :
    g.denomM * g.denomM * ((2 * g.tailBound) * (2 * g.tailBound)) ≤
      (4 * g.scaleN) * (g.tailNum * g.tailNum) := by
  have hL : g.denomM * g.denomM * ((2 * g.tailBound) * (2 * g.tailBound)) =
      4 * (g.denomM * g.denomM * (g.tailBound * g.tailBound)) := by ac_rfl
  have hR : (4 * g.scaleN) * (g.tailNum * g.tailNum) =
      4 * (g.scaleN * (g.tailNum * g.tailNum)) := by ac_rfl
  rw [hL, hR]
  exact Nat.mul_le_mul_left 4 g.gate_le

-- =============================================================================
-- Part 4: Short-Interval Chebyshev Tightening & Beyond-7/8 Ladder Certificates
-- =============================================================================

/-- Theorem (Short-Interval Dyadic-Shell & Abel Summation Envelope):
Couples a `ShortIntervalChebyshevSpec` `s`, a dyadic shell partition `[M, M * 2^k)` of
Chebyshev step remainders, a cleared-denominator quadratic `SqrtTailGateSpec`
(`m^2 * bound^2 ≤ N * num^2`), and discrete Abel summation remainder `effErr ≤ s.errUpper`
to certify:
1. Exact dyadic shell conservation `rangeSumInt psiStep M (M * 2^k) = ∑_{j < k} ∑_{dyadicShell M j} psiStep`.
2. Tightened short-interval Chebyshev remainder `|ψ(x + h) - ψ(x) - h| ≤ 2 * effErr`
   with `effErr ≤ s.errUpper` and `m^2 * effErr^2 ≤ N * num^2`.
3. Positivity `(0 : Int) < thetaXH - thetaX` whenever `2 * effErr + s.primePowerCorr < 10 ^ s.hScaleExp`
   (which holds whenever `s.HasGuaranteedPrime` holds!).
Zero `Classical.choice`, zero `sorryAx`. -/
theorem short_interval_dyadic_abel_envelope
    (spec : ChebyshevRemainderSpec) (s : ShortIntervalChebyshevSpec)
    (psiStep : Nat → Int) (M k : Nat)
    (gate : SqrtTailGateSpec) (effErr : Nat)
    (hHleX : s.hScaleExp ≤ s.xScaleExp)
    (hEnv : qrhRemainderBoundAtTwoTenPow spec ≤ s.errUpper)
    (hEffGate : gate.tailBound = effErr)
    (hEffLe : effErr ≤ s.errUpper)
    (psiX psiXH thetaX thetaXH : Int)
    (hBoundX : Int.natAbs (psiX - ((10 ^ s.xScaleExp : Nat) : Int)) ≤ effErr)
    (hBoundXH :
      Int.natAbs (psiXH - ((10 ^ s.xScaleExp + 10 ^ s.hScaleExp : Nat) : Int)) ≤ effErr)
    (hCorr : (psiXH - psiX) - (thetaXH - thetaX) ≤ (s.primePowerCorr : Int))
    (hPrime : s.HasGuaranteedPrime) :
    rangeSumInt psiStep M (M * 2 ^ k) =
      listSum (List.range k) (fun j => listSum (dyadicShell M j) psiStep) ∧
    gate.denomM * gate.denomM * (effErr * effErr) ≤
      gate.scaleN * (gate.tailNum * gate.tailNum) ∧
    Int.natAbs (psiXH - psiX - ((10 ^ s.hScaleExp : Nat) : Int)) ≤ 2 * effErr ∧
    2 * effErr ≤ 2 * s.errUpper ∧
    (0 : Int) < thetaXH - thetaX := by
  have hPart := dyadic_shell_sum_partition M k psiStep
  have hGate : gate.denomM * gate.denomM * (effErr * effErr) ≤
      gate.scaleN * (gate.tailNum * gate.tailNum) := by
    rw [← hEffGate]
    exact gate.gate_le
  have hBoundX' : Int.natAbs (psiX - ((10 ^ s.xScaleExp : Nat) : Int)) ≤ s.errUpper :=
    Nat.le_trans hBoundX hEffLe
  have hBoundXH' :
      Int.natAbs (psiXH - ((10 ^ s.xScaleExp + 10 ^ s.hScaleExp : Nat) : Int)) ≤ s.errUpper :=
    Nat.le_trans hBoundXH hEffLe
  have hX := bounds_of_natAbs_le hBoundX
  have hXH := bounds_of_natAbs_le hBoundXH
  have hTwo : ((2 * effErr : Nat) : Int) = (effErr : Int) + (effErr : Int) := by omega
  have hDiffLo : -((2 * effErr : Nat) : Int) ≤
      psiXH - psiX - ((10 ^ s.hScaleExp : Nat) : Int) := by
    rw [hTwo]
    rw [Int.natCast_add] at hXH
    omega
  have hDiffHi :
      psiXH - psiX - ((10 ^ s.hScaleExp : Nat) : Int) ≤ ((2 * effErr : Nat) : Int) := by
    rw [hTwo]
    rw [Int.natCast_add] at hXH
    omega
  have hAbsTight :
      Int.natAbs (psiXH - psiX - ((10 ^ s.hScaleExp : Nat) : Int)) ≤ 2 * effErr :=
    natAbs_le_of_int_bounds hDiffLo hDiffHi
  have hPos := short_interval_spec_guarantees_theta_pos spec s hHleX hEnv psiX psiXH thetaX thetaXH
    hBoundX' hBoundXH' hCorr hPrime
  exact ⟨hPart, hGate, hAbsTight, Nat.mul_le_mul_left 2 hEffLe, hPos⟩

/-- Concrete `SqrtTailGateSpec` benchmark (`m = 10, bound = 31, N = 1000, num = 1`, verifying
`10^2 * 31^2 = 96100 ≤ 1000 * 1^2 * 100` — scaled `10^2 * 31^2 ≤ 1000 * 10^2` matching
`31 / 10 ≤ sqrt(10)`). -/
def dyadicSqrt10Gate : SqrtTailGateSpec where
  denomM := 10
  tailBound := 31
  scaleN := 1000
  tailNum := 10
  denomM_pos := by decide
  scaleN_pos := by decide
  gate_le := by decide

/-- Concrete `InvSqrtTailGateSpec` benchmark (`bound / m ≤ num / sqrt(N)` with
`m = 16, bound = 1, N = 256, num = 1`: `256 * 1^2 ≤ 16^2 * 1^2`). -/
def dyadicInvSqrt256Gate : InvSqrtTailGateSpec where
  denomM := 16
  tailBound := 1
  scaleN := 256
  tailNum := 1
  denomM_pos := by decide
  scaleN_pos := by decide
  gate_le := by decide

set_option exponentiation.threshold 2000 in
/-- Master concrete certificate for Issue #71 bundling:
1. Concrete dyadic-shell partition `[1, 16) = [1, 2) ∪ [2, 4) ∪ [4, 8) ∪ [8, 16)`.
2. Quadratic tail gates `dyadicSqrt10Gate` and `dyadicInvSqrt256Gate` plus dyadic `4 * N` scaling.
3. Short-interval prime positivity across the beyond-`7/8` QRH ladder
   `shortIntervalQrh1732Spec` (`17/32`), `shortIntervalQrh916Spec` (`9/16`),
   `shortIntervalQrh58Spec` (`5/8`), `shortIntervalQrh23Spec` (`2/3`),
   and `shortIntervalQrh34Spec` (`3/4`), ordered strictly inside `(1/2, 7/8)`.
Zero `Classical.choice`, zero `sorryAx`. -/
theorem dyadic_abel_short_interval_certs :
    (dyadicShellPartition 1 4).flatten = halfOpenRange 1 16 ∧
    dyadicSqrt10Gate.denomM * dyadicSqrt10Gate.denomM *
        (dyadicSqrt10Gate.tailBound * dyadicSqrt10Gate.tailBound) ≤
      dyadicSqrt10Gate.scaleN * (dyadicSqrt10Gate.tailNum * dyadicSqrt10Gate.tailNum) ∧
    (4 * dyadicInvSqrt256Gate.scaleN) *
        (dyadicInvSqrt256Gate.tailBound * dyadicInvSqrt256Gate.tailBound) ≤
      ((2 * dyadicInvSqrt256Gate.denomM) * (2 * dyadicInvSqrt256Gate.denomM)) *
        (dyadicInvSqrt256Gate.tailNum * dyadicInvSqrt256Gate.tailNum) ∧
    shortIntervalQrh1732Spec.HasGuaranteedPrime ∧
    shortIntervalQrh916Spec.HasGuaranteedPrime ∧
    shortIntervalQrh58Spec.HasGuaranteedPrime ∧
    shortIntervalQrh23Spec.HasGuaranteedPrime ∧
    shortIntervalQrh34Spec.HasGuaranteedPrime ∧
    (QRat.mk' 1 2 < shortIntervalQrh1732Spec.thetaQRat ∧
     shortIntervalQrh1732Spec.thetaQRat < shortIntervalQrh916Spec.thetaQRat ∧
     shortIntervalQrh916Spec.thetaQRat < shortIntervalQrh58Spec.thetaQRat ∧
     shortIntervalQrh58Spec.thetaQRat < shortIntervalQrh23Spec.thetaQRat ∧
     shortIntervalQrh23Spec.thetaQRat < shortIntervalQrh34Spec.thetaQRat ∧
     shortIntervalQrh34Spec.thetaQRat < qrhThresholdSevenEighths) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact dyadicSqrt10Gate.gate_le
  · exact inv_sqrt_tail_gate_dyadic_step dyadicInvSqrt256Gate
  · exact shortIntervalQrh1732Spec_has_prime
  · exact sub_three_quarters_qrh_ladder_certs.2.2.2.2.2.1
  · exact sub_three_quarters_qrh_ladder_certs.2.2.2.2.1.1
  · exact sub_three_quarters_qrh_ladder_certs.2.2.2.1.1
  · exact qrh_short_interval_positivity_certs.2.1
  · decide

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/DyadicAbelBridge.lean
