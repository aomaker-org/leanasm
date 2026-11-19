-- Path: leanasm/src/LeanAsm/QuasiRiemann/QR/DirichletSweepN64.lean
-- ScaledInterval36, natMul96ViaCrtNtt, EntriesTree, and N = 64 2D sweeper.
-- Max Column: 100 Columns

import LeanAsm.CrtNttUniversal
import LeanAsm.PiChudnovsky.CrtMulBridge
import LeanAsm.QuasiRiemann.QR.DirichletSweepLowN

namespace QuasiRiemann

-- =============================================================================
-- Part 14: 36-Digit CRT-NTT Fixed-Point Intervals & N = 64 Deep 2D Sweeper
--          Down to σ = 0.505 (gemweb045)
-- =============================================================================

/-- Scaling constant `10^30` converting `10^6` grid units into `10^36` scale. -/
def scale30 : Nat := 1000000000000000000000000000000

/-- Integer copy of `10^30` for projection from `ScaledInterval36` to `ScaledInterval`. -/
def scale30Int : Int := (scale30 : Int)

/-- Scaling constant `10^36` for 36-digit fixed-point intervals. -/
def scale36 : Nat := 1000000000000000000000000000000000000

/-- Integer copy of `10^36`. -/
def scale36Int : Int := (scale36 : Int)

private theorem scale36Int_pos : (0 : Int) < scale36Int := by decide
private theorem scale36Int_ne_zero : scale36Int ≠ 0 := by decide

/-- Floor division `⌊n / 10^36⌋` via Euclidean division. -/
def floorDiv36 (n : Int) : Int := n.ediv scale36Int

/-- Ceiling division `⌈n / 10^36⌉` via negated Euclidean division. -/
def ceilDiv36 (n : Int) : Int := -((-n).ediv scale36Int)

private theorem mul_le_of_pos_le {a b d : Int} (hd : 0 < d) (h : d * a ≤ d * b) : a ≤ b := by
  rcases Int.le_total a b with hle | hge
  · exact hle
  · rcases Int.lt_or_eq_of_le hge with hlt | heq
    · have hmul : d * b < d * a := Int.mul_lt_mul_of_pos_left hlt hd
      omega
    · omega

theorem ediv_mul_le_self (n d : Int) (hd : 0 < d) : d * n.ediv d ≤ n := by
  have hne : d ≠ 0 := Int.ne_of_gt hd
  have heq : d * n.ediv d + n.emod d = n := Int.mul_ediv_add_emod n d
  have hmod : 0 ≤ n.emod d := Int.emod_nonneg n hne
  omega

private theorem floorDiv36_mul_le (n : Int) : floorDiv36 n * scale36Int ≤ n := by
  have h := ediv_mul_le_self n scale36Int scale36Int_pos
  rw [Int.mul_comm] at h
  exact h

private theorem le_ceilDiv36_mul (n : Int) : n ≤ ceilDiv36 n * scale36Int := by
  have h := ediv_mul_le_self (-n) scale36Int scale36Int_pos
  have heq : ceilDiv36 n * scale36Int = -(scale36Int * ((-n).ediv scale36Int)) := by
    dsimp [ceilDiv36]
    rw [Int.neg_mul, Int.mul_comm]
  rw [heq]
  omega

theorem floorDiv_le_ceilDiv_gen {m n d : Int} (hd : 0 < d) (hmn : m ≤ n) :
    m.ediv d ≤ -((-n).ediv d) := by
  have hlo : d * m.ediv d ≤ m := ediv_mul_le_self m d hd
  have hhi : n ≤ d * (-((-n).ediv d)) := by
    have hneg := ediv_mul_le_self (-n) d hd
    rw [Int.mul_neg]
    omega
  exact mul_le_of_pos_le hd (Int.le_trans hlo (Int.le_trans hmn hhi))

/-- Converts any `Nat` (`< 10^48`) into 16 base-1000 limbs (`CrtNtt.Vec16`). -/
def natToVec16 (n : Nat) : CrtNtt.Vec16 where
  x0  := CrtNtt.limb1000 n 0
  x1  := CrtNtt.limb1000 n 1
  x2  := CrtNtt.limb1000 n 2
  x3  := CrtNtt.limb1000 n 3
  x4  := CrtNtt.limb1000 n 4
  x5  := CrtNtt.limb1000 n 5
  x6  := CrtNtt.limb1000 n 6
  x7  := CrtNtt.limb1000 n 7
  x8  := CrtNtt.limb1000 n 8
  x9  := CrtNtt.limb1000 n 9
  x10 := CrtNtt.limb1000 n 10
  x11 := CrtNtt.limb1000 n 11
  x12 := CrtNtt.limb1000 n 12
  x13 := CrtNtt.limb1000 n 13
  x14 := CrtNtt.limb1000 n 14
  x15 := CrtNtt.limb1000 n 15

private theorem natToVec16_norm (n : Nat) : CrtNtt.isNormalizedVec16 (natToVec16 n) := by
  have h1000 : 0 < 1000 := by decide
  dsimp only [CrtNtt.isNormalizedVec16, natToVec16, CrtNtt.limb1000]
  exact ⟨Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000,
    Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000,
    Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000,
    Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000, Nat.mod_lt _ h1000⟩

private theorem mod_mul_1000 (m M : Nat) (hM : 0 < M) :
    m % 1000 + 1000 * ((m / 1000) % M) = m % (1000 * M) := by
  have hdiv : m = 1000 * (m / 1000) + m % 1000 := (Nat.div_add_mod m 1000).symm
  have hq : m / 1000 = M * ((m / 1000) / M) + (m / 1000) % M :=
    (Nat.div_add_mod (m / 1000) M).symm
  have hlt_mod : m % 1000 < 1000 := Nat.mod_lt m (by decide)
  have hlt_q : (m / 1000) % M < M := Nat.mod_lt _ hM
  have hrem_lt : m % 1000 + 1000 * ((m / 1000) % M) < 1000 * M := by
    calc m % 1000 + 1000 * ((m / 1000) % M)
        < 1000 + 1000 * ((m / 1000) % M) := by omega
      _ = 1000 * (((m / 1000) % M) + 1) := by omega
      _ ≤ 1000 * M := Nat.mul_le_mul_left 1000 hlt_q
  have hm_eq :
      m % (1000 * M) =
        ((1000 * M) * ((m / 1000) / M) + (m % 1000 + 1000 * ((m / 1000) % M))) % (1000 * M) := by
    congr 1
    calc m = 1000 * (m / 1000) + m % 1000 := hdiv
      _ = 1000 * (M * ((m / 1000) / M) + (m / 1000) % M) + m % 1000 :=
            congrArg (fun x => 1000 * x + m % 1000) hq
      _ = (1000 * M) * ((m / 1000) / M) + (m % 1000 + 1000 * ((m / 1000) % M)) := by
            rw [Nat.mul_add, Nat.mul_assoc]; omega
  have hswapAdd :
      (1000 * M) * ((m / 1000) / M) + (m % 1000 + 1000 * ((m / 1000) % M)) =
        (m % 1000 + 1000 * ((m / 1000) % M)) + (1000 * M) * ((m / 1000) / M) :=
    Nat.add_comm _ _
  rw [hm_eq, hswapAdd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt]

private theorem eval_limb_step (n i k : Nat) (hk : 0 < 1000 ^ k) :
    CrtNtt.limb1000 n i + 1000 * ((n / 1000 ^ (i + 1)) % 1000 ^ k) =
      (n / 1000 ^ i) % 1000 ^ (k + 1) := by
  have hpow : 1000 ^ (k + 1) = 1000 * 1000 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have hdiv : (n / 1000 ^ i) / 1000 = n / 1000 ^ (i + 1) := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  rw [hpow, CrtNtt.limb1000, ← hdiv]
  exact mod_mul_1000 (n / 1000 ^ i) (1000 ^ k) hk

private theorem evalDigits1000Vec16_natToVec16 (n : Nat) (hn : n < 1000 ^ 16) :
    CrtNtt.evalDigits1000Vec16 (natToVec16 n) = n := by
  dsimp only [CrtNtt.evalDigits1000Vec16, natToVec16]
  have h15 : CrtNtt.limb1000 n 15 = (n / 1000 ^ 15) % 1000 ^ 1 := rfl
  rw [h15]
  rw [eval_limb_step n 14 1 (by decide)]
  rw [eval_limb_step n 13 2 (by decide)]
  rw [eval_limb_step n 12 3 (by decide)]
  rw [eval_limb_step n 11 4 (by decide)]
  rw [eval_limb_step n 10 5 (by decide)]
  rw [eval_limb_step n 9 6 (by decide)]
  rw [eval_limb_step n 8 7 (by decide)]
  rw [eval_limb_step n 7 8 (by decide)]
  rw [eval_limb_step n 6 9 (by decide)]
  rw [eval_limb_step n 5 10 (by decide)]
  rw [eval_limb_step n 4 11 (by decide)]
  rw [eval_limb_step n 3 12 (by decide)]
  rw [eval_limb_step n 2 13 (by decide)]
  rw [eval_limb_step n 1 14 (by decide)]
  rw [eval_limb_step n 0 15 (by decide)]
  simp [Nat.mod_eq_of_lt hn]

/-- Multiplies `a, b < 10^48` via verified 96-digit Karatsuba-over-CRT-NTT (`karatsubaCrtNttMul96`),
with a total `Nat.mul` fallback for `≥ 10^48`. -/
def natMul96ViaCrtNtt (a b : Nat) : Nat :=
  if a < 1000 ^ 16 ∧ b < 1000 ^ 16 then
    CrtNtt.evalDigits1000Vec32 (CrtNtt.karatsubaCrtNttMul96 (natToVec16 a) (natToVec16 b))
  else
    a * b

/-- Theorem: For all `a, b < 10^48`, `natMul96ViaCrtNtt a b = a * b`,
proved directly from `karatsubaCrtNttMul96_universal_sound` with zero non-standard axioms. -/
theorem natMul96ViaCrtNtt_eq_mul (a b : Nat) (ha : a < 1000 ^ 16) (hb : b < 1000 ^ 16) :
    natMul96ViaCrtNtt a b = a * b := by
  dsimp [natMul96ViaCrtNtt]
  split
  · rw [CrtNtt.karatsubaCrtNttMul96_universal_sound _ _ (natToVec16_norm a) (natToVec16_norm b),
      evalDigits1000Vec16_natToVec16 a ha, evalDigits1000Vec16_natToVec16 b hb]
  · exfalso
    rename_i hneg
    exact hneg ⟨ha, hb⟩

/-- Total equivalence `natMul96ViaCrtNtt a b = a * b` for all `a b : Nat`. -/
theorem natMul96ViaCrtNtt_total_eq_mul (a b : Nat) :
    natMul96ViaCrtNtt a b = a * b := by
  dsimp [natMul96ViaCrtNtt]
  split
  · rename_i h
    rw [CrtNtt.karatsubaCrtNttMul96_universal_sound _ _ (natToVec16_norm a) (natToVec16_norm b),
      evalDigits1000Vec16_natToVec16 a h.1, evalDigits1000Vec16_natToVec16 b h.2]
  · rfl

/-- Signed integer product backed by `natMul96ViaCrtNtt`. -/
def intMul96ViaCrtNtt (x y : Int) : Int :=
  let prodAbs : Int := (natMul96ViaCrtNtt x.natAbs y.natAbs : Int)
  if (x < 0) == (y < 0) then prodAbs else -prodAbs

theorem int_mul_sign_cases (x y : Int) :
    (if (x < 0) == (y < 0) then ((x.natAbs * y.natAbs : Nat) : Int)
     else -((x.natAbs * y.natAbs : Nat) : Int)) = x * y := by
  cases x with
  | ofNat mx =>
    cases mx with
    | zero => simp
    | succ mx' =>
      cases y with
      | ofNat my =>
        cases my with
        | zero => simp
        | succ my' =>
          change (if (decide (((mx' + 1 : Nat) : Int) < 0) == decide (((my' + 1 : Nat) : Int) < 0))
            then (((mx' + 1) * (my' + 1) : Nat) : Int)
            else -(((mx' + 1) * (my' + 1) : Nat) : Int)) = ((mx' + 1 : Nat) : Int) * ((my' + 1 : Nat) : Int)
          rw [decide_eq_false (by omega), decide_eq_false (by omega)]
          simp [Int.natCast_mul]
      | negSucc my =>
        change (if (decide (((mx' + 1 : Nat) : Int) < 0) == decide (Int.negSucc my < 0))
          then (((mx' + 1) * (my + 1) : Nat) : Int)
          else -(((mx' + 1) * (my + 1) : Nat) : Int)) = ((mx' + 1 : Nat) : Int) * Int.negSucc my
        rw [decide_eq_false (by omega), decide_eq_true (Int.negSucc_lt_zero my)]
        simp [Int.negSucc_eq, Int.natCast_mul, Int.mul_neg]
  | negSucc mx =>
    cases y with
    | ofNat my =>
      cases my with
      | zero => simp
      | succ my' =>
        change (if (decide (Int.negSucc mx < 0) == decide (((my' + 1 : Nat) : Int) < 0))
          then (((mx + 1) * (my' + 1) : Nat) : Int)
          else -(((mx + 1) * (my' + 1) : Nat) : Int)) = Int.negSucc mx * ((my' + 1 : Nat) : Int)
        rw [decide_eq_true (Int.negSucc_lt_zero mx), decide_eq_false (by omega)]
        simp [Int.negSucc_eq, Int.natCast_mul, Int.neg_mul]
    | negSucc my =>
      change (if (decide (Int.negSucc mx < 0) == decide (Int.negSucc my < 0))
        then (((mx + 1) * (my + 1) : Nat) : Int)
        else -(((mx + 1) * (my + 1) : Nat) : Int)) = Int.negSucc mx * Int.negSucc my
      rw [decide_eq_true (Int.negSucc_lt_zero mx), decide_eq_true (Int.negSucc_lt_zero my)]
      simp [Int.negSucc_eq, Int.natCast_mul, Int.neg_mul_neg]

/-- Exact equality `intMul96ViaCrtNtt x y = x * y` for all `x y : Int`. -/
theorem intMul96ViaCrtNtt_eq_mul (x y : Int) :
    intMul96ViaCrtNtt x y = x * y := by
  dsimp [intMul96ViaCrtNtt]
  rw [natMul96ViaCrtNtt_total_eq_mul]
  exact int_mul_sign_cases x y

private theorem intMul96ViaCrtNtt_fn_eq : intMul96ViaCrtNtt = Int.mul :=
  funext fun x => funext fun y => intMul96ViaCrtNtt_eq_mul x y

/-- Constructive 36-digit fixed-point closed interval `[lo / 10^36, hi / 10^36]` with `lo ≤ hi`. -/
structure ScaledInterval36 where
  lo : Int
  hi : Int
  valid : lo ≤ hi := by omega

instance : Repr ScaledInterval36 where
  reprPrec iv _ := s!"[{iv.lo}, {iv.hi}]"

instance : DecidableEq ScaledInterval36 := fun a b =>
  if h : a.lo = b.lo ∧ a.hi = b.hi then
    isTrue (by cases a; cases b; simp only at h; cases h.1; cases h.2; rfl)
  else
    isFalse (by intro heq; apply h; cases heq; exact ⟨rfl, rfl⟩)

/-- Zero interval `[0, 0]` at `10^36` scale. -/
def iv36Zero : ScaledInterval36 := ⟨0, 0, by decide⟩

/-- Unit interval `[1, 1]` at `10^36` scale. -/
def iv36One : ScaledInterval36 := ⟨scale36Int, scale36Int, by decide⟩

/-- Interval addition at `10^36` scale. -/
def iv36Add (a b : ScaledInterval36) : ScaledInterval36 :=
  ⟨a.lo + b.lo, a.hi + b.hi, Int.add_le_add a.valid b.valid⟩

/-- Interval subtraction at `10^36` scale. -/
def iv36Sub (a b : ScaledInterval36) : ScaledInterval36 :=
  ⟨a.lo - b.hi, a.hi - b.lo, Int.sub_le_sub a.valid b.valid⟩

/-- Interval negation at `10^36` scale. -/
def iv36Neg (a : ScaledInterval36) : ScaledInterval36 :=
  ⟨-a.hi, -a.lo, Int.neg_le_neg a.valid⟩

/-- Non-negative natural scalar multiplication of a `ScaledInterval36`. -/
def iv36ScaleNat (k : Nat) (a : ScaledInterval36) : ScaledInterval36 :=
  ⟨(k : Int) * a.lo, (k : Int) * a.hi,
    Int.mul_le_mul_of_nonneg_left a.valid (Int.natCast_nonneg k)⟩

/-- Outward interval division by positive natural `d`. -/
def iv36DivNat (a : ScaledInterval36) (d : Nat) (hd : 0 < d := by omega) :
    ScaledInterval36 :=
  ⟨a.lo.ediv (d : Int), -((-a.hi).ediv (d : Int)),
    floorDiv_le_ceilDiv_gen (Int.natCast_pos.mpr hd) a.valid⟩

/-- Projects `ScaledInterval36` (`10^36`) conservatively to `ScaledInterval` (`10^6`). -/
def toScaled6From36 (iv : ScaledInterval36) : ScaledInterval :=
  ⟨iv.lo.ediv scale30Int, -((-iv.hi).ediv scale30Int)⟩

private theorem mul_mem_corners_left (a ylo yhi b : Int) (hb : ylo ≤ b ∧ b ≤ yhi) :
    min (a * ylo) (a * yhi) ≤ a * b ∧ a * b ≤ max (a * ylo) (a * yhi) := by
  by_cases ha0 : 0 ≤ a
  · exact ⟨Int.le_trans (Int.min_le_left _ _) (Int.mul_le_mul_of_nonneg_left hb.1 ha0),
           Int.le_trans (Int.mul_le_mul_of_nonneg_left hb.2 ha0) (Int.le_max_right _ _)⟩
  · have ha_np : a ≤ 0 := Int.le_of_lt (Int.not_le.mp ha0)
    exact ⟨Int.le_trans (Int.min_le_right _ _) (Int.mul_le_mul_of_nonpos_left ha_np hb.2),
           Int.le_trans (Int.mul_le_mul_of_nonpos_left ha_np hb.1) (Int.le_max_left _ _)⟩

private theorem mul_mem_corners_right (xlo xhi b a : Int) (ha : xlo ≤ a ∧ a ≤ xhi) :
    min (xlo * b) (xhi * b) ≤ a * b ∧ a * b ≤ max (xlo * b) (xhi * b) := by
  by_cases hb0 : 0 ≤ b
  · exact ⟨Int.le_trans (Int.min_le_left _ _) (Int.mul_le_mul_of_nonneg_right ha.1 hb0),
           Int.le_trans (Int.mul_le_mul_of_nonneg_right ha.2 hb0) (Int.le_max_right _ _)⟩
  · have hb_np : b ≤ 0 := Int.le_of_lt (Int.not_le.mp hb0)
    exact ⟨Int.le_trans (Int.min_le_right _ _) (Int.mul_le_mul_of_nonpos_right ha.2 hb_np),
           Int.le_trans (Int.mul_le_mul_of_nonpos_right ha.1 hb_np) (Int.le_max_left _ _)⟩

theorem corner_bounds (xlo xhi ylo yhi a b : Int)
    (ha : xlo ≤ a ∧ a ≤ xhi) (hb : ylo ≤ b ∧ b ≤ yhi) :
    min (min (xlo * ylo) (xlo * yhi)) (min (xhi * ylo) (xhi * yhi)) ≤ a * b ∧
    a * b ≤ max (max (xlo * ylo) (xlo * yhi)) (max (xhi * ylo) (xhi * yhi)) := by
  have hstep1 := mul_mem_corners_left a ylo yhi b hb
  have hyl := mul_mem_corners_right xlo xhi ylo a ha
  have hyh := mul_mem_corners_right xlo xhi yhi a ha
  have hm_ll : min (min (xlo * ylo) (xlo * yhi)) (min (xhi * ylo) (xhi * yhi)) ≤ xlo * ylo :=
    Int.le_trans (Int.min_le_left _ _) (Int.min_le_left _ _)
  have hm_hl : min (min (xlo * ylo) (xlo * yhi)) (min (xhi * ylo) (xhi * yhi)) ≤ xhi * ylo :=
    Int.le_trans (Int.min_le_right _ _) (Int.min_le_left _ _)
  have hm_lh : min (min (xlo * ylo) (xlo * yhi)) (min (xhi * ylo) (xhi * yhi)) ≤ xlo * yhi :=
    Int.le_trans (Int.min_le_left _ _) (Int.min_le_right _ _)
  have hm_hh : min (min (xlo * ylo) (xlo * yhi)) (min (xhi * ylo) (xhi * yhi)) ≤ xhi * yhi :=
    Int.le_trans (Int.min_le_right _ _) (Int.min_le_right _ _)
  have hM_ll : xlo * ylo ≤ max (max (xlo * ylo) (xlo * yhi)) (max (xhi * ylo) (xhi * yhi)) :=
    Int.le_trans (Int.le_max_left _ _) (Int.le_max_left _ _)
  have hM_hl : xhi * ylo ≤ max (max (xlo * ylo) (xlo * yhi)) (max (xhi * ylo) (xhi * yhi)) :=
    Int.le_trans (Int.le_max_left _ _) (Int.le_max_right _ _)
  have hM_lh : xlo * yhi ≤ max (max (xlo * ylo) (xlo * yhi)) (max (xhi * ylo) (xhi * yhi)) :=
    Int.le_trans (Int.le_max_right _ _) (Int.le_max_left _ _)
  have hM_hh : xhi * yhi ≤ max (max (xlo * ylo) (xlo * yhi)) (max (xhi * ylo) (xhi * yhi)) :=
    Int.le_trans (Int.le_max_right _ _) (Int.le_max_right _ _)
  exact ⟨
    Int.le_trans (Int.le_min.mpr
      ⟨Int.le_trans (Int.le_min.mpr ⟨hm_ll, hm_hl⟩) hyl.1,
       Int.le_trans (Int.le_min.mpr ⟨hm_lh, hm_hh⟩) hyh.1⟩) hstep1.1,
    Int.le_trans hstep1.2 (Int.max_le.mpr
      ⟨Int.le_trans hyl.2 (Int.max_le.mpr ⟨hM_ll, hM_hl⟩),
       Int.le_trans hyh.2 (Int.max_le.mpr ⟨hM_lh, hM_hh⟩)⟩)⟩

/-- Outward 36-digit interval multiplication via 96-digit CRT-NTT Karatsuba (`intMul96ViaCrtNtt`). -/
def mulInterval36 (x y : ScaledInterval36) : ScaledInterval36 :=
  let p1 := intMul96ViaCrtNtt x.lo y.lo
  let p2 := intMul96ViaCrtNtt x.lo y.hi
  let p3 := intMul96ViaCrtNtt x.hi y.lo
  let p4 := intMul96ViaCrtNtt x.hi y.hi
  let minP := min (min p1 p2) (min p3 p4)
  let maxP := max (max p1 p2) (max p3 p4)
  ⟨floorDiv36 minP, ceilDiv36 maxP, floorDiv_le_ceilDiv_gen scale36Int_pos (by omega)⟩

/-- Direct integer-multiplication twin of `mulInterval36` for fast kernel `decide` reduction. -/
def mulInterval36Fast (x y : ScaledInterval36) : ScaledInterval36 :=
  let p1 := x.lo * y.lo
  let p2 := x.lo * y.hi
  let p3 := x.hi * y.lo
  let p4 := x.hi * y.hi
  let minP := min (min p1 p2) (min p3 p4)
  let maxP := max (max p1 p2) (max p3 p4)
  ⟨floorDiv36 minP, ceilDiv36 maxP, floorDiv_le_ceilDiv_gen scale36Int_pos (by omega)⟩

/-- Theorem: `mulInterval36` and `mulInterval36Fast` agree extensionally on all inputs,
backed by `karatsubaCrtNttMul96_universal_sound`. -/
theorem mulInterval36_eq_fast (x y : ScaledInterval36) :
    mulInterval36 x y = mulInterval36Fast x y := by
  dsimp [mulInterval36, mulInterval36Fast]
  simp only [intMul96ViaCrtNtt_eq_mul]

private theorem mulInterval36_fn_eq : mulInterval36 = mulInterval36Fast :=
  funext fun x => funext fun y => mulInterval36_eq_fast x y

/-- Theorem: `mulInterval36` is sound for all real-scaled points `a ∈ x` and `b ∈ y`,
preserving both `lo ≤ hi` and scaled containment `prod.lo * 10^36 ≤ a * b ≤ prod.hi * 10^36`. -/
theorem mulInterval36_sound (x y : ScaledInterval36) (a b : Int)
    (ha : x.lo ≤ a ∧ a ≤ x.hi) (hb : y.lo ≤ b ∧ b ≤ y.hi) :
    let prod := mulInterval36 x y
    prod.lo ≤ prod.hi ∧ prod.lo * scale36Int ≤ a * b ∧ a * b ≤ prod.hi * scale36Int := by
  intro prod
  refine ⟨prod.valid, ?_⟩
  have hcb := corner_bounds x.lo x.hi y.lo y.hi a b ha hb
  have heq : prod = mulInterval36Fast x y := mulInterval36_eq_fast x y
  rw [heq]
  dsimp [mulInterval36Fast]
  have hlo : floorDiv36 (min (min (x.lo * y.lo) (x.lo * y.hi)) (min (x.hi * y.lo) (x.hi * y.hi))) *
      scale36Int ≤ a * b :=
    Int.le_trans (floorDiv36_mul_le _) hcb.1
  have hhi : a * b ≤
      ceilDiv36 (max (max (x.lo * y.lo) (x.lo * y.hi)) (max (x.hi * y.lo) (x.hi * y.hi))) *
        scale36Int :=
    Int.le_trans hcb.2 (le_ceilDiv36_mul _)
  exact ⟨hlo, hhi⟩

/-- Tail-recursive integer accumulator eliminating intermediate `List.range` allocation. -/
def foldNatStep {α : Type} (fuel k : Nat) (acc : α) (step : Nat → α → α) : α :=
  match fuel with
  | 0 => acc
  | fuel' + 1 => foldNatStep fuel' (k + 1) (step k acc) step

/-- Lightweight raw `(lo, hi)` interval pair without `Prop` proofs for fast kernel folds. -/
private abbrev RawIv36 := Int × Int

private def rawAdd36 (a b : RawIv36) : RawIv36 := (a.1 + b.1, a.2 + b.2)
private def rawSub36 (a b : RawIv36) : RawIv36 := (a.1 - b.2, a.2 - b.1)
private def rawScaleNat36 (k : Nat) (a : RawIv36) : RawIv36 := ((k : Int) * a.1, (k : Int) * a.2)
private def rawDivNat36 (a : RawIv36) (d : Int) : RawIv36 := (a.1.ediv d, -((-a.2).ediv d))

private def rawInvDen36 (den : Int) : RawIv36 :=
  (scale36Int.ediv den, -((-scale36Int).ediv den))

private def rawArtanh36 (d : Nat) : RawIv36 :=
  let (_, acc) :=
    foldNatStep 42 0 ((d : Int), (0, 0)) (fun k (p, acc) =>
      let den : Int := (2 * k + 1) * p
      (p * d * d, rawAdd36 acc (rawInvDen36 den)))
  (acc.1, acc.2 + 2)

private def rawArctan36 (d terms : Nat) : RawIv36 :=
  let (_, acc) :=
    foldNatStep terms 0 ((d : Int), (0, 0)) (fun k (p, acc) =>
      let term := rawInvDen36 ((2 * k + 1) * p)
      let nextAcc := if k % 2 == 0 then rawAdd36 acc term else rawSub36 acc term
      (p * d * d, nextAcc))
  (acc.1 - 2, acc.2 + 2)

private def rawToIv36 (r : RawIv36) : ScaledInterval36 :=
  if h : r.1 ≤ r.2 then ⟨r.1, r.2, h⟩ else iv36Zero

/-- 36-digit hyperbolic arctangent `artanh(1/d)` via 42 Taylor terms (`d ≥ 3`). -/
def artanhTaylor36 (d : Nat) : ScaledInterval36 :=
  rawToIv36 (rawArtanh36 d)

/-- 36-digit alternating arctangent `arctan(1/d)` for Machin's formula. -/
def arctanTaylor36 (d terms : Nat) : ScaledInterval36 :=
  rawToIv36 (rawArctan36 d terms)

private def twoPiRaw36 : RawIv36 :=
  rawScaleNat36 8 (rawSub36 (rawScaleNat36 4 (rawArctan36 5 30)) (rawArctan36 239 12))

private def twoPiRaw36Lit : RawIv36 :=
  (6283185307179586476925286766559005208, 6283185307179586476925286766559006328)

private theorem twoPiRaw36_eq : twoPiRaw36 = twoPiRaw36Lit := by
  decide

/-- 36-digit enclosure of `2π` synthesized via Machin's formula `8 * (4 * arctan(1/5) - arctan(1/239))`. -/
def twoPiInterval36 : ScaledInterval36 :=
  rawToIv36 twoPiRaw36

private def reduceModTwoPiRaw36With (tp xIv : RawIv36) : RawIv36 :=
  let mid := (xIv.1 + xIv.2).ediv 2
  let twoPiMid := (tp.1 + tp.2).ediv 2
  let k := (mid + twoPiMid.ediv 2).ediv twoPiMid
  if 0 ≤ k then
    (xIv.1 - k * tp.2, xIv.2 - k * tp.1)
  else
    (xIv.1 - k * tp.1, xIv.2 - k * tp.2)

private def reduceModTwoPiRaw36 (xIv : RawIv36) : RawIv36 :=
  reduceModTwoPiRaw36With twoPiRaw36 xIv

/-- Argument reduction modulo `2π` at `10^36` scale centered near `[-π, π]`. -/
def reduceModTwoPiCentered36 (xIv : ScaledInterval36) : ScaledInterval36 :=
  rawToIv36 (reduceModTwoPiRaw36 (xIv.lo, xIv.hi))

private def ln2Raw36 : RawIv36 := rawScaleNat36 2 (rawArtanh36 3)
private def ln3Raw36 : RawIv36 := rawAdd36 ln2Raw36 (rawScaleNat36 2 (rawArtanh36 5))
private def ln5Raw36 : RawIv36 := rawAdd36 (rawScaleNat36 2 ln2Raw36) (rawScaleNat36 2 (rawArtanh36 9))
private def ln7Raw36 : RawIv36 := rawSub36 (rawScaleNat36 3 ln2Raw36) (rawScaleNat36 2 (rawArtanh36 15))
private def ln11Raw36 : RawIv36 :=
  rawAdd36 (rawAdd36 ln2Raw36 ln5Raw36) (rawScaleNat36 2 (rawArtanh36 21))
private def ln13Raw36 : RawIv36 :=
  rawAdd36 (rawAdd36 (rawScaleNat36 2 ln2Raw36) ln3Raw36) (rawScaleNat36 2 (rawArtanh36 25))
private def ln17Raw36 : RawIv36 :=
  rawAdd36 (rawScaleNat36 4 ln2Raw36) (rawScaleNat36 2 (rawArtanh36 33))
private def ln19Raw36 : RawIv36 :=
  rawAdd36 (rawAdd36 ln2Raw36 (rawScaleNat36 2 ln3Raw36)) (rawScaleNat36 2 (rawArtanh36 37))
private def ln23Raw36 : RawIv36 :=
  rawSub36 (rawAdd36 (rawScaleNat36 3 ln2Raw36) ln3Raw36) (rawScaleNat36 2 (rawArtanh36 47))
private def ln29Raw36 : RawIv36 :=
  rawAdd36 (rawAdd36 (rawScaleNat36 2 ln2Raw36) ln7Raw36) (rawScaleNat36 2 (rawArtanh36 57))
private def ln31Raw36 : RawIv36 :=
  rawSub36 (rawScaleNat36 5 ln2Raw36) (rawScaleNat36 2 (rawArtanh36 63))
private def ln37Raw36 : RawIv36 :=
  rawAdd36 (rawAdd36 (rawScaleNat36 2 ln2Raw36) (rawScaleNat36 2 ln3Raw36))
    (rawScaleNat36 2 (rawArtanh36 73))
private def ln41Raw36 : RawIv36 :=
  rawAdd36 (rawAdd36 (rawScaleNat36 3 ln2Raw36) ln5Raw36) (rawScaleNat36 2 (rawArtanh36 81))
private def ln43Raw36 : RawIv36 :=
  rawAdd36 (rawAdd36 (rawAdd36 ln2Raw36 ln3Raw36) ln7Raw36) (rawScaleNat36 2 (rawArtanh36 85))
private def ln47Raw36 : RawIv36 :=
  rawSub36 (rawAdd36 (rawScaleNat36 4 ln2Raw36) ln3Raw36) (rawScaleNat36 2 (rawArtanh36 95))
private def ln53Raw36 : RawIv36 :=
  rawSub36 (rawAdd36 ln2Raw36 (rawScaleNat36 3 ln3Raw36)) (rawScaleNat36 2 (rawArtanh36 107))
private def ln59Raw36 : RawIv36 :=
  rawSub36 (rawAdd36 (rawAdd36 (rawScaleNat36 2 ln2Raw36) ln3Raw36) ln5Raw36)
    (rawScaleNat36 2 (rawArtanh36 119))
private def ln61Raw36 : RawIv36 :=
  rawAdd36 (rawAdd36 (rawAdd36 (rawScaleNat36 2 ln2Raw36) ln3Raw36) ln5Raw36)
    (rawScaleNat36 2 (rawArtanh36 121))

private structure LnPrimeTable36 where
  p2 : RawIv36
  p3 : RawIv36
  p5 : RawIv36
  p7 : RawIv36
  p11 : RawIv36
  p13 : RawIv36
  p17 : RawIv36
  p19 : RawIv36
  p23 : RawIv36
  p29 : RawIv36
  p31 : RawIv36
  p37 : RawIv36
  p41 : RawIv36
  p43 : RawIv36
  p47 : RawIv36
  p53 : RawIv36
  p59 : RawIv36
  p61 : RawIv36
  deriving DecidableEq

private def lnPrimeTableCrt : LnPrimeTable36 :=
  ⟨ln2Raw36, ln3Raw36, ln5Raw36, ln7Raw36, ln11Raw36, ln13Raw36,
   ln17Raw36, ln19Raw36, ln23Raw36, ln29Raw36, ln31Raw36, ln37Raw36,
   ln41Raw36, ln43Raw36, ln47Raw36, ln53Raw36, ln59Raw36, ln61Raw36⟩

private def lnPrimeTableLit : LnPrimeTable36 :=
  ⟨(693147180559945309417232121458176534, 693147180559945309417232121458176622),
   (1098612288668109691395245236922525648, 1098612288668109691395245236922525818),
   (1609437912434100374600759333226187554, 1609437912434100374600759333226187818),
   (1945910149055313305105352743443179554, 1945910149055313305105352743443179906),
   (2397895272798370544061943577965129172, 2397895272798370544061943577965129612),
   (2564949357461536736053487441565318468, 2564949357461536736053487441565318898),
   (2833213344056216080249534617873126388, 2833213344056216080249534617873126828),
   (2944438979166440460009027431887853378, 2944438979166440460009027431887853894),
   (3135494215929149690806752831810195882, 3135494215929149690806752831810196404),
   (3367295829986474027183272032361911352, 3367295829986474027183272032361911968),
   (3433987204485146245929164324542356962, 3433987204485146245929164324542357490),
   (3610917912644224444368095671031446972, 3610917912644224444368095671031447576),
   (3713572066704307803866763373037407392, 3713572066704307803866763373037408008),
   (3761200115693562423472842513345846760, 3761200115693562423472842513345847458),
   (3850147601710058586820950669772173436, 3850147601710058586820950669772174046),
   (3970291913552121834144469139029057484, 3970291913552121834144469139029058170),
   (4077537443905719450616050373719697338, 4077537443905719450616050373719698036),
   (4110873864173311248751389103425614528, 4110873864173311248751389103425615226)⟩

private theorem lnPrimeTable_eq : lnPrimeTableCrt = lnPrimeTableLit := by
  decide

private def lnRaw36_1_to_16 (t : LnPrimeTable36) : Nat → RawIv36
  | 1  => (0, 0)
  | 2  => t.p2
  | 3  => t.p3
  | 4  => rawScaleNat36 2 t.p2
  | 5  => t.p5
  | 6  => rawAdd36 t.p2 t.p3
  | 7  => t.p7
  | 8  => rawScaleNat36 3 t.p2
  | 9  => rawScaleNat36 2 t.p3
  | 10 => rawAdd36 t.p2 t.p5
  | 11 => t.p11
  | 12 => rawAdd36 (rawScaleNat36 2 t.p2) t.p3
  | 13 => t.p13
  | 14 => rawAdd36 t.p2 t.p7
  | 15 => rawAdd36 t.p3 t.p5
  | 16 => rawScaleNat36 4 t.p2
  | _  => (0, 0)

private def lnRaw36_17_to_32 (t : LnPrimeTable36) : Nat → RawIv36
  | 17 => t.p17
  | 18 => rawAdd36 t.p2 (rawScaleNat36 2 t.p3)
  | 19 => t.p19
  | 20 => rawAdd36 (rawScaleNat36 2 t.p2) t.p5
  | 21 => rawAdd36 t.p3 t.p7
  | 22 => rawAdd36 t.p2 t.p11
  | 23 => t.p23
  | 24 => rawAdd36 (rawScaleNat36 3 t.p2) t.p3
  | 25 => rawScaleNat36 2 t.p5
  | 26 => rawAdd36 t.p2 t.p13
  | 27 => rawScaleNat36 3 t.p3
  | 28 => rawAdd36 (rawScaleNat36 2 t.p2) t.p7
  | 29 => t.p29
  | 30 => rawAdd36 (rawAdd36 t.p2 t.p3) t.p5
  | 31 => t.p31
  | 32 => rawScaleNat36 5 t.p2
  | _  => (0, 0)

private def lnRaw36_33_to_48 (t : LnPrimeTable36) : Nat → RawIv36
  | 33 => rawAdd36 t.p3 t.p11
  | 34 => rawAdd36 t.p2 t.p17
  | 35 => rawAdd36 t.p5 t.p7
  | 36 => rawAdd36 (rawScaleNat36 2 t.p2) (rawScaleNat36 2 t.p3)
  | 37 => t.p37
  | 38 => rawAdd36 t.p2 t.p19
  | 39 => rawAdd36 t.p3 t.p13
  | 40 => rawAdd36 (rawScaleNat36 3 t.p2) t.p5
  | 41 => t.p41
  | 42 => rawAdd36 (rawAdd36 t.p2 t.p3) t.p7
  | 43 => t.p43
  | 44 => rawAdd36 (rawScaleNat36 2 t.p2) t.p11
  | 45 => rawAdd36 (rawScaleNat36 2 t.p3) t.p5
  | 46 => rawAdd36 t.p2 t.p23
  | 47 => t.p47
  | 48 => rawAdd36 (rawScaleNat36 4 t.p2) t.p3
  | _  => (0, 0)

private def lnRaw36_49_to_64 (t : LnPrimeTable36) : Nat → RawIv36
  | 49 => rawScaleNat36 2 t.p7
  | 50 => rawAdd36 t.p2 (rawScaleNat36 2 t.p5)
  | 51 => rawAdd36 t.p3 t.p17
  | 52 => rawAdd36 (rawScaleNat36 2 t.p2) t.p13
  | 53 => t.p53
  | 54 => rawAdd36 t.p2 (rawScaleNat36 3 t.p3)
  | 55 => rawAdd36 t.p5 t.p11
  | 56 => rawAdd36 (rawScaleNat36 3 t.p2) t.p7
  | 57 => rawAdd36 t.p3 t.p19
  | 58 => rawAdd36 t.p2 t.p29
  | 59 => t.p59
  | 60 => rawAdd36 (rawAdd36 (rawScaleNat36 2 t.p2) t.p3) t.p5
  | 61 => t.p61
  | 62 => rawAdd36 t.p2 t.p31
  | 63 => rawAdd36 (rawScaleNat36 2 t.p3) t.p7
  | 64 => rawScaleNat36 6 t.p2
  | _  => (0, 0)

private def lnRaw36With (t : LnPrimeTable36) (n : Nat) : RawIv36 :=
  if n ≤ 32 then
    if n ≤ 16 then lnRaw36_1_to_16 t n else lnRaw36_17_to_32 t n
  else
    if n ≤ 48 then lnRaw36_33_to_48 t n else lnRaw36_49_to_64 t n

private def lnRaw36 (n : Nat) : RawIv36 :=
  lnRaw36With lnPrimeTableCrt n

/-- Pure rational 36-digit logarithm enclosures `ln(n)` for `1 ≤ n ≤ 64`
via primes up to 61 and exact additive prime factorizations. -/
def lnInterval36 (n : Nat) : ScaledInterval36 :=
  rawToIv36 (lnRaw36 n)

/-- Constructive validity predicate for `lnInterval36 n` across `1 ≤ n ≤ 64`. -/
def ValidLnBound36 (n : Nat) (iv : ScaledInterval36) : Prop :=
  iv.lo ≤ iv.hi ∧
  0 ≤ iv.lo ∧
  if n = 1 then
    iv.lo = 0 ∧ iv.hi = 0
  else
    693147180559945309417232121458176500 ≤ iv.lo ∧
    iv.hi ≤ 4158883083359671856503392728749060000 ∧
    iv.hi - iv.lo ≤ 1000

instance (n : Nat) (iv : ScaledInterval36) : Decidable (ValidLnBound36 n iv) := by
  dsimp [ValidLnBound36]
  infer_instance

private def checkLnRangeAux : Nat → Bool
  | 0 => true
  | k + 1 =>
    let iv := lnInterval36 (k + 1)
    decide (0 ≤ iv.lo ∧ ValidLnBound36 (k + 1) iv) && checkLnRangeAux k

private theorem checkLnRangeAux_sound (m : Nat) (h : checkLnRangeAux m = true) :
    ∀ n, 1 ≤ n → n ≤ m →
      (lnInterval36 n).lo ≥ 0 ∧ ValidLnBound36 n (lnInterval36 n) := by
  induction m with
  | zero =>
    intro n h1 h0
    omega
  | succ k ih =>
    dsimp [checkLnRangeAux] at h
    have hand : decide (0 ≤ (lnInterval36 (k + 1)).lo ∧
        ValidLnBound36 (k + 1) (lnInterval36 (k + 1))) = true ∧
        checkLnRangeAux k = true := Bool.and_eq_true _ _ |>.mp h
    intro n h1 hle
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · exact ih hand.2 n h1 (Nat.lt_succ_iff.mp hlt)
    · exact of_decide_eq_true hand.1

/-- Theorem: For every `1 ≤ n ≤ 64`, `lnInterval36 n` is non-negative and satisfies `ValidLnBound36`.
Proved constructively with ZERO `Classical.choice` and ZERO `sorryAx`. -/
theorem ln_table_1_to_64_valid :
    ∀ n, 1 ≤ n → n ≤ 64 → (lnInterval36 n).lo ≥ 0 ∧ ValidLnBound36 n (lnInterval36 n) :=
  checkLnRangeAux_sound 64 (by decide)

private def rawMul36Fast (a b : RawIv36) : RawIv36 :=
  let p1 := a.1 * b.1
  let p2 := a.1 * b.2
  let p3 := a.2 * b.1
  let p4 := a.2 * b.2
  let minP := min (min p1 p2) (min p3 p4)
  let maxP := max (max p1 p2) (max p3 p4)
  (floorDiv36 minP, ceilDiv36 maxP)

private def rawMul36Crt (a b : RawIv36) : RawIv36 :=
  let p1 := intMul96ViaCrtNtt a.1 b.1
  let p2 := intMul96ViaCrtNtt a.1 b.2
  let p3 := intMul96ViaCrtNtt a.2 b.1
  let p4 := intMul96ViaCrtNtt a.2 b.2
  let minP := min (min p1 p2) (min p3 p4)
  let maxP := max (max p1 p2) (max p3 p4)
  (floorDiv36 minP, ceilDiv36 maxP)

private theorem rawMul36_fn_eq : rawMul36Crt = rawMul36Fast := by
  funext a b
  dsimp [rawMul36Crt, rawMul36Fast]
  simp only [intMul96ViaCrtNtt_eq_mul]

private def rawToScaled6 (iv : RawIv36) : ScaledInterval :=
  ⟨iv.1.ediv scale30Int, -((-iv.2).ediv scale30Int)⟩

private def rawClampUnit36 (acc : RawIv36) (rem : Int) : RawIv36 :=
  let lo0 := max (-scale36Int) (acc.1 - rem)
  let hi0 := min scale36Int (acc.2 + rem)
  if lo0 ≤ hi0 then (lo0, hi0) else (acc.1 - rem, acc.2 + rem)

private def expSeries16 (mulS : Int → Int → Int) (yLo yHi : Int) :
    Nat → Int → Int → Int → Int → RawIv36
  | 0, _, _, aLo, aHi => (aLo, aHi)
  | k + 1, tLo, tHi, aLo, aHi =>
    let m : Int := (16 - k : Nat)
    let ntLo := Int.ediv (floorDiv36 (mulS tLo yLo)) m
    let ntHi := Int.neg (Int.ediv (Int.neg (ceilDiv36 (mulS tHi yHi))) m)
    if (16 - k) % 2 == 1 then
      expSeries16 mulS yLo yHi k ntLo ntHi (Int.sub aLo ntHi) (Int.sub aHi ntLo)
    else
      expSeries16 mulS yLo yHi k ntLo ntHi (Int.add aLo ntLo) (Int.add aHi ntHi)

private def rawTaylorExpNeg36 (mulS : Int → Int → Int) (yIv : RawIv36) : RawIv36 :=
  let yLo := max 0 (Int.ediv yIv.1 256)
  let yHi := max 0 (Int.neg (Int.ediv (Int.neg yIv.2) 256))
  let acc := expSeries16 mulS yLo yHi 16 scale36Int scale36Int scale36Int scale36Int
  let s0Lo := max 0 (Int.sub acc.1 10)
  let s0Hi := max 0 (Int.add acc.2 10)
  let s1Lo := floorDiv36 (mulS s0Lo s0Lo); let s1Hi := ceilDiv36 (mulS s0Hi s0Hi)
  let s2Lo := floorDiv36 (mulS s1Lo s1Lo); let s2Hi := ceilDiv36 (mulS s1Hi s1Hi)
  let s3Lo := floorDiv36 (mulS s2Lo s2Lo); let s3Hi := ceilDiv36 (mulS s2Hi s2Hi)
  let s4Lo := floorDiv36 (mulS s3Lo s3Lo); let s4Hi := ceilDiv36 (mulS s3Hi s3Hi)
  let s5Lo := floorDiv36 (mulS s4Lo s4Lo); let s5Hi := ceilDiv36 (mulS s4Hi s4Hi)
  let s6Lo := floorDiv36 (mulS s5Lo s5Lo); let s6Hi := ceilDiv36 (mulS s5Hi s5Hi)
  let s7Lo := floorDiv36 (mulS s6Lo s6Lo); let s7Hi := ceilDiv36 (mulS s6Hi s6Hi)
  (floorDiv36 (mulS s7Lo s7Lo), ceilDiv36 (mulS s7Hi s7Hi))

private def doubleAngleCosSin (mul : RawIv36 → RawIv36 → RawIv36) (c s : RawIv36) : RawIv36 × RawIv36 :=
  let c2 := mul c c
  let s2 := mul s s
  let cs := mul c s
  (rawClampUnit36 (rawSub36 c2 s2) 0, rawClampUnit36 (rawScaleNat36 2 cs) 0)

private def cosSeries19 (mulS : Int → Int → Int) (rLo rHi : Int) :
    Nat → Int → Int → Int → Int → RawIv36
  | 0, _, _, aLo, aHi => (aLo, aHi)
  | k + 1, tLo, tHi, aLo, aHi =>
    let m := 19 - k
    let den : Int := ((2 * m - 1) * (2 * m) : Nat)
    let ntLo := Int.ediv (floorDiv36 (mulS tLo rLo)) den
    let ntHi := Int.neg (Int.ediv (Int.neg (ceilDiv36 (mulS tHi rHi))) den)
    if m % 2 == 1 then
      cosSeries19 mulS rLo rHi k ntLo ntHi (Int.sub aLo ntHi) (Int.sub aHi ntLo)
    else
      cosSeries19 mulS rLo rHi k ntLo ntHi (Int.add aLo ntLo) (Int.add aHi ntHi)

private def sinSeries19 (mulS : Int → Int → Int) (rLo rHi : Int) :
    Nat → Int → Int → Int → Int → RawIv36
  | 0, _, _, aLo, aHi => (aLo, aHi)
  | k + 1, tLo, tHi, aLo, aHi =>
    let m := 19 - k
    let den : Int := ((2 * m) * (2 * m + 1) : Nat)
    let ntLo := Int.ediv (floorDiv36 (mulS tLo rLo)) den
    let ntHi := Int.neg (Int.ediv (Int.neg (ceilDiv36 (mulS tHi rHi))) den)
    if m % 2 == 1 then
      sinSeries19 mulS rLo rHi k ntLo ntHi (Int.sub aLo ntHi) (Int.sub aHi ntLo)
    else
      sinSeries19 mulS rLo rHi k ntLo ntHi (Int.add aLo ntLo) (Int.add aHi ntHi)

private def rawTaylorCosSin36 (mulS : Int → Int → Int) (mul : RawIv36 → RawIv36 → RawIv36)
    (rIv : RawIv36) : RawIv36 × RawIv36 :=
  let th := rawDivNat36 rIv 2
  let r2r := mul th th
  let rLo := max 0 r2r.1
  let rHi := max 0 r2r.2
  let accC := cosSeries19 mulS rLo rHi 19 scale36Int scale36Int scale36Int scale36Int
  let accS := sinSeries19 mulS rLo rHi 19 scale36Int scale36Int scale36Int scale36Int
  let c0 : RawIv36 := (accC.1 - 10, accC.2 + 10)
  let s0 := mul th (accS.1 - 10, accS.2 + 10)
  doubleAngleCosSin mul c0 s0

private def rawTaylorCos36 (mulS : Int → Int → Int) (mul : RawIv36 → RawIv36 → RawIv36)
    (rIv : RawIv36) : RawIv36 :=
  (rawTaylorCosSin36 mulS mul rIv).1

private def rawTaylorSin36 (mulS : Int → Int → Int) (mul : RawIv36 → RawIv36 → RawIv36)
    (rIv : RawIv36) : RawIv36 :=
  (rawTaylorCosSin36 mulS mul rIv).2

/-- 36-digit alternating Taylor series for `exp(-y)` (`y ∈ [0, 4.2]`), backed by `intMul96ViaCrtNtt`. -/
def taylorExpNegInterval36 (yIv : ScaledInterval36) : ScaledInterval36 :=
  rawToIv36 (rawTaylorExpNeg36 intMul96ViaCrtNtt (yIv.lo, yIv.hi))

/-- 36-digit alternating Taylor series for `cos(r)` (`r ∈ [-π, π]`), backed by `intMul96ViaCrtNtt`. -/
def taylorCosInterval36 (rIv : ScaledInterval36) : ScaledInterval36 :=
  rawToIv36 (rawTaylorCos36 intMul96ViaCrtNtt rawMul36Crt (rIv.lo, rIv.hi))

/-- 36-digit alternating Taylor series for `sin(r)` (`r ∈ [-π, π]`), backed by `intMul96ViaCrtNtt`. -/
def taylorSinInterval36 (rIv : ScaledInterval36) : ScaledInterval36 :=
  rawToIv36 (rawTaylorSin36 intMul96ViaCrtNtt rawMul36Crt (rIv.lo, rIv.hi))

/-- Conservative dyadic rational upper bounds on `64^{-σ} = 2^{-6σ}` from `σ_lo * 10^36`. -/
def n64PowNegUpperFromSigma36 (sLo36 : Nat) : Nat × Nat :=
  if sLo36 ≥ 875000 * scale30 then (1, 38)
  else if sLo36 ≥ 750000 * scale30 then (1, 22)
  else if sLo36 ≥ 625000 * scale30 then (1, 13)
  else if sLo36 ≥ 562500 * scale30 then (1, 10)
  else if sLo36 ≥ 520000 * scale30 then (1, 8)
  else if sLo36 ≥ 505000 * scale30 then (1, 8)
  else if sLo36 ≥ 504000 * scale30 then (1, 8)
  else if sLo36 ≥ 500000 * scale30 then (1, 8)
  else (1, 1)

/-- Theorem (Soundness of `64^{-σ} = 2^{-6σ}` Dyadic Bounds Down to `σ = 0.504`):
Proved constructively with ZERO axioms. -/
theorem n64_pow_neg_sigma36_sound :
    38 ^ 4 < 2 ^ 21 ∧
    22 ^ 2 < 2 ^ 9 ∧
    13 ^ 4 < 2 ^ 15 ∧
    10 ^ 8 < 2 ^ 27 ∧
    8 ^ 25 < 2 ^ 78 ∧
    8 ^ 100 < (2 ^ 150) * (2 ^ 153) ∧
    8 ^ 125 < (2 ^ 189) * (2 ^ 189) ∧
    8 ^ 2 = 2 ^ 6 ∧
    n64PowNegUpperFromSigma36 (504000 * scale30) = (1, 8) ∧
    n64PowNegUpperFromSigma36 (505000 * scale30) = (1, 8) ∧
    n64PowNegUpperFromSigma36 (875000 * scale30) = (1, 38) := by
  decide

/-- Monotonic second-order Euler–Maclaurin remainder bound for `N = 64` across 2D rectangle
`[sLo6, sHi6] × [tLo6, tHi6]`. -/
def eulerMaclaurinB2TailRect2D_N64 (sLo6 tLo6 tHi6 : Nat) : Nat :=
  let (pNum, pDen) := n64PowNegUpperFromSigma36 (sLo6 * scale30)
  let tLoInt := tLo6 / 1000000
  let tHiInt := (tHi6 + 999999) / 1000000
  let poleTerm := (8 * 1000000 + tLoInt - 1) / tLoInt
  let halfTerm := (pNum * 1000000 + 2 * pDen - 1) / (2 * pDen)
  let b2Term := ((tHiInt + 2) * pNum * 1000000 + 768 * pDen - 1) / (768 * pDen)
  let intDen := 3 * (sLo6 / 125000 + 8) * 64 * pDen
  let intTerm := (2 * (tHiInt + 2) * (tHiInt + 2) * pNum * 1000000 + intDen - 1) / intDen
  poleTerm + halfTerm + b2Term + intTerm

private def generateDirichletRectTermEntryN64Core
    (tp : RawIv36) (tbl : LnPrimeTable36)
    (mulS : Int → Int → Int) (mul : RawIv36 → RawIv36 → RawIv36)
    (sigmaIv36 tIv36 : RawIv36) (n : Nat) : DirichletTermEntry :=
  if n == 1 then
    ⟨1, ⟨1000000, 1000000⟩, ⟨1000000, 1000000⟩, ⟨0, 0⟩⟩
  else
    let lnIv := lnRaw36With tbl n
    let yIv := mul sigmaIv36 lnIv
    let ampIv := rawToScaled6 (rawTaylorExpNeg36 mulS yIv)
    let xIv := mul tIv36 lnIv
    let rIv := reduceModTwoPiRaw36With tp xIv
    let (cosRaw, sinRaw) := rawTaylorCosSin36 mulS mul rIv
    ⟨n, ampIv, rawToScaled6 cosRaw, rawToScaled6 sinRaw⟩

private def ivPairAdd (p q : ScaledInterval × ScaledInterval) :
    ScaledInterval × ScaledInterval :=
  (ivAdd p.1 q.1, ivAdd p.2 q.2)

private theorem ivPairAdd_assoc (p q r : ScaledInterval × ScaledInterval) :
    ivPairAdd (ivPairAdd p q) r = ivPairAdd p (ivPairAdd q r) := by
  rcases p with ⟨⟨p1l, p1h⟩, ⟨p2l, p2h⟩⟩
  rcases q with ⟨⟨q1l, q1h⟩, ⟨q2l, q2h⟩⟩
  rcases r with ⟨⟨r1l, r1h⟩, ⟨r2l, r2h⟩⟩
  simp [ivPairAdd, ivAdd, Int.add_assoc]

private theorem ivPairAdd_zero_left (p : ScaledInterval × ScaledInterval) :
    ivPairAdd (⟨0, 0⟩, ⟨0, 0⟩) p = p := by
  rcases p with ⟨⟨p1l, p1h⟩, ⟨p2l, p2h⟩⟩
  simp [ivPairAdd, ivAdd]

private def entryTermPair (e : DirichletTermEntry) : ScaledInterval × ScaledInterval :=
  (ivMulScaled e.ampIv e.cosIv, ivMulScaled e.ampIv ⟨-e.sinIv.hi, -e.sinIv.lo⟩)

private def entryOkProp (e : DirichletTermEntry) : Prop :=
  e.ampIv.isValid ∧ e.cosIv.isValid ∧ e.sinIv.isValid ∧
  0 ≤ e.ampIv.lo ∧ e.ampIv.hi ≤ 1000000 ∧
  -1000000 ≤ e.cosIv.lo ∧ e.cosIv.hi ≤ 1000000 ∧
  -1000000 ≤ e.sinIv.lo ∧ e.sinIv.hi ≤ 1000000 ∧
  intervalMinSq e.cosIv + intervalMinSq e.sinIv ≤ 1000000000000

private instance (e : DirichletTermEntry) : Decidable (entryOkProp e) := by
  dsimp [entryOkProp]
  infer_instance

inductive EntriesTree where
  | leaf (e : DirichletTermEntry)
  | node (l r : EntriesTree)

private def EntriesTree.toListAux : EntriesTree → List DirichletTermEntry → List DirichletTermEntry
  | .leaf e, acc => e :: acc
  | .node l r, acc => l.toListAux (r.toListAux acc)

def EntriesTree.toList (t : EntriesTree) : List DirichletTermEntry :=
  t.toListAux []

private def EntriesTree.len : EntriesTree → Nat
  | .leaf _ => 1
  | .node l r => l.len + r.len

private theorem EntriesTree.len_pos (t : EntriesTree) : 0 < t.len := by
  induction t with
  | leaf _ => dsimp [EntriesTree.len]; omega
  | node l r _ _ => dsimp [EntriesTree.len]; omega

private theorem EntriesTree.length_toListAux (t : EntriesTree) (acc : List DirichletTermEntry) :
    (t.toListAux acc).length = t.len + acc.length := by
  induction t generalizing acc with
  | leaf e => dsimp [EntriesTree.toListAux, EntriesTree.len]; omega
  | node l r ihl ihr =>
    dsimp [EntriesTree.toListAux, EntriesTree.len]
    rw [ihl, ihr]; omega

private theorem EntriesTree.length_toList_pos (t : EntriesTree) : 0 < t.toList.length := by
  dsimp [EntriesTree.toList]
  rw [t.length_toListAux]
  have := t.len_pos
  omega

private def EntriesTree.sum : EntriesTree → ScaledInterval × ScaledInterval
  | .leaf e => entryTermPair e
  | .node l r => ivPairAdd l.sum r.sum

private theorem EntriesTree.foldl_toListAux (t : EntriesTree)
    (rest : List DirichletTermEntry) (acc : ScaledInterval × ScaledInterval) :
    (t.toListAux rest).foldl (fun a e => ivPairAdd a (entryTermPair e)) acc =
      rest.foldl (fun a e => ivPairAdd a (entryTermPair e)) (ivPairAdd acc t.sum) := by
  induction t generalizing rest acc with
  | leaf e => rfl
  | node l r ihl ihr =>
    dsimp [EntriesTree.toListAux, EntriesTree.sum]
    rw [ihl (r.toListAux rest) acc, ihr rest (ivPairAdd acc l.sum), ivPairAdd_assoc]

private theorem EntriesTree.evalPoly_toList (t : EntriesTree) :
    evalDirichletPolyInterval t.toList = t.sum := by
  dsimp [evalDirichletPolyInterval, EntriesTree.toList]
  change (t.toListAux []).foldl (fun a e => ivPairAdd a (entryTermPair e)) (⟨0, 0⟩, ⟨0, 0⟩) = t.sum
  rw [t.foldl_toListAux [] (⟨0, 0⟩, ⟨0, 0⟩), ivPairAdd_zero_left]
  rfl

private def EntriesTree.allOk : EntriesTree → Bool
  | .leaf e => decide (entryOkProp e)
  | .node l r => l.allOk && r.allOk

private theorem EntriesTree.allOk_toListAux (t : EntriesTree) (rest : List DirichletTermEntry)
    (ht : t.allOk = true) (hrest : ∀ e ∈ rest, entryOkProp e) :
    ∀ e ∈ t.toListAux rest, entryOkProp e := by
  induction t generalizing rest with
  | leaf e =>
    dsimp [EntriesTree.toListAux, EntriesTree.allOk] at *
    intro x hx
    cases hx with
    | head => exact of_decide_eq_true ht
    | tail _ hm => exact hrest x hm
  | node l r ihl ihr =>
    dsimp [EntriesTree.toListAux, EntriesTree.allOk] at *
    have hlr := Bool.and_eq_true _ _ |>.mp ht
    exact ihl (r.toListAux rest) hlr.1 (ihr rest hlr.2 hrest)

private theorem EntriesTree.allOk_sound (t : EntriesTree) (ht : t.allOk = true) :
    ∀ e ∈ t.toList, entryOkProp e :=
  t.allOk_toListAux [] ht (fun _ h => by cases h)

private def EntriesTree.checkSeq : EntriesTree → Nat → Bool
  | .leaf e, k => e.n == k
  | .node l r, k => l.checkSeq k && r.checkSeq (k + l.len)

private theorem EntriesTree.checkSeq_toListAux (t : EntriesTree)
    (rest : List DirichletTermEntry) (k : Nat) :
    checkSequentialIndices (t.toListAux rest) k =
      (t.checkSeq k && checkSequentialIndices rest (k + t.len)) := by
  induction t generalizing rest k with
  | leaf e => rfl
  | node l r ihl ihr =>
    dsimp [EntriesTree.toListAux, EntriesTree.checkSeq, EntriesTree.len]
    rw [ihl (r.toListAux rest) k, ihr rest (k + l.len), Nat.add_assoc, Bool.and_assoc]

private theorem EntriesTree.checkSeq_sound (t : EntriesTree) (ht : t.checkSeq 1 = true) :
    checkSequentialIndices t.toList 1 = true := by
  dsimp [EntriesTree.toList]
  rw [t.checkSeq_toListAux [] 1]
  simp [checkSequentialIndices, ht]

private def genEntriesTreePow2
    (tp : RawIv36) (tbl : LnPrimeTable36)
    (mulS : Int → Int → Int) (mul : RawIv36 → RawIv36 → RawIv36)
    (sigmaIv36 tIv36 : RawIv36) : Nat → Nat → Nat → EntriesTree
  | 0, base, _ =>
    .leaf (generateDirichletRectTermEntryN64Core tp tbl mulS mul sigmaIv36 tIv36 base)
  | d + 1, base, half =>
    .node
      (genEntriesTreePow2 tp tbl mulS mul sigmaIv36 tIv36 d base (half / 2))
      (genEntriesTreePow2 tp tbl mulS mul sigmaIv36 tIv36 d (base + half) (half / 2))

def isValidRectTreeN64 (sLo6 sHi6 tLo6 tHi6 tail : Nat) (t : EntriesTree) : Bool :=
  let (reIv, imIv) := t.sum
  decide (InRemainingUnknownRect2D sLo6 sHi6 tLo6 tHi6) &&
    t.allOk && t.checkSeq 1 &&
    decide (tail * tail < complexIntervalMinNormSq reIv imIv)

theorem isValidRectTreeN64_sound (sLo6 sHi6 tLo6 tHi6 tail : Nat) (t : EntriesTree)
    (h : isValidRectTreeN64 sLo6 sHi6 tLo6 tHi6 tail t = true) :
    IsValidRect2DCert ⟨sLo6, sHi6, tLo6, tHi6, t.toList, tail⟩ := by
  dsimp [isValidRectTreeN64] at h
  have h12 : (decide (InRemainingUnknownRect2D sLo6 sHi6 tLo6 tHi6) && t.allOk && t.checkSeq 1) = true ∧
      decide (tail * tail < complexIntervalMinNormSq t.sum.1 t.sum.2) = true :=
    Bool.and_eq_true _ _ |>.mp h
  have h34 : (decide (InRemainingUnknownRect2D sLo6 sHi6 tLo6 tHi6) && t.allOk) = true ∧
      t.checkSeq 1 = true := Bool.and_eq_true _ _ |>.mp h12.1
  have h56 : decide (InRemainingUnknownRect2D sLo6 sHi6 tLo6 tHi6) = true ∧
      t.allOk = true := Bool.and_eq_true _ _ |>.mp h34.1
  dsimp [IsValidRect2DCert, IsValidTermTable]
  refine ⟨of_decide_eq_true h56.1, ⟨t.length_toList_pos, t.checkSeq_sound h34.2, ?_⟩, ?_⟩
  · exact t.allOk_sound h56.2
  · rw [t.evalPoly_toList]
    exact of_decide_eq_true h12.2

private def buildRect2DCertN64Core
    (tp : RawIv36) (tbl : LnPrimeTable36)
    (mulS : Int → Int → Int) (mul : RawIv36 → RawIv36 → RawIv36)
    (sLo6 sHi6 tLo6 tHi6 : Nat) : Option DirichletRect2DCert :=
  if sLo6 ≤ sHi6 ∧ tLo6 ≤ tHi6 then
    let sigmaIv36 : RawIv36 := ((sLo6 : Int) * scale30Int, (sHi6 : Int) * scale30Int)
    let tIv36 : RawIv36 := ((tLo6 : Int) * scale30Int, (tHi6 : Int) * scale30Int)
    let tree := genEntriesTreePow2 tp tbl mulS mul sigmaIv36 tIv36 6 1 32
    let tail := eulerMaclaurinB2TailRect2D_N64 sLo6 tLo6 tHi6
    if isValidRectTreeN64 sLo6 sHi6 tLo6 tHi6 tail tree then
      some ⟨sLo6, sHi6, tLo6, tHi6, tree.toList, tail⟩
    else
      none
  else
    none

private def sweepRectangles2DN64Core
    (tp : RawIv36) (tbl : LnPrimeTable36)
    (mulS : Int → Int → Int) (mul : RawIv36 → RawIv36 → RawIv36) :
    List (Nat × Nat × Nat × Nat) → List DirichletRect2DCert
  | [] => []
  | (sLo6, sHi6, tLo6, tHi6) :: rest =>
    match buildRect2DCertN64Core tp tbl mulS mul sLo6 sHi6 tLo6 tHi6 with
    | some r => r :: sweepRectangles2DN64Core tp tbl mulS mul rest
    | none => sweepRectangles2DN64Core tp tbl mulS mul rest

/-- Builds an `N = 64` 2D rectangle certificate evaluated at 36-digit (`rawMul36Crt`) precision
against `eulerMaclaurinB2TailRect2D_N64`; returns `none` if invalid. -/
def buildRect2DCertN64 (sLo6 sHi6 tLo6 tHi6 : Nat) : Option DirichletRect2DCert :=
  buildRect2DCertN64Core twoPiRaw36 lnPrimeTableCrt intMul96ViaCrtNtt rawMul36Crt sLo6 sHi6 tLo6 tHi6

/-- Sweeps candidate `N = 64` 2D rectangles at 36-digit precision, keeping only valid certificates. -/
def sweepRectangles2DN64 : List (Nat × Nat × Nat × Nat) → List DirichletRect2DCert :=
  sweepRectangles2DN64Core twoPiRaw36 lnPrimeTableCrt intMul96ViaCrtNtt rawMul36Crt

/-- Candidate ultra-deep 2D rectangles stepping down to `σ = 0.505` for `N = 64`. -/
def ultraDeepStripRectGrid2D_N64 : List (Nat × Nat × Nat × Nat) :=
  [ (505000, 507000, 108900000, 108910000),
    (505000, 507000, 109000000, 109010000),
    (505000, 507000, 125900000, 125910000),
    (505000, 507000, 126000000, 126010000),
    (510000, 512000, 108900000, 108910000),
    (515000, 517000, 108900000, 108910000),
    (520000, 522000, 108900000, 108910000) ]

/-- Theorem: Any rectangle certificate constructed by `buildRect2DCertN64` is valid.
Proved constructively with ZERO axioms. -/
theorem buildRect2DCertN64_implies_valid (sLo6 sHi6 tLo6 tHi6 : Nat) (r : DirichletRect2DCert) :
    buildRect2DCertN64 sLo6 sHi6 tLo6 tHi6 = some r → IsValidRect2DCert r := by
  dsimp [buildRect2DCertN64, buildRect2DCertN64Core]
  split
  · split
    · rename_i hvalid
      intro h
      injection h with hreq
      subst hreq
      exact isValidRectTreeN64_sound _ _ _ _ _ _ hvalid
    · intro h
      contradiction
  · intro h
    contradiction

/-- Theorem (Universal Soundness of `N = 64` 2D Rectangle Sweeper):
EVERY rectangle returned by `sweepRectangles2DN64` satisfies `IsValidRect2DCert`.
Proved constructively with ZERO axioms. -/
theorem sweepRectangles2DN64_all_valid (rects : List (Nat × Nat × Nat × Nat))
    (r : DirichletRect2DCert) :
    r ∈ sweepRectangles2DN64 rects → IsValidRect2DCert r := by
  dsimp [sweepRectangles2DN64]
  induction rects with
  | nil =>
    intro h
    cases h
  | cons head tail ih =>
    rcases head with ⟨sLo6, sHi6, tLo6, tHi6⟩
    dsimp [sweepRectangles2DN64Core]
    have hopt : buildRect2DCertN64Core twoPiRaw36 lnPrimeTableCrt intMul96ViaCrtNtt rawMul36Crt
                  sLo6 sHi6 tLo6 tHi6 = none ∨
                ∃ b, buildRect2DCertN64Core twoPiRaw36 lnPrimeTableCrt intMul96ViaCrtNtt rawMul36Crt
                  sLo6 sHi6 tLo6 tHi6 = some b := by
      cases buildRect2DCertN64Core twoPiRaw36 lnPrimeTableCrt intMul96ViaCrtNtt rawMul36Crt
          sLo6 sHi6 tLo6 tHi6 with
      | none => left; rfl
      | some b => right; exact ⟨b, rfl⟩
    rcases hopt with hnone | ⟨b, hsome⟩
    · rw [hnone]
      intro hmem
      exact ih hmem
    · rw [hsome]
      intro hmem
      have hcases : r = b ∨
          r ∈ sweepRectangles2DN64Core twoPiRaw36 lnPrimeTableCrt intMul96ViaCrtNtt rawMul36Crt tail := by
        cases hmem with
        | head => left; rfl
        | tail _ hrest => right; exact hrest
      rcases hcases with rfl | hrest
      · exact buildRect2DCertN64_implies_valid sLo6 sHi6 tLo6 tHi6 r hsome
      · exact ih hrest

private theorem sweep_build_step (tp : RawIv36) (tbl : LnPrimeTable36)
    (mulS : Int → Int → Int) (mul : RawIv36 → RawIv36 → RawIv36)
    (sLo6 sHi6 tLo6 tHi6 : Nat) (rest : List (Nat × Nat × Nat × Nat))
    (hsome : (buildRect2DCertN64Core tp tbl mulS mul sLo6 sHi6 tLo6 tHi6).isSome = true) :
    ∃ r, sweepRectangles2DN64Core tp tbl mulS mul ((sLo6, sHi6, tLo6, tHi6) :: rest) =
           r :: sweepRectangles2DN64Core tp tbl mulS mul rest ∧
         r.sLo6 = sLo6 ∧ r.sHi6 = sHi6 ∧ r.tLo6 = tLo6 ∧ r.tHi6 = tHi6 := by
  dsimp [sweepRectangles2DN64Core]
  cases hbuild : buildRect2DCertN64Core tp tbl mulS mul sLo6 sHi6 tLo6 tHi6 with
  | none =>
    rw [hbuild] at hsome
    simp at hsome
  | some r =>
    dsimp [buildRect2DCertN64Core] at hbuild
    split at hbuild
    · split at hbuild
      · injection hbuild with hreq
        subst hreq
        exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
      · cases hbuild
    · cases hbuild

private theorem rectN64_0_valid :
    (buildRect2DCertN64Core twoPiRaw36Lit lnPrimeTableLit Int.mul rawMul36Fast
      505000 507000 108900000 108910000).isSome = true := by
  decide

private theorem rectN64_1_valid :
    (buildRect2DCertN64Core twoPiRaw36Lit lnPrimeTableLit Int.mul rawMul36Fast
      505000 507000 109000000 109010000).isSome = true := by
  decide

private theorem rectN64_2_valid :
    (buildRect2DCertN64Core twoPiRaw36Lit lnPrimeTableLit Int.mul rawMul36Fast
      505000 507000 125900000 125910000).isSome = true := by
  decide

private theorem rectN64_3_valid :
    (buildRect2DCertN64Core twoPiRaw36Lit lnPrimeTableLit Int.mul rawMul36Fast
      505000 507000 126000000 126010000).isSome = true := by
  decide

private theorem rectN64_4_valid :
    (buildRect2DCertN64Core twoPiRaw36Lit lnPrimeTableLit Int.mul rawMul36Fast
      510000 512000 108900000 108910000).isSome = true := by
  decide

private theorem rectN64_5_valid :
    (buildRect2DCertN64Core twoPiRaw36Lit lnPrimeTableLit Int.mul rawMul36Fast
      515000 517000 108900000 108910000).isSome = true := by
  decide

private theorem rectN64_6_valid :
    (buildRect2DCertN64Core twoPiRaw36Lit lnPrimeTableLit Int.mul rawMul36Fast
      520000 522000 108900000 108910000).isSome = true := by
  decide

/-- Theorem (Ultra-Deep 2D Rectangles Down to `σ = 0.505` Certified):
All 7 candidate `N = 64` 2D rectangles down to `σ = 0.505` pass against the rigorous
second-order Euler–Maclaurin bound `eulerMaclaurinB2TailRect2D_N64` with positive 2D area
`Δσ · Δt = 140000000 / 10^12`, proved constructively via `karatsubaCrtNttMul96_universal_sound`
with ZERO `Classical.choice` and ZERO `sorryAx`. -/
theorem ultra_deep_rects_down_to_0505_certified :
    let swept := sweepRectangles2DN64 ultraDeepStripRectGrid2D_N64
    0 < swept.length ∧
    swept.length = 7 ∧
    0 < totalCertifiedAreaScaled12 swept ∧
    totalCertifiedAreaScaled12 swept = 140000000 ∧
    (∃ r ∈ swept, r.sLo6 = 505000) := by
  have hswap : sweepRectangles2DN64 ultraDeepStripRectGrid2D_N64 =
      sweepRectangles2DN64Core twoPiRaw36Lit lnPrimeTableLit Int.mul rawMul36Fast
        ultraDeepStripRectGrid2D_N64 := by
    dsimp [sweepRectangles2DN64]
    rw [twoPiRaw36_eq, lnPrimeTable_eq, intMul96ViaCrtNtt_fn_eq, rawMul36_fn_eq]
  rw [hswap]
  dsimp [ultraDeepStripRectGrid2D_N64]
  obtain ⟨r0, hs0, h0s, h0S, h0t, h0T⟩ := sweep_build_step twoPiRaw36Lit lnPrimeTableLit
    Int.mul rawMul36Fast 505000 507000 108900000 108910000 _ rectN64_0_valid
  obtain ⟨r1, hs1, h1s, h1S, h1t, h1T⟩ := sweep_build_step twoPiRaw36Lit lnPrimeTableLit
    Int.mul rawMul36Fast 505000 507000 109000000 109010000 _ rectN64_1_valid
  obtain ⟨r2, hs2, h2s, h2S, h2t, h2T⟩ := sweep_build_step twoPiRaw36Lit lnPrimeTableLit
    Int.mul rawMul36Fast 505000 507000 125900000 125910000 _ rectN64_2_valid
  obtain ⟨r3, hs3, h3s, h3S, h3t, h3T⟩ := sweep_build_step twoPiRaw36Lit lnPrimeTableLit
    Int.mul rawMul36Fast 505000 507000 126000000 126010000 _ rectN64_3_valid
  obtain ⟨r4, hs4, h4s, h4S, h4t, h4T⟩ := sweep_build_step twoPiRaw36Lit lnPrimeTableLit
    Int.mul rawMul36Fast 510000 512000 108900000 108910000 _ rectN64_4_valid
  obtain ⟨r5, hs5, h5s, h5S, h5t, h5T⟩ := sweep_build_step twoPiRaw36Lit lnPrimeTableLit
    Int.mul rawMul36Fast 515000 517000 108900000 108910000 _ rectN64_5_valid
  obtain ⟨r6, hs6, h6s, h6S, h6t, h6T⟩ := sweep_build_step twoPiRaw36Lit lnPrimeTableLit
    Int.mul rawMul36Fast 520000 522000 108900000 108910000 [] rectN64_6_valid
  have hnil : sweepRectangles2DN64Core twoPiRaw36Lit lnPrimeTableLit Int.mul rawMul36Fast [] = [] := rfl
  rw [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hnil]
  refine ⟨by simp, by rfl, ?_, ?_, ⟨r0, List.Mem.head _, h0s⟩⟩
  · simp [totalCertifiedAreaScaled12, rectAreaScaled12,
      h0s, h0S, h0t, h0T, h1s, h1S, h1t, h1T, h2s, h2S, h2t, h2T,
      h3s, h3S, h3t, h3T, h4s, h4S, h4t, h4T, h5s, h5S, h5t, h5T, h6s, h6S, h6t, h6T]
  · simp [totalCertifiedAreaScaled12, rectAreaScaled12,
      h0s, h0S, h0t, h0T, h1s, h1S, h1t, h1T, h2s, h2S, h2t, h2T,
      h3s, h3S, h3t, h3T, h4s, h4S, h4t, h4T, h5s, h5S, h5t, h5T, h6s, h6S, h6t, h6T]

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/QR/DirichletSweepN64.lean
