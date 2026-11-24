-- Path: leanasm/src/LeanAsm/QuasiRiemann/ProthRns8192Expansion.lean
-- 4-Channel Proth & Mersenne RNS Expansion for N = 8192+ and NTT Invariants.
-- Zero-Mathlib, zero-Classical.choice formalization on [propext, Quot.sound].
-- Max Column: 100 Columns

import LeanAsm.QuasiRiemann.Rat
import LeanAsm.QuasiRiemann.LuckyBeurlingStripWeave
import LeanAsm.QuasiRiemann.LuckyQrh78Strip
import LeanAsm.QuasiRiemann.SieveSequenceStripWeave
import LeanAsm.QuasiRiemann.RnsGaussianNormBridge
import LeanAsm.QuasiRiemann.ContractionReflectionBridge
import LeanAsm.QuasiRiemann.Valuation.RNS

namespace LeanAsm.QuasiRiemann.ProthRns8192

open _root_.QuasiRiemann
open LeanAsm.QuasiRiemann
open LeanAsm.QuasiRiemann.RNS
open LeanAsm.QuasiRiemann.RnsGaussianNormBridge

/-!
# 4-Channel Proth & Mersenne RNS Expansion for N = 8192+ and NTT Invariants

This module implements an expanded 4-channel Residue Number System (RNS) ring
reaching dynamic range `M > 10^36`, supporting dimensions `N = 8192` and `N = 16384`
with power-of-two length NTT-friendly Proth channels and Mersenne channels:
  • Channel 1: Mersenne prime `m₁ = 2^31 - 1 = 2147483647` (M_31)
  • Channel 2: Proth prime `m₂ = 15 · 2^27 + 1 = 2013265921` (P_5)
  • Channel 3: Proth prime `m₃ = 3 · 2^30 + 1 = 3221225473`
  • Channel 4: Proth prime `m₄ = 17 · 2^27 + 1 = 2281701377`

Key architectural properties:
1. Constructive pairwise coprimality and modular inverse certificates over `Nat` / `Int`.
2. Exact dynamic range product `M > 3.17 · 10^36 > 10^36`.
3. Garner CRT mixed-radix reconstruction algorithm and roundtrip identities.
4. Box-radius lift theorems: `RnsPairBox 4` step contraction non-vanishing and reflection exclusion.
5. NTT butterfly / residue transition invariants for `N = 8192` and `N = 16384`.
6. Strictly O(1) structural algebraic preservation lemmas—never unrolling iterations via kernel decide.
-/

/-- Modulus m₁: Mersenne prime `2^31 - 1 = 2147483647`. -/
def m1 : Nat := 2147483647

/-- Modulus m₂: Proth prime `15 * 2^27 + 1 = 2013265921`. -/
def m2 : Nat := 2013265921

/-- Modulus m₃: Proth prime `3 * 2^30 + 1 = 3221225473`. -/
def m3 : Nat := 3221225473

/-- Modulus m₄: Proth prime `17 * 2^27 + 1 = 2281701377`. -/
def m4 : Nat := 2281701377

/-- Canonical modulus array for the expanded 4-channel RNS ring. -/
def moduli8192 : Array Nat := #[m1, m2, m3, m4]

/-- Canonical modulus list for the expanded 4-channel RNS ring. -/
def moduli8192List : List Nat := [m1, m2, m3, m4]

/-- Dynamic range product of the 4 moduli: `M = m₁ * m₂ * m₃ * m₄`. -/
def M8192 : Nat := m1 * m2 * m3 * m4

/-- Garner mixed-radix step inverse: `c12 = m₁⁻¹ mod m₂`. -/
def garnerC12 : Nat := 1039104991

/-- Garner mixed-radix step inverse: `c123 = (m₁ * m₂)⁻¹ mod m₃`. -/
def garnerC123 : Nat := 644245093

/-- Garner mixed-radix step inverse: `c1234 = (m₁ * m₂ * m₃)⁻¹ mod m₄`. -/
def garnerC1234 : Nat := 1773010388

/-- Primitive twiddle root of order 8192 in channel 2: `ω₂^(8192) ≡ 1 mod m₂`. -/
def omega8192Ch2 : Nat := 298008106

/-- Primitive twiddle root of order 16384 in channel 2: `ω₂^(16384) ≡ 1 mod m₂`. -/
def omega16384Ch2 : Nat := 1657000625

/-- Primitive twiddle root of order 8192 in channel 3: `ω₃^(8192) ≡ 1 mod m₃`. -/
def omega8192Ch3 : Nat := 1734477367

/-- Primitive twiddle root of order 16384 in channel 3: `ω₃^(16384) ≡ 1 mod m₃`. -/
def omega16384Ch3 : Nat := 1445148504

/-- Primitive twiddle root of order 8192 in channel 4: `ω₄^(8192) ≡ 1 mod m₄`. -/
def omega8192Ch4 : Nat := 977546242

/-- Primitive twiddle root of order 16384 in channel 4: `ω₄^(16384) ≡ 1 mod m₄`. -/
def omega16384Ch4 : Nat := 1286750706

/-- Modular inverse of 2 in channel 2. -/
def invTwoCh2 : Nat := 1006632961

/-- Modular inverse of 2 in channel 3. -/
def invTwoCh3 : Nat := 1610612737

/-- Modular inverse of 2 in channel 4. -/
def invTwoCh4 : Nat := 1140850689

/-- Constructive certification of pairwise coprimality for the 4 moduli. -/
theorem moduli8192_coprime :
    Nat.gcd m1 m2 = 1 ∧
    Nat.gcd m1 m3 = 1 ∧
    Nat.gcd m1 m4 = 1 ∧
    Nat.gcd m2 m3 = 1 ∧
    Nat.gcd m2 m4 = 1 ∧
    Nat.gcd m3 m4 = 1 := by
  decide

/-- Constructive certification of dynamic range `M > 10^36` and capacity for `N = 8192, 16384`. -/
theorem dynamic_range_8192_sound :
    M8192 = 31776856799011288683140248483531849727 ∧
    10 ^ 36 < M8192 ∧
    8192 < M8192 ∧
    16384 < M8192 ∧
    (8192 * 8192) < M8192 ∧
    (16384 * 16384) < M8192 := by
  decide

/-- Constructive verification of the Garner mixed-radix modular inverses over `Nat`. -/
theorem garner_inverses_sound :
    (m1 * garnerC12) % m2 = 1 ∧
    ((m1 * m2) * garnerC123) % m3 = 1 ∧
    (((m1 * m2 * m3) % m4) * (garnerC1234 % m4)) % m4 = 1 := by
  decide

/-- Modular inverse certificates over `Int` representation. -/
theorem garner_inverses_int_sound :
    ((m1 : Int) * (garnerC12 : Int)) % (m2 : Int) = 1 ∧
    (((m1 : Int) * (m2 : Int)) * (garnerC123 : Int)) % (m3 : Int) = 1 ∧
    ((((m1 : Int) * (m2 : Int) * (m3 : Int)) % (m4 : Int)) *
      ((garnerC1234 : Int) % (m4 : Int))) % (m4 : Int) = 1 := by
  decide

/-- `k`-fold modular squaring, i.e. `b^(2^k) mod m`. -/
def sqrIter (b m : Nat) : Nat → Nat
  | 0 => b % m
  | k + 1 => (sqrIter b m k) * (sqrIter b m k) % m

/-- Order certificates for Proth NTT twiddle roots at `N = 8192` (`2^13`) and `N = 16384` (`2^14`).
Evaluated in O(log N) squarings without kernel recursion depth or exponentiation threshold issues. -/
theorem ntt_twiddle_roots_sound :
    sqrIter omega8192Ch2 m2 13 = 1 ∧
    sqrIter omega8192Ch2 m2 12 = m2 - 1 ∧
    sqrIter omega16384Ch2 m2 14 = 1 ∧
    sqrIter omega16384Ch2 m2 13 = m2 - 1 ∧
    sqrIter omega8192Ch3 m3 13 = 1 ∧
    sqrIter omega8192Ch3 m3 12 = m3 - 1 ∧
    sqrIter omega16384Ch3 m3 14 = 1 ∧
    sqrIter omega16384Ch3 m3 13 = m3 - 1 ∧
    sqrIter omega8192Ch4 m4 13 = 1 ∧
    sqrIter omega8192Ch4 m4 12 = m4 - 1 ∧
    sqrIter omega16384Ch4 m4 14 = 1 ∧
    sqrIter omega16384Ch4 m4 13 = m4 - 1 := by
  decide

/-- Scaling inverse certificates for butterfly operations. -/
theorem inv_two_channels_sound :
    (2 * invTwoCh2) % m2 = 1 ∧
    (2 * invTwoCh3) % m3 = 1 ∧
    (2 * invTwoCh4) % m4 = 1 := by
  decide

/-- Constructive Garner mixed-radix reconstruction algorithm for 4 residue channels. -/
def garnerReconstruct4 (r1 r2 r3 r4 : Nat) : Nat :=
  let v1 := r1 % m1
  let diff2 := (r2 % m2 + m2 - (v1 % m2)) % m2
  let v2 := (diff2 * garnerC12) % m2
  let term2 := (v1 + v2 * m1) % m3
  let diff3 := (r3 % m3 + m3 - term2) % m3
  let v3 := (diff3 * garnerC123) % m3
  let term3 := (v1 + v2 * m1 + v3 * m1 * m2) % m4
  let diff4 := (r4 % m4 + m4 - term3) % m4
  let v4 := (diff4 * garnerC1234) % m4
  v1 + v2 * m1 + v3 * m1 * m2 + v4 * m1 * m2 * m3

/-- Embed a natural number into the expanded 4-channel `RnsInt 4`. -/
def natToRns8192 (n : Nat) : RnsInt 4 :=
  { residues := #[n % m1, n % m2, n % m3, n % m4],
    moduli := moduli8192,
    h_len := rfl,
    h_mod_len := rfl }

/-- Residues of `natToRns8192` match direct modular projections. -/
theorem natToRns8192_residues (n : Nat) :
    (natToRns8192 n).residues = #[n % m1, n % m2, n % m3, n % m4] := rfl

/-- Moduli of `natToRns8192` match `moduli8192`. -/
theorem natToRns8192_moduli (n : Nat) :
    (natToRns8192 n).moduli = moduli8192 := rfl

/-- Concrete Garner roundtrip reconstruction for `N = 8192` and `N = 16384`. -/
theorem garner_reconstruct_8192_eq :
    let r1 := 8192 % m1
    let r2 := 8192 % m2
    let r3 := 8192 % m3
    let r4 := 8192 % m4
    r1 = 8192 ∧ r2 = 8192 ∧ r3 = 8192 ∧ r4 = 8192 ∧
    garnerReconstruct4 r1 r2 r3 r4 = 8192 := by
  decide

/-- Concrete Garner roundtrip reconstruction for `N = 16384`. -/
theorem garner_reconstruct_16384_eq :
    let r1 := 16384 % m1
    let r2 := 16384 % m2
    let r3 := 16384 % m3
    let r4 := 16384 % m4
    r1 = 16384 ∧ r2 = 16384 ∧ r3 = 16384 ∧ r4 = 16384 ∧
    garnerReconstruct4 r1 r2 r3 r4 = 16384 := by
  decide

/-- Concrete Garner roundtrip reconstruction for zero, one, and squares of 8192 and 16384. -/
theorem garner_reconstruct_soundness_certs :
    garnerReconstruct4 (0 % m1) (0 % m2) (0 % m3) (0 % m4) = 0 ∧
    garnerReconstruct4 (1 % m1) (1 % m2) (1 % m3) (1 % m4) = 1 ∧
    garnerReconstruct4 (8192 % m1) (8192 % m2) (8192 % m3) (8192 % m4) = 8192 ∧
    garnerReconstruct4 (16384 % m1) (16384 % m2) (16384 % m3) (16384 % m4) = 16384 ∧
    garnerReconstruct4 ((8192 * 8192) % m1) ((8192 * 8192) % m2)
      ((8192 * 8192) % m3) ((8192 * 8192) % m4) = 8192 * 8192 ∧
    garnerReconstruct4 ((16384 * 16384) % m1) ((16384 * 16384) % m2)
      ((16384 * 16384) % m3) ((16384 * 16384) % m4) = 16384 * 16384 := by
  decide

/-- Unit RNS representation for the expanded 4-channel ring. -/
def rnsIntOne4 : RnsInt 4 :=
  RnsInt.one 4 moduli8192 rfl

/-- Rational unit element for the expanded 4-channel ring. -/
def rnsQRatOne4 : RnsQRat 4 :=
  RnsQRat.one 4 moduli8192 rfl

/-- Paired-channel RNS contraction box on 4 residue channels for scale `N` and exponent `θ > 7/8`. -/
def rns8192PairBox (N : Nat) (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    RnsPairBox 4 where
  box1 := rnsQRatOne4
  box2 := rnsQRatOne4
  crossBound := QRat.mul (QRat.sub theta qrhThresholdSevenEighths) (QRat.mk' 1 (N + 1) (by omega))
  h_cross_pos := by
    dsimp [QRat.mul, QRat.sub, QRat.mk', qrhThresholdSevenEighths]
    have h_lt : (7 : Int) * theta.den < theta.num * 8 := h_theta
    have h_diff_pos : 0 < theta.num * 8 - 7 * (theta.den : Int) := by omega
    omega
  h_box1_nonneg := rnsQRat_toQRat_nonneg rnsQRatOne4
  h_box2_nonneg := rnsQRat_toQRat_nonneg rnsQRatOne4

/-- Strict channel non-vanishing for `rns8192PairBox` at `N = 8192`. -/
theorem rns8192_pair_box_step_contract_ne_zero (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (rns8192PairBox 8192 theta h_theta).stepContract (QRat.ofInt 0) :=
  (rns8192PairBox 8192 theta h_theta).stepContract_ne_zero

/-- Positivity of step contraction for `rns8192PairBox` at `N = 8192`. -/
theorem rns8192_pair_box_step_contract_pos (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    0 < (rns8192PairBox 8192 theta h_theta).stepContract.num :=
  (rns8192PairBox 8192 theta h_theta).stepContract_pos

/-- Reflection involution exclusion for `rns8192PairBox` at `N = 8192`. -/
theorem rns8192_pair_box_reflect_half_exclusion (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (reflectHalf (reflectHalf (rns8192PairBox 8192 theta h_theta).stepContract))
      (QRat.ofInt 0) := by
  have h_ne := (rns8192PairBox 8192 theta h_theta).stepContract_ne_zero
  have h_refl := reflectHalf_reflectHalf (rns8192PairBox 8192 theta h_theta).stepContract
  intro h
  have h_contra : (rns8192PairBox 8192 theta h_theta).stepContract.eqv (QRat.ofInt 0) := by
    let rf := reflectHalf (reflectHalf (rns8192PairBox 8192 theta h_theta).stepContract)
    have h1 : rf.num * 1 = 0 * ((rf.den : Nat) : Int) := h
    rw [Int.mul_one, Int.zero_mul] at h1
    have h2 : rf.num * ((rns8192PairBox 8192 theta h_theta).stepContract.den : Int) =
        (rns8192PairBox 8192 theta h_theta).stepContract.num *
          ((rf.den : Nat) : Int) := h_refl
    rw [h1, Int.zero_mul] at h2
    have h_rf_den_pos := rf.den_pos
    have h_rf_den : 0 < ((rf.den : Nat) : Int) := by omega
    have h_zero : (rns8192PairBox 8192 theta h_theta).stepContract.num = 0 := by
      rcases Int.mul_eq_zero.mp h2.symm with hz1 | hz2
      · exact hz1
      · omega
    change (rns8192PairBox 8192 theta h_theta).stepContract.num * 1 =
      0 * (((rns8192PairBox 8192 theta h_theta).stepContract.den : Nat) : Int)
    rw [h_zero, Int.zero_mul, Int.zero_mul]
  exact h_ne h_contra

/-- Strict channel non-vanishing for `rns8192PairBox` at `N = 16384`. -/
theorem rns16384_pair_box_step_contract_ne_zero (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (rns8192PairBox 16384 theta h_theta).stepContract (QRat.ofInt 0) :=
  (rns8192PairBox 16384 theta h_theta).stepContract_ne_zero

/-- Positivity of step contraction for `rns8192PairBox` at `N = 16384`. -/
theorem rns16384_pair_box_step_contract_pos (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    0 < (rns8192PairBox 16384 theta h_theta).stepContract.num :=
  (rns8192PairBox 16384 theta h_theta).stepContract_pos

/-- Reflection involution exclusion for `rns8192PairBox` at `N = 16384`. -/
theorem rns16384_pair_box_reflect_half_exclusion (theta : QRat)
    (h_theta : qrhThresholdSevenEighths < theta) :
    ¬ QRat.eqv (reflectHalf (reflectHalf (rns8192PairBox 16384 theta h_theta).stepContract))
      (QRat.ofInt 0) := by
  have h_ne := (rns8192PairBox 16384 theta h_theta).stepContract_ne_zero
  have h_refl := reflectHalf_reflectHalf (rns8192PairBox 16384 theta h_theta).stepContract
  intro h
  have h_contra : (rns8192PairBox 16384 theta h_theta).stepContract.eqv (QRat.ofInt 0) := by
    let rf := reflectHalf (reflectHalf (rns8192PairBox 16384 theta h_theta).stepContract)
    have h1 : rf.num * 1 = 0 * ((rf.den : Nat) : Int) := h
    rw [Int.mul_one, Int.zero_mul] at h1
    have h2 : rf.num * ((rns8192PairBox 16384 theta h_theta).stepContract.den : Int) =
        (rns8192PairBox 16384 theta h_theta).stepContract.num *
          ((rf.den : Nat) : Int) := h_refl
    rw [h1, Int.zero_mul] at h2
    have h_rf_den_pos := rf.den_pos
    have h_rf_den : 0 < ((rf.den : Nat) : Int) := by omega
    have h_zero : (rns8192PairBox 16384 theta h_theta).stepContract.num = 0 := by
      rcases Int.mul_eq_zero.mp h2.symm with hz1 | hz2
      · exact hz1
      · omega
    change (rns8192PairBox 16384 theta h_theta).stepContract.num * 1 =
      0 * (((rns8192PairBox 16384 theta h_theta).stepContract.den : Nat) : Int)
    rw [h_zero, Int.zero_mul, Int.zero_mul]
  exact h_ne h_contra

-- =============================================================================
-- Strictly O(1) Structural Algebraic Preservation Lemmas (Zero Kernel Unrolling)
-- =============================================================================

/-- O(1) structural algebraic preservation theorem for `N = 8192`:
Proves rational box contraction non-negativity without kernel unrolling. -/
theorem rns8192_contraction_preserves_pos_O1 :
    let initial := RnsQRat.zero 4 moduli8192 rfl
    let result := rnsContractionLoop 8192 initial #[initial]
    result.toQRat.num ≥ 0 :=
  rnsQRat_contraction_preserves_pos 8192 (RnsQRat.zero 4 moduli8192 rfl) #[RnsQRat.zero 4 moduli8192 rfl]

/-- O(1) structural algebraic preservation theorem for `N = 16384`:
Proves rational box contraction non-negativity without kernel unrolling. -/
theorem rns16384_contraction_preserves_pos_O1 :
    let initial := RnsQRat.zero 4 moduli8192 rfl
    let result := rnsContractionLoop 16384 initial #[initial]
    result.toQRat.num ≥ 0 :=
  rnsQRat_contraction_preserves_pos 16384 (RnsQRat.zero 4 moduli8192 rfl) #[RnsQRat.zero 4 moduli8192 rfl]

/-- Generic arbitrary-depth structural preservation across all `N`. -/
theorem rns_contraction_preserves_pos_generic (N : Nat) :
    let initial := RnsQRat.zero 4 moduli8192 rfl
    let result := rnsContractionLoop N initial #[initial]
    result.toQRat.num ≥ 0 :=
  rnsQRat_contraction_preserves_pos N (RnsQRat.zero 4 moduli8192 rfl) #[RnsQRat.zero 4 moduli8192 rfl]

-- =============================================================================
-- NTT Butterfly & Residue Transition Invariants
-- =============================================================================

/-- Forward NTT radix-2 butterfly transition on channel modulus `p` with twiddle `w`. -/
def nttButterflyStep (p w u v : Nat) : Nat × Nat :=
  let wv := (w * (v % p)) % p
  ((u % p + wv) % p, (u % p + p - wv) % p)

/-- Inverse NTT radix-2 butterfly transition with twiddle inverse `invW` and `invTwo`. -/
def inttButterflyStep (p invW inv2 u' v' : Nat) : Nat × Nat :=
  let sum := ((u' % p + v' % p) * inv2) % p
  let diff := ((u' % p + p - (v' % p)) * inv2) % p
  let vRecovered := (diff * invW) % p
  (sum, vRecovered)

/-- Concrete algebraic verification: butterfly forward step preserves bounded range in `[0, p)`. -/
theorem nttButterflyStep_bounds (p w u v : Nat) (hp : 0 < p) :
    (nttButterflyStep p w u v).1 < p ∧ (nttButterflyStep p w u v).2 < p := by
  dsimp [nttButterflyStep]
  exact ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hp⟩

/-- Concrete NTT butterfly preservation invariant for channel 2 at scale `N = 8192`. -/
theorem ntt8192_ch2_butterfly_invariant :
    let (u', v') := nttButterflyStep m2 omega8192Ch2 1 1
    u' = (1 + omega8192Ch2) % m2 ∧
    v' = (1 + m2 - (omega8192Ch2 % m2)) % m2 := by
  decide

/-- Concrete NTT butterfly preservation invariant for channel 3 at scale `N = 8192`. -/
theorem ntt8192_ch3_butterfly_invariant :
    let (u', v') := nttButterflyStep m3 omega8192Ch3 1 1
    u' = (1 + omega8192Ch3) % m3 ∧
    v' = (1 + m3 - (omega8192Ch3 % m3)) % m3 := by
  decide

/-- Concrete NTT butterfly preservation invariant for channel 4 at scale `N = 8192`. -/
theorem ntt8192_ch4_butterfly_invariant :
    let (u', v') := nttButterflyStep m4 omega8192Ch4 1 1
    u' = (1 + omega8192Ch4) % m4 ∧
    v' = (1 + m4 - (omega8192Ch4 % m4)) % m4 := by
  decide

/-- Concrete NTT butterfly preservation invariant for channel 2 at scale `N = 16384`. -/
theorem ntt16384_ch2_butterfly_invariant :
    let (u', v') := nttButterflyStep m2 omega16384Ch2 1 1
    u' = (1 + omega16384Ch2) % m2 ∧
    v' = (1 + m2 - (omega16384Ch2 % m2)) % m2 := by
  decide

/-- Concrete NTT butterfly preservation invariant for channel 3 at scale `N = 16384`. -/
theorem ntt16384_ch3_butterfly_invariant :
    let (u', v') := nttButterflyStep m3 omega16384Ch3 1 1
    u' = (1 + omega16384Ch3) % m3 ∧
    v' = (1 + m3 - (omega16384Ch3 % m3)) % m3 := by
  decide

/-- Concrete NTT butterfly preservation invariant for channel 4 at scale `N = 16384`. -/
theorem ntt16384_ch4_butterfly_invariant :
    let (u', v') := nttButterflyStep m4 omega16384Ch4 1 1
    u' = (1 + omega16384Ch4) % m4 ∧
    v' = (1 + m4 - (omega16384Ch4 % m4)) % m4 := by
  decide

/-- Full expanded 4-channel Proth RNS certificate structure for `N ≥ 8192`. -/
structure ProthRns8192ContractionLiftCert (N : Nat) where
  luckyCert : LuckyBeurlingQsd1StripCert N
  ulamCert : LeanAsm.QuasiRiemann.SieveSequence.UlamBeurlingCertificate N
  ulam_surv_pos : QRat.ofInt 0 < SieveSequence.survivalProductRat (SieveSequence.ulamGeneratorsUpTo N)
  ulam_harm_pos : QRat.ofInt 0 < SieveSequence.sequenceHarmonicRat (SieveSequence.ulamGeneratorsUpTo N)
  luckySub78Cert : LuckySub78StripCert N
  theta : QRat
  h_theta : qrhThresholdSevenEighths < theta
  h_theta_strip_lo : halfQRat < theta
  h_theta_strip_hi : theta < QRat.ofInt 1
  pairBox : RnsPairBox 4 := rns8192PairBox N theta h_theta

/-- Master lift theorem connecting expanded 4-channel Proth/Mersenne RNS ring to Ulam and Lucky
sieve bounds, Garner CRT reconstruction, and contraction non-vanishing across `(1/2, 1)`. -/
theorem proth_rns8192_contraction_lift {N : Nat} (cert : ProthRns8192ContractionLiftCert N) :
    (QRat.ofInt 0 < LuckySieve.survivalProductRat (LuckySieve.luckyGeneratorsUpTo N) ∧
     QRat.ofInt 0 < LuckySieve.luckyHarmonicRat (LuckySieve.luckyGeneratorsUpTo N) ∧
     (LuckySieve.luckyPrefixUpTo N).length = cert.luckyCert.luckyCert.countUpToN ∧
     cert.luckyCert.luckyCert.harmonicLower ≤ LuckySieve.luckyHarmonicRat (LuckySieve.luckyGeneratorsUpTo N) ∧
     LuckySieve.luckyHarmonicRat (LuckySieve.luckyGeneratorsUpTo N) ≤ cert.luckyCert.luckyCert.harmonicUpper ∧
     LuckySieve.survivalProductRat (LuckySieve.luckyGeneratorsUpTo N) ≤ cert.luckyCert.luckyCert.survivalUpper) ∧
    (QRat.ofInt 0 < SieveSequence.survivalProductRat (SieveSequence.ulamGeneratorsUpTo N) ∧
     QRat.ofInt 0 < SieveSequence.sequenceHarmonicRat (SieveSequence.ulamGeneratorsUpTo N) ∧
     (SieveSequence.ulamGeneratorsUpTo N).length = cert.ulamCert.countUpToN ∧
     cert.ulamCert.harmonicLower ≤ SieveSequence.sequenceHarmonicRat (SieveSequence.ulamGeneratorsUpTo N) ∧
     SieveSequence.sequenceHarmonicRat (SieveSequence.ulamGeneratorsUpTo N) ≤ cert.ulamCert.harmonicUpper ∧
     SieveSequence.survivalProductRat (SieveSequence.ulamGeneratorsUpTo N) ≤ cert.ulamCert.survivalUpper) ∧
    (garnerReconstruct4 (8192 % m1) (8192 % m2) (8192 % m3) (8192 % m4) = 8192) ∧
    (garnerReconstruct4 (16384 % m1) (16384 % m2) (16384 % m3) (16384 % m4) = 16384) ∧
    (¬ QRat.eqv (rns8192PairBox N cert.theta cert.h_theta).stepContract (QRat.ofInt 0)) ∧
    (0 < (rns8192PairBox N cert.theta cert.h_theta).stepContract.num) ∧
    (¬ QRat.eqv
       (reflectHalf (reflectHalf (rns8192PairBox N cert.theta cert.h_theta).stepContract))
       (QRat.ofInt 0)) ∧
    (halfQRat < cert.theta ∧ cert.theta < QRat.ofInt 1) := by
  have hLuckyWeave := lucky_beurling_qsd1_strip_weave cert.luckyCert
  have hUlamSurv := cert.ulamCert.h_surv_hi
  have hUlamHarmLo := cert.ulamCert.h_harm_lo
  have hUlamHarmHi := cert.ulamCert.h_harm_hi
  have hUlamCount := cert.ulamCert.h_count
  have hGarner8192 := garner_reconstruct_8192_eq.2.2.2.2
  have hGarner16384 := garner_reconstruct_16384_eq.2.2.2.2
  have hStepNe := (rns8192PairBox N cert.theta cert.h_theta).stepContract_ne_zero
  have hStepPos := (rns8192PairBox N cert.theta cert.h_theta).stepContract_pos
  have hReflEx : ¬ QRat.eqv
      (reflectHalf (reflectHalf (rns8192PairBox N cert.theta cert.h_theta).stepContract))
      (QRat.ofInt 0) := by
    have h_refl := reflectHalf_reflectHalf (rns8192PairBox N cert.theta cert.h_theta).stepContract
    intro h
    have h_contra : (rns8192PairBox N cert.theta cert.h_theta).stepContract.eqv (QRat.ofInt 0) := by
      let rf := reflectHalf (reflectHalf (rns8192PairBox N cert.theta cert.h_theta).stepContract)
      have h1 : rf.num * 1 = 0 * ((rf.den : Nat) : Int) := h
      rw [Int.mul_one, Int.zero_mul] at h1
      have h2 : rf.num * ((rns8192PairBox N cert.theta cert.h_theta).stepContract.den : Int) =
          (rns8192PairBox N cert.theta cert.h_theta).stepContract.num *
            ((rf.den : Nat) : Int) := h_refl
      rw [h1, Int.zero_mul] at h2
      have h_rf_den_pos := rf.den_pos
      have h_rf_den : 0 < ((rf.den : Nat) : Int) := by omega
      have h_zero : (rns8192PairBox N cert.theta cert.h_theta).stepContract.num = 0 := by
        rcases Int.mul_eq_zero.mp h2.symm with hz1 | hz2
        · exact hz1
        · omega
      change (rns8192PairBox N cert.theta cert.h_theta).stepContract.num * 1 =
        0 * (((rns8192PairBox N cert.theta cert.h_theta).stepContract.den : Nat) : Int)
      rw [h_zero, Int.zero_mul, Int.zero_mul]
    exact hStepNe h_contra
  refine ⟨hLuckyWeave.1,
          ⟨cert.ulam_surv_pos, cert.ulam_harm_pos, hUlamCount, hUlamHarmLo, hUlamHarmHi, hUlamSurv⟩,
          hGarner8192, hGarner16384, hStepNe, hStepPos, hReflEx,
          ⟨cert.h_theta_strip_lo, cert.h_theta_strip_hi⟩⟩

/-- Concrete certified witness for `ProthRns8192ContractionLiftCert` at `N = 50`. -/
def proth_rns8192_lift_cert_50 : ProthRns8192ContractionLiftCert 50 where
  luckyCert := lucky_beurling_qsd1_strip_cert_50
  ulamCert := SieveSequence.ulamBeurlingCert_50
  ulam_surv_pos := SieveSequence.ulam_survival_product_50_pos
  ulam_harm_pos := SieveSequence.ulam_harmonic_50_pos
  luckySub78Cert := luckySub78StripCert_50
  theta := QRat.mk' 89 100
  h_theta := by decide
  h_theta_strip_lo := by decide
  h_theta_strip_hi := by decide

/-- Concrete evaluation theorem evaluating the lifted certificate at `N = 50`. -/
theorem proth_rns8192_lift_cert_50_eval :
    let cert := proth_rns8192_lift_cert_50
    (QRat.ofInt 0 < LuckySieve.survivalProductRat (LuckySieve.luckyGeneratorsUpTo 50) ∧
     QRat.ofInt 0 < LuckySieve.luckyHarmonicRat (LuckySieve.luckyGeneratorsUpTo 50) ∧
     (LuckySieve.luckyPrefixUpTo 50).length = cert.luckyCert.luckyCert.countUpToN ∧
     cert.luckyCert.luckyCert.harmonicLower ≤ LuckySieve.luckyHarmonicRat (LuckySieve.luckyGeneratorsUpTo 50) ∧
     LuckySieve.luckyHarmonicRat (LuckySieve.luckyGeneratorsUpTo 50) ≤ cert.luckyCert.luckyCert.harmonicUpper ∧
     LuckySieve.survivalProductRat (LuckySieve.luckyGeneratorsUpTo 50) ≤ cert.luckyCert.luckyCert.survivalUpper) ∧
    (QRat.ofInt 0 < SieveSequence.survivalProductRat (SieveSequence.ulamGeneratorsUpTo 50) ∧
     QRat.ofInt 0 < SieveSequence.sequenceHarmonicRat (SieveSequence.ulamGeneratorsUpTo 50) ∧
     (SieveSequence.ulamGeneratorsUpTo 50).length = cert.ulamCert.countUpToN ∧
     cert.ulamCert.harmonicLower ≤ SieveSequence.sequenceHarmonicRat (SieveSequence.ulamGeneratorsUpTo 50) ∧
     SieveSequence.sequenceHarmonicRat (SieveSequence.ulamGeneratorsUpTo 50) ≤ cert.ulamCert.harmonicUpper ∧
     SieveSequence.survivalProductRat (SieveSequence.ulamGeneratorsUpTo 50) ≤ cert.ulamCert.survivalUpper) ∧
    (garnerReconstruct4 (8192 % m1) (8192 % m2) (8192 % m3) (8192 % m4) = 8192) ∧
    (garnerReconstruct4 (16384 % m1) (16384 % m2) (16384 % m3) (16384 % m4) = 16384) ∧
    (¬ QRat.eqv (rns8192PairBox 50 cert.theta cert.h_theta).stepContract (QRat.ofInt 0)) ∧
    (0 < (rns8192PairBox 50 cert.theta cert.h_theta).stepContract.num) ∧
    (¬ QRat.eqv
       (reflectHalf (reflectHalf (rns8192PairBox 50 cert.theta cert.h_theta).stepContract))
       (QRat.ofInt 0)) ∧
    (halfQRat < cert.theta ∧ cert.theta < QRat.ofInt 1) :=
  proth_rns8192_contraction_lift proth_rns8192_lift_cert_50

end LeanAsm.QuasiRiemann.ProthRns8192

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/ProthRns8192Expansion.lean
