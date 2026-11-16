-- Path: leanasm/src/LeanAsm/ProthNttTowerBridge.lean
-- 5-prime Proth NTT tower {5, 17, 257, 65537, 2013265921}: Garner CRT and Dedekind strip bounds.
-- Zero Mathlib, zero axioms beyond propext / Quot.sound.

import LeanAsm.CrtNttUniversal
import LeanAsm.EulerFactorNonVanishing

namespace ProthNttTowerBridge

open CrtNtt

/-- 31-bit Proth NTT prime `P_5 = 15 * 2^27 + 1`. -/
def prothPrime5 : Nat := 2013265921

/-- The 5-prime tower. -/
def prothTowerPrimes : List Nat := [5, 17, 257, 65537, 2013265921]

/-- 5-prime CRT modulus `M_5 = M_4 * P_5`. -/
def prothTowerMod5 : Nat := fermatTowerMod4 * prothPrime5

/-- `M_4⁻¹ mod P_5`. -/
def m4InvModP5 : Nat := 1327898798

theorem prothPrime5_eq : prothPrime5 = 15 * 2 ^ 27 + 1 := by decide

theorem prothTower_eq_fermat_append :
    prothTowerPrimes = EulerFactorNonVanishing.fermatTowerPrimes ++ [prothPrime5] := by decide

/-- Coprimality of `P_5` with `M_4 = 5 * 17 * 257 * 65537` (`3 * M_4 = 2^32 - 1`), plus the
Bezout-style inverse certificate. -/
theorem prothPrime5_coprime_M4 :
    Nat.gcd prothPrime5 fermatTowerMod4 = 1 ∧
    Nat.gcd prothPrime5 5 = 1 ∧ Nat.gcd prothPrime5 17 = 1 ∧
    Nat.gcd prothPrime5 257 = 1 ∧ Nat.gcd prothPrime5 65537 = 1 ∧
    3 * fermatTowerMod4 = 2 ^ 32 - 1 ∧
    (fermatTowerMod4 * m4InvModP5) % prothPrime5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Dynamic range `M_5 > 2^61`. -/
theorem prothTowerMod5_gt_2pow61 :
    prothTowerMod5 = 2882303762277684565 ∧ 2305843009213693952 < prothTowerMod5 ∧
    2 ^ 61 < prothTowerMod5 ∧ prothTowerMod5 < 2 ^ 62 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- ===== Primitive root / 2^27-th twiddle root =====

/-- Fuel-bounded square-and-multiply modular exponentiation. -/
def powModF : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 1
  | f + 1, b, e, m =>
    if e = 0 then 1
    else
      let h := powModF f (b * b % m) (e / 2) m
      if e % 2 = 1 then (b % m) * h % m else h

/-- `k`-fold modular squaring, i.e. `b^(2^k) mod m`. -/
def sqrIter (b m : Nat) : Nat → Nat
  | 0 => b % m
  | k + 1 => (sqrIter b m k) * (sqrIter b m k) % m

/-- Primitive root `g = 31` of `F_{P_5}`. -/
def prothGen : Nat := 31

/-- Principal `2^27`-th root of unity `ω = 31^15 mod P_5`. -/
def prothOmega27 : Nat := 440564289

/-- `P_5 - 1 = 2^27 * 3 * 5`. -/
theorem prothPrime5_pred_factor : prothPrime5 - 1 = 2 ^ 27 * 3 * 5 := by decide

/-- `31` is a primitive root: `g^((P-1)/q) ≠ 1` for `q ∈ {2, 3, 5}` and `g^(P-1) = 1`. -/
theorem prothGen_primitive_root :
    powModF 40 prothGen (prothPrime5 - 1) prothPrime5 = 1 ∧
    powModF 40 prothGen ((prothPrime5 - 1) / 2) prothPrime5 = prothPrime5 - 1 ∧
    powModF 40 prothGen ((prothPrime5 - 1) / 3) prothPrime5 ≠ 1 ∧
    powModF 40 prothGen ((prothPrime5 - 1) / 5) prothPrime5 ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `ω = 31^15` has exact multiplicative order `2^27`: `ω^(2^27) = 1`, `ω^(2^26) = -1`.
Hence NTT lengths `2^k`, `k ≤ 27`, are supported (`ω^(2^(27-k))` is a primitive `2^k`-th root). -/
theorem prothOmega27_order :
    powModF 40 prothGen 15 prothPrime5 = prothOmega27 ∧
    sqrIter prothOmega27 prothPrime5 27 = 1 ∧
    sqrIter prothOmega27 prothPrime5 26 = prothPrime5 - 1 ∧
    sqrIter prothOmega27 prothPrime5 26 ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- ===== 5-channel Garner CRT =====

/-- 5-channel Garner reconstruction: stages 1-4 reuse `garnerReconstruct4`; stage 5 uses
`M_4⁻¹ mod P_5`. -/
def garnerReconstruct5Asm (r1 r2 r3 r4 r5 : Nat) : Nat :=
  let x4 := garnerReconstruct4 r1 r2 r3 r4
  let v5 := ((r5 % prothPrime5 + prothPrime5 - (x4 % prothPrime5)) * m4InvModP5) % prothPrime5
  x4 + fermatTowerMod4 * v5

theorem garnerReconstruct5Asm_lt (r1 r2 r3 r4 r5 : Nat) :
    garnerReconstruct5Asm r1 r2 r3 r4 r5 < prothTowerMod5 := by
  have h4 := garnerReconstruct4_lt r1 r2 r3 r4
  have hv : ((r5 % prothPrime5 + prothPrime5 - (garnerReconstruct4 r1 r2 r3 r4 % prothPrime5))
      * m4InvModP5) % prothPrime5 < prothPrime5 := Nat.mod_lt _ (by decide)
  dsimp only [garnerReconstruct5Asm, prothTowerMod5]
  generalize garnerReconstruct4 r1 r2 r3 r4 = a at *
  generalize ((r5 % prothPrime5 + prothPrime5 - (a % prothPrime5)) * m4InvModP5)
    % prothPrime5 = v at *
  have : fermatTowerMod4 * (v + 1) ≤ fermatTowerMod4 * prothPrime5 :=
    Nat.mul_le_mul_left _ hv
  rw [Nat.mul_succ] at this
  omega

/-- Stage-5 digit: for `x < M_5`, the Garner digit equals `x / M_4`. -/
private theorem stage5_digit (x : Nat) (hx : x < prothTowerMod5) :
    ((x % prothPrime5 + prothPrime5 - ((x % fermatTowerMod4) % prothPrime5)) * m4InvModP5)
      % prothPrime5 = x / fermatTowerMod4 := by
  have hM : fermatTowerMod4 = 1431655765 := by decide
  have hP : prothPrime5 = 2013265921 := rfl
  have hq : x / fermatTowerMod4 < prothPrime5 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    rw [Nat.mul_comm]; exact hx
  have hinv : (fermatTowerMod4 * m4InvModP5) % prothPrime5 = 1 := by decide
  generalize hq' : x / fermatTowerMod4 = q at *
  generalize hr : x % fermatTowerMod4 = r at *
  have hx' : x = fermatTowerMod4 * q + r := by
    rw [← hq', ← hr]; exact (Nat.div_add_mod x fermatTowerMod4).symm
  have hMn : fermatTowerMod4 = 1431655765 := hM
  have hPn : prothPrime5 = 2013265921 := hP
  dsimp only [m4InvModP5]
  rw [hMn] at hx'
  rw [hPn] at hq ⊢
  omega

/-- `garnerReconstruct5Asm_sound`: exact reconstruction of every `x < M_5` from its five residues. -/
theorem garnerReconstruct5Asm_sound (x : Nat) (hx : x < prothTowerMod5) :
    garnerReconstruct5Asm (x % 5) (x % 17) (x % 257) (x % 65537) (x % prothPrime5) = x := by
  have hM4 : 0 < fermatTowerMod4 := by decide
  have hlt : x % fermatTowerMod4 < fermatTowerMod4 := Nat.mod_lt _ hM4
  have h5 : x % fermatTowerMod4 % 5 = x % 5 :=
    Nat.mod_mod_of_dvd x (show 5 ∣ fermatTowerMod4 from ⟨17 * 257 * 65537, by decide⟩)
  have h17 : x % fermatTowerMod4 % 17 = x % 17 :=
    Nat.mod_mod_of_dvd x (show 17 ∣ fermatTowerMod4 from ⟨5 * 257 * 65537, by decide⟩)
  have h257 : x % fermatTowerMod4 % 257 = x % 257 :=
    Nat.mod_mod_of_dvd x (show 257 ∣ fermatTowerMod4 from ⟨5 * 17 * 65537, by decide⟩)
  have h65537 : x % fermatTowerMod4 % 65537 = x % 65537 :=
    Nat.mod_mod_of_dvd x (show 65537 ∣ fermatTowerMod4 from ⟨5 * 17 * 257, by decide⟩)
  have h4 : garnerReconstruct4 (x % 5) (x % 17) (x % 257) (x % 65537) = x % fermatTowerMod4 := by
    have := garnerReconstruct4_sound (x % fermatTowerMod4) hlt
    rwa [h5, h17, h257, h65537] at this
  dsimp only [garnerReconstruct5Asm]
  rw [h4, Nat.mod_mod, stage5_digit x hx]
  exact Nat.mod_add_div x fermatTowerMod4

/-- Residue recovery: the reconstruction reduces to `x` modulo each of the five primes. -/
theorem garnerReconstruct5Asm_residues (x : Nat) (hx : x < prothTowerMod5) :
    ∀ p ∈ prothTowerPrimes,
      garnerReconstruct5Asm (x % 5) (x % 17) (x % 257) (x % 65537) (x % prothPrime5) % p = x % p := by
  intro p _
  rw [garnerReconstruct5Asm_sound x hx]

/-- Direct residue recovery for stage 5 for arbitrary inputs: result `≡ r5 (mod P_5)`. -/
theorem garnerReconstruct5Asm_mod_P5 (r1 r2 r3 r4 r5 : Nat) :
    garnerReconstruct5Asm r1 r2 r3 r4 r5 % prothPrime5 = r5 % prothPrime5 := by
  have hv : ∀ a : Nat, ((r5 % prothPrime5 + prothPrime5 - (a % prothPrime5)) * m4InvModP5)
      % prothPrime5 < prothPrime5 := fun _ => Nat.mod_lt _ (by decide)
  dsimp only [garnerReconstruct5Asm, m4InvModP5, fermatTowerMod4, prothPrime5] at *
  have := hv (garnerReconstruct4 r1 r2 r3 r4)
  generalize garnerReconstruct4 r1 r2 r3 r4 = a at *
  omega

-- ===== 5-prime Dedekind Euler strip bounds =====

open EulerFactorNonVanishing

theorem prothTower_primes_ge_two : ∀ p ∈ prothTowerPrimes, 2 ≤ p := by
  intro p hp
  simp only [prothTowerPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  omega

/-- Local-factor and list-product margins over the 5-prime tower are strictly positive. -/
theorem proth_tower_euler_margin_pos (num : Nat) (hnum : 1 ≤ num) :
    (∀ p ∈ prothTowerPrimes, 0 < eulerFactorMargin p num) ∧
    0 < listEulerProductMargin prothTowerPrimes num :=
  ⟨fun p hp => local_euler_factor_nonvanishing p num (prothTower_primes_ge_two p hp) hnum,
   list_euler_product_nonvanishing prothTowerPrimes num prothTower_primes_ge_two hnum⟩

/-- Predicate: `fs` instantiates the 5-prime Proth tower with admissible local factors. -/
def IsProthTowerFactors (fs : List EulerLocalFactorSpec) : Prop :=
  fs.map (·.p) = prothTowerPrimes ∧ ∀ f ∈ fs, ValidEulerLocalFactorSpec f

/-- 5-prime Dedekind Euler strip non-vanishing, reusing the generic finite-product bound. -/
theorem proth_tower_euler_product_nonvanishing (fs : List EulerLocalFactorSpec)
    (hfs : IsProthTowerFactors fs) :
    fs.length = 5 ∧
    fs.map (·.p) = [5, 17, 257, 65537, 2013265921] ∧
    0 < eulerProdMarginSq fs ∧
    eulerProdMarginSq fs ≤ eulerProdNormSq fs ∧
    0 < eulerProdDenSq fs := by
  rcases hfs with ⟨hp, hvalid⟩
  obtain ⟨hm, hle, hd⟩ := euler_product_finite_norm_lower_bound fs hvalid
  have hlen : fs.length = 5 := by
    have h : (fs.map (·.p)).length = 5 := by rw [hp]; rfl
    simpa [List.length_map] using h
  exact ⟨hlen, hp, hm, hle, hd⟩

/-- `σ = 1/2` cleared-denominator certificate over `{5, 17, 257, 65537, P_5}`
(`⌊√P_5⌋ = 44869`), product `> 1/3`. -/
structure ProthStripHalfCert : Prop where
  p5_admissible : 1 ^ 2 * 2013265921 ≥ 44869 ^ 2
  margin_prod_eq : (2 - 1) * (4 - 1) * (16 - 1) * (256 - 1) * (44869 - 1) = 514860300
  den_prod_eq : 2 * 4 * 16 * 256 * 44869 = 1470267392
  gt_one_third : 1470267392 ^ 2 < 9 * 514860300 ^ 2

/-- `σ = 1` certificate: totient product vs tower product, ratio `> 7/10`. -/
structure ProthStripOneCert : Prop where
  tower_prod_eq : 5 * 17 * 257 * 65537 * 2013265921 = 2882303762277684565
  totient_prod_eq :
    (5 - 1) * (17 - 1) * (257 - 1) * (65537 - 1) * (2013265921 - 1) = 2161727821137838080
  gt_seven_tenths : 7 * 2882303762277684565 < 10 * 2161727821137838080

structure ProthTowerStripCert : Prop where
  half : ProthStripHalfCert
  one : ProthStripOneCert

theorem proth_tower_euler_strip_certs : ProthTowerStripCert :=
  ⟨⟨by decide, by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

end ProthNttTowerBridge

-- end of file: leanasm/src/LeanAsm/ProthNttTowerBridge.lean
