-- Path: leanasm/src/LeanAsm/CrtNtt/CrtBridge.lean
-- Multi-prime CRT reconstruction, roundtrip theorems, universal convolution
-- proofs, and concrete certificates across Fermat primes.
-- Max Column: 100 Columns

import LeanAsm.NttArithmetic
import LeanAsm.CrtNtt.Core

namespace CrtNtt

open NttArithmetic

-- =============================================================================
-- Formally Verified Theorems about Multi-Prime CRT-NTT (ZERO AXIOMS)
-- =============================================================================

/-- Theorem: Modulo 5 4th roots of unity and modular inverses are sound. -/
theorem ntt4_mod5_roots_sound :
    (omega4Mod5 ^ 4) % p5 = 1 ∧
    (omega4Mod5 ^ 2) % p5 = 4 ∧
    (1 + omega4Mod5 + 4 + invOmega4Mod5) % p5 = 0 ∧
    (omega4Mod5 * invOmega4Mod5) % p5 = 1 ∧
    (4 * invFourMod5) % p5 = 1 := by
  decide

/-- Theorem: Modulo 17 inverse for Garner 5_17 reconstruction is sound. -/
theorem garner_5_17_inverse_sound :
    (5 * 7) % 17 = 1 ∧ 5 * 17 = 85 := by
  decide

/--
Theorem: Exhaustive Garner reconstruction soundness across all 85 states of F_5 x F_17.
Proved constructively with ZERO axioms via decide.
-/
theorem garner_5_17_roundtrip_all :
    ∀ (x : Fin 85), garner5_17 (x.val % 5) (x.val % 17) = x.val := by
  decide

/--
Theorem: 4-Point NTT modulo 5 roundtrip invertibility on test vector (1, 2, 3, 4).
Proved constructively with ZERO axioms.
-/
theorem ntt4_mod5_roundtrip_concrete :
    let v : Vec4 := ⟨1, 2, 3, 4⟩
    intt4Mod5 (ntt4Mod5 v) = v := by
  decide

/--
Theorem (4-Point CRT-NTT Exact Integer Convolution):
Recovers exact unreduced integer convolution ⟨66, 68, 66, 60⟩ without wrap-around:
  crtNttConv4 ⟨1, 2, 3, 4⟩ ⟨5, 6, 7, 8⟩ = ⟨66, 68, 66, 60⟩
Proved constructively with ZERO axioms.
-/
theorem crt_ntt_exact_integer_convolution :
    let a : Vec4 := ⟨1, 2, 3, 4⟩
    let b : Vec4 := ⟨5, 6, 7, 8⟩
    crtNttConv4 a b = exactIntCyclicConv4 a b ∧
    crtNttConv4 a b = ⟨66, 68, 66, 60⟩ := by
  decide

/-- Theorem: 8th roots of unity and inverse identities modulo 17 are sound. -/
theorem ntt8_mod17_roots_sound :
    (9 ^ 8) % 17 = 1 ∧
    (9 ^ 4) % 17 = 16 ∧
    (9 * 2) % 17 = 1 ∧
    (13 * 4) % 17 = 1 ∧
    (15 * 8) % 17 = 1 ∧
    (8 * 15) % 17 = 1 := by
  decide

/-- Theorem: 8th roots of unity and inverse identities modulo 257 are sound. -/
theorem ntt8_mod257_roots_sound :
    (4 ^ 8) % 257 = 1 ∧
    (4 ^ 4) % 257 = 256 ∧
    (4 * 193) % 257 = 1 ∧
    (16 * 241) % 257 = 1 ∧
    (64 * 253) % 257 = 1 ∧
    (8 * 225) % 257 = 1 := by
  decide

/-- Theorem: Modulo 257 inverse for Garner 17_257 reconstruction is sound. -/
theorem garner_17_257_inverse_sound :
    (17 * 121) % 257 = 1 ∧ 17 * 257 = 4369 := by
  decide

/--
Theorem: Garner 17_257 reconstruction soundness on boundary and sample states.
Verifies exact reconstruction across zero, small, medium, inverse, and max values (4368).
Proved constructively with ZERO axioms.
-/
theorem garner_17_257_roundtrip_samples :
    garner17_257 (0 % 17) (0 % 257) = 0 ∧
    garner17_257 (1 % 17) (1 % 257) = 1 ∧
    garner17_257 (17 % 17) (17 % 257) = 17 ∧
    garner17_257 (257 % 17) (257 % 257) = 257 ∧
    garner17_257 (1000 % 17) (1000 % 257) = 1000 ∧
    garner17_257 (2057 % 17) (2057 % 257) = 2057 ∧
    garner17_257 (4368 % 17) (4368 % 257) = 4368 := by
  decide

/--
Theorem (Universal Garner 17_257 Reconstruction Soundness):
Reconstructs EVERY integer y < 4369 from its residues modulo 17 and 257.
Proved constructively with ZERO axioms.
-/
theorem garner17_257_roundtrip_all (y : Nat) (hy : y < 4369) :
    garner17_257 (y % 17) (y % 257) = y := by
  dsimp [garner17_257]
  omega

/--
Theorem: 8-Point NTT roundtrip invertibility on test vector (1, 2, 3, 4, 5, 6, 7, 8)
for both F_17 and F_257 channels.
Proved constructively with ZERO axioms.
-/
theorem ntt8_mod17_and_mod257_roundtrip_concrete :
    let v : Vec8 := ⟨1, 2, 3, 4, 5, 6, 7, 8⟩
    intt8Mod17 (ntt8Mod17 v) = v ∧
    intt8Mod257 (ntt8Mod257 v) = v := by
  decide

/--
Theorem (8-Point CRT-NTT Exact Integer Convolution):
Recovers exact unreduced integer cyclic convolution ⟨176, 156, 144, 140, 144, 156, 176, 204⟩
exceeding both single channels mod 17 and mod 257, verified across dynamic range M = 4,369.
Proved constructively with ZERO axioms.
-/
theorem crt_ntt8_exact_integer_convolution :
    let a : Vec8 := ⟨1, 2, 3, 4, 5, 6, 7, 8⟩
    let b : Vec8 := ⟨8, 7, 6, 5, 4, 3, 2, 1⟩
    crtNttConv8 a b = exactIntCyclicConv8 a b ∧
    crtNttConv8 a b = ⟨176, 156, 144, 140, 144, 156, 176, 204⟩ := by
  decide

-- =============================================================================
-- Universal 8-Point NTT Soundness & Cyclic Convolution Theorems (gemweb042)
-- =============================================================================

set_option maxHeartbeats 2000000

/-- Equality helper for Vec8 components. -/
theorem vec8_eq_intro (u v : Vec8)
    (h0 : u.x0 = v.x0) (h1 : u.x1 = v.x1) (h2 : u.x2 = v.x2) (h3 : u.x3 = v.x3)
    (h4 : u.x4 = v.x4) (h5 : u.x5 = v.x5) (h6 : u.x6 = v.x6) (h7 : u.x7 = v.x7) :
    u = v := by
  cases u; cases v; congr

/-- Canonical reduction of a Vec8 into F_p. -/
def normVec8 (p : Nat) (v : Vec8) : Vec8 :=
  ⟨v.x0 % p, v.x1 % p, v.x2 % p, v.x3 % p, v.x4 % p, v.x5 % p, v.x6 % p, v.x7 % p⟩

theorem ntt8Mod17_lane0 (v : Vec8) :
    (ntt8Mod17 v).x0 = (v.x0 + v.x1 + v.x2 + v.x3 + v.x4 + v.x5 + v.x6 + v.x7) % 17 := by
  dsimp [ntt8Mod17, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod17_lane1 (v : Vec8) :
    (ntt8Mod17 v).x1 = (v.x0 + 9 * v.x1 + 13 * v.x2 + 15 * v.x3 + 16 * v.x4 + 8 * v.x5
      + 4 * v.x6 + 2 * v.x7) % 17 := by
  dsimp [ntt8Mod17, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod17_lane2 (v : Vec8) :
    (ntt8Mod17 v).x2 = (v.x0 + 13 * v.x1 + 16 * v.x2 + 4 * v.x3 + v.x4 + 13 * v.x5 + 16 * v.x6
      + 4 * v.x7) % 17 := by
  dsimp [ntt8Mod17, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod17_lane3 (v : Vec8) :
    (ntt8Mod17 v).x3 = (v.x0 + 15 * v.x1 + 4 * v.x2 + 9 * v.x3 + 16 * v.x4 + 2 * v.x5
      + 13 * v.x6 + 8 * v.x7) % 17 := by
  dsimp [ntt8Mod17, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod17_lane4 (v : Vec8) :
    (ntt8Mod17 v).x4 = (v.x0 + 16 * v.x1 + v.x2 + 16 * v.x3 + v.x4 + 16 * v.x5 + v.x6
      + 16 * v.x7) % 17 := by
  dsimp [ntt8Mod17, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod17_lane5 (v : Vec8) :
    (ntt8Mod17 v).x5 = (v.x0 + 8 * v.x1 + 13 * v.x2 + 2 * v.x3 + 16 * v.x4 + 9 * v.x5
      + 4 * v.x6 + 15 * v.x7) % 17 := by
  dsimp [ntt8Mod17, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod17_lane6 (v : Vec8) :
    (ntt8Mod17 v).x6 = (v.x0 + 4 * v.x1 + 16 * v.x2 + 13 * v.x3 + v.x4 + 4 * v.x5 + 16 * v.x6
      + 13 * v.x7) % 17 := by
  dsimp [ntt8Mod17, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod17_lane7 (v : Vec8) :
    (ntt8Mod17 v).x7 = (v.x0 + 2 * v.x1 + 4 * v.x2 + 8 * v.x3 + 16 * v.x4 + 15 * v.x5
      + 13 * v.x6 + 9 * v.x7) % 17 := by
  dsimp [ntt8Mod17, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod257_lane0 (v : Vec8) :
    (ntt8Mod257 v).x0 = (v.x0 + v.x1 + v.x2 + v.x3 + v.x4 + v.x5 + v.x6 + v.x7) % 257 := by
  dsimp [ntt8Mod257, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod257_lane1 (v : Vec8) :
    (ntt8Mod257 v).x1 = (v.x0 + 4 * v.x1 + 16 * v.x2 + 64 * v.x3 + 256 * v.x4 + 253 * v.x5
      + 241 * v.x6 + 193 * v.x7) % 257 := by
  dsimp [ntt8Mod257, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod257_lane2 (v : Vec8) :
    (ntt8Mod257 v).x2 = (v.x0 + 16 * v.x1 + 256 * v.x2 + 241 * v.x3 + v.x4 + 16 * v.x5
      + 256 * v.x6 + 241 * v.x7) % 257 := by
  dsimp [ntt8Mod257, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod257_lane3 (v : Vec8) :
    (ntt8Mod257 v).x3 = (v.x0 + 64 * v.x1 + 241 * v.x2 + 4 * v.x3 + 256 * v.x4 + 193 * v.x5
      + 16 * v.x6 + 253 * v.x7) % 257 := by
  dsimp [ntt8Mod257, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod257_lane4 (v : Vec8) :
    (ntt8Mod257 v).x4 = (v.x0 + 256 * v.x1 + v.x2 + 256 * v.x3 + v.x4 + 256 * v.x5 + v.x6
      + 256 * v.x7) % 257 := by
  dsimp [ntt8Mod257, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod257_lane5 (v : Vec8) :
    (ntt8Mod257 v).x5 = (v.x0 + 253 * v.x1 + 16 * v.x2 + 193 * v.x3 + 256 * v.x4 + 4 * v.x5
      + 241 * v.x6 + 64 * v.x7) % 257 := by
  dsimp [ntt8Mod257, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod257_lane6 (v : Vec8) :
    (ntt8Mod257 v).x6 = (v.x0 + 241 * v.x1 + 256 * v.x2 + 16 * v.x3 + v.x4 + 241 * v.x5
      + 256 * v.x6 + 16 * v.x7) % 257 := by
  dsimp [ntt8Mod257, ntt8WithRoots, butterfly2]; omega

theorem ntt8Mod257_lane7 (v : Vec8) :
    (ntt8Mod257 v).x7 = (v.x0 + 193 * v.x1 + 241 * v.x2 + 253 * v.x3 + 256 * v.x4 + 64 * v.x5
      + 16 * v.x6 + 4 * v.x7) % 257 := by
  dsimp [ntt8Mod257, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod17_lane0 (X : Vec8) :
    (intt8Mod17 X).x0 = ((X.x0 + X.x1 + X.x2 + X.x3 + X.x4 + X.x5 + X.x6 + X.x7) * 15) % 17 := by
  dsimp [intt8Mod17, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod17_lane1 (X : Vec8) :
    (intt8Mod17 X).x1 = ((X.x0 + 2 * X.x1 + 4 * X.x2 + 8 * X.x3 + 16 * X.x4 + 15 * X.x5
      + 13 * X.x6 + 9 * X.x7) * 15) % 17 := by
  dsimp [intt8Mod17, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod17_lane2 (X : Vec8) :
    (intt8Mod17 X).x2 = ((X.x0 + 4 * X.x1 + 16 * X.x2 + 13 * X.x3 + X.x4 + 4 * X.x5 + 16 * X.x6
      + 13 * X.x7) * 15) % 17 := by
  dsimp [intt8Mod17, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod17_lane3 (X : Vec8) :
    (intt8Mod17 X).x3 = ((X.x0 + 8 * X.x1 + 13 * X.x2 + 2 * X.x3 + 16 * X.x4 + 9 * X.x5
      + 4 * X.x6 + 15 * X.x7) * 15) % 17 := by
  dsimp [intt8Mod17, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod17_lane4 (X : Vec8) :
    (intt8Mod17 X).x4 = ((X.x0 + 16 * X.x1 + X.x2 + 16 * X.x3 + X.x4 + 16 * X.x5 + X.x6
      + 16 * X.x7) * 15) % 17 := by
  dsimp [intt8Mod17, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod17_lane5 (X : Vec8) :
    (intt8Mod17 X).x5 = ((X.x0 + 15 * X.x1 + 4 * X.x2 + 9 * X.x3 + 16 * X.x4 + 2 * X.x5
      + 13 * X.x6 + 8 * X.x7) * 15) % 17 := by
  dsimp [intt8Mod17, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod17_lane6 (X : Vec8) :
    (intt8Mod17 X).x6 = ((X.x0 + 13 * X.x1 + 16 * X.x2 + 4 * X.x3 + X.x4 + 13 * X.x5
      + 16 * X.x6 + 4 * X.x7) * 15) % 17 := by
  dsimp [intt8Mod17, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod17_lane7 (X : Vec8) :
    (intt8Mod17 X).x7 = ((X.x0 + 9 * X.x1 + 13 * X.x2 + 15 * X.x3 + 16 * X.x4 + 8 * X.x5
      + 4 * X.x6 + 2 * X.x7) * 15) % 17 := by
  dsimp [intt8Mod17, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod257_lane0 (X : Vec8) :
    (intt8Mod257 X).x0 = ((X.x0 + X.x1 + X.x2 + X.x3 + X.x4 + X.x5 + X.x6 + X.x7) * 225) % 257 := by
  dsimp [intt8Mod257, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod257_lane1 (X : Vec8) :
    (intt8Mod257 X).x1 = ((X.x0 + 193 * X.x1 + 241 * X.x2 + 253 * X.x3 + 256 * X.x4 + 64 * X.x5
      + 16 * X.x6 + 4 * X.x7) * 225) % 257 := by
  dsimp [intt8Mod257, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod257_lane2 (X : Vec8) :
    (intt8Mod257 X).x2 = ((X.x0 + 241 * X.x1 + 256 * X.x2 + 16 * X.x3 + X.x4 + 241 * X.x5
      + 256 * X.x6 + 16 * X.x7) * 225) % 257 := by
  dsimp [intt8Mod257, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod257_lane3 (X : Vec8) :
    (intt8Mod257 X).x3 = ((X.x0 + 253 * X.x1 + 16 * X.x2 + 193 * X.x3 + 256 * X.x4 + 4 * X.x5
      + 241 * X.x6 + 64 * X.x7) * 225) % 257 := by
  dsimp [intt8Mod257, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod257_lane4 (X : Vec8) :
    (intt8Mod257 X).x4 = ((X.x0 + 256 * X.x1 + X.x2 + 256 * X.x3 + X.x4 + 256 * X.x5 + X.x6
      + 256 * X.x7) * 225) % 257 := by
  dsimp [intt8Mod257, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod257_lane5 (X : Vec8) :
    (intt8Mod257 X).x5 = ((X.x0 + 64 * X.x1 + 241 * X.x2 + 4 * X.x3 + 256 * X.x4 + 193 * X.x5
      + 16 * X.x6 + 253 * X.x7) * 225) % 257 := by
  dsimp [intt8Mod257, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod257_lane6 (X : Vec8) :
    (intt8Mod257 X).x6 = ((X.x0 + 16 * X.x1 + 256 * X.x2 + 241 * X.x3 + X.x4 + 16 * X.x5
      + 256 * X.x6 + 241 * X.x7) * 225) % 257 := by
  dsimp [intt8Mod257, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem intt8Mod257_lane7 (X : Vec8) :
    (intt8Mod257 X).x7 = ((X.x0 + 4 * X.x1 + 16 * X.x2 + 64 * X.x3 + 256 * X.x4 + 253 * X.x5
      + 241 * X.x6 + 193 * X.x7) * 225) % 257 := by
  dsimp [intt8Mod257, intt8WithRoots, ntt8WithRoots, butterfly2]; omega

theorem inv_all_lanes_17 (a0 a1 a2 a3 a4 a5 a6 a7 Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7 : Nat)
    (hY0 : Y0 % 17 = (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) % 17)
    (hY1 : Y1 % 17 = (a0 + 9 * a1 + 13 * a2 + 15 * a3 + 16 * a4 + 8 * a5 + 4 * a6 + 2 * a7) % 17)
    (hY2 : Y2 % 17 = (a0 + 13 * a1 + 16 * a2 + 4 * a3 + a4 + 13 * a5 + 16 * a6 + 4 * a7) % 17)
    (hY3 : Y3 % 17 = (a0 + 15 * a1 + 4 * a2 + 9 * a3 + 16 * a4 + 2 * a5 + 13 * a6 + 8 * a7) % 17)
    (hY4 : Y4 % 17 = (a0 + 16 * a1 + a2 + 16 * a3 + a4 + 16 * a5 + a6 + 16 * a7) % 17)
    (hY5 : Y5 % 17 = (a0 + 8 * a1 + 13 * a2 + 2 * a3 + 16 * a4 + 9 * a5 + 4 * a6 + 15 * a7) % 17)
    (hY6 : Y6 % 17 = (a0 + 4 * a1 + 16 * a2 + 13 * a3 + a4 + 4 * a5 + 16 * a6 + 13 * a7) % 17)
    (hY7 : Y7 % 17 = (a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 15 * a5 + 13 * a6 + 9 * a7) % 17)
    :
    ((Y0 + Y1 + Y2 + Y3 + Y4 + Y5 + Y6 + Y7) * 15) % 17 = a0 % 17 ∧
    ((Y0 + 2 * Y1 + 4 * Y2 + 8 * Y3 + 16 * Y4 + 15 * Y5 + 13 * Y6 + 9 * Y7) * 15) % 17 = a1 % 17 ∧
    ((Y0 + 4 * Y1 + 16 * Y2 + 13 * Y3 + Y4 + 4 * Y5 + 16 * Y6 + 13 * Y7) * 15) % 17 = a2 % 17 ∧
    ((Y0 + 8 * Y1 + 13 * Y2 + 2 * Y3 + 16 * Y4 + 9 * Y5 + 4 * Y6 + 15 * Y7) * 15) % 17 = a3 % 17 ∧
    ((Y0 + 16 * Y1 + Y2 + 16 * Y3 + Y4 + 16 * Y5 + Y6 + 16 * Y7) * 15) % 17 = a4 % 17 ∧
    ((Y0 + 15 * Y1 + 4 * Y2 + 9 * Y3 + 16 * Y4 + 2 * Y5 + 13 * Y6 + 8 * Y7) * 15) % 17 = a5 % 17 ∧
    ((Y0 + 13 * Y1 + 16 * Y2 + 4 * Y3 + Y4 + 13 * Y5 + 16 * Y6 + 4 * Y7) * 15) % 17 = a6 % 17 ∧
    ((Y0 + 9 * Y1 + 13 * Y2 + 15 * Y3 + 16 * Y4 + 8 * Y5 + 4 * Y6 + 2 * Y7) * 15) % 17 = a7 % 17 := by
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem right_inv_all_lanes_17 (y0 y1 y2 y3 y4 y5 y6 y7 A0 A1 A2 A3 A4 A5 A6 A7 : Nat)
    (hA0 : A0 % 17 = ((y0 + y1 + y2 + y3 + y4 + y5 + y6 + y7) * 15) % 17)
    (hA1 : A1 % 17 = ((y0 + 2 * y1 + 4 * y2 + 8 * y3 + 16 * y4 + 15 * y5 + 13 * y6 + 9 * y7) * 15) % 17)
    (hA2 : A2 % 17 = ((y0 + 4 * y1 + 16 * y2 + 13 * y3 + y4 + 4 * y5 + 16 * y6 + 13 * y7) * 15) % 17)
    (hA3 : A3 % 17 = ((y0 + 8 * y1 + 13 * y2 + 2 * y3 + 16 * y4 + 9 * y5 + 4 * y6 + 15 * y7) * 15) % 17)
    (hA4 : A4 % 17 = ((y0 + 16 * y1 + y2 + 16 * y3 + y4 + 16 * y5 + y6 + 16 * y7) * 15) % 17)
    (hA5 : A5 % 17 = ((y0 + 15 * y1 + 4 * y2 + 9 * y3 + 16 * y4 + 2 * y5 + 13 * y6 + 8 * y7) * 15) % 17)
    (hA6 : A6 % 17 = ((y0 + 13 * y1 + 16 * y2 + 4 * y3 + y4 + 13 * y5 + 16 * y6 + 4 * y7) * 15) % 17)
    (hA7 : A7 % 17 = ((y0 + 9 * y1 + 13 * y2 + 15 * y3 + 16 * y4 + 8 * y5 + 4 * y6 + 2 * y7) * 15) % 17)
    :
    (A0 + A1 + A2 + A3 + A4 + A5 + A6 + A7) % 17 = y0 % 17 ∧
    (A0 + 9 * A1 + 13 * A2 + 15 * A3 + 16 * A4 + 8 * A5 + 4 * A6 + 2 * A7) % 17 = y1 % 17 ∧
    (A0 + 13 * A1 + 16 * A2 + 4 * A3 + A4 + 13 * A5 + 16 * A6 + 4 * A7) % 17 = y2 % 17 ∧
    (A0 + 15 * A1 + 4 * A2 + 9 * A3 + 16 * A4 + 2 * A5 + 13 * A6 + 8 * A7) % 17 = y3 % 17 ∧
    (A0 + 16 * A1 + A2 + 16 * A3 + A4 + 16 * A5 + A6 + 16 * A7) % 17 = y4 % 17 ∧
    (A0 + 8 * A1 + 13 * A2 + 2 * A3 + 16 * A4 + 9 * A5 + 4 * A6 + 15 * A7) % 17 = y5 % 17 ∧
    (A0 + 4 * A1 + 16 * A2 + 13 * A3 + A4 + 4 * A5 + 16 * A6 + 13 * A7) % 17 = y6 % 17 ∧
    (A0 + 2 * A1 + 4 * A2 + 8 * A3 + 16 * A4 + 15 * A5 + 13 * A6 + 9 * A7) % 17 = y7 % 17 := by
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem inv_all_lanes_257 (a0 a1 a2 a3 a4 a5 a6 a7 Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7 : Nat)
    (hY0 : Y0 % 257 = (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) % 257)
    (hY1 : Y1 % 257 = (a0 + 4 * a1 + 16 * a2 + 64 * a3 + 256 * a4 + 253 * a5 + 241 * a6
      + 193 * a7) % 257)
    (hY2 : Y2 % 257 = (a0 + 16 * a1 + 256 * a2 + 241 * a3 + a4 + 16 * a5 + 256 * a6 + 241 * a7) % 257)
    (hY3 : Y3 % 257 = (a0 + 64 * a1 + 241 * a2 + 4 * a3 + 256 * a4 + 193 * a5 + 16 * a6
      + 253 * a7) % 257)
    (hY4 : Y4 % 257 = (a0 + 256 * a1 + a2 + 256 * a3 + a4 + 256 * a5 + a6 + 256 * a7) % 257)
    (hY5 : Y5 % 257 = (a0 + 253 * a1 + 16 * a2 + 193 * a3 + 256 * a4 + 4 * a5 + 241 * a6
      + 64 * a7) % 257)
    (hY6 : Y6 % 257 = (a0 + 241 * a1 + 256 * a2 + 16 * a3 + a4 + 241 * a5 + 256 * a6 + 16 * a7) % 257)
    (hY7 : Y7 % 257 = (a0 + 193 * a1 + 241 * a2 + 253 * a3 + 256 * a4 + 64 * a5 + 16 * a6
      + 4 * a7) % 257)
    :
    ((Y0 + Y1 + Y2 + Y3 + Y4 + Y5 + Y6 + Y7) * 225) % 257 = a0 % 257 ∧
    ((Y0 + 193 * Y1 + 241 * Y2 + 253 * Y3 + 256 * Y4 + 64 * Y5 + 16 * Y6 + 4 * Y7) * 225) % 257 = a1 % 257 ∧
    ((Y0 + 241 * Y1 + 256 * Y2 + 16 * Y3 + Y4 + 241 * Y5 + 256 * Y6 + 16 * Y7) * 225) % 257 = a2 % 257 ∧
    ((Y0 + 253 * Y1 + 16 * Y2 + 193 * Y3 + 256 * Y4 + 4 * Y5 + 241 * Y6 + 64 * Y7) * 225) % 257 = a3 % 257 ∧
    ((Y0 + 256 * Y1 + Y2 + 256 * Y3 + Y4 + 256 * Y5 + Y6 + 256 * Y7) * 225) % 257 = a4 % 257 ∧
    ((Y0 + 64 * Y1 + 241 * Y2 + 4 * Y3 + 256 * Y4 + 193 * Y5 + 16 * Y6 + 253 * Y7) * 225) % 257 = a5 % 257 ∧
    ((Y0 + 16 * Y1 + 256 * Y2 + 241 * Y3 + Y4 + 16 * Y5 + 256 * Y6 + 241 * Y7) * 225) % 257 = a6 % 257 ∧
    ((Y0 + 4 * Y1 + 16 * Y2 + 64 * Y3 + 256 * Y4 + 253 * Y5 + 241 * Y6 + 193 * Y7) * 225) % 257 = a7 % 257 := by
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem right_inv_all_lanes_257 (y0 y1 y2 y3 y4 y5 y6 y7 A0 A1 A2 A3 A4 A5 A6 A7 : Nat)
    (hA0 : A0 % 257 = ((y0 + y1 + y2 + y3 + y4 + y5 + y6 + y7) * 225) % 257)
    (hA1 : A1 % 257 = ((y0 + 193 * y1 + 241 * y2 + 253 * y3 + 256 * y4 + 64 * y5 + 16 * y6
      + 4 * y7) * 225) % 257)
    (hA2 : A2 % 257 = ((y0 + 241 * y1 + 256 * y2 + 16 * y3 + y4 + 241 * y5 + 256 * y6 + 16 * y7) * 225) % 257)
    (hA3 : A3 % 257 = ((y0 + 253 * y1 + 16 * y2 + 193 * y3 + 256 * y4 + 4 * y5 + 241 * y6
      + 64 * y7) * 225) % 257)
    (hA4 : A4 % 257 = ((y0 + 256 * y1 + y2 + 256 * y3 + y4 + 256 * y5 + y6 + 256 * y7) * 225) % 257)
    (hA5 : A5 % 257 = ((y0 + 64 * y1 + 241 * y2 + 4 * y3 + 256 * y4 + 193 * y5 + 16 * y6
      + 253 * y7) * 225) % 257)
    (hA6 : A6 % 257 = ((y0 + 16 * y1 + 256 * y2 + 241 * y3 + y4 + 16 * y5 + 256 * y6 + 241 * y7) * 225) % 257)
    (hA7 : A7 % 257 = ((y0 + 4 * y1 + 16 * y2 + 64 * y3 + 256 * y4 + 253 * y5 + 241 * y6
      + 193 * y7) * 225) % 257)
    :
    (A0 + A1 + A2 + A3 + A4 + A5 + A6 + A7) % 257 = y0 % 257 ∧
    (A0 + 4 * A1 + 16 * A2 + 64 * A3 + 256 * A4 + 253 * A5 + 241 * A6 + 193 * A7) % 257 = y1 % 257 ∧
    (A0 + 16 * A1 + 256 * A2 + 241 * A3 + A4 + 16 * A5 + 256 * A6 + 241 * A7) % 257 = y2 % 257 ∧
    (A0 + 64 * A1 + 241 * A2 + 4 * A3 + 256 * A4 + 193 * A5 + 16 * A6 + 253 * A7) % 257 = y3 % 257 ∧
    (A0 + 256 * A1 + A2 + 256 * A3 + A4 + 256 * A5 + A6 + 256 * A7) % 257 = y4 % 257 ∧
    (A0 + 253 * A1 + 16 * A2 + 193 * A3 + 256 * A4 + 4 * A5 + 241 * A6 + 64 * A7) % 257 = y5 % 257 ∧
    (A0 + 241 * A1 + 256 * A2 + 16 * A3 + A4 + 241 * A5 + 256 * A6 + 16 * A7) % 257 = y6 % 257 ∧
    (A0 + 193 * A1 + 241 * A2 + 253 * A3 + 256 * A4 + 64 * A5 + 16 * A6 + 4 * A7) % 257 = y7 % 257 := by
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem intt8_ntt8_universal_F17_lanes (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) :
    intt8Mod17 (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩) =
    ⟨a0 % 17, a1 % 17, a2 % 17, a3 % 17, a4 % 17, a5 % 17, a6 % 17, a7 % 17⟩ := by
  have h0 : (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x0 % 17 =
      (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) % 17 := by
    rw [ntt8Mod17_lane0]; exact Nat.mod_mod _ 17
  have h1 : (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x1 % 17 =
      (a0 + 9 * a1 + 13 * a2 + 15 * a3 + 16 * a4 + 8 * a5 + 4 * a6 + 2 * a7) % 17 := by
    rw [ntt8Mod17_lane1]; exact Nat.mod_mod _ 17
  have h2 : (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x2 % 17 =
      (a0 + 13 * a1 + 16 * a2 + 4 * a3 + a4 + 13 * a5 + 16 * a6 + 4 * a7) % 17 := by
    rw [ntt8Mod17_lane2]; exact Nat.mod_mod _ 17
  have h3 : (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x3 % 17 =
      (a0 + 15 * a1 + 4 * a2 + 9 * a3 + 16 * a4 + 2 * a5 + 13 * a6 + 8 * a7) % 17 := by
    rw [ntt8Mod17_lane3]; exact Nat.mod_mod _ 17
  have h4 : (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x4 % 17 =
      (a0 + 16 * a1 + a2 + 16 * a3 + a4 + 16 * a5 + a6 + 16 * a7) % 17 := by
    rw [ntt8Mod17_lane4]; exact Nat.mod_mod _ 17
  have h5 : (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x5 % 17 =
      (a0 + 8 * a1 + 13 * a2 + 2 * a3 + 16 * a4 + 9 * a5 + 4 * a6 + 15 * a7) % 17 := by
    rw [ntt8Mod17_lane5]; exact Nat.mod_mod _ 17
  have h6 : (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x6 % 17 =
      (a0 + 4 * a1 + 16 * a2 + 13 * a3 + a4 + 4 * a5 + 16 * a6 + 13 * a7) % 17 := by
    rw [ntt8Mod17_lane6]; exact Nat.mod_mod _ 17
  have h7 : (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x7 % 17 =
      (a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 15 * a5 + 13 * a6 + 9 * a7) % 17 := by
    rw [ntt8Mod17_lane7]; exact Nat.mod_mod _ 17
  have hi0 := intt8Mod17_lane0 (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have hi1 := intt8Mod17_lane1 (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have hi2 := intt8Mod17_lane2 (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have hi3 := intt8Mod17_lane3 (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have hi4 := intt8Mod17_lane4 (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have hi5 := intt8Mod17_lane5 (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have hi6 := intt8Mod17_lane6 (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have hi7 := intt8Mod17_lane7 (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have h_comb := inv_all_lanes_17 a0 a1 a2 a3 a4 a5 a6 a7
    (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x0
    (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x1
    (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x2
    (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x3
    (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x4
    (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x5
    (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x6
    (ntt8Mod17 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x7
    h0 h1 h2 h3 h4 h5 h6 h7
  apply vec8_eq_intro
  · rw [hi0]; exact h_comb.1
  · rw [hi1]; exact h_comb.2.1
  · rw [hi2]; exact h_comb.2.2.1
  · rw [hi3]; exact h_comb.2.2.2.1
  · rw [hi4]; exact h_comb.2.2.2.2.1
  · rw [hi5]; exact h_comb.2.2.2.2.2.1
  · rw [hi6]; exact h_comb.2.2.2.2.2.2.1
  · rw [hi7]; exact h_comb.2.2.2.2.2.2.2

/-- Universal 8-Point NTT Invertibility (Left Inverse) over F_17. -/
theorem intt8_ntt8_universal_F17 (a : Vec8) :
    intt8Mod17 (ntt8Mod17 a) = normVec8 17 a := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  exact intt8_ntt8_universal_F17_lanes a0 a1 a2 a3 a4 a5 a6 a7

theorem ntt8_intt8_universal_F17_lanes (y0 y1 y2 y3 y4 y5 y6 y7 : Nat) :
    ntt8Mod17 (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩) =
    ⟨y0 % 17, y1 % 17, y2 % 17, y3 % 17, y4 % 17, y5 % 17, y6 % 17, y7 % 17⟩ := by
  have h0 : (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x0 % 17 =
      ((y0 + y1 + y2 + y3 + y4 + y5 + y6 + y7) * 15) % 17 := by
    rw [intt8Mod17_lane0]; exact Nat.mod_mod _ 17
  have h1 : (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x1 % 17 =
      ((y0 + 2 * y1 + 4 * y2 + 8 * y3 + 16 * y4 + 15 * y5 + 13 * y6 + 9 * y7) * 15) % 17 := by
    rw [intt8Mod17_lane1]; exact Nat.mod_mod _ 17
  have h2 : (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x2 % 17 =
      ((y0 + 4 * y1 + 16 * y2 + 13 * y3 + y4 + 4 * y5 + 16 * y6 + 13 * y7) * 15) % 17 := by
    rw [intt8Mod17_lane2]; exact Nat.mod_mod _ 17
  have h3 : (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x3 % 17 =
      ((y0 + 8 * y1 + 13 * y2 + 2 * y3 + 16 * y4 + 9 * y5 + 4 * y6 + 15 * y7) * 15) % 17 := by
    rw [intt8Mod17_lane3]; exact Nat.mod_mod _ 17
  have h4 : (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x4 % 17 =
      ((y0 + 16 * y1 + y2 + 16 * y3 + y4 + 16 * y5 + y6 + 16 * y7) * 15) % 17 := by
    rw [intt8Mod17_lane4]; exact Nat.mod_mod _ 17
  have h5 : (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x5 % 17 =
      ((y0 + 15 * y1 + 4 * y2 + 9 * y3 + 16 * y4 + 2 * y5 + 13 * y6 + 8 * y7) * 15) % 17 := by
    rw [intt8Mod17_lane5]; exact Nat.mod_mod _ 17
  have h6 : (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x6 % 17 =
      ((y0 + 13 * y1 + 16 * y2 + 4 * y3 + y4 + 13 * y5 + 16 * y6 + 4 * y7) * 15) % 17 := by
    rw [intt8Mod17_lane6]; exact Nat.mod_mod _ 17
  have h7 : (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x7 % 17 =
      ((y0 + 9 * y1 + 13 * y2 + 15 * y3 + 16 * y4 + 8 * y5 + 4 * y6 + 2 * y7) * 15) % 17 := by
    rw [intt8Mod17_lane7]; exact Nat.mod_mod _ 17
  have hn0 := ntt8Mod17_lane0 (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have hn1 := ntt8Mod17_lane1 (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have hn2 := ntt8Mod17_lane2 (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have hn3 := ntt8Mod17_lane3 (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have hn4 := ntt8Mod17_lane4 (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have hn5 := ntt8Mod17_lane5 (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have hn6 := ntt8Mod17_lane6 (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have hn7 := ntt8Mod17_lane7 (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have h_comb := right_inv_all_lanes_17 y0 y1 y2 y3 y4 y5 y6 y7
    (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x0
    (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x1
    (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x2
    (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x3
    (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x4
    (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x5
    (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x6
    (intt8Mod17 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x7
    h0 h1 h2 h3 h4 h5 h6 h7
  apply vec8_eq_intro
  · rw [hn0]; exact h_comb.1
  · rw [hn1]; exact h_comb.2.1
  · rw [hn2]; exact h_comb.2.2.1
  · rw [hn3]; exact h_comb.2.2.2.1
  · rw [hn4]; exact h_comb.2.2.2.2.1
  · rw [hn5]; exact h_comb.2.2.2.2.2.1
  · rw [hn6]; exact h_comb.2.2.2.2.2.2.1
  · rw [hn7]; exact h_comb.2.2.2.2.2.2.2

/-- Universal 8-Point NTT Invertibility (Right Inverse) over F_17. -/
theorem ntt8_intt8_universal_F17 (y : Vec8) :
    ntt8Mod17 (intt8Mod17 y) = normVec8 17 y := by
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ := y
  exact ntt8_intt8_universal_F17_lanes y0 y1 y2 y3 y4 y5 y6 y7

theorem intt8_ntt8_universal_F257_lanes (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) :
    intt8Mod257 (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩) =
    ⟨a0 % 257, a1 % 257, a2 % 257, a3 % 257, a4 % 257, a5 % 257, a6 % 257, a7 % 257⟩ := by
  have h0 : (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x0 % 257 =
      (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) % 257 := by
    rw [ntt8Mod257_lane0]; exact Nat.mod_mod _ 257
  have h1 : (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x1 % 257 =
      (a0 + 4 * a1 + 16 * a2 + 64 * a3 + 256 * a4 + 253 * a5 + 241 * a6 + 193 * a7) % 257 := by
    rw [ntt8Mod257_lane1]; exact Nat.mod_mod _ 257
  have h2 : (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x2 % 257 =
      (a0 + 16 * a1 + 256 * a2 + 241 * a3 + a4 + 16 * a5 + 256 * a6 + 241 * a7) % 257 := by
    rw [ntt8Mod257_lane2]; exact Nat.mod_mod _ 257
  have h3 : (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x3 % 257 =
      (a0 + 64 * a1 + 241 * a2 + 4 * a3 + 256 * a4 + 193 * a5 + 16 * a6 + 253 * a7) % 257 := by
    rw [ntt8Mod257_lane3]; exact Nat.mod_mod _ 257
  have h4 : (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x4 % 257 =
      (a0 + 256 * a1 + a2 + 256 * a3 + a4 + 256 * a5 + a6 + 256 * a7) % 257 := by
    rw [ntt8Mod257_lane4]; exact Nat.mod_mod _ 257
  have h5 : (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x5 % 257 =
      (a0 + 253 * a1 + 16 * a2 + 193 * a3 + 256 * a4 + 4 * a5 + 241 * a6 + 64 * a7) % 257 := by
    rw [ntt8Mod257_lane5]; exact Nat.mod_mod _ 257
  have h6 : (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x6 % 257 =
      (a0 + 241 * a1 + 256 * a2 + 16 * a3 + a4 + 241 * a5 + 256 * a6 + 16 * a7) % 257 := by
    rw [ntt8Mod257_lane6]; exact Nat.mod_mod _ 257
  have h7 : (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x7 % 257 =
      (a0 + 193 * a1 + 241 * a2 + 253 * a3 + 256 * a4 + 64 * a5 + 16 * a6 + 4 * a7) % 257 := by
    rw [ntt8Mod257_lane7]; exact Nat.mod_mod _ 257
  have hi0 := intt8Mod257_lane0 (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have hi1 := intt8Mod257_lane1 (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have hi2 := intt8Mod257_lane2 (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have hi3 := intt8Mod257_lane3 (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have hi4 := intt8Mod257_lane4 (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have hi5 := intt8Mod257_lane5 (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have hi6 := intt8Mod257_lane6 (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have hi7 := intt8Mod257_lane7 (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩)
  have h_comb := inv_all_lanes_257 a0 a1 a2 a3 a4 a5 a6 a7
    (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x0
    (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x1
    (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x2
    (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x3
    (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x4
    (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x5
    (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x6
    (ntt8Mod257 ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩).x7
    h0 h1 h2 h3 h4 h5 h6 h7
  apply vec8_eq_intro
  · rw [hi0]; exact h_comb.1
  · rw [hi1]; exact h_comb.2.1
  · rw [hi2]; exact h_comb.2.2.1
  · rw [hi3]; exact h_comb.2.2.2.1
  · rw [hi4]; exact h_comb.2.2.2.2.1
  · rw [hi5]; exact h_comb.2.2.2.2.2.1
  · rw [hi6]; exact h_comb.2.2.2.2.2.2.1
  · rw [hi7]; exact h_comb.2.2.2.2.2.2.2

/-- Universal 8-Point NTT Invertibility (Left Inverse) over F_257. -/
theorem intt8_ntt8_universal_F257 (a : Vec8) :
    intt8Mod257 (ntt8Mod257 a) = normVec8 257 a := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  exact intt8_ntt8_universal_F257_lanes a0 a1 a2 a3 a4 a5 a6 a7

theorem ntt8_intt8_universal_F257_lanes (y0 y1 y2 y3 y4 y5 y6 y7 : Nat) :
    ntt8Mod257 (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩) =
    ⟨y0 % 257, y1 % 257, y2 % 257, y3 % 257, y4 % 257, y5 % 257, y6 % 257, y7 % 257⟩ := by
  have h0 : (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x0 % 257 =
      ((y0 + y1 + y2 + y3 + y4 + y5 + y6 + y7) * 225) % 257 := by
    rw [intt8Mod257_lane0]; exact Nat.mod_mod _ 257
  have h1 : (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x1 % 257 =
      ((y0 + 193 * y1 + 241 * y2 + 253 * y3 + 256 * y4 + 64 * y5 + 16 * y6 + 4 * y7) * 225) % 257 := by
    rw [intt8Mod257_lane1]; exact Nat.mod_mod _ 257
  have h2 : (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x2 % 257 =
      ((y0 + 241 * y1 + 256 * y2 + 16 * y3 + y4 + 241 * y5 + 256 * y6 + 16 * y7) * 225) % 257 := by
    rw [intt8Mod257_lane2]; exact Nat.mod_mod _ 257
  have h3 : (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x3 % 257 =
      ((y0 + 253 * y1 + 16 * y2 + 193 * y3 + 256 * y4 + 4 * y5 + 241 * y6 + 64 * y7) * 225) % 257 := by
    rw [intt8Mod257_lane3]; exact Nat.mod_mod _ 257
  have h4 : (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x4 % 257 =
      ((y0 + 256 * y1 + y2 + 256 * y3 + y4 + 256 * y5 + y6 + 256 * y7) * 225) % 257 := by
    rw [intt8Mod257_lane4]; exact Nat.mod_mod _ 257
  have h5 : (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x5 % 257 =
      ((y0 + 64 * y1 + 241 * y2 + 4 * y3 + 256 * y4 + 193 * y5 + 16 * y6 + 253 * y7) * 225) % 257 := by
    rw [intt8Mod257_lane5]; exact Nat.mod_mod _ 257
  have h6 : (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x6 % 257 =
      ((y0 + 16 * y1 + 256 * y2 + 241 * y3 + y4 + 16 * y5 + 256 * y6 + 241 * y7) * 225) % 257 := by
    rw [intt8Mod257_lane6]; exact Nat.mod_mod _ 257
  have h7 : (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x7 % 257 =
      ((y0 + 4 * y1 + 16 * y2 + 64 * y3 + 256 * y4 + 253 * y5 + 241 * y6 + 193 * y7) * 225) % 257 := by
    rw [intt8Mod257_lane7]; exact Nat.mod_mod _ 257
  have hn0 := ntt8Mod257_lane0 (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have hn1 := ntt8Mod257_lane1 (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have hn2 := ntt8Mod257_lane2 (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have hn3 := ntt8Mod257_lane3 (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have hn4 := ntt8Mod257_lane4 (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have hn5 := ntt8Mod257_lane5 (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have hn6 := ntt8Mod257_lane6 (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have hn7 := ntt8Mod257_lane7 (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩)
  have h_comb := right_inv_all_lanes_257 y0 y1 y2 y3 y4 y5 y6 y7
    (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x0
    (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x1
    (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x2
    (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x3
    (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x4
    (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x5
    (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x6
    (intt8Mod257 ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩).x7
    h0 h1 h2 h3 h4 h5 h6 h7
  apply vec8_eq_intro
  · rw [hn0]; exact h_comb.1
  · rw [hn1]; exact h_comb.2.1
  · rw [hn2]; exact h_comb.2.2.1
  · rw [hn3]; exact h_comb.2.2.2.1
  · rw [hn4]; exact h_comb.2.2.2.2.1
  · rw [hn5]; exact h_comb.2.2.2.2.2.1
  · rw [hn6]; exact h_comb.2.2.2.2.2.2.1
  · rw [hn7]; exact h_comb.2.2.2.2.2.2.2

/-- Universal 8-Point NTT Invertibility (Right Inverse) over F_257. -/
theorem ntt8_intt8_universal_F257 (y : Vec8) :
    ntt8Mod257 (intt8Mod257 y) = normVec8 257 y := by
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ := y
  exact ntt8_intt8_universal_F257_lanes y0 y1 y2 y3 y4 y5 y6 y7

theorem mul_mod_expand_lane0_17 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) * (b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7) =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl

theorem mul_mod_expand_lane1_17 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  ((a0 + 9 * a1 + 13 * a2 + 15 * a3 + 16 * a4 + 8 * a5 + 4 * a6 + 2 * a7) *
   (b0 + 9 * b1 + 13 * b2 + 15 * b3 + 16 * b4 + 8 * b5 + 4 * b6 + 2 * b7)) % 17 =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   9 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   13 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   15 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   16 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   8 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   4 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   2 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
  have h_exp :
    (a0 + 9 * a1 + 13 * a2 + 15 * a3 + 16 * a4 + 8 * a5 + 4 * a6 + 2 * a7) *
    (b0 + 9 * b1 + 13 * b2 + 15 * b3 + 16 * b4 + 8 * b5 + 4 * b6 + 2 * b7) =
    (a0*b0 + 9*(a0*b1) + 13*(a0*b2) + 15*(a0*b3) + 16*(a0*b4) + 8*(a0*b5) + 4*(a0*b6)
      + 2*(a0*b7) + 9*(a1*b0) + 81*(a1*b1) + 117*(a1*b2) + 135*(a1*b3) + 144*(a1*b4)
      + 72*(a1*b5) + 36*(a1*b6) + 18*(a1*b7) + 13*(a2*b0) + 117*(a2*b1) + 169*(a2*b2)
      + 195*(a2*b3) + 208*(a2*b4) + 104*(a2*b5) + 52*(a2*b6) + 26*(a2*b7) + 15*(a3*b0)
      + 135*(a3*b1) + 195*(a3*b2) + 225*(a3*b3) + 240*(a3*b4) + 120*(a3*b5) + 60*(a3*b6)
      + 30*(a3*b7) + 16*(a4*b0) + 144*(a4*b1) + 208*(a4*b2) + 240*(a4*b3) + 256*(a4*b4)
      + 128*(a4*b5) + 64*(a4*b6) + 32*(a4*b7) + 8*(a5*b0) + 72*(a5*b1) + 104*(a5*b2)
      + 120*(a5*b3) + 128*(a5*b4) + 64*(a5*b5) + 32*(a5*b6) + 16*(a5*b7) + 4*(a6*b0)
      + 36*(a6*b1) + 52*(a6*b2) + 60*(a6*b3) + 64*(a6*b4) + 32*(a6*b5) + 16*(a6*b6) + 8*(a6*b7)
      + 2*(a7*b0) + 18*(a7*b1) + 26*(a7*b2) + 30*(a7*b3) + 32*(a7*b4) + 16*(a7*b5) + 8*(a7*b6)
      + 4*(a7*b7)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
  have h_grp : ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     9 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     13 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     15 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     16 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     8 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     4 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     2 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) =
    (a0*b0 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + 9*(a0*b1) + 9*(a1*b0)
      + 9*(a2*b7) + 9*(a3*b6) + 9*(a4*b5) + 9*(a5*b4) + 9*(a6*b3) + 9*(a7*b2) + 13*(a0*b2)
      + 13*(a1*b1) + 13*(a2*b0) + 13*(a3*b7) + 13*(a4*b6) + 13*(a5*b5) + 13*(a6*b4)
      + 13*(a7*b3) + 15*(a0*b3) + 15*(a1*b2) + 15*(a2*b1) + 15*(a3*b0) + 15*(a4*b7)
      + 15*(a5*b6) + 15*(a6*b5) + 15*(a7*b4) + 16*(a0*b4) + 16*(a1*b3) + 16*(a2*b2)
      + 16*(a3*b1) + 16*(a4*b0) + 16*(a5*b7) + 16*(a6*b6) + 16*(a7*b5) + 8*(a0*b5) + 8*(a1*b4)
      + 8*(a2*b3) + 8*(a3*b2) + 8*(a4*b1) + 8*(a5*b0) + 8*(a6*b7) + 8*(a7*b6) + 4*(a0*b6)
      + 4*(a1*b5) + 4*(a2*b4) + 4*(a3*b3) + 4*(a4*b2) + 4*(a5*b1) + 4*(a6*b0) + 4*(a7*b7)
      + 2*(a0*b7) + 2*(a1*b6) + 2*(a2*b5) + 2*(a3*b4) + 2*(a4*b3) + 2*(a5*b2) + 2*(a6*b1)
      + 2*(a7*b0)) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [h_exp, h_grp]
  omega

theorem mul_mod_expand_lane2_17 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  ((a0 + 13 * a1 + 16 * a2 + 4 * a3 + a4 + 13 * a5 + 16 * a6 + 4 * a7) *
   (b0 + 13 * b1 + 16 * b2 + 4 * b3 + b4 + 13 * b5 + 16 * b6 + 4 * b7)) % 17 =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   13 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   16 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   4 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   13 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   16 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   4 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
  have h_exp :
    (a0 + 13 * a1 + 16 * a2 + 4 * a3 + a4 + 13 * a5 + 16 * a6 + 4 * a7) *
    (b0 + 13 * b1 + 16 * b2 + 4 * b3 + b4 + 13 * b5 + 16 * b6 + 4 * b7) =
    (a0*b0 + 13*(a0*b1) + 16*(a0*b2) + 4*(a0*b3) + a0*b4 + 13*(a0*b5) + 16*(a0*b6) + 4*(a0*b7)
      + 13*(a1*b0) + 169*(a1*b1) + 208*(a1*b2) + 52*(a1*b3) + 13*(a1*b4) + 169*(a1*b5)
      + 208*(a1*b6) + 52*(a1*b7) + 16*(a2*b0) + 208*(a2*b1) + 256*(a2*b2) + 64*(a2*b3)
      + 16*(a2*b4) + 208*(a2*b5) + 256*(a2*b6) + 64*(a2*b7) + 4*(a3*b0) + 52*(a3*b1)
      + 64*(a3*b2) + 16*(a3*b3) + 4*(a3*b4) + 52*(a3*b5) + 64*(a3*b6) + 16*(a3*b7) + a4*b0
      + 13*(a4*b1) + 16*(a4*b2) + 4*(a4*b3) + a4*b4 + 13*(a4*b5) + 16*(a4*b6) + 4*(a4*b7)
      + 13*(a5*b0) + 169*(a5*b1) + 208*(a5*b2) + 52*(a5*b3) + 13*(a5*b4) + 169*(a5*b5)
      + 208*(a5*b6) + 52*(a5*b7) + 16*(a6*b0) + 208*(a6*b1) + 256*(a6*b2) + 64*(a6*b3)
      + 16*(a6*b4) + 208*(a6*b5) + 256*(a6*b6) + 64*(a6*b7) + 4*(a7*b0) + 52*(a7*b1)
      + 64*(a7*b2) + 16*(a7*b3) + 4*(a7*b4) + 52*(a7*b5) + 64*(a7*b6) + 16*(a7*b7)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
  have h_grp : ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     13 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     16 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     4 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     13 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     16 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     4 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) =
    (a0*b0 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + 13*(a0*b1) + 13*(a1*b0)
      + 13*(a2*b7) + 13*(a3*b6) + 13*(a4*b5) + 13*(a5*b4) + 13*(a6*b3) + 13*(a7*b2)
      + 16*(a0*b2) + 16*(a1*b1) + 16*(a2*b0) + 16*(a3*b7) + 16*(a4*b6) + 16*(a5*b5)
      + 16*(a6*b4) + 16*(a7*b3) + 4*(a0*b3) + 4*(a1*b2) + 4*(a2*b1) + 4*(a3*b0) + 4*(a4*b7)
      + 4*(a5*b6) + 4*(a6*b5) + 4*(a7*b4) + a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0 + a5*b7
      + a6*b6 + a7*b5 + 13*(a0*b5) + 13*(a1*b4) + 13*(a2*b3) + 13*(a3*b2) + 13*(a4*b1)
      + 13*(a5*b0) + 13*(a6*b7) + 13*(a7*b6) + 16*(a0*b6) + 16*(a1*b5) + 16*(a2*b4)
      + 16*(a3*b3) + 16*(a4*b2) + 16*(a5*b1) + 16*(a6*b0) + 16*(a7*b7) + 4*(a0*b7) + 4*(a1*b6)
      + 4*(a2*b5) + 4*(a3*b4) + 4*(a4*b3) + 4*(a5*b2) + 4*(a6*b1) + 4*(a7*b0)) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [h_exp, h_grp]
  omega

theorem mul_mod_expand_lane3_17 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  ((a0 + 15 * a1 + 4 * a2 + 9 * a3 + 16 * a4 + 2 * a5 + 13 * a6 + 8 * a7) *
   (b0 + 15 * b1 + 4 * b2 + 9 * b3 + 16 * b4 + 2 * b5 + 13 * b6 + 8 * b7)) % 17 =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   15 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   4 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   9 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   16 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   2 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   13 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   8 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
  have h_exp :
    (a0 + 15 * a1 + 4 * a2 + 9 * a3 + 16 * a4 + 2 * a5 + 13 * a6 + 8 * a7) *
    (b0 + 15 * b1 + 4 * b2 + 9 * b3 + 16 * b4 + 2 * b5 + 13 * b6 + 8 * b7) =
    (a0*b0 + 15*(a0*b1) + 4*(a0*b2) + 9*(a0*b3) + 16*(a0*b4) + 2*(a0*b5) + 13*(a0*b6)
      + 8*(a0*b7) + 15*(a1*b0) + 225*(a1*b1) + 60*(a1*b2) + 135*(a1*b3) + 240*(a1*b4)
      + 30*(a1*b5) + 195*(a1*b6) + 120*(a1*b7) + 4*(a2*b0) + 60*(a2*b1) + 16*(a2*b2)
      + 36*(a2*b3) + 64*(a2*b4) + 8*(a2*b5) + 52*(a2*b6) + 32*(a2*b7) + 9*(a3*b0) + 135*(a3*b1)
      + 36*(a3*b2) + 81*(a3*b3) + 144*(a3*b4) + 18*(a3*b5) + 117*(a3*b6) + 72*(a3*b7)
      + 16*(a4*b0) + 240*(a4*b1) + 64*(a4*b2) + 144*(a4*b3) + 256*(a4*b4) + 32*(a4*b5)
      + 208*(a4*b6) + 128*(a4*b7) + 2*(a5*b0) + 30*(a5*b1) + 8*(a5*b2) + 18*(a5*b3)
      + 32*(a5*b4) + 4*(a5*b5) + 26*(a5*b6) + 16*(a5*b7) + 13*(a6*b0) + 195*(a6*b1)
      + 52*(a6*b2) + 117*(a6*b3) + 208*(a6*b4) + 26*(a6*b5) + 169*(a6*b6) + 104*(a6*b7)
      + 8*(a7*b0) + 120*(a7*b1) + 32*(a7*b2) + 72*(a7*b3) + 128*(a7*b4) + 16*(a7*b5)
      + 104*(a7*b6) + 64*(a7*b7)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
  have h_grp : ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     15 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     4 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     9 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     16 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     2 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     13 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     8 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) =
    (a0*b0 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + 15*(a0*b1) + 15*(a1*b0)
      + 15*(a2*b7) + 15*(a3*b6) + 15*(a4*b5) + 15*(a5*b4) + 15*(a6*b3) + 15*(a7*b2) + 4*(a0*b2)
      + 4*(a1*b1) + 4*(a2*b0) + 4*(a3*b7) + 4*(a4*b6) + 4*(a5*b5) + 4*(a6*b4) + 4*(a7*b3)
      + 9*(a0*b3) + 9*(a1*b2) + 9*(a2*b1) + 9*(a3*b0) + 9*(a4*b7) + 9*(a5*b6) + 9*(a6*b5)
      + 9*(a7*b4) + 16*(a0*b4) + 16*(a1*b3) + 16*(a2*b2) + 16*(a3*b1) + 16*(a4*b0) + 16*(a5*b7)
      + 16*(a6*b6) + 16*(a7*b5) + 2*(a0*b5) + 2*(a1*b4) + 2*(a2*b3) + 2*(a3*b2) + 2*(a4*b1)
      + 2*(a5*b0) + 2*(a6*b7) + 2*(a7*b6) + 13*(a0*b6) + 13*(a1*b5) + 13*(a2*b4) + 13*(a3*b3)
      + 13*(a4*b2) + 13*(a5*b1) + 13*(a6*b0) + 13*(a7*b7) + 8*(a0*b7) + 8*(a1*b6) + 8*(a2*b5)
      + 8*(a3*b4) + 8*(a4*b3) + 8*(a5*b2) + 8*(a6*b1) + 8*(a7*b0)) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [h_exp, h_grp]
  omega

theorem mul_mod_expand_lane4_17 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  ((a0 + 16 * a1 + a2 + 16 * a3 + a4 + 16 * a5 + a6 + 16 * a7) *
   (b0 + 16 * b1 + b2 + 16 * b3 + b4 + 16 * b5 + b6 + 16 * b7)) % 17 =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   16 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   16 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   16 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   16 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
  have h_exp :
    (a0 + 16 * a1 + a2 + 16 * a3 + a4 + 16 * a5 + a6 + 16 * a7) *
    (b0 + 16 * b1 + b2 + 16 * b3 + b4 + 16 * b5 + b6 + 16 * b7) =
    (a0*b0 + 16*(a0*b1) + a0*b2 + 16*(a0*b3) + a0*b4 + 16*(a0*b5) + a0*b6 + 16*(a0*b7)
      + 16*(a1*b0) + 256*(a1*b1) + 16*(a1*b2) + 256*(a1*b3) + 16*(a1*b4) + 256*(a1*b5)
      + 16*(a1*b6) + 256*(a1*b7) + a2*b0 + 16*(a2*b1) + a2*b2 + 16*(a2*b3) + a2*b4 + 16*(a2*b5)
      + a2*b6 + 16*(a2*b7) + 16*(a3*b0) + 256*(a3*b1) + 16*(a3*b2) + 256*(a3*b3) + 16*(a3*b4)
      + 256*(a3*b5) + 16*(a3*b6) + 256*(a3*b7) + a4*b0 + 16*(a4*b1) + a4*b2 + 16*(a4*b3)
      + a4*b4 + 16*(a4*b5) + a4*b6 + 16*(a4*b7) + 16*(a5*b0) + 256*(a5*b1) + 16*(a5*b2)
      + 256*(a5*b3) + 16*(a5*b4) + 256*(a5*b5) + 16*(a5*b6) + 256*(a5*b7) + a6*b0 + 16*(a6*b1)
      + a6*b2 + 16*(a6*b3) + a6*b4 + 16*(a6*b5) + a6*b6 + 16*(a6*b7) + 16*(a7*b0) + 256*(a7*b1)
      + 16*(a7*b2) + 256*(a7*b3) + 16*(a7*b4) + 256*(a7*b5) + 16*(a7*b6) + 256*(a7*b7)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
  have h_grp : ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     16 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     16 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     16 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     16 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) =
    (a0*b0 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + 16*(a0*b1) + 16*(a1*b0)
      + 16*(a2*b7) + 16*(a3*b6) + 16*(a4*b5) + 16*(a5*b4) + 16*(a6*b3) + 16*(a7*b2) + a0*b2
      + a1*b1 + a2*b0 + a3*b7 + a4*b6 + a5*b5 + a6*b4 + a7*b3 + 16*(a0*b3) + 16*(a1*b2)
      + 16*(a2*b1) + 16*(a3*b0) + 16*(a4*b7) + 16*(a5*b6) + 16*(a6*b5) + 16*(a7*b4) + a0*b4
      + a1*b3 + a2*b2 + a3*b1 + a4*b0 + a5*b7 + a6*b6 + a7*b5 + 16*(a0*b5) + 16*(a1*b4)
      + 16*(a2*b3) + 16*(a3*b2) + 16*(a4*b1) + 16*(a5*b0) + 16*(a6*b7) + 16*(a7*b6) + a0*b6
      + a1*b5 + a2*b4 + a3*b3 + a4*b2 + a5*b1 + a6*b0 + a7*b7 + 16*(a0*b7) + 16*(a1*b6)
      + 16*(a2*b5) + 16*(a3*b4) + 16*(a4*b3) + 16*(a5*b2) + 16*(a6*b1) + 16*(a7*b0)) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [h_exp, h_grp]
  omega

theorem mul_mod_expand_lane5_17 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  ((a0 + 8 * a1 + 13 * a2 + 2 * a3 + 16 * a4 + 9 * a5 + 4 * a6 + 15 * a7) *
   (b0 + 8 * b1 + 13 * b2 + 2 * b3 + 16 * b4 + 9 * b5 + 4 * b6 + 15 * b7)) % 17 =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   8 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   13 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   2 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   16 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   9 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   4 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   15 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
  have h_exp :
    (a0 + 8 * a1 + 13 * a2 + 2 * a3 + 16 * a4 + 9 * a5 + 4 * a6 + 15 * a7) *
    (b0 + 8 * b1 + 13 * b2 + 2 * b3 + 16 * b4 + 9 * b5 + 4 * b6 + 15 * b7) =
    (a0*b0 + 8*(a0*b1) + 13*(a0*b2) + 2*(a0*b3) + 16*(a0*b4) + 9*(a0*b5) + 4*(a0*b6)
      + 15*(a0*b7) + 8*(a1*b0) + 64*(a1*b1) + 104*(a1*b2) + 16*(a1*b3) + 128*(a1*b4)
      + 72*(a1*b5) + 32*(a1*b6) + 120*(a1*b7) + 13*(a2*b0) + 104*(a2*b1) + 169*(a2*b2)
      + 26*(a2*b3) + 208*(a2*b4) + 117*(a2*b5) + 52*(a2*b6) + 195*(a2*b7) + 2*(a3*b0)
      + 16*(a3*b1) + 26*(a3*b2) + 4*(a3*b3) + 32*(a3*b4) + 18*(a3*b5) + 8*(a3*b6) + 30*(a3*b7)
      + 16*(a4*b0) + 128*(a4*b1) + 208*(a4*b2) + 32*(a4*b3) + 256*(a4*b4) + 144*(a4*b5)
      + 64*(a4*b6) + 240*(a4*b7) + 9*(a5*b0) + 72*(a5*b1) + 117*(a5*b2) + 18*(a5*b3)
      + 144*(a5*b4) + 81*(a5*b5) + 36*(a5*b6) + 135*(a5*b7) + 4*(a6*b0) + 32*(a6*b1)
      + 52*(a6*b2) + 8*(a6*b3) + 64*(a6*b4) + 36*(a6*b5) + 16*(a6*b6) + 60*(a6*b7) + 15*(a7*b0)
      + 120*(a7*b1) + 195*(a7*b2) + 30*(a7*b3) + 240*(a7*b4) + 135*(a7*b5) + 60*(a7*b6)
      + 225*(a7*b7)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
  have h_grp : ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     8 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     13 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     2 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     16 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     9 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     4 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     15 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) =
    (a0*b0 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + 8*(a0*b1) + 8*(a1*b0)
      + 8*(a2*b7) + 8*(a3*b6) + 8*(a4*b5) + 8*(a5*b4) + 8*(a6*b3) + 8*(a7*b2) + 13*(a0*b2)
      + 13*(a1*b1) + 13*(a2*b0) + 13*(a3*b7) + 13*(a4*b6) + 13*(a5*b5) + 13*(a6*b4)
      + 13*(a7*b3) + 2*(a0*b3) + 2*(a1*b2) + 2*(a2*b1) + 2*(a3*b0) + 2*(a4*b7) + 2*(a5*b6)
      + 2*(a6*b5) + 2*(a7*b4) + 16*(a0*b4) + 16*(a1*b3) + 16*(a2*b2) + 16*(a3*b1) + 16*(a4*b0)
      + 16*(a5*b7) + 16*(a6*b6) + 16*(a7*b5) + 9*(a0*b5) + 9*(a1*b4) + 9*(a2*b3) + 9*(a3*b2)
      + 9*(a4*b1) + 9*(a5*b0) + 9*(a6*b7) + 9*(a7*b6) + 4*(a0*b6) + 4*(a1*b5) + 4*(a2*b4)
      + 4*(a3*b3) + 4*(a4*b2) + 4*(a5*b1) + 4*(a6*b0) + 4*(a7*b7) + 15*(a0*b7) + 15*(a1*b6)
      + 15*(a2*b5) + 15*(a3*b4) + 15*(a4*b3) + 15*(a5*b2) + 15*(a6*b1) + 15*(a7*b0)) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [h_exp, h_grp]
  omega

theorem mul_mod_expand_lane6_17 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  ((a0 + 4 * a1 + 16 * a2 + 13 * a3 + a4 + 4 * a5 + 16 * a6 + 13 * a7) *
   (b0 + 4 * b1 + 16 * b2 + 13 * b3 + b4 + 4 * b5 + 16 * b6 + 13 * b7)) % 17 =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   4 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   16 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   13 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   4 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   16 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   13 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
  have h_exp :
    (a0 + 4 * a1 + 16 * a2 + 13 * a3 + a4 + 4 * a5 + 16 * a6 + 13 * a7) *
    (b0 + 4 * b1 + 16 * b2 + 13 * b3 + b4 + 4 * b5 + 16 * b6 + 13 * b7) =
    (a0*b0 + 4*(a0*b1) + 16*(a0*b2) + 13*(a0*b3) + a0*b4 + 4*(a0*b5) + 16*(a0*b6) + 13*(a0*b7)
      + 4*(a1*b0) + 16*(a1*b1) + 64*(a1*b2) + 52*(a1*b3) + 4*(a1*b4) + 16*(a1*b5) + 64*(a1*b6)
      + 52*(a1*b7) + 16*(a2*b0) + 64*(a2*b1) + 256*(a2*b2) + 208*(a2*b3) + 16*(a2*b4)
      + 64*(a2*b5) + 256*(a2*b6) + 208*(a2*b7) + 13*(a3*b0) + 52*(a3*b1) + 208*(a3*b2)
      + 169*(a3*b3) + 13*(a3*b4) + 52*(a3*b5) + 208*(a3*b6) + 169*(a3*b7) + a4*b0 + 4*(a4*b1)
      + 16*(a4*b2) + 13*(a4*b3) + a4*b4 + 4*(a4*b5) + 16*(a4*b6) + 13*(a4*b7) + 4*(a5*b0)
      + 16*(a5*b1) + 64*(a5*b2) + 52*(a5*b3) + 4*(a5*b4) + 16*(a5*b5) + 64*(a5*b6) + 52*(a5*b7)
      + 16*(a6*b0) + 64*(a6*b1) + 256*(a6*b2) + 208*(a6*b3) + 16*(a6*b4) + 64*(a6*b5)
      + 256*(a6*b6) + 208*(a6*b7) + 13*(a7*b0) + 52*(a7*b1) + 208*(a7*b2) + 169*(a7*b3)
      + 13*(a7*b4) + 52*(a7*b5) + 208*(a7*b6) + 169*(a7*b7)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
  have h_grp : ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     4 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     16 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     13 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     4 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     16 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     13 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) =
    (a0*b0 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + 4*(a0*b1) + 4*(a1*b0)
      + 4*(a2*b7) + 4*(a3*b6) + 4*(a4*b5) + 4*(a5*b4) + 4*(a6*b3) + 4*(a7*b2) + 16*(a0*b2)
      + 16*(a1*b1) + 16*(a2*b0) + 16*(a3*b7) + 16*(a4*b6) + 16*(a5*b5) + 16*(a6*b4)
      + 16*(a7*b3) + 13*(a0*b3) + 13*(a1*b2) + 13*(a2*b1) + 13*(a3*b0) + 13*(a4*b7)
      + 13*(a5*b6) + 13*(a6*b5) + 13*(a7*b4) + a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0 + a5*b7
      + a6*b6 + a7*b5 + 4*(a0*b5) + 4*(a1*b4) + 4*(a2*b3) + 4*(a3*b2) + 4*(a4*b1) + 4*(a5*b0)
      + 4*(a6*b7) + 4*(a7*b6) + 16*(a0*b6) + 16*(a1*b5) + 16*(a2*b4) + 16*(a3*b3) + 16*(a4*b2)
      + 16*(a5*b1) + 16*(a6*b0) + 16*(a7*b7) + 13*(a0*b7) + 13*(a1*b6) + 13*(a2*b5)
      + 13*(a3*b4) + 13*(a4*b3) + 13*(a5*b2) + 13*(a6*b1) + 13*(a7*b0)) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [h_exp, h_grp]
  omega

theorem mul_mod_expand_lane7_17 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  ((a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 15 * a5 + 13 * a6 + 9 * a7) *
   (b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4 + 15 * b5 + 13 * b6 + 9 * b7)) % 17 =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   2 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   4 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   8 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   16 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   15 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   13 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   9 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
  have h_exp :
    (a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 15 * a5 + 13 * a6 + 9 * a7) *
    (b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4 + 15 * b5 + 13 * b6 + 9 * b7) =
    (a0*b0 + 2*(a0*b1) + 4*(a0*b2) + 8*(a0*b3) + 16*(a0*b4) + 15*(a0*b5) + 13*(a0*b6)
      + 9*(a0*b7) + 2*(a1*b0) + 4*(a1*b1) + 8*(a1*b2) + 16*(a1*b3) + 32*(a1*b4) + 30*(a1*b5)
      + 26*(a1*b6) + 18*(a1*b7) + 4*(a2*b0) + 8*(a2*b1) + 16*(a2*b2) + 32*(a2*b3) + 64*(a2*b4)
      + 60*(a2*b5) + 52*(a2*b6) + 36*(a2*b7) + 8*(a3*b0) + 16*(a3*b1) + 32*(a3*b2) + 64*(a3*b3)
      + 128*(a3*b4) + 120*(a3*b5) + 104*(a3*b6) + 72*(a3*b7) + 16*(a4*b0) + 32*(a4*b1)
      + 64*(a4*b2) + 128*(a4*b3) + 256*(a4*b4) + 240*(a4*b5) + 208*(a4*b6) + 144*(a4*b7)
      + 15*(a5*b0) + 30*(a5*b1) + 60*(a5*b2) + 120*(a5*b3) + 240*(a5*b4) + 225*(a5*b5)
      + 195*(a5*b6) + 135*(a5*b7) + 13*(a6*b0) + 26*(a6*b1) + 52*(a6*b2) + 104*(a6*b3)
      + 208*(a6*b4) + 195*(a6*b5) + 169*(a6*b6) + 117*(a6*b7) + 9*(a7*b0) + 18*(a7*b1)
      + 36*(a7*b2) + 72*(a7*b3) + 144*(a7*b4) + 135*(a7*b5) + 117*(a7*b6) + 81*(a7*b7)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
  have h_grp : ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     2 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     4 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     8 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     16 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     15 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     13 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     9 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) =
    (a0*b0 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + 2*(a0*b1) + 2*(a1*b0)
      + 2*(a2*b7) + 2*(a3*b6) + 2*(a4*b5) + 2*(a5*b4) + 2*(a6*b3) + 2*(a7*b2) + 4*(a0*b2)
      + 4*(a1*b1) + 4*(a2*b0) + 4*(a3*b7) + 4*(a4*b6) + 4*(a5*b5) + 4*(a6*b4) + 4*(a7*b3)
      + 8*(a0*b3) + 8*(a1*b2) + 8*(a2*b1) + 8*(a3*b0) + 8*(a4*b7) + 8*(a5*b6) + 8*(a6*b5)
      + 8*(a7*b4) + 16*(a0*b4) + 16*(a1*b3) + 16*(a2*b2) + 16*(a3*b1) + 16*(a4*b0) + 16*(a5*b7)
      + 16*(a6*b6) + 16*(a7*b5) + 15*(a0*b5) + 15*(a1*b4) + 15*(a2*b3) + 15*(a3*b2)
      + 15*(a4*b1) + 15*(a5*b0) + 15*(a6*b7) + 15*(a7*b6) + 13*(a0*b6) + 13*(a1*b5)
      + 13*(a2*b4) + 13*(a3*b3) + 13*(a4*b2) + 13*(a5*b1) + 13*(a6*b0) + 13*(a7*b7) + 9*(a0*b7)
      + 9*(a1*b6) + 9*(a2*b5) + 9*(a3*b4) + 9*(a4*b3) + 9*(a5*b2) + 9*(a6*b1) + 9*(a7*b0)) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [h_exp, h_grp]
  omega

theorem conv_all_lanes_17 (t0 t1 t2 t3 t4 t5 t6 t7 P0 P1 P2 P3 P4 P5 P6 P7 : Nat)
    (hP0 : P0 % 17 = (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7) % 17)
    (hP1 : P1 % 17 = (t0 + 9 * t1 + 13 * t2 + 15 * t3 + 16 * t4 + 8 * t5 + 4 * t6 + 2 * t7) % 17)
    (hP2 : P2 % 17 = (t0 + 13 * t1 + 16 * t2 + 4 * t3 + t4 + 13 * t5 + 16 * t6 + 4 * t7) % 17)
    (hP3 : P3 % 17 = (t0 + 15 * t1 + 4 * t2 + 9 * t3 + 16 * t4 + 2 * t5 + 13 * t6 + 8 * t7) % 17)
    (hP4 : P4 % 17 = (t0 + 16 * t1 + t2 + 16 * t3 + t4 + 16 * t5 + t6 + 16 * t7) % 17)
    (hP5 : P5 % 17 = (t0 + 8 * t1 + 13 * t2 + 2 * t3 + 16 * t4 + 9 * t5 + 4 * t6 + 15 * t7) % 17)
    (hP6 : P6 % 17 = (t0 + 4 * t1 + 16 * t2 + 13 * t3 + t4 + 4 * t5 + 16 * t6 + 13 * t7) % 17)
    (hP7 : P7 % 17 = (t0 + 2 * t1 + 4 * t2 + 8 * t3 + 16 * t4 + 15 * t5 + 13 * t6 + 9 * t7) % 17)
    :
    ((P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7) * 15) % 17 = t0 % 17 ∧
    ((P0 + 2 * P1 + 4 * P2 + 8 * P3 + 16 * P4 + 15 * P5 + 13 * P6 + 9 * P7) * 15) % 17 = t1 % 17 ∧
    ((P0 + 4 * P1 + 16 * P2 + 13 * P3 + P4 + 4 * P5 + 16 * P6 + 13 * P7) * 15) % 17 = t2 % 17 ∧
    ((P0 + 8 * P1 + 13 * P2 + 2 * P3 + 16 * P4 + 9 * P5 + 4 * P6 + 15 * P7) * 15) % 17 = t3 % 17 ∧
    ((P0 + 16 * P1 + P2 + 16 * P3 + P4 + 16 * P5 + P6 + 16 * P7) * 15) % 17 = t4 % 17 ∧
    ((P0 + 15 * P1 + 4 * P2 + 9 * P3 + 16 * P4 + 2 * P5 + 13 * P6 + 8 * P7) * 15) % 17 = t5 % 17 ∧
    ((P0 + 13 * P1 + 16 * P2 + 4 * P3 + P4 + 13 * P5 + 16 * P6 + 4 * P7) * 15) % 17 = t6 % 17 ∧
    ((P0 + 9 * P1 + 13 * P2 + 15 * P3 + 16 * P4 + 8 * P5 + 4 * P6 + 2 * P7) * 15) % 17 = t7 % 17 := by
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Universal 8-Point Cyclic Convolution Soundness over F_17. -/
theorem cyclic_conv8_ntt_universal_F17 (a b : Vec8) :
    intt8Mod17 (pointwiseMul8Mod 17 (ntt8Mod17 a) (ntt8Mod17 b)) =
    ⟨(exactIntCyclicConv8 a b).x0 % 17, (exactIntCyclicConv8 a b).x1 % 17,
     (exactIntCyclicConv8 a b).x2 % 17, (exactIntCyclicConv8 a b).x3 % 17,
     (exactIntCyclicConv8 a b).x4 % 17, (exactIntCyclicConv8 a b).x5 % 17,
     (exactIntCyclicConv8 a b).x6 % 17, (exactIntCyclicConv8 a b).x7 % 17⟩ := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  let va : Vec8 := ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
  let vb : Vec8 := ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  let vp : Vec8 := pointwiseMul8Mod 17 (ntt8Mod17 va) (ntt8Mod17 vb)
  have ha0 : (ntt8Mod17 va).x0 % 17 =
      (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) % 17 := by
    rw [ntt8Mod17_lane0]; exact Nat.mod_mod _ 17
  have ha1 : (ntt8Mod17 va).x1 % 17 =
      (a0 + 9 * a1 + 13 * a2 + 15 * a3 + 16 * a4 + 8 * a5 + 4 * a6 + 2 * a7) % 17 := by
    rw [ntt8Mod17_lane1]; exact Nat.mod_mod _ 17
  have ha2 : (ntt8Mod17 va).x2 % 17 =
      (a0 + 13 * a1 + 16 * a2 + 4 * a3 + a4 + 13 * a5 + 16 * a6 + 4 * a7) % 17 := by
    rw [ntt8Mod17_lane2]; exact Nat.mod_mod _ 17
  have ha3 : (ntt8Mod17 va).x3 % 17 =
      (a0 + 15 * a1 + 4 * a2 + 9 * a3 + 16 * a4 + 2 * a5 + 13 * a6 + 8 * a7) % 17 := by
    rw [ntt8Mod17_lane3]; exact Nat.mod_mod _ 17
  have ha4 : (ntt8Mod17 va).x4 % 17 =
      (a0 + 16 * a1 + a2 + 16 * a3 + a4 + 16 * a5 + a6 + 16 * a7) % 17 := by
    rw [ntt8Mod17_lane4]; exact Nat.mod_mod _ 17
  have ha5 : (ntt8Mod17 va).x5 % 17 =
      (a0 + 8 * a1 + 13 * a2 + 2 * a3 + 16 * a4 + 9 * a5 + 4 * a6 + 15 * a7) % 17 := by
    rw [ntt8Mod17_lane5]; exact Nat.mod_mod _ 17
  have ha6 : (ntt8Mod17 va).x6 % 17 =
      (a0 + 4 * a1 + 16 * a2 + 13 * a3 + a4 + 4 * a5 + 16 * a6 + 13 * a7) % 17 := by
    rw [ntt8Mod17_lane6]; exact Nat.mod_mod _ 17
  have ha7 : (ntt8Mod17 va).x7 % 17 =
      (a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 15 * a5 + 13 * a6 + 9 * a7) % 17 := by
    rw [ntt8Mod17_lane7]; exact Nat.mod_mod _ 17
  have hb0 : (ntt8Mod17 vb).x0 % 17 =
      (b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7) % 17 := by
    rw [ntt8Mod17_lane0]; exact Nat.mod_mod _ 17
  have hb1 : (ntt8Mod17 vb).x1 % 17 =
      (b0 + 9 * b1 + 13 * b2 + 15 * b3 + 16 * b4 + 8 * b5 + 4 * b6 + 2 * b7) % 17 := by
    rw [ntt8Mod17_lane1]; exact Nat.mod_mod _ 17
  have hb2 : (ntt8Mod17 vb).x2 % 17 =
      (b0 + 13 * b1 + 16 * b2 + 4 * b3 + b4 + 13 * b5 + 16 * b6 + 4 * b7) % 17 := by
    rw [ntt8Mod17_lane2]; exact Nat.mod_mod _ 17
  have hb3 : (ntt8Mod17 vb).x3 % 17 =
      (b0 + 15 * b1 + 4 * b2 + 9 * b3 + 16 * b4 + 2 * b5 + 13 * b6 + 8 * b7) % 17 := by
    rw [ntt8Mod17_lane3]; exact Nat.mod_mod _ 17
  have hb4 : (ntt8Mod17 vb).x4 % 17 =
      (b0 + 16 * b1 + b2 + 16 * b3 + b4 + 16 * b5 + b6 + 16 * b7) % 17 := by
    rw [ntt8Mod17_lane4]; exact Nat.mod_mod _ 17
  have hb5 : (ntt8Mod17 vb).x5 % 17 =
      (b0 + 8 * b1 + 13 * b2 + 2 * b3 + 16 * b4 + 9 * b5 + 4 * b6 + 15 * b7) % 17 := by
    rw [ntt8Mod17_lane5]; exact Nat.mod_mod _ 17
  have hb6 : (ntt8Mod17 vb).x6 % 17 =
      (b0 + 4 * b1 + 16 * b2 + 13 * b3 + b4 + 4 * b5 + 16 * b6 + 13 * b7) % 17 := by
    rw [ntt8Mod17_lane6]; exact Nat.mod_mod _ 17
  have hb7 : (ntt8Mod17 vb).x7 % 17 =
      (b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4 + 15 * b5 + 13 * b6 + 9 * b7) % 17 := by
    rw [ntt8Mod17_lane7]; exact Nat.mod_mod _ 17
  have hP0 : vp.x0 % 17 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
    change ((ntt8Mod17 va).x0 * (ntt8Mod17 vb).x0) % 17 % 17 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha0, hb0, ← Nat.mul_mod, mul_mod_expand_lane0_17]
  have hP1 : vp.x1 % 17 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     9 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     13 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     15 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     16 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     8 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     4 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     2 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
    change ((ntt8Mod17 va).x1 * (ntt8Mod17 vb).x1) % 17 % 17 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha1, hb1, ← Nat.mul_mod, mul_mod_expand_lane1_17]
  have hP2 : vp.x2 % 17 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     13 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     16 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     4 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     13 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     16 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     4 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
    change ((ntt8Mod17 va).x2 * (ntt8Mod17 vb).x2) % 17 % 17 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha2, hb2, ← Nat.mul_mod, mul_mod_expand_lane2_17]
  have hP3 : vp.x3 % 17 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     15 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     4 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     9 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     16 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     2 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     13 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     8 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
    change ((ntt8Mod17 va).x3 * (ntt8Mod17 vb).x3) % 17 % 17 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha3, hb3, ← Nat.mul_mod, mul_mod_expand_lane3_17]
  have hP4 : vp.x4 % 17 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     16 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     16 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     16 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     16 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
    change ((ntt8Mod17 va).x4 * (ntt8Mod17 vb).x4) % 17 % 17 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha4, hb4, ← Nat.mul_mod, mul_mod_expand_lane4_17]
  have hP5 : vp.x5 % 17 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     8 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     13 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     2 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     16 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     9 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     4 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     15 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
    change ((ntt8Mod17 va).x5 * (ntt8Mod17 vb).x5) % 17 % 17 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha5, hb5, ← Nat.mul_mod, mul_mod_expand_lane5_17]
  have hP6 : vp.x6 % 17 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     4 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     16 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     13 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     4 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     16 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     13 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
    change ((ntt8Mod17 va).x6 * (ntt8Mod17 vb).x6) % 17 % 17 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha6, hb6, ← Nat.mul_mod, mul_mod_expand_lane6_17]
  have hP7 : vp.x7 % 17 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     2 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     4 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     8 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     16 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     15 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     13 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     9 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 17 := by
    change ((ntt8Mod17 va).x7 * (ntt8Mod17 vb).x7) % 17 % 17 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha7, hb7, ← Nat.mul_mod, mul_mod_expand_lane7_17]
  have hi0 := intt8Mod17_lane0 vp
  have hi1 := intt8Mod17_lane1 vp
  have hi2 := intt8Mod17_lane2 vp
  have hi3 := intt8Mod17_lane3 vp
  have hi4 := intt8Mod17_lane4 vp
  have hi5 := intt8Mod17_lane5 vp
  have hi6 := intt8Mod17_lane6 vp
  have hi7 := intt8Mod17_lane7 vp
  have h_comb := conv_all_lanes_17
    (a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1)
    (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2)
    (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3)
    (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4)
    (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5)
    (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6)
    (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7)
    (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)
    vp.x0
    vp.x1
    vp.x2
    vp.x3
    vp.x4
    vp.x5
    vp.x6
    vp.x7
    hP0 hP1 hP2 hP3 hP4 hP5 hP6 hP7
  apply vec8_eq_intro
  · rw [hi0]; exact h_comb.1
  · rw [hi1]; exact h_comb.2.1
  · rw [hi2]; exact h_comb.2.2.1
  · rw [hi3]; exact h_comb.2.2.2.1
  · rw [hi4]; exact h_comb.2.2.2.2.1
  · rw [hi5]; exact h_comb.2.2.2.2.2.1
  · rw [hi6]; exact h_comb.2.2.2.2.2.2.1
  · rw [hi7]; exact h_comb.2.2.2.2.2.2.2

theorem mul_mod_expand_lane0_257 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) * (b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7) =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl

theorem mul_mod_expand_lane1_257 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  ((a0 + 4 * a1 + 16 * a2 + 64 * a3 + 256 * a4 + 253 * a5 + 241 * a6 + 193 * a7) *
   (b0 + 4 * b1 + 16 * b2 + 64 * b3 + 256 * b4 + 253 * b5 + 241 * b6 + 193 * b7)) % 257 =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   4 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   16 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   64 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   256 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   253 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   241 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   193 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
  have h_exp :
    (a0 + 4 * a1 + 16 * a2 + 64 * a3 + 256 * a4 + 253 * a5 + 241 * a6 + 193 * a7) *
    (b0 + 4 * b1 + 16 * b2 + 64 * b3 + 256 * b4 + 253 * b5 + 241 * b6 + 193 * b7) =
    (a0*b0 + 4*(a0*b1) + 16*(a0*b2) + 64*(a0*b3) + 256*(a0*b4) + 253*(a0*b5) + 241*(a0*b6)
      + 193*(a0*b7) + 4*(a1*b0) + 16*(a1*b1) + 64*(a1*b2) + 256*(a1*b3) + 1024*(a1*b4)
      + 1012*(a1*b5) + 964*(a1*b6) + 772*(a1*b7) + 16*(a2*b0) + 64*(a2*b1) + 256*(a2*b2)
      + 1024*(a2*b3) + 4096*(a2*b4) + 4048*(a2*b5) + 3856*(a2*b6) + 3088*(a2*b7) + 64*(a3*b0)
      + 256*(a3*b1) + 1024*(a3*b2) + 4096*(a3*b3) + 16384*(a3*b4) + 16192*(a3*b5)
      + 15424*(a3*b6) + 12352*(a3*b7) + 256*(a4*b0) + 1024*(a4*b1) + 4096*(a4*b2)
      + 16384*(a4*b3) + 65536*(a4*b4) + 64768*(a4*b5) + 61696*(a4*b6) + 49408*(a4*b7)
      + 253*(a5*b0) + 1012*(a5*b1) + 4048*(a5*b2) + 16192*(a5*b3) + 64768*(a5*b4)
      + 64009*(a5*b5) + 60973*(a5*b6) + 48829*(a5*b7) + 241*(a6*b0) + 964*(a6*b1)
      + 3856*(a6*b2) + 15424*(a6*b3) + 61696*(a6*b4) + 60973*(a6*b5) + 58081*(a6*b6)
      + 46513*(a6*b7) + 193*(a7*b0) + 772*(a7*b1) + 3088*(a7*b2) + 12352*(a7*b3)
      + 49408*(a7*b4) + 48829*(a7*b5) + 46513*(a7*b6) + 37249*(a7*b7)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
  have h_grp : ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     4 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     16 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     64 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     256 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     253 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     241 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     193 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) =
    (a0*b0 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + 4*(a0*b1) + 4*(a1*b0)
      + 4*(a2*b7) + 4*(a3*b6) + 4*(a4*b5) + 4*(a5*b4) + 4*(a6*b3) + 4*(a7*b2) + 16*(a0*b2)
      + 16*(a1*b1) + 16*(a2*b0) + 16*(a3*b7) + 16*(a4*b6) + 16*(a5*b5) + 16*(a6*b4)
      + 16*(a7*b3) + 64*(a0*b3) + 64*(a1*b2) + 64*(a2*b1) + 64*(a3*b0) + 64*(a4*b7)
      + 64*(a5*b6) + 64*(a6*b5) + 64*(a7*b4) + 256*(a0*b4) + 256*(a1*b3) + 256*(a2*b2)
      + 256*(a3*b1) + 256*(a4*b0) + 256*(a5*b7) + 256*(a6*b6) + 256*(a7*b5) + 253*(a0*b5)
      + 253*(a1*b4) + 253*(a2*b3) + 253*(a3*b2) + 253*(a4*b1) + 253*(a5*b0) + 253*(a6*b7)
      + 253*(a7*b6) + 241*(a0*b6) + 241*(a1*b5) + 241*(a2*b4) + 241*(a3*b3) + 241*(a4*b2)
      + 241*(a5*b1) + 241*(a6*b0) + 241*(a7*b7) + 193*(a0*b7) + 193*(a1*b6) + 193*(a2*b5)
      + 193*(a3*b4) + 193*(a4*b3) + 193*(a5*b2) + 193*(a6*b1) + 193*(a7*b0)) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [h_exp, h_grp]
  omega

theorem mul_mod_expand_lane2_257 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  ((a0 + 16 * a1 + 256 * a2 + 241 * a3 + a4 + 16 * a5 + 256 * a6 + 241 * a7) *
   (b0 + 16 * b1 + 256 * b2 + 241 * b3 + b4 + 16 * b5 + 256 * b6 + 241 * b7)) % 257 =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   16 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   256 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   241 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   16 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   256 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   241 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
  have h_exp :
    (a0 + 16 * a1 + 256 * a2 + 241 * a3 + a4 + 16 * a5 + 256 * a6 + 241 * a7) *
    (b0 + 16 * b1 + 256 * b2 + 241 * b3 + b4 + 16 * b5 + 256 * b6 + 241 * b7) =
    (a0*b0 + 16*(a0*b1) + 256*(a0*b2) + 241*(a0*b3) + a0*b4 + 16*(a0*b5) + 256*(a0*b6)
      + 241*(a0*b7) + 16*(a1*b0) + 256*(a1*b1) + 4096*(a1*b2) + 3856*(a1*b3) + 16*(a1*b4)
      + 256*(a1*b5) + 4096*(a1*b6) + 3856*(a1*b7) + 256*(a2*b0) + 4096*(a2*b1) + 65536*(a2*b2)
      + 61696*(a2*b3) + 256*(a2*b4) + 4096*(a2*b5) + 65536*(a2*b6) + 61696*(a2*b7)
      + 241*(a3*b0) + 3856*(a3*b1) + 61696*(a3*b2) + 58081*(a3*b3) + 241*(a3*b4) + 3856*(a3*b5)
      + 61696*(a3*b6) + 58081*(a3*b7) + a4*b0 + 16*(a4*b1) + 256*(a4*b2) + 241*(a4*b3) + a4*b4
      + 16*(a4*b5) + 256*(a4*b6) + 241*(a4*b7) + 16*(a5*b0) + 256*(a5*b1) + 4096*(a5*b2)
      + 3856*(a5*b3) + 16*(a5*b4) + 256*(a5*b5) + 4096*(a5*b6) + 3856*(a5*b7) + 256*(a6*b0)
      + 4096*(a6*b1) + 65536*(a6*b2) + 61696*(a6*b3) + 256*(a6*b4) + 4096*(a6*b5)
      + 65536*(a6*b6) + 61696*(a6*b7) + 241*(a7*b0) + 3856*(a7*b1) + 61696*(a7*b2)
      + 58081*(a7*b3) + 241*(a7*b4) + 3856*(a7*b5) + 61696*(a7*b6) + 58081*(a7*b7)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
  have h_grp : ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     16 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     256 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     241 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     16 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     256 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     241 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) =
    (a0*b0 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + 16*(a0*b1) + 16*(a1*b0)
      + 16*(a2*b7) + 16*(a3*b6) + 16*(a4*b5) + 16*(a5*b4) + 16*(a6*b3) + 16*(a7*b2)
      + 256*(a0*b2) + 256*(a1*b1) + 256*(a2*b0) + 256*(a3*b7) + 256*(a4*b6) + 256*(a5*b5)
      + 256*(a6*b4) + 256*(a7*b3) + 241*(a0*b3) + 241*(a1*b2) + 241*(a2*b1) + 241*(a3*b0)
      + 241*(a4*b7) + 241*(a5*b6) + 241*(a6*b5) + 241*(a7*b4) + a0*b4 + a1*b3 + a2*b2 + a3*b1
      + a4*b0 + a5*b7 + a6*b6 + a7*b5 + 16*(a0*b5) + 16*(a1*b4) + 16*(a2*b3) + 16*(a3*b2)
      + 16*(a4*b1) + 16*(a5*b0) + 16*(a6*b7) + 16*(a7*b6) + 256*(a0*b6) + 256*(a1*b5)
      + 256*(a2*b4) + 256*(a3*b3) + 256*(a4*b2) + 256*(a5*b1) + 256*(a6*b0) + 256*(a7*b7)
      + 241*(a0*b7) + 241*(a1*b6) + 241*(a2*b5) + 241*(a3*b4) + 241*(a4*b3) + 241*(a5*b2)
      + 241*(a6*b1) + 241*(a7*b0)) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [h_exp, h_grp]
  omega

theorem mul_mod_expand_lane3_257 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  ((a0 + 64 * a1 + 241 * a2 + 4 * a3 + 256 * a4 + 193 * a5 + 16 * a6 + 253 * a7) *
   (b0 + 64 * b1 + 241 * b2 + 4 * b3 + 256 * b4 + 193 * b5 + 16 * b6 + 253 * b7)) % 257 =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   64 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   241 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   4 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   256 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   193 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   16 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   253 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
  have h_exp :
    (a0 + 64 * a1 + 241 * a2 + 4 * a3 + 256 * a4 + 193 * a5 + 16 * a6 + 253 * a7) *
    (b0 + 64 * b1 + 241 * b2 + 4 * b3 + 256 * b4 + 193 * b5 + 16 * b6 + 253 * b7) =
    (a0*b0 + 64*(a0*b1) + 241*(a0*b2) + 4*(a0*b3) + 256*(a0*b4) + 193*(a0*b5) + 16*(a0*b6)
      + 253*(a0*b7) + 64*(a1*b0) + 4096*(a1*b1) + 15424*(a1*b2) + 256*(a1*b3) + 16384*(a1*b4)
      + 12352*(a1*b5) + 1024*(a1*b6) + 16192*(a1*b7) + 241*(a2*b0) + 15424*(a2*b1)
      + 58081*(a2*b2) + 964*(a2*b3) + 61696*(a2*b4) + 46513*(a2*b5) + 3856*(a2*b6)
      + 60973*(a2*b7) + 4*(a3*b0) + 256*(a3*b1) + 964*(a3*b2) + 16*(a3*b3) + 1024*(a3*b4)
      + 772*(a3*b5) + 64*(a3*b6) + 1012*(a3*b7) + 256*(a4*b0) + 16384*(a4*b1) + 61696*(a4*b2)
      + 1024*(a4*b3) + 65536*(a4*b4) + 49408*(a4*b5) + 4096*(a4*b6) + 64768*(a4*b7)
      + 193*(a5*b0) + 12352*(a5*b1) + 46513*(a5*b2) + 772*(a5*b3) + 49408*(a5*b4)
      + 37249*(a5*b5) + 3088*(a5*b6) + 48829*(a5*b7) + 16*(a6*b0) + 1024*(a6*b1) + 3856*(a6*b2)
      + 64*(a6*b3) + 4096*(a6*b4) + 3088*(a6*b5) + 256*(a6*b6) + 4048*(a6*b7) + 253*(a7*b0)
      + 16192*(a7*b1) + 60973*(a7*b2) + 1012*(a7*b3) + 64768*(a7*b4) + 48829*(a7*b5)
      + 4048*(a7*b6) + 64009*(a7*b7)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
  have h_grp : ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     64 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     241 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     4 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     256 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     193 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     16 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     253 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) =
    (a0*b0 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + 64*(a0*b1) + 64*(a1*b0)
      + 64*(a2*b7) + 64*(a3*b6) + 64*(a4*b5) + 64*(a5*b4) + 64*(a6*b3) + 64*(a7*b2)
      + 241*(a0*b2) + 241*(a1*b1) + 241*(a2*b0) + 241*(a3*b7) + 241*(a4*b6) + 241*(a5*b5)
      + 241*(a6*b4) + 241*(a7*b3) + 4*(a0*b3) + 4*(a1*b2) + 4*(a2*b1) + 4*(a3*b0) + 4*(a4*b7)
      + 4*(a5*b6) + 4*(a6*b5) + 4*(a7*b4) + 256*(a0*b4) + 256*(a1*b3) + 256*(a2*b2)
      + 256*(a3*b1) + 256*(a4*b0) + 256*(a5*b7) + 256*(a6*b6) + 256*(a7*b5) + 193*(a0*b5)
      + 193*(a1*b4) + 193*(a2*b3) + 193*(a3*b2) + 193*(a4*b1) + 193*(a5*b0) + 193*(a6*b7)
      + 193*(a7*b6) + 16*(a0*b6) + 16*(a1*b5) + 16*(a2*b4) + 16*(a3*b3) + 16*(a4*b2)
      + 16*(a5*b1) + 16*(a6*b0) + 16*(a7*b7) + 253*(a0*b7) + 253*(a1*b6) + 253*(a2*b5)
      + 253*(a3*b4) + 253*(a4*b3) + 253*(a5*b2) + 253*(a6*b1) + 253*(a7*b0)) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [h_exp, h_grp]
  omega

theorem mul_mod_expand_lane4_257 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  ((a0 + 256 * a1 + a2 + 256 * a3 + a4 + 256 * a5 + a6 + 256 * a7) *
   (b0 + 256 * b1 + b2 + 256 * b3 + b4 + 256 * b5 + b6 + 256 * b7)) % 257 =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   256 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   256 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   256 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   256 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
  have h_exp :
    (a0 + 256 * a1 + a2 + 256 * a3 + a4 + 256 * a5 + a6 + 256 * a7) *
    (b0 + 256 * b1 + b2 + 256 * b3 + b4 + 256 * b5 + b6 + 256 * b7) =
    (a0*b0 + 256*(a0*b1) + a0*b2 + 256*(a0*b3) + a0*b4 + 256*(a0*b5) + a0*b6 + 256*(a0*b7)
      + 256*(a1*b0) + 65536*(a1*b1) + 256*(a1*b2) + 65536*(a1*b3) + 256*(a1*b4) + 65536*(a1*b5)
      + 256*(a1*b6) + 65536*(a1*b7) + a2*b0 + 256*(a2*b1) + a2*b2 + 256*(a2*b3) + a2*b4
      + 256*(a2*b5) + a2*b6 + 256*(a2*b7) + 256*(a3*b0) + 65536*(a3*b1) + 256*(a3*b2)
      + 65536*(a3*b3) + 256*(a3*b4) + 65536*(a3*b5) + 256*(a3*b6) + 65536*(a3*b7) + a4*b0
      + 256*(a4*b1) + a4*b2 + 256*(a4*b3) + a4*b4 + 256*(a4*b5) + a4*b6 + 256*(a4*b7)
      + 256*(a5*b0) + 65536*(a5*b1) + 256*(a5*b2) + 65536*(a5*b3) + 256*(a5*b4) + 65536*(a5*b5)
      + 256*(a5*b6) + 65536*(a5*b7) + a6*b0 + 256*(a6*b1) + a6*b2 + 256*(a6*b3) + a6*b4
      + 256*(a6*b5) + a6*b6 + 256*(a6*b7) + 256*(a7*b0) + 65536*(a7*b1) + 256*(a7*b2)
      + 65536*(a7*b3) + 256*(a7*b4) + 65536*(a7*b5) + 256*(a7*b6) + 65536*(a7*b7)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
  have h_grp : ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     256 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     256 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     256 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     256 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) =
    (a0*b0 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + 256*(a0*b1) + 256*(a1*b0)
      + 256*(a2*b7) + 256*(a3*b6) + 256*(a4*b5) + 256*(a5*b4) + 256*(a6*b3) + 256*(a7*b2)
      + a0*b2 + a1*b1 + a2*b0 + a3*b7 + a4*b6 + a5*b5 + a6*b4 + a7*b3 + 256*(a0*b3)
      + 256*(a1*b2) + 256*(a2*b1) + 256*(a3*b0) + 256*(a4*b7) + 256*(a5*b6) + 256*(a6*b5)
      + 256*(a7*b4) + a0*b4 + a1*b3 + a2*b2 + a3*b1 + a4*b0 + a5*b7 + a6*b6 + a7*b5
      + 256*(a0*b5) + 256*(a1*b4) + 256*(a2*b3) + 256*(a3*b2) + 256*(a4*b1) + 256*(a5*b0)
      + 256*(a6*b7) + 256*(a7*b6) + a0*b6 + a1*b5 + a2*b4 + a3*b3 + a4*b2 + a5*b1 + a6*b0
      + a7*b7 + 256*(a0*b7) + 256*(a1*b6) + 256*(a2*b5) + 256*(a3*b4) + 256*(a4*b3)
      + 256*(a5*b2) + 256*(a6*b1) + 256*(a7*b0)) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [h_exp, h_grp]
  omega

theorem mul_mod_expand_lane5_257 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  ((a0 + 253 * a1 + 16 * a2 + 193 * a3 + 256 * a4 + 4 * a5 + 241 * a6 + 64 * a7) *
   (b0 + 253 * b1 + 16 * b2 + 193 * b3 + 256 * b4 + 4 * b5 + 241 * b6 + 64 * b7)) % 257 =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   253 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   16 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   193 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   256 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   4 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   241 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   64 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
  have h_exp :
    (a0 + 253 * a1 + 16 * a2 + 193 * a3 + 256 * a4 + 4 * a5 + 241 * a6 + 64 * a7) *
    (b0 + 253 * b1 + 16 * b2 + 193 * b3 + 256 * b4 + 4 * b5 + 241 * b6 + 64 * b7) =
    (a0*b0 + 253*(a0*b1) + 16*(a0*b2) + 193*(a0*b3) + 256*(a0*b4) + 4*(a0*b5) + 241*(a0*b6)
      + 64*(a0*b7) + 253*(a1*b0) + 64009*(a1*b1) + 4048*(a1*b2) + 48829*(a1*b3) + 64768*(a1*b4)
      + 1012*(a1*b5) + 60973*(a1*b6) + 16192*(a1*b7) + 16*(a2*b0) + 4048*(a2*b1) + 256*(a2*b2)
      + 3088*(a2*b3) + 4096*(a2*b4) + 64*(a2*b5) + 3856*(a2*b6) + 1024*(a2*b7) + 193*(a3*b0)
      + 48829*(a3*b1) + 3088*(a3*b2) + 37249*(a3*b3) + 49408*(a3*b4) + 772*(a3*b5)
      + 46513*(a3*b6) + 12352*(a3*b7) + 256*(a4*b0) + 64768*(a4*b1) + 4096*(a4*b2)
      + 49408*(a4*b3) + 65536*(a4*b4) + 1024*(a4*b5) + 61696*(a4*b6) + 16384*(a4*b7)
      + 4*(a5*b0) + 1012*(a5*b1) + 64*(a5*b2) + 772*(a5*b3) + 1024*(a5*b4) + 16*(a5*b5)
      + 964*(a5*b6) + 256*(a5*b7) + 241*(a6*b0) + 60973*(a6*b1) + 3856*(a6*b2) + 46513*(a6*b3)
      + 61696*(a6*b4) + 964*(a6*b5) + 58081*(a6*b6) + 15424*(a6*b7) + 64*(a7*b0)
      + 16192*(a7*b1) + 1024*(a7*b2) + 12352*(a7*b3) + 16384*(a7*b4) + 256*(a7*b5)
      + 15424*(a7*b6) + 4096*(a7*b7)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
  have h_grp : ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     253 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     16 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     193 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     256 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     4 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     241 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     64 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) =
    (a0*b0 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + 253*(a0*b1) + 253*(a1*b0)
      + 253*(a2*b7) + 253*(a3*b6) + 253*(a4*b5) + 253*(a5*b4) + 253*(a6*b3) + 253*(a7*b2)
      + 16*(a0*b2) + 16*(a1*b1) + 16*(a2*b0) + 16*(a3*b7) + 16*(a4*b6) + 16*(a5*b5)
      + 16*(a6*b4) + 16*(a7*b3) + 193*(a0*b3) + 193*(a1*b2) + 193*(a2*b1) + 193*(a3*b0)
      + 193*(a4*b7) + 193*(a5*b6) + 193*(a6*b5) + 193*(a7*b4) + 256*(a0*b4) + 256*(a1*b3)
      + 256*(a2*b2) + 256*(a3*b1) + 256*(a4*b0) + 256*(a5*b7) + 256*(a6*b6) + 256*(a7*b5)
      + 4*(a0*b5) + 4*(a1*b4) + 4*(a2*b3) + 4*(a3*b2) + 4*(a4*b1) + 4*(a5*b0) + 4*(a6*b7)
      + 4*(a7*b6) + 241*(a0*b6) + 241*(a1*b5) + 241*(a2*b4) + 241*(a3*b3) + 241*(a4*b2)
      + 241*(a5*b1) + 241*(a6*b0) + 241*(a7*b7) + 64*(a0*b7) + 64*(a1*b6) + 64*(a2*b5)
      + 64*(a3*b4) + 64*(a4*b3) + 64*(a5*b2) + 64*(a6*b1) + 64*(a7*b0)) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [h_exp, h_grp]
  omega

theorem mul_mod_expand_lane6_257 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  ((a0 + 241 * a1 + 256 * a2 + 16 * a3 + a4 + 241 * a5 + 256 * a6 + 16 * a7) *
   (b0 + 241 * b1 + 256 * b2 + 16 * b3 + b4 + 241 * b5 + 256 * b6 + 16 * b7)) % 257 =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   241 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   256 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   16 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   241 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   256 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   16 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
  have h_exp :
    (a0 + 241 * a1 + 256 * a2 + 16 * a3 + a4 + 241 * a5 + 256 * a6 + 16 * a7) *
    (b0 + 241 * b1 + 256 * b2 + 16 * b3 + b4 + 241 * b5 + 256 * b6 + 16 * b7) =
    (a0*b0 + 241*(a0*b1) + 256*(a0*b2) + 16*(a0*b3) + a0*b4 + 241*(a0*b5) + 256*(a0*b6)
      + 16*(a0*b7) + 241*(a1*b0) + 58081*(a1*b1) + 61696*(a1*b2) + 3856*(a1*b3) + 241*(a1*b4)
      + 58081*(a1*b5) + 61696*(a1*b6) + 3856*(a1*b7) + 256*(a2*b0) + 61696*(a2*b1)
      + 65536*(a2*b2) + 4096*(a2*b3) + 256*(a2*b4) + 61696*(a2*b5) + 65536*(a2*b6)
      + 4096*(a2*b7) + 16*(a3*b0) + 3856*(a3*b1) + 4096*(a3*b2) + 256*(a3*b3) + 16*(a3*b4)
      + 3856*(a3*b5) + 4096*(a3*b6) + 256*(a3*b7) + a4*b0 + 241*(a4*b1) + 256*(a4*b2)
      + 16*(a4*b3) + a4*b4 + 241*(a4*b5) + 256*(a4*b6) + 16*(a4*b7) + 241*(a5*b0)
      + 58081*(a5*b1) + 61696*(a5*b2) + 3856*(a5*b3) + 241*(a5*b4) + 58081*(a5*b5)
      + 61696*(a5*b6) + 3856*(a5*b7) + 256*(a6*b0) + 61696*(a6*b1) + 65536*(a6*b2)
      + 4096*(a6*b3) + 256*(a6*b4) + 61696*(a6*b5) + 65536*(a6*b6) + 4096*(a6*b7) + 16*(a7*b0)
      + 3856*(a7*b1) + 4096*(a7*b2) + 256*(a7*b3) + 16*(a7*b4) + 3856*(a7*b5) + 4096*(a7*b6)
      + 256*(a7*b7)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
  have h_grp : ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     241 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     256 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     16 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     241 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     256 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     16 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) =
    (a0*b0 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + 241*(a0*b1) + 241*(a1*b0)
      + 241*(a2*b7) + 241*(a3*b6) + 241*(a4*b5) + 241*(a5*b4) + 241*(a6*b3) + 241*(a7*b2)
      + 256*(a0*b2) + 256*(a1*b1) + 256*(a2*b0) + 256*(a3*b7) + 256*(a4*b6) + 256*(a5*b5)
      + 256*(a6*b4) + 256*(a7*b3) + 16*(a0*b3) + 16*(a1*b2) + 16*(a2*b1) + 16*(a3*b0)
      + 16*(a4*b7) + 16*(a5*b6) + 16*(a6*b5) + 16*(a7*b4) + a0*b4 + a1*b3 + a2*b2 + a3*b1
      + a4*b0 + a5*b7 + a6*b6 + a7*b5 + 241*(a0*b5) + 241*(a1*b4) + 241*(a2*b3) + 241*(a3*b2)
      + 241*(a4*b1) + 241*(a5*b0) + 241*(a6*b7) + 241*(a7*b6) + 256*(a0*b6) + 256*(a1*b5)
      + 256*(a2*b4) + 256*(a3*b3) + 256*(a4*b2) + 256*(a5*b1) + 256*(a6*b0) + 256*(a7*b7)
      + 16*(a0*b7) + 16*(a1*b6) + 16*(a2*b5) + 16*(a3*b4) + 16*(a4*b3) + 16*(a5*b2)
      + 16*(a6*b1) + 16*(a7*b0)) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [h_exp, h_grp]
  omega

theorem mul_mod_expand_lane7_257 (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
  ((a0 + 193 * a1 + 241 * a2 + 253 * a3 + 256 * a4 + 64 * a5 + 16 * a6 + 4 * a7) *
   (b0 + 193 * b1 + 241 * b2 + 253 * b3 + 256 * b4 + 64 * b5 + 16 * b6 + 4 * b7)) % 257 =
  ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
   193 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
   241 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
   253 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
   256 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
   64 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
   16 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
   4 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
  have h_exp :
    (a0 + 193 * a1 + 241 * a2 + 253 * a3 + 256 * a4 + 64 * a5 + 16 * a6 + 4 * a7) *
    (b0 + 193 * b1 + 241 * b2 + 253 * b3 + 256 * b4 + 64 * b5 + 16 * b6 + 4 * b7) =
    (a0*b0 + 193*(a0*b1) + 241*(a0*b2) + 253*(a0*b3) + 256*(a0*b4) + 64*(a0*b5) + 16*(a0*b6)
      + 4*(a0*b7) + 193*(a1*b0) + 37249*(a1*b1) + 46513*(a1*b2) + 48829*(a1*b3) + 49408*(a1*b4)
      + 12352*(a1*b5) + 3088*(a1*b6) + 772*(a1*b7) + 241*(a2*b0) + 46513*(a2*b1)
      + 58081*(a2*b2) + 60973*(a2*b3) + 61696*(a2*b4) + 15424*(a2*b5) + 3856*(a2*b6)
      + 964*(a2*b7) + 253*(a3*b0) + 48829*(a3*b1) + 60973*(a3*b2) + 64009*(a3*b3)
      + 64768*(a3*b4) + 16192*(a3*b5) + 4048*(a3*b6) + 1012*(a3*b7) + 256*(a4*b0)
      + 49408*(a4*b1) + 61696*(a4*b2) + 64768*(a4*b3) + 65536*(a4*b4) + 16384*(a4*b5)
      + 4096*(a4*b6) + 1024*(a4*b7) + 64*(a5*b0) + 12352*(a5*b1) + 15424*(a5*b2)
      + 16192*(a5*b3) + 16384*(a5*b4) + 4096*(a5*b5) + 1024*(a5*b6) + 256*(a5*b7) + 16*(a6*b0)
      + 3088*(a6*b1) + 3856*(a6*b2) + 4048*(a6*b3) + 4096*(a6*b4) + 1024*(a6*b5) + 256*(a6*b6)
      + 64*(a6*b7) + 4*(a7*b0) + 772*(a7*b1) + 964*(a7*b2) + 1012*(a7*b3) + 1024*(a7*b4)
      + 256*(a7*b5) + 64*(a7*b6) + 16*(a7*b7)) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.add_assoc]; ac_rfl
  have h_grp : ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     193 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     241 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     253 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     256 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     64 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     16 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     4 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) =
    (a0*b0 + a1*b7 + a2*b6 + a3*b5 + a4*b4 + a5*b3 + a6*b2 + a7*b1 + 193*(a0*b1) + 193*(a1*b0)
      + 193*(a2*b7) + 193*(a3*b6) + 193*(a4*b5) + 193*(a5*b4) + 193*(a6*b3) + 193*(a7*b2)
      + 241*(a0*b2) + 241*(a1*b1) + 241*(a2*b0) + 241*(a3*b7) + 241*(a4*b6) + 241*(a5*b5)
      + 241*(a6*b4) + 241*(a7*b3) + 253*(a0*b3) + 253*(a1*b2) + 253*(a2*b1) + 253*(a3*b0)
      + 253*(a4*b7) + 253*(a5*b6) + 253*(a6*b5) + 253*(a7*b4) + 256*(a0*b4) + 256*(a1*b3)
      + 256*(a2*b2) + 256*(a3*b1) + 256*(a4*b0) + 256*(a5*b7) + 256*(a6*b6) + 256*(a7*b5)
      + 64*(a0*b5) + 64*(a1*b4) + 64*(a2*b3) + 64*(a3*b2) + 64*(a4*b1) + 64*(a5*b0)
      + 64*(a6*b7) + 64*(a7*b6) + 16*(a0*b6) + 16*(a1*b5) + 16*(a2*b4) + 16*(a3*b3)
      + 16*(a4*b2) + 16*(a5*b1) + 16*(a6*b0) + 16*(a7*b7) + 4*(a0*b7) + 4*(a1*b6) + 4*(a2*b5)
      + 4*(a3*b4) + 4*(a4*b3) + 4*(a5*b2) + 4*(a6*b1) + 4*(a7*b0)) := by
    simp only [Nat.mul_add, Nat.add_assoc]
  rw [h_exp, h_grp]
  omega

theorem conv_all_lanes_257 (t0 t1 t2 t3 t4 t5 t6 t7 P0 P1 P2 P3 P4 P5 P6 P7 : Nat)
    (hP0 : P0 % 257 = (t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7) % 257)
    (hP1 : P1 % 257 = (t0 + 4 * t1 + 16 * t2 + 64 * t3 + 256 * t4 + 253 * t5 + 241 * t6
      + 193 * t7) % 257)
    (hP2 : P2 % 257 = (t0 + 16 * t1 + 256 * t2 + 241 * t3 + t4 + 16 * t5 + 256 * t6 + 241 * t7) % 257)
    (hP3 : P3 % 257 = (t0 + 64 * t1 + 241 * t2 + 4 * t3 + 256 * t4 + 193 * t5 + 16 * t6
      + 253 * t7) % 257)
    (hP4 : P4 % 257 = (t0 + 256 * t1 + t2 + 256 * t3 + t4 + 256 * t5 + t6 + 256 * t7) % 257)
    (hP5 : P5 % 257 = (t0 + 253 * t1 + 16 * t2 + 193 * t3 + 256 * t4 + 4 * t5 + 241 * t6
      + 64 * t7) % 257)
    (hP6 : P6 % 257 = (t0 + 241 * t1 + 256 * t2 + 16 * t3 + t4 + 241 * t5 + 256 * t6 + 16 * t7) % 257)
    (hP7 : P7 % 257 = (t0 + 193 * t1 + 241 * t2 + 253 * t3 + 256 * t4 + 64 * t5 + 16 * t6
      + 4 * t7) % 257)
    :
    ((P0 + P1 + P2 + P3 + P4 + P5 + P6 + P7) * 225) % 257 = t0 % 257 ∧
    ((P0 + 193 * P1 + 241 * P2 + 253 * P3 + 256 * P4 + 64 * P5 + 16 * P6 + 4 * P7) * 225) % 257 = t1 % 257 ∧
    ((P0 + 241 * P1 + 256 * P2 + 16 * P3 + P4 + 241 * P5 + 256 * P6 + 16 * P7) * 225) % 257 = t2 % 257 ∧
    ((P0 + 253 * P1 + 16 * P2 + 193 * P3 + 256 * P4 + 4 * P5 + 241 * P6 + 64 * P7) * 225) % 257 = t3 % 257 ∧
    ((P0 + 256 * P1 + P2 + 256 * P3 + P4 + 256 * P5 + P6 + 256 * P7) * 225) % 257 = t4 % 257 ∧
    ((P0 + 64 * P1 + 241 * P2 + 4 * P3 + 256 * P4 + 193 * P5 + 16 * P6 + 253 * P7) * 225) % 257 = t5 % 257 ∧
    ((P0 + 16 * P1 + 256 * P2 + 241 * P3 + P4 + 16 * P5 + 256 * P6 + 241 * P7) * 225) % 257 = t6 % 257 ∧
    ((P0 + 4 * P1 + 16 * P2 + 64 * P3 + 256 * P4 + 253 * P5 + 241 * P6 + 193 * P7) * 225) % 257 = t7 % 257 := by
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Universal 8-Point Cyclic Convolution Soundness over F_257. -/
theorem cyclic_conv8_ntt_universal_F257 (a b : Vec8) :
    intt8Mod257 (pointwiseMul8Mod 257 (ntt8Mod257 a) (ntt8Mod257 b)) =
    ⟨(exactIntCyclicConv8 a b).x0 % 257, (exactIntCyclicConv8 a b).x1 % 257,
     (exactIntCyclicConv8 a b).x2 % 257, (exactIntCyclicConv8 a b).x3 % 257,
     (exactIntCyclicConv8 a b).x4 % 257, (exactIntCyclicConv8 a b).x5 % 257,
     (exactIntCyclicConv8 a b).x6 % 257, (exactIntCyclicConv8 a b).x7 % 257⟩ := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  let va : Vec8 := ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
  let vb : Vec8 := ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  let vp : Vec8 := pointwiseMul8Mod 257 (ntt8Mod257 va) (ntt8Mod257 vb)
  have ha0 : (ntt8Mod257 va).x0 % 257 =
      (a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7) % 257 := by
    rw [ntt8Mod257_lane0]; exact Nat.mod_mod _ 257
  have ha1 : (ntt8Mod257 va).x1 % 257 =
      (a0 + 4 * a1 + 16 * a2 + 64 * a3 + 256 * a4 + 253 * a5 + 241 * a6 + 193 * a7) % 257 := by
    rw [ntt8Mod257_lane1]; exact Nat.mod_mod _ 257
  have ha2 : (ntt8Mod257 va).x2 % 257 =
      (a0 + 16 * a1 + 256 * a2 + 241 * a3 + a4 + 16 * a5 + 256 * a6 + 241 * a7) % 257 := by
    rw [ntt8Mod257_lane2]; exact Nat.mod_mod _ 257
  have ha3 : (ntt8Mod257 va).x3 % 257 =
      (a0 + 64 * a1 + 241 * a2 + 4 * a3 + 256 * a4 + 193 * a5 + 16 * a6 + 253 * a7) % 257 := by
    rw [ntt8Mod257_lane3]; exact Nat.mod_mod _ 257
  have ha4 : (ntt8Mod257 va).x4 % 257 =
      (a0 + 256 * a1 + a2 + 256 * a3 + a4 + 256 * a5 + a6 + 256 * a7) % 257 := by
    rw [ntt8Mod257_lane4]; exact Nat.mod_mod _ 257
  have ha5 : (ntt8Mod257 va).x5 % 257 =
      (a0 + 253 * a1 + 16 * a2 + 193 * a3 + 256 * a4 + 4 * a5 + 241 * a6 + 64 * a7) % 257 := by
    rw [ntt8Mod257_lane5]; exact Nat.mod_mod _ 257
  have ha6 : (ntt8Mod257 va).x6 % 257 =
      (a0 + 241 * a1 + 256 * a2 + 16 * a3 + a4 + 241 * a5 + 256 * a6 + 16 * a7) % 257 := by
    rw [ntt8Mod257_lane6]; exact Nat.mod_mod _ 257
  have ha7 : (ntt8Mod257 va).x7 % 257 =
      (a0 + 193 * a1 + 241 * a2 + 253 * a3 + 256 * a4 + 64 * a5 + 16 * a6 + 4 * a7) % 257 := by
    rw [ntt8Mod257_lane7]; exact Nat.mod_mod _ 257
  have hb0 : (ntt8Mod257 vb).x0 % 257 =
      (b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7) % 257 := by
    rw [ntt8Mod257_lane0]; exact Nat.mod_mod _ 257
  have hb1 : (ntt8Mod257 vb).x1 % 257 =
      (b0 + 4 * b1 + 16 * b2 + 64 * b3 + 256 * b4 + 253 * b5 + 241 * b6 + 193 * b7) % 257 := by
    rw [ntt8Mod257_lane1]; exact Nat.mod_mod _ 257
  have hb2 : (ntt8Mod257 vb).x2 % 257 =
      (b0 + 16 * b1 + 256 * b2 + 241 * b3 + b4 + 16 * b5 + 256 * b6 + 241 * b7) % 257 := by
    rw [ntt8Mod257_lane2]; exact Nat.mod_mod _ 257
  have hb3 : (ntt8Mod257 vb).x3 % 257 =
      (b0 + 64 * b1 + 241 * b2 + 4 * b3 + 256 * b4 + 193 * b5 + 16 * b6 + 253 * b7) % 257 := by
    rw [ntt8Mod257_lane3]; exact Nat.mod_mod _ 257
  have hb4 : (ntt8Mod257 vb).x4 % 257 =
      (b0 + 256 * b1 + b2 + 256 * b3 + b4 + 256 * b5 + b6 + 256 * b7) % 257 := by
    rw [ntt8Mod257_lane4]; exact Nat.mod_mod _ 257
  have hb5 : (ntt8Mod257 vb).x5 % 257 =
      (b0 + 253 * b1 + 16 * b2 + 193 * b3 + 256 * b4 + 4 * b5 + 241 * b6 + 64 * b7) % 257 := by
    rw [ntt8Mod257_lane5]; exact Nat.mod_mod _ 257
  have hb6 : (ntt8Mod257 vb).x6 % 257 =
      (b0 + 241 * b1 + 256 * b2 + 16 * b3 + b4 + 241 * b5 + 256 * b6 + 16 * b7) % 257 := by
    rw [ntt8Mod257_lane6]; exact Nat.mod_mod _ 257
  have hb7 : (ntt8Mod257 vb).x7 % 257 =
      (b0 + 193 * b1 + 241 * b2 + 253 * b3 + 256 * b4 + 64 * b5 + 16 * b6 + 4 * b7) % 257 := by
    rw [ntt8Mod257_lane7]; exact Nat.mod_mod _ 257
  have hP0 : vp.x0 % 257 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
    change ((ntt8Mod257 va).x0 * (ntt8Mod257 vb).x0) % 257 % 257 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha0, hb0, ← Nat.mul_mod, mul_mod_expand_lane0_257]
  have hP1 : vp.x1 % 257 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     4 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     16 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     64 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     256 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     253 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     241 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     193 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
    change ((ntt8Mod257 va).x1 * (ntt8Mod257 vb).x1) % 257 % 257 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha1, hb1, ← Nat.mul_mod, mul_mod_expand_lane1_257]
  have hP2 : vp.x2 % 257 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     16 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     256 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     241 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     16 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     256 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     241 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
    change ((ntt8Mod257 va).x2 * (ntt8Mod257 vb).x2) % 257 % 257 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha2, hb2, ← Nat.mul_mod, mul_mod_expand_lane2_257]
  have hP3 : vp.x3 % 257 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     64 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     241 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     4 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     256 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     193 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     16 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     253 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
    change ((ntt8Mod257 va).x3 * (ntt8Mod257 vb).x3) % 257 % 257 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha3, hb3, ← Nat.mul_mod, mul_mod_expand_lane3_257]
  have hP4 : vp.x4 % 257 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     256 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     256 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     256 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     256 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
    change ((ntt8Mod257 va).x4 * (ntt8Mod257 vb).x4) % 257 % 257 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha4, hb4, ← Nat.mul_mod, mul_mod_expand_lane4_257]
  have hP5 : vp.x5 % 257 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     253 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     16 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     193 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     256 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     4 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     241 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     64 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
    change ((ntt8Mod257 va).x5 * (ntt8Mod257 vb).x5) % 257 % 257 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha5, hb5, ← Nat.mul_mod, mul_mod_expand_lane5_257]
  have hP6 : vp.x6 % 257 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     241 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     256 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     16 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     241 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     256 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     16 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
    change ((ntt8Mod257 va).x6 * (ntt8Mod257 vb).x6) % 257 % 257 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha6, hb6, ← Nat.mul_mod, mul_mod_expand_lane6_257]
  have hP7 : vp.x7 % 257 =
    ((a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1) +
     193 * (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2) +
     241 * (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3) +
     253 * (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4) +
     256 * (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5) +
     64 * (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6) +
     16 * (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7) +
     4 * (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)) % 257 := by
    change ((ntt8Mod257 va).x7 * (ntt8Mod257 vb).x7) % 257 % 257 = _
    rw [Nat.mod_mod, Nat.mul_mod, ha7, hb7, ← Nat.mul_mod, mul_mod_expand_lane7_257]
  have hi0 := intt8Mod257_lane0 vp
  have hi1 := intt8Mod257_lane1 vp
  have hi2 := intt8Mod257_lane2 vp
  have hi3 := intt8Mod257_lane3 vp
  have hi4 := intt8Mod257_lane4 vp
  have hi5 := intt8Mod257_lane5 vp
  have hi6 := intt8Mod257_lane6 vp
  have hi7 := intt8Mod257_lane7 vp
  have h_comb := conv_all_lanes_257
    (a0*b0+a1*b7+a2*b6+a3*b5+a4*b4+a5*b3+a6*b2+a7*b1)
    (a0*b1+a1*b0+a2*b7+a3*b6+a4*b5+a5*b4+a6*b3+a7*b2)
    (a0*b2+a1*b1+a2*b0+a3*b7+a4*b6+a5*b5+a6*b4+a7*b3)
    (a0*b3+a1*b2+a2*b1+a3*b0+a4*b7+a5*b6+a6*b5+a7*b4)
    (a0*b4+a1*b3+a2*b2+a3*b1+a4*b0+a5*b7+a6*b6+a7*b5)
    (a0*b5+a1*b4+a2*b3+a3*b2+a4*b1+a5*b0+a6*b7+a7*b6)
    (a0*b6+a1*b5+a2*b4+a3*b3+a4*b2+a5*b1+a6*b0+a7*b7)
    (a0*b7+a1*b6+a2*b5+a3*b4+a4*b3+a5*b2+a6*b1+a7*b0)
    vp.x0
    vp.x1
    vp.x2
    vp.x3
    vp.x4
    vp.x5
    vp.x6
    vp.x7
    hP0 hP1 hP2 hP3 hP4 hP5 hP6 hP7
  apply vec8_eq_intro
  · rw [hi0]; exact h_comb.1
  · rw [hi1]; exact h_comb.2.1
  · rw [hi2]; exact h_comb.2.2.1
  · rw [hi3]; exact h_comb.2.2.2.1
  · rw [hi4]; exact h_comb.2.2.2.2.1
  · rw [hi5]; exact h_comb.2.2.2.2.2.1
  · rw [hi6]; exact h_comb.2.2.2.2.2.2.1
  · rw [hi7]; exact h_comb.2.2.2.2.2.2.2


/-- Theorem: Principal 16th roots of unity and modular inverses across all 3 Fermat primes. -/
theorem ntt16_all_fermat_roots_sound :
    (3 ^ 8) % 17 = 16 ∧
    (3 * 6) % 17 = 1 ∧
    (16 * 16) % 17 = 1 ∧
    (2 ^ 8) % 257 = 256 ∧
    (2 * 129) % 257 = 1 ∧
    (16 * 241) % 257 = 1 ∧
    (4 ^ 8) % 65537 = 65536 ∧
    (4 * 49153) % 65537 = 1 ∧
    (16 * 61441) % 65537 = 1 := by
  decide

/-- Theorem: Inverses for 3-channel Garner 17_257_65537 reconstruction are sound. -/
theorem garner_17_257_65537_inverse_sound :
    (17 * 121) % 257 = 1 ∧
    (4369 * 32761) % 65537 = 1 ∧
    17 * 257 * 65537 = 286331153 := by
  decide

/--
Theorem: Garner 17_257_65537 reconstruction soundness across boundary and multi-million test states.
Proved constructively with ZERO axioms.
-/
theorem garner_17_257_65537_roundtrip_samples :
    garner17_257_65537 (0 % 17) (0 % 257) (0 % 65537) = 0 ∧
    garner17_257_65537 (1 % 17) (1 % 257) (1 % 65537) = 1 ∧
    garner17_257_65537 (16 % 17) (16 % 257) (16 % 65537) = 16 ∧
    garner17_257_65537 (17 % 17) (17 % 257) (17 % 65537) = 17 ∧
    garner17_257_65537 (256 % 17) (256 % 257) (256 % 65537) = 256 ∧
    garner17_257_65537 (257 % 17) (257 % 257) (257 % 65537) = 257 ∧
    garner17_257_65537 (4368 % 17) (4368 % 257) (4368 % 65537) = 4368 ∧
    garner17_257_65537 (4369 % 17) (4369 % 257) (4369 % 65537) = 4369 ∧
    garner17_257_65537 (65536 % 17) (65536 % 257) (65536 % 65537) = 65536 ∧
    garner17_257_65537 (65537 % 17) (65537 % 257) (65537 % 65537) = 65537 ∧
    garner17_257_65537 (1000000 % 17) (1000000 % 257) (1000000 % 65537) = 1000000 ∧
    garner17_257_65537 (123456789 % 17) (123456789 % 257) (123456789 % 65537) = 123456789 ∧
    garner17_257_65537 (286331152 % 17) (286331152 % 257) (286331152 % 65537) = 286331152 := by
  decide

/--
Theorem (Universal 3-Channel Garner Reconstruction Soundness):
Reconstructs EVERY integer x < 286,331,153 across all 3 Fermat prime channels
(17, 257, 65537) without modular wrap-around.
Proved constructively with ZERO axioms.
-/
theorem garner_17_257_65537_roundtrip_all (x : Nat) (hx : x < 286331153) :
    garner17_257_65537 (x % 17) (x % 257) (x % 65537) = x := by
  dsimp [garner17_257_65537]
  let y := x % 4369
  have hy : y < 4369 := Nat.mod_lt x (by decide)
  have hpart : (x % 17 % 17 + 17 * (((x % 257 % 257 + 257 - x % 17 % 17 % 257) * 121) % 257)) = y := by
    have hd17 : 17 ∣ 4369 := ⟨257, rfl⟩
    have hd257 : 257 ∣ 4369 := ⟨17, by decide⟩
    rw [← Nat.mod_mod_of_dvd x hd17, ← Nat.mod_mod_of_dvd x hd257]
    exact garner17_257_roundtrip_all y hy
  rw [hpart]
  omega

/--
Theorem (Universal Base-1000 Limb Normalization):
All 16 output limbs of carryPassBase1000 v are strictly normalized (< 1000) for every v : Vec16.
Proved constructively with ZERO axioms.
-/
theorem carryPassBase1000_limbs_lt_1000 (v : Vec16) :
    let d := carryPassBase1000 v
    d.x0 < 1000 ∧ d.x1 < 1000 ∧ d.x2 < 1000 ∧ d.x3 < 1000 ∧
    d.x4 < 1000 ∧ d.x5 < 1000 ∧ d.x6 < 1000 ∧ d.x7 < 1000 ∧
    d.x8 < 1000 ∧ d.x9 < 1000 ∧ d.x10 < 1000 ∧ d.x11 < 1000 ∧
    d.x12 < 1000 ∧ d.x13 < 1000 ∧ d.x14 < 1000 ∧ d.x15 < 1000 := by
  dsimp [carryPassBase1000]
  refine ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
          Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
          Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
          Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
          Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
          Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
          Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
          Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

/--
Lemma (Carry Propagation Horner Decomposition):
The uncarried Horner polynomial decomposes into the carried Horner value plus carryOut15 * 1000^16.
-/
theorem carryPassBase1000_horner_eq (v : Vec16) :
    evalDigits1000Vec16 (carryPassBase1000 v) + carryOut15 v * (1000 ^ 16) =
    evalPoly1000Vec16 v := by
  dsimp [evalDigits1000Vec16, carryPassBase1000, evalPoly1000Vec16, carryOut15]
  omega

/--
Theorem (Universal Base-1000 Carry Value Preservation Modulo 1000^16):
Carrying preserves the exact positional polynomial value modulo 1000^16 for EVERY v : Vec16.
Proved constructively with ZERO axioms.
-/
theorem carryPassBase1000_preserves_value_mod (v : Vec16) :
    evalDigits1000Vec16 (carryPassBase1000 v) = evalPoly1000Vec16 v % (1000 ^ 16) := by
  have h := carryPassBase1000_horner_eq v
  have h1 : (evalDigits1000Vec16 (carryPassBase1000 v) + carryOut15 v * (1000 ^ 16)) % (1000 ^ 16) =
            evalPoly1000Vec16 v % (1000 ^ 16) := by rw [h]
  rw [Nat.add_mul_mod_self_right] at h1
  have hd_lt : evalDigits1000Vec16 (carryPassBase1000 v) < 1000 ^ 16 := by
    dsimp [evalDigits1000Vec16, carryPassBase1000]
    omega
  rw [Nat.mod_eq_of_lt hd_lt] at h1
  exact h1

/--
Theorem (Universal Exact Base-1000 Carry Value Preservation When Bounded):
When the polynomial value is strictly bounded below 1000^16, carryPassBase1000
preserves the exact integer value without alteration.
Proved constructively with ZERO axioms.
-/
theorem carryPassBase1000_exact_when_bounded (v : Vec16)
    (h : evalPoly1000Vec16 v < 1000 ^ 16) :
    evalDigits1000Vec16 (carryPassBase1000 v) = evalPoly1000Vec16 v := by
  have h_eq := carryPassBase1000_horner_eq v
  omega

/--
Theorem: 16-Point NTT roundtrip invertibility on test vector ⟨1..16⟩ across all 3 Fermat channels.
Proved constructively with ZERO axioms.
-/
theorem ntt16_three_channels_roundtrip_concrete :
    let v : Vec16 := ⟨1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16⟩
    intt16Mod17 (ntt16Mod17 v) = v ∧
    intt16Mod257 (ntt16Mod257 v) = v ∧
    intt16Mod65537 (ntt16Mod65537 v) = v := by
  decide

/--
Theorem (16-Point CRT-NTT Exact Integer Convolution):
Recovers exact unreduced integer cyclic convolution whose peak coefficient is 149,600,
exceeding every individual Fermat channel modulus (17, 257, 65537), verified over M = 286,331,153.
Proved constructively with ZERO axioms.
-/
theorem crt_ntt16_exact_integer_convolution :
    let a : Vec16 := ⟨10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150, 160⟩
    let b : Vec16 := ⟨160, 150, 140, 130, 120, 110, 100, 90, 80, 70, 60, 50, 40, 30, 20, 10⟩
    crtNttConv16 a b = exactIntCyclicConv16 a b ∧
    (crtNttConv16 a b).x15 = 149600 := by
  decide

/-- Theorem: Base-1000 8-limb capacity bound: worst-case coefficient strictly below CRT modulus. -/
theorem base1000_limb_capacity_bound :
    8 * 999 ^ 2 < 17 * 257 * 65537 ∧
    8 * 999 ^ 2 = 7984008 ∧
    17 * 257 * 65537 = 286331153 := by
  decide

/-- Theorem: Base-1000 roundtrip lossless encoding for 24-digit integer. -/
theorem base1000_roundtrip_concrete :
    evalDigits1000Vec16 (toBase1000Vec16 123456789012345678901234) =
      123456789012345678901234 := by
  decide

/-- Theorem: Multi-limb CRT-NTT multiplication on 12-digit integers. -/
theorem crt_ntt_big_mul_12_digit :
    crtNttBigMul 123456789012 987654321098 =
      123456789012 * 987654321098 := by
  decide

/-- Theorem: Multi-limb CRT-NTT multiplication on 24-digit integers (48-digit product). -/
theorem crt_ntt_big_mul_24_digit_max :
    crtNttBigMul 123456789012345678901234 987654321098765432109876 =
      123456789012345678901234 * 987654321098765432109876 ∧
    crtNttBigMul 999999999999999999999999 999999999999999999999999 =
      999999999999999999999999 * 999999999999999999999999 := by
  decide


end CrtNtt

-- end of file: leanasm/src/LeanAsm/CrtNtt/CrtBridge.lean
