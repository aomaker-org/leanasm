-- Path: leanasm/src/LeanAsm/QuasiRiemann/Rat.lean
-- Exact constructive rational arithmetic (QRat) shared across QuasiRiemann modules.
-- Max Column: 100 Columns

namespace QuasiRiemann

/-- Exact constructive rational `num / den` with strictly positive denominator. -/
structure QRat where
  num : Int
  den : Nat
  den_pos : 0 < den

/-- Raw display for `QRat` (`num` or `(num/den)` without automatic GCD reduction). -/
instance : Repr QRat where
  reprPrec q _ :=
    if q.den = 1 then repr q.num else s!"({q.num}/{q.den})"

/-- Embed an `Int` as a `QRat`. -/
def QRat.ofInt (n : Int) : QRat :=
  ⟨n, 1, Nat.zero_lt_one⟩

/-- Construct a `QRat` from numerator and positive denominator. -/
def QRat.mk' (num : Int) (den : Nat) (den_pos : 0 < den := by omega) : QRat :=
  ⟨num, den, den_pos⟩

instance : Inhabited QRat := ⟨QRat.ofInt 0⟩

instance : DecidableEq QRat := fun a b =>
  if hn : a.num = b.num then
    if hd : a.den = b.den then
      isTrue (by cases a; cases b; simp_all)
    else
      isFalse (by intro h; cases h; exact hd rfl)
  else
    isFalse (by intro h; cases h; exact hn rfl)

/-- Explicit helper to reduce a `QRat` by `Nat.gcd` (`Repr QRat` does not call this
automatically). -/
def QRat.reduce (q : QRat) : QRat :=
  let g := Nat.gcd q.num.natAbs q.den
  if hg : 0 < g then
    ⟨q.num / (g : Int), q.den / g,
      Nat.div_pos (Nat.le_of_dvd q.den_pos (Nat.gcd_dvd_right _ _)) hg⟩
  else
    q

/-- Cross-multiplied rational equivalence `a = b`. -/
def QRat.eqv (a b : QRat) : Prop :=
  a.num * (b.den : Int) = b.num * (a.den : Int)

/-- Cross-multiplied strict inequality `a < b`. -/
def QRat.lt (a b : QRat) : Prop :=
  a.num * (b.den : Int) < b.num * (a.den : Int)

/-- Cross-multiplied non-strict inequality `a ≤ b`. -/
def QRat.le (a b : QRat) : Prop :=
  a.num * (b.den : Int) ≤ b.num * (a.den : Int)

instance (a b : QRat) : Decidable (QRat.eqv a b) :=
  inferInstanceAs (Decidable (a.num * (b.den : Int) = b.num * (a.den : Int)))

instance (a b : QRat) : Decidable (QRat.lt a b) :=
  inferInstanceAs (Decidable (a.num * (b.den : Int) < b.num * (a.den : Int)))

instance (a b : QRat) : Decidable (QRat.le a b) :=
  inferInstanceAs (Decidable (a.num * (b.den : Int) ≤ b.num * (a.den : Int)))

/-- Exact rational addition. -/
def QRat.add (a b : QRat) : QRat :=
  ⟨a.num * (b.den : Int) + b.num * (a.den : Int), a.den * b.den,
    Nat.mul_pos a.den_pos b.den_pos⟩

/-- Exact rational negation. -/
def QRat.neg (a : QRat) : QRat :=
  ⟨-a.num, a.den, a.den_pos⟩

/-- Exact rational subtraction. -/
def QRat.sub (a b : QRat) : QRat :=
  ⟨a.num * (b.den : Int) - b.num * (a.den : Int), a.den * b.den,
    Nat.mul_pos a.den_pos b.den_pos⟩

/-- Exact rational multiplication. -/
def QRat.mul (a b : QRat) : QRat :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

/-- Exact rational absolute value `|a|`. -/
def QRat.abs (a : QRat) : QRat :=
  ⟨(a.num.natAbs : Int), a.den, a.den_pos⟩

/-- Checked exact rational division requiring a non-zero divisor (`b.num ≠ 0`). -/
def QRat.div (a b : QRat) (hb : b.num ≠ 0) : QRat :=
  if _hb_pos : 0 < b.num then
    ⟨a.num * (b.den : Int), a.den * b.num.natAbs,
      Nat.mul_pos a.den_pos (Int.natAbs_pos.mpr hb)⟩
  else
    ⟨-(a.num * (b.den : Int)), a.den * b.num.natAbs,
      Nat.mul_pos a.den_pos (Int.natAbs_pos.mpr hb)⟩

/-- Safe exact rational division returning `none` on a zero divisor (`b.num = 0`). -/
def QRat.div? (a b : QRat) : Option QRat :=
  if hb : b.num = 0 then none else some (QRat.div a b hb)

/-- Explicit total rational division returning `0` when the divisor is `0`.
Prefer `QRat.div` (proof-carrying) or `QRat.div?` (`Option`) when division by zero should be
rejected. -/
def QRat.divOrZero (a b : QRat) : QRat :=
  if hb : b.num = 0 then QRat.ofInt 0 else QRat.div a b hb

instance : Add QRat := ⟨QRat.add⟩
instance : Neg QRat := ⟨QRat.neg⟩
instance : Sub QRat := ⟨QRat.sub⟩
instance : Mul QRat := ⟨QRat.mul⟩
instance : LT QRat := ⟨QRat.lt⟩
instance : LE QRat := ⟨QRat.le⟩

instance (a b : QRat) : Decidable (a < b) :=
  inferInstanceAs (Decidable (QRat.lt a b))

instance (a b : QRat) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (QRat.le a b))

end QuasiRiemann

-- end of file: leanasm/src/LeanAsm/QuasiRiemann/Rat.lean
