import Cuboid2.LinearQuartic.FiniteCounts

/-!
# Exact finite certificates for the linear--quartic 2-descent

This file checks the purely algebraic and finite-linear-algebra part of the
Schaefer--Stoll certificate for

`w² = (t + 1) (t⁴ + 20t³ + 6t² + 4t + 1)`.

The quartic field is represented in the integral power basis
`1, π, π², π³`, where `π = z - 1`.  Thus
`π⁴ + 4π³ + 6π² + 2π - 2 = 0`.  The residue calculation at `2` is
performed in the exact 512-element quotient

`ℤ[z] / (z⁴ - 2z - 1, (z - 1)⁹)`.

No external number-field computation is used by the declarations below.
The remaining non-finite bridge is the general Schaefer--Stoll theorem which
identifies these checked local conditions with an upper bound for the
2-Selmer group.
-/

namespace Cuboid2

open Polynomial

noncomputable section

set_option maxRecDepth 100000

/-! ## Integral arithmetic in the quartic power basis -/

/-- An element `a₀ + a₁π + a₂π² + a₃π³` in the translated integral power
basis of `ℚ[z]/(z⁴ - 2z - 1)`, where `π=z-1`. -/
structure LinearQuarticDescentElt where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
deriving DecidableEq, Repr

namespace LinearQuarticDescentElt

/-- Addition in the integral power basis. -/
def add (a b : LinearQuarticDescentElt) : LinearQuarticDescentElt :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩

/-- Additive inverse in the integral power basis. -/
def neg (a : LinearQuarticDescentElt) : LinearQuarticDescentElt :=
  ⟨-a.c0, -a.c1, -a.c2, -a.c3⟩

/-- Integral scalar multiplication. -/
def smul (n : ℤ) (a : LinearQuarticDescentElt) :
    LinearQuarticDescentElt :=
  ⟨n * a.c0, n * a.c1, n * a.c2, n * a.c3⟩

/--
Multiplication reduced with

`z⁴ = 2 - 2z - 6z² - 4z³`,
`z⁵ = -8 + 10z + 22z² + 10z³`, and
`z⁶ = 20 - 28z - 50z² - 18z³`.
-/
def mul (a b : LinearQuarticDescentElt) : LinearQuarticDescentElt :=
  let d0 := a.c0 * b.c0
  let d1 := a.c0 * b.c1 + a.c1 * b.c0
  let d2 := a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0
  let d3 :=
    a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0
  let d4 := a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1
  let d5 := a.c2 * b.c3 + a.c3 * b.c2
  let d6 := a.c3 * b.c3
  ⟨d0 + 2 * d4 - 8 * d5 + 20 * d6,
   d1 - 2 * d4 + 10 * d5 - 28 * d6,
   d2 - 6 * d4 + 22 * d5 - 50 * d6,
   d3 - 4 * d4 + 10 * d5 - 18 * d6⟩

/-- Natural powers for the exact certificate computations. -/
def pow (a : LinearQuarticDescentElt) : ℕ → LinearQuarticDescentElt
  | 0 => ⟨1, 0, 0, 0⟩
  | n + 1 => mul (pow a n) a

/-- The element `0`. -/
def zero : LinearQuarticDescentElt := ⟨0, 0, 0, 0⟩

/-- The element `1`. -/
def one : LinearQuarticDescentElt := ⟨1, 0, 0, 0⟩

/-- The original power-basis generator `z=1+π`. -/
def z : LinearQuarticDescentElt := ⟨1, 1, 0, 0⟩

/-- The 2-adic uniformizer `π = z - 1`. -/
def pi : LinearQuarticDescentElt := ⟨0, 1, 0, 0⟩

/-- The image of the root of the quartic factor of the genus-two equation. -/
def theta : LinearQuarticDescentElt := ⟨-11, 18, 20, 8⟩

/-- The first fundamental unit `-z`. -/
def epsilon1 : LinearQuarticDescentElt := ⟨-1, -1, 0, 0⟩

/-- The second fundamental unit `z³ + z - 1`. -/
def epsilon2 : LinearQuarticDescentElt := ⟨1, 4, 3, 1⟩

/-- The square root used for the rational 2-torsion Kummer class. -/
def torsionSquareRoot : LinearQuarticDescentElt := ⟨2, -4, -5, -2⟩

/-- The square root proving that the Kummer image of `(0,1)-∞` is trivial. -/
def halfSquareRoot : LinearQuarticDescentElt := ⟨3, -4, -5, -2⟩

/-- Coefficient access, used to form the exact multiplication determinant. -/
def coeff (a : LinearQuarticDescentElt) : Fin 4 → ℤ
  | ⟨0, _⟩ => a.c0
  | ⟨1, _⟩ => a.c1
  | ⟨2, _⟩ => a.c2
  | ⟨3, _⟩ => a.c3

/-- The four power-basis vectors. -/
def basis : Fin 4 → LinearQuarticDescentElt
  | ⟨0, _⟩ => ⟨1, 0, 0, 0⟩
  | ⟨1, _⟩ => ⟨0, 1, 0, 0⟩
  | ⟨2, _⟩ => ⟨0, 0, 1, 0⟩
  | ⟨3, _⟩ => ⟨0, 0, 0, 1⟩

/-- The matrix of multiplication by an integral quartic element. -/
def multiplicationMatrix (a : LinearQuarticDescentElt) :
    Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => coeff (mul a (basis j)) i

/-- The exact power-basis norm, defined as a determinant. -/
def norm (a : LinearQuarticDescentElt) : ℤ :=
  Matrix.det (multiplicationMatrix a)

theorem pi_defining_equation :
    add
        (add
          (add (pow pi 4) (smul 4 (pow pi 3)))
          (smul 6 (pow pi 2)))
        (add (smul 2 pi) (smul (-2) one)) =
      zero := by
  decide

theorem z_defining_equation :
    add (add (pow z 4) (smul (-2) z)) (neg one) = zero := by
  decide

theorem theta_quartic_equation :
    add
        (add
          (add (pow theta 4) (smul 20 (pow theta 3)))
          (smul 6 (pow theta 2)))
        (add (smul 4 theta) one) =
      zero := by
  decide

theorem norm_pi : norm pi = -2 := by
  decide

theorem norm_epsilon1 : norm epsilon1 = -1 := by
  decide

theorem norm_epsilon2 : norm epsilon2 = -1 := by
  decide

theorem norm_one_sub_theta :
    norm (add one (neg theta)) = 32 := by
  decide

theorem torsion_square_identity :
    mul epsilon2 (pow torsionSquareRoot 2) = add theta one := by
  decide

theorem half_square_identity :
    pow halfSquareRoot 2 = neg theta := by
  decide

/-- The four displayed norm-kernel generators have square pair norms
`1, 64, 1, 1`. -/
theorem global_basis_pair_norms :
    [norm ⟨-1, 0, 0, 0⟩,
      2 * norm (add one (neg theta)),
      (-1) * norm epsilon1,
      (-1) * norm epsilon2] =
      [1, 64, 1, 1] := by
  decide

end LinearQuarticDescentElt

/-! ## Polynomial and bad-prime identities -/

/-- The defining polynomial of the quartic field. -/
def linearQuarticDescentFieldPolynomial : ℤ[X] :=
  X ^ 4 - C 2 * X - 1

/-- The translated polynomial is 2-Eisenstein.  The identity is kept
separate from the Eisenstein criterion so all coefficients are visible. -/
theorem linearQuarticDescentField_shift :
    linearQuarticDescentFieldPolynomial.comp (X + 1) =
      X ^ 4 + C 4 * X ^ 3 + C 6 * X ^ 2 + C 2 * X - 2 := by
  simp [linearQuarticDescentFieldPolynomial]
  ring

/-- The degree-five curve polynomial has the exact factorization modulo 43
used in the tame-prime part of the descent. -/
theorem linearQuarticPolynomial_factor_mod43 :
    (linearQuarticPolynomial : (ZMod 43)[X]) =
      (X - C 3) ^ 2 * (X + C 1) * (X + C 9) * (X + C 17) := by
  have hZ :
      ((X - 3) ^ 2 * (X + 1) * (X + 9) * (X + 17) :
          ℤ[X]) =
        (X ^ 5 + 21 * X ^ 4 + 26 * X ^ 3 +
            10 * X ^ 2 + 5 * X + 1) +
          43 * (-16 * X ^ 2 + 16 * X + 32) := by
    ring
  have hm :=
    congrArg
      (Polynomial.map (Int.castRingHom (ZMod 43))) hZ
  have h43p : (43 : (ZMod 43)[X]) = 0 := by
    rw [← Polynomial.C_ofNat]
    have hz : (43 : ZMod 43) = 0 := ZMod.natCast_self 43
    rw [hz]
    exact map_zero C
  simpa [linearQuarticPolynomial, Polynomial.C_ofNat,
    ZMod.natCast_self, h43p] using hm.symm

/-! ## The exact `(z-1)⁹` quotient -/

open LinearQuarticDescentElt

/--
The four coefficient vectors generating the ideal `(π⁹)` in the power
basis.  They are `π⁹, π¹⁰, π¹¹, π¹²`.
-/
def piNinthLatticeBasis : Fin 4 → LinearQuarticDescentElt
  | ⟨0, _⟩ => ⟨-16, 60, -32, -44⟩
  | ⟨1, _⟩ => ⟨-88, 72, 324, 144⟩
  | ⟨2, _⟩ => ⟨288, -376, -792, -252⟩
  | ⟨3, _⟩ => ⟨-504, 792, 1136, 216⟩

theorem piNinthLatticeBasis_eq_pow (j : Fin 4) :
    piNinthLatticeBasis j = pow pi (9 + j.val) := by
  fin_cases j <;> decide

/-- The Hermite-normal-form lattice for `(π⁹)`: coefficient moduli
`8,4,4,4`. -/
def piNinthHermiteBasis : Fin 4 → LinearQuarticDescentElt
  | ⟨0, _⟩ => ⟨8, 0, 0, 0⟩
  | ⟨1, _⟩ => ⟨0, 4, 0, 0⟩
  | ⟨2, _⟩ => ⟨0, 0, 4, 0⟩
  | ⟨3, _⟩ => ⟨0, 0, 0, 4⟩

/-- Integer matrix expressing the Hermite basis through
`π⁹,π¹⁰,π¹¹,π¹²`. -/
def piNinthToHermite : Fin 4 → Fin 4 → ℤ :=
  ![![19350, 3825, 1512, 598],
    ![29596, 5850, 2313, 914],
    ![16812, 3323, 1314, 519],
    ![3825, 756, 299, 118]]

/-- Integer matrix expressing `π⁹,π¹⁰,π¹¹,π¹²` through the Hermite basis. -/
def hermiteToPiNinth : Fin 4 → Fin 4 → ℤ :=
  ![![-2, -11, 36, -63],
    ![15, 18, -94, 198],
    ![-8, 81, -198, 284],
    ![-11, 36, -63, 54]]

/-- Exact certificate that the diagonal Hermite lattice is contained in
the lattice generated by `π⁹,π¹⁰,π¹¹,π¹²`. -/
theorem piNinth_spans_Hermite (j : Fin 4) :
    piNinthHermiteBasis j =
      add
        (smul (piNinthToHermite 0 j) (piNinthLatticeBasis 0))
        (add
          (smul (piNinthToHermite 1 j) (piNinthLatticeBasis 1))
          (add
            (smul (piNinthToHermite 2 j) (piNinthLatticeBasis 2))
            (smul (piNinthToHermite 3 j) (piNinthLatticeBasis 3)))) := by
  fin_cases j <;> decide

/-- Exact certificate for the reverse containment of the two lattices. -/
theorem Hermite_spans_piNinth (j : Fin 4) :
    piNinthLatticeBasis j =
      add
        (smul (hermiteToPiNinth 0 j) (piNinthHermiteBasis 0))
        (add
          (smul (hermiteToPiNinth 1 j) (piNinthHermiteBasis 1))
          (add
            (smul (hermiteToPiNinth 2 j) (piNinthHermiteBasis 2))
            (smul (hermiteToPiNinth 3 j) (piNinthHermiteBasis 3)))) := by
  fin_cases j <;> decide

/--
The 512-element coefficient model of
`ℤ[z]/(z⁴-2z-1,(z-1)⁹)`, justified by the two lattice-containment
certificates above.
-/
structure LinearQuarticRamifiedResidue where
  c0 : ZMod 8
  c1 : ZMod 4
  c2 : ZMod 4
  c3 : ZMod 4
deriving DecidableEq, Fintype, Repr

namespace LinearQuarticRamifiedResidue

/-- Reduce four integer coefficients modulo the exact Hermite lattice. -/
def ofInts (a0 a1 a2 a3 : ℤ) : LinearQuarticRamifiedResidue :=
  ⟨a0, a1, a2, a3⟩

/-- Coefficientwise addition in the finite quotient. -/
def add (a b : LinearQuarticRamifiedResidue) :
    LinearQuarticRamifiedResidue :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩

/-- Multiplication using the same exact quartic reduction as above. -/
def mul (a b : LinearQuarticRamifiedResidue) :
    LinearQuarticRamifiedResidue :=
  let a0 : ℤ := a.c0.val
  let a1 : ℤ := a.c1.val
  let a2 : ℤ := a.c2.val
  let a3 : ℤ := a.c3.val
  let b0 : ℤ := b.c0.val
  let b1 : ℤ := b.c1.val
  let b2 : ℤ := b.c2.val
  let b3 : ℤ := b.c3.val
  let d0 := a0 * b0
  let d1 := a0 * b1 + a1 * b0
  let d2 := a0 * b2 + a1 * b1 + a2 * b0
  let d3 := a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
  let d4 := a1 * b3 + a2 * b2 + a3 * b1
  let d5 := a2 * b3 + a3 * b2
  let d6 := a3 * b3
  ofInts
    (d0 + 2 * d4 - 8 * d5 + 20 * d6)
    (d1 - 2 * d4 + 10 * d5 - 28 * d6)
    (d2 - 6 * d4 + 22 * d5 - 50 * d6)
    (d3 - 4 * d4 + 10 * d5 - 18 * d6)

/-- Powers in the finite quotient. -/
def pow (a : LinearQuarticRamifiedResidue) :
    ℕ → LinearQuarticRamifiedResidue
  | 0 => ofInts 1 0 0 0
  | n + 1 => mul (pow a n) a

/-- The residue of the uniformizer `π=z-1`. -/
def pi : LinearQuarticRamifiedResidue := ofInts 0 1 0 0

/-- The residue of `-1`. -/
def minusOne : LinearQuarticRamifiedResidue := ofInts (-1) 0 0 0

/-- The residue of `z=1+π`. -/
def z : LinearQuarticRamifiedResidue := ofInts 1 1 0 0

/-- The residue of `2-z`. -/
def twoSubZ : LinearQuarticRamifiedResidue := ofInts 1 (-1) 0 0

/-- The residue of `2z-1`. -/
def twoZSubOne : LinearQuarticRamifiedResidue := ofInts 1 2 0 0

/-- The integral unit `2/π⁴`, reduced in the power basis. -/
def twoDivPiFourth : LinearQuarticRamifiedResidue :=
  ofInts 47 71 40 9

theorem card_ramifiedResidue :
    Fintype.card LinearQuarticRamifiedResidue = 512 := by
  decide

theorem pi_pow_nine : pow pi 9 = ofInts 0 0 0 0 := by
  decide

theorem pi_pow_four_mul_twoDivPiFourth :
    mul (pow pi 4) twoDivPiFourth = ofInts 2 0 0 0 := by
  decide

/-- The 256 binary `π`-adic unit representatives modulo `π⁹`. -/
def henselUnitRepresentative (mask : Fin 256) :
    LinearQuarticRamifiedResidue :=
  (List.range 8).foldl
    (fun a i =>
      if mask.val.testBit i then add a (pow pi (i + 1)) else a)
    (ofInts 1 0 0 0)

/-- A bit of the binary residue mask, as a natural number `0` or `1`. -/
def maskBit (mask bit : Nat) : Nat :=
  if mask.testBit bit then 1 else 0

/--
Closed coefficient formula for the same binary representative.  Keeping
this formula separate makes the subsequent finite table reduction small.
-/
def henselUnitRepresentativeDirect (mask : Fin 256) :
    LinearQuarticRamifiedResidue :=
  let b0 := maskBit mask.val 0
  let b1 := maskBit mask.val 1
  let b2 := maskBit mask.val 2
  let b3 := maskBit mask.val 3
  let b4 := maskBit mask.val 4
  let b5 := maskBit mask.val 5
  let b6 := maskBit mask.val 6
  let b7 := maskBit mask.val 7
  ofInts
    (1 + 2 * b3 + 4 * b5 + 4 * b6 + 4 * b7)
    (b0 + 2 * b3 + 2 * b4)
    (b1 + 2 * b3 + 2 * b4 + 2 * b5)
    (b2 + 2 * b4 + 2 * b5 + 2 * b6)

/-- The folded `π`-adic expression agrees with its closed coefficient
formula for all 256 masks. -/
theorem henselUnitRepresentative_eq_direct (mask : Fin 256) :
    henselUnitRepresentative mask = henselUnitRepresentativeDirect mask := by
  fin_cases mask <;> decide

/-- A residue is a unit exactly when its constant coefficient is odd. -/
def IsUnitResidue (a : LinearQuarticRamifiedResidue) : Prop :=
  a.c0.val % 2 = 1

instance (a : LinearQuarticRamifiedResidue) :
    Decidable (IsUnitResidue a) := by
  unfold IsUnitResidue
  infer_instance

/-- The binary expressions have no duplicates. -/
def henselDecode (a : LinearQuarticRamifiedResidue) : Nat :=
  let t0 := ((a.c0.val + 7) % 8) / 2
  let b0 := a.c1.val % 2
  let b1 := a.c2.val % 2
  let b2 := a.c3.val % 2
  let b3 := t0 % 2
  let h0 := t0 / 2
  let h1 := a.c1.val / 2
  let h2 := a.c2.val / 2
  let h3 := a.c3.val / 2
  let b4 := Nat.xor h1 b3
  let b5 := Nat.xor (Nat.xor h2 b3) b4
  let b6 := Nat.xor (Nat.xor h3 b4) b5
  let b7 := Nat.xor (Nat.xor h0 b5) b6
  b0 + 2 * b1 + 4 * b2 + 8 * b3 +
    16 * b4 + 32 * b5 + 64 * b6 + 128 * b7

/-- The displayed decoder is a left inverse to the binary expansion. -/
theorem henselDecode_representative (mask : Fin 256) :
    henselDecode (henselUnitRepresentative mask) = mask.val := by
  rw [henselUnitRepresentative_eq_direct]
  fin_cases mask <;> decide

/-- The binary expressions have no duplicates. -/
theorem henselUnitRepresentative_injective :
    Function.Injective henselUnitRepresentative := by
  intro a b hab
  apply Fin.ext
  have h := congrArg henselDecode hab
  simpa only [henselDecode_representative] using h

/-- Every binary expression is a unit residue. -/
theorem henselUnitRepresentative_isUnit (mask : Fin 256) :
    IsUnitResidue (henselUnitRepresentative mask) := by
  rw [henselUnitRepresentative_eq_direct]
  fin_cases mask <;> decide

/-- The subtype of the 256 unit residues modulo `π⁹`. -/
abbrev UnitResidue :=
  {a : LinearQuarticRamifiedResidue // IsUnitResidue a}

theorem card_unitResidue : Fintype.card UnitResidue = 256 := by
  decide

/-- The binary expansion as a map to the exact unit-residue subtype. -/
def henselUnitMap (mask : Fin 256) : UnitResidue :=
  ⟨henselUnitRepresentative mask, henselUnitRepresentative_isUnit mask⟩

theorem henselUnitMap_bijective :
    Function.Bijective henselUnitMap := by
  apply (Fintype.bijective_iff_injective_and_card henselUnitMap).2
  constructor
  · intro a b hab
    apply henselUnitRepresentative_injective
    exact congrArg Subtype.val hab
  · simp [card_unitResidue]

/-- Consequently the binary expressions exhaust all unit residues. -/
theorem henselUnitRepresentative_exhausts
    (a : LinearQuarticRamifiedResidue) :
    IsUnitResidue a ↔
      ∃ mask : Fin 256, henselUnitRepresentative mask = a := by
  constructor
  · intro ha
    obtain ⟨mask, hmask⟩ :=
      henselUnitMap_bijective.2 ⟨a, ha⟩
    exact ⟨mask, congrArg Subtype.val hmask⟩
  · rintro ⟨mask, rfl⟩
    exact henselUnitRepresentative_isUnit mask

/-- The normalized unit part of a product of the six proposed local
squareclass generators

`(π,-1,2,z,2-z,2z-1)`.

The `π` bit records valuation parity separately; the `2` bit contributes
the unit `2/π⁴`.
-/
def normalizedLocalBasisProduct (mask : Fin 64) :
    LinearQuarticRamifiedResidue :=
  let factors :=
    [(1, minusOne), (2, twoDivPiFourth), (3, z),
      (4, twoSubZ), (5, twoZSubOne)]
  factors.foldl
    (fun a entry =>
      if mask.val.testBit entry.1 then mul a entry.2 else a)
    (ofInts 1 0 0 0)

/-- Squares of unit residues are already obtained from the first eight
binary representatives. -/
def henselSquareResidues : List LinearQuarticRamifiedResidue :=
  (List.finRange 8).map
    (fun mask =>
      mul
        (henselUnitRepresentativeDirect
          ⟨mask.val, lt_trans mask.isLt (by norm_num)⟩)
        (henselUnitRepresentativeDirect
          ⟨mask.val, lt_trans mask.isLt (by norm_num)⟩))

/-- The eight square residues displayed by the Hensel computation. -/
theorem henselSquareResidues_eq :
    henselSquareResidues =
      [ofInts 1 0 0 0, ofInts 1 2 1 0, ofInts 3 2 0 0,
        ofInts 3 0 1 2, ofInts 5 0 2 0, ofInts 1 2 3 0,
        ofInts 7 2 2 0, ofInts 3 0 3 2] := by
  decide

/-- Finite square test after separating valuation parity. -/
def LocalBasisProductIsSquare (mask : Fin 64) : Prop :=
  mask.val.testBit 0 = false ∧
    normalizedLocalBasisProduct mask ∈ henselSquareResidues

instance (mask : Fin 64) :
    Decidable (LocalBasisProductIsSquare mask) := by
  unfold LocalBasisProductIsSquare
  infer_instance

/--
Among the 64 products of `(π,-1,2,z,2-z,2z-1)`, only the empty product
occurs in the checked eight-entry square table after valuation
normalization.  The separate global descent bridge must additionally show
that this table exhausts all unit squares modulo `π⁹`.
-/
theorem localBasisProduct_square_iff_zero (mask : Fin 64) :
    LocalBasisProductIsSquare mask ↔ mask.val = 0 := by
  decide +revert

end LinearQuarticRamifiedResidue

/-! ## Exact `F₂` row-space intersections -/

/-- XOR-combination of rows, with the low bit of `mask` selecting the
first row.  Rows themselves are bit-packed vectors over `F₂`. -/
def xorRowCombination : List Nat → Nat → Nat
  | [], _ => 0
  | row :: rows, mask =>
      Nat.xor (if mask % 2 = 1 then row else 0)
        (xorRowCombination rows (mask / 2))

/-- The four global norm-kernel rows at `2`, in nine local squareclass
coordinates. -/
def linearQuarticGlobalRowsAtTwo : List Nat :=
  [16, 74, 81, 97]

/-- Three independent local point rows at `2`. -/
def linearQuarticLocalImageRowsAtTwo : List Nat :=
  [74, 158, 165]

/-- The local row space generated by the three displayed 2-adic points. -/
def linearQuarticLocalImageAtTwo : List Nat :=
  (List.range 8).map
    (xorRowCombination linearQuarticLocalImageRowsAtTwo)

theorem linearQuarticGlobalRows_independent :
    ((List.range 16).map
      (xorRowCombination linearQuarticGlobalRowsAtTwo)).Nodup := by
  decide

theorem linearQuarticLocalRows_independent :
    linearQuarticLocalImageAtTwo.Nodup := by
  decide

/-- The intersection of the four-dimensional global candidate space with
the complete three-dimensional displayed local row space has four masks. -/
theorem linearQuartic_masks_surviving_two :
    (List.range 16).filter
        (fun mask =>
          xorRowCombination linearQuarticGlobalRowsAtTwo mask ∈
            linearQuarticLocalImageAtTwo) =
      [0, 2, 9, 11] := by
  decide

/-- The four global sign rows in the order
`(-1, θ_low, θ_high)`. -/
def linearQuarticInfinityRows : List Nat := [6, 0, 5, 3]

/-- The two sign patterns in the real Kummer image. -/
def linearQuarticAllowedInfinityRows : List Nat := [0, 5]

theorem linearQuartic_masks_surviving_infinity :
    (List.range 16).filter
        (fun mask =>
          xorRowCombination linearQuarticInfinityRows mask ∈
            linearQuarticAllowedInfinityRows) =
      [0, 2, 4, 6, 9, 11, 13, 15] := by
  decide

theorem linearQuartic_final_selmer_masks :
    (List.range 16).filter
        (fun mask =>
          xorRowCombination linearQuarticGlobalRowsAtTwo mask ∈
              linearQuarticLocalImageAtTwo ∧
            xorRowCombination linearQuarticInfinityRows mask ∈
              linearQuarticAllowedInfinityRows) =
      [0, 2, 9, 11] := by
  decide

/-! ## Exact local point values -/

theorem linearQuartic_local_point_values :
    [linearQuarticCurveRhs (1 : ℤ),
      linearQuarticCurveRhs (-7 : ℤ),
      linearQuarticCurveRhs (11 : ℤ)] =
      [64, 25152, 504384] := by
  norm_num [linearQuarticCurveRhs]

theorem linearQuartic_local_point_odd_units :
    [64 / 64 % 8, 25152 / 64 % 8, 504384 / 64 % 8] =
      [1, 1, 1] := by
  decide

end

end Cuboid2
