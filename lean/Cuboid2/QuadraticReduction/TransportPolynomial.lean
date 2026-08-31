import Mathlib

/-!
# Executable sparse bivariate-polynomial checker

The large transport certificates are checked with a small, transparent
normalizer on lists of integer monomials.  Unlike `MvPolynomial`, every
operation here is executable, so `native_decide` can compare the exact
normal forms while the lemmas below connect those computations to evaluation
over `ℚ`.
-/

namespace Cuboid2

/-- A monomial `(U-power,V-power,coefficient)`. -/
abbrev TransportUVTerm := Nat × Nat × Int

/-- A monomial `(x-power,U-power,V-power,coefficient)`. -/
abbrev TransportXUVTerm := Nat × Nat × Nat × Int

/-- Parse one generated comma-separated bivariate monomial. -/
def transportParseUVTerm (text : String) : TransportUVTerm :=
  match text.splitOn "," with
  | [u, v, c] => (u.toNat?.getD 0, v.toNat?.getD 0, c.toInt?.getD 0)
  | _ => (0, 0, 0)

/-- Parse generated semicolon-separated bivariate coefficient data. -/
def transportParseUVTerms (text : String) : List TransportUVTerm :=
  if text.isEmpty then [] else (text.splitOn ";").map transportParseUVTerm

/-- Parse one generated comma-separated trivariate monomial. -/
def transportParseXUVTerm (text : String) : TransportXUVTerm :=
  match text.splitOn "," with
  | [i, u, v, c] =>
      (i.toNat?.getD 0, u.toNat?.getD 0, v.toNat?.getD 0, c.toInt?.getD 0)
  | _ => (0, 0, 0, 0)

/-- Parse generated semicolon-separated trivariate coefficient data. -/
def transportParseXUVTerms (text : String) : List TransportXUVTerm :=
  if text.isEmpty then [] else (text.splitOn ";").map transportParseXUVTerm

/-- Evaluate one sparse integer monomial over `ℚ`. -/
def transportEvalUVTerm (term : TransportUVTerm) (U V : ℚ) : ℚ :=
  (term.2.2 : ℚ) * U ^ term.1 * V ^ term.2.1

/-- Evaluate a sparse list of integer monomials over `ℚ`. -/
def transportEvalUVTerms : List TransportUVTerm → ℚ → ℚ → ℚ
  | [], _, _ => 0
  | term :: rest, U, V =>
      transportEvalUVTerm term U V + transportEvalUVTerms rest U V

/-- Evaluate a sparse trivariate integer polynomial over `ℚ`. -/
def transportEvalXUVTerms : List TransportXUVTerm → ℚ → ℚ → ℚ → ℚ
  | [], _, _, _ => 0
  | (i, u, v, c) :: rest, x, U, V =>
      (c : ℚ) * x ^ i * U ^ u * V ^ v +
        transportEvalXUVTerms rest x U V

/-- Descending lexicographic monomial order used by the generated data. -/
def transportUVTermBefore (left right : TransportUVTerm) : Bool :=
  left.1 > right.1 || (left.1 == right.1 && left.2.1 > right.2.1)

/--
Insert one term into a normalized descending list, combining an existing
coefficient with the same powers and removing a resulting zero.
-/
def transportInsertUVTerm (term : TransportUVTerm) :
    List TransportUVTerm → List TransportUVTerm
  | [] => if term.2.2 = 0 then [] else [term]
  | head :: rest =>
      if term.1 = head.1 ∧ term.2.1 = head.2.1 then
        let coefficient := term.2.2 + head.2.2
        if coefficient = 0 then rest
        else (term.1, term.2.1, coefficient) :: rest
      else if transportUVTermBefore term head then
        term :: head :: rest
      else
        head :: transportInsertUVTerm term rest

/-- Normalize a raw sparse list. -/
def transportNormalizeUVTerms : List TransportUVTerm → List TransportUVTerm
  | [] => []
  | term :: rest =>
      transportInsertUVTerm term (transportNormalizeUVTerms rest)

/-- Product of two monomials. -/
def transportMulUVTerm (left right : TransportUVTerm) : TransportUVTerm :=
  (left.1 + right.1, left.2.1 + right.2.1, left.2.2 * right.2.2)

/-- Raw distributive product of two sparse lists. -/
def transportRawMulUVTerms
    (left right : List TransportUVTerm) : List TransportUVTerm :=
  left.flatMap fun leftTerm => right.map (transportMulUVTerm leftTerm)

/-- Normalized sparse product. -/
def transportMulUVTerms
    (left right : List TransportUVTerm) : List TransportUVTerm :=
  transportNormalizeUVTerms (transportRawMulUVTerms left right)

/-- Negate a sparse integer polynomial. -/
def transportNegUVTerms : List TransportUVTerm → List TransportUVTerm
  | [] => []
  | term :: rest =>
      (term.1, term.2.1, -term.2.2) :: transportNegUVTerms rest

/-- Normalized sparse sum. -/
def transportAddUVTerms
    (left right : List TransportUVTerm) : List TransportUVTerm :=
  transportNormalizeUVTerms (left ++ right)

/-- Normalized natural power. -/
def transportPowUVTerms (terms : List TransportUVTerm) : Nat → List TransportUVTerm
  | 0 => [(0, 0, 1)]
  | n + 1 => transportMulUVTerms (transportPowUVTerms terms n) terms

/--
Homogenize one `x,U,V` term after substituting `x=-B/A`, clearing the
common denominator `A^degree`.
-/
def transportSubstituteLinearXTerm
    (degree : ℕ) (A B : List TransportUVTerm)
    (term : TransportXUVTerm) : List TransportUVTerm :=
  let coefficient : List TransportUVTerm := [(term.2.1, term.2.2.1, term.2.2.2)]
  transportMulUVTerms coefficient
    (transportMulUVTerms
      (transportPowUVTerms (transportNegUVTerms B) term.1)
      (transportPowUVTerms A (degree - term.1)))

/-- Homogenized substitution for a sparse trivariate polynomial. -/
def transportSubstituteLinearXTerms
    (degree : ℕ) (terms : List TransportXUVTerm)
    (A B : List TransportUVTerm) : List TransportUVTerm :=
  terms.foldl
    (fun answer term =>
      transportAddUVTerms answer
        (transportSubstituteLinearXTerm degree A B term))
    []

theorem transportEvalUVTerm_coefficient_zero
    (u v : ℕ) (U V : ℚ) :
    transportEvalUVTerm (u, v, 0) U V = 0 := by
  simp [transportEvalUVTerm]

theorem transportEvalInsertUVTerm
    (term : TransportUVTerm) (terms : List TransportUVTerm) (U V : ℚ) :
    transportEvalUVTerms (transportInsertUVTerm term terms) U V =
      transportEvalUVTerm term U V + transportEvalUVTerms terms U V := by
  rcases term with ⟨u, v, c⟩
  induction terms with
  | nil =>
      by_cases hc : c = 0
      · simp [transportInsertUVTerm, hc, transportEvalUVTerms,
          transportEvalUVTerm]
      · simp [transportInsertUVTerm, hc, transportEvalUVTerms,
          transportEvalUVTerm]
  | cons head rest ih =>
      rcases head with ⟨u', v', c'⟩
      by_cases hp : u = u' ∧ v = v'
      · rcases hp with ⟨rfl, rfl⟩
        by_cases hc : c + c' = 0
        · have hcq : (c : ℚ) + (c' : ℚ) = 0 := by exact_mod_cast hc
          have hmonomial :
              (c : ℚ) * U ^ u * V ^ v + (c' : ℚ) * U ^ u * V ^ v = 0 := by
            calc
              (c : ℚ) * U ^ u * V ^ v + (c' : ℚ) * U ^ u * V ^ v =
                  ((c : ℚ) + (c' : ℚ)) * U ^ u * V ^ v := by ring
              _ = 0 := by rw [hcq]; simp
          simp [transportInsertUVTerm, hc, transportEvalUVTerms,
            transportEvalUVTerm]
          linarith
        · simp [transportInsertUVTerm, hc, transportEvalUVTerms,
            transportEvalUVTerm]
          push_cast
          ring
      · by_cases hbefore :
          transportUVTermBefore (u, v, c) (u', v', c')
        · simp [transportInsertUVTerm, hp, hbefore, transportEvalUVTerms,
            transportEvalUVTerm]
        · simp [transportInsertUVTerm, hp, hbefore, transportEvalUVTerms,
            transportEvalUVTerm, ih]
          ring

theorem transportEvalNormalizeUVTerms
    (terms : List TransportUVTerm) (U V : ℚ) :
    transportEvalUVTerms (transportNormalizeUVTerms terms) U V =
      transportEvalUVTerms terms U V := by
  induction terms with
  | nil => rfl
  | cons term rest ih =>
      rw [transportNormalizeUVTerms, transportEvalInsertUVTerm, ih]
      rfl

theorem transportEvalMulUVTerm
    (left right : TransportUVTerm) (U V : ℚ) :
    transportEvalUVTerm (transportMulUVTerm left right) U V =
      transportEvalUVTerm left U V * transportEvalUVTerm right U V := by
  rcases left with ⟨u, v, c⟩
  rcases right with ⟨u', v', c'⟩
  simp [transportMulUVTerm, transportEvalUVTerm, pow_add]
  push_cast
  ring

private theorem transportEvalAppendUVTerms
    (left right : List TransportUVTerm) (U V : ℚ) :
    transportEvalUVTerms (left ++ right) U V =
      transportEvalUVTerms left U V + transportEvalUVTerms right U V := by
  induction left with
  | nil => simp [transportEvalUVTerms]
  | cons head rest ih =>
      simp [transportEvalUVTerms, ih]
      ring

private theorem transportEvalMapMulUVTerm
    (left : TransportUVTerm) (right : List TransportUVTerm) (U V : ℚ) :
    transportEvalUVTerms (right.map (transportMulUVTerm left)) U V =
      transportEvalUVTerm left U V * transportEvalUVTerms right U V := by
  induction right with
  | nil => simp [transportEvalUVTerms]
  | cons head rest ih =>
      simp [transportEvalUVTerms, transportEvalMulUVTerm, ih]
      ring

theorem transportEvalRawMulUVTerms
    (left right : List TransportUVTerm) (U V : ℚ) :
    transportEvalUVTerms (transportRawMulUVTerms left right) U V =
      transportEvalUVTerms left U V * transportEvalUVTerms right U V := by
  induction left with
  | nil => simp [transportRawMulUVTerms, transportEvalUVTerms]
  | cons head rest ih =>
      rw [transportRawMulUVTerms, List.flatMap_cons,
        transportEvalAppendUVTerms, transportEvalMapMulUVTerm]
      change
        transportEvalUVTerm head U V * transportEvalUVTerms right U V +
            transportEvalUVTerms (transportRawMulUVTerms rest right) U V =
          transportEvalUVTerms (head :: rest) U V *
            transportEvalUVTerms right U V
      rw [ih]
      simp only [transportEvalUVTerms]
      ring

theorem transportEvalMulUVTerms
    (left right : List TransportUVTerm) (U V : ℚ) :
    transportEvalUVTerms (transportMulUVTerms left right) U V =
      transportEvalUVTerms left U V * transportEvalUVTerms right U V := by
  rw [transportMulUVTerms, transportEvalNormalizeUVTerms,
    transportEvalRawMulUVTerms]

theorem transportEvalNegUVTerms
    (terms : List TransportUVTerm) (U V : ℚ) :
    transportEvalUVTerms (transportNegUVTerms terms) U V =
      -transportEvalUVTerms terms U V := by
  induction terms with
  | nil => simp [transportNegUVTerms, transportEvalUVTerms]
  | cons term rest ih =>
      rcases term with ⟨u, v, c⟩
      simp [transportNegUVTerms, transportEvalUVTerms,
        transportEvalUVTerm, ih]
      push_cast
      ring

theorem transportEvalAddUVTerms
    (left right : List TransportUVTerm) (U V : ℚ) :
    transportEvalUVTerms (transportAddUVTerms left right) U V =
      transportEvalUVTerms left U V + transportEvalUVTerms right U V := by
  rw [transportAddUVTerms, transportEvalNormalizeUVTerms]
  exact transportEvalAppendUVTerms left right U V

theorem transportEvalPowUVTerms
    (terms : List TransportUVTerm) (n : ℕ) (U V : ℚ) :
    transportEvalUVTerms (transportPowUVTerms terms n) U V =
      transportEvalUVTerms terms U V ^ n := by
  induction n with
  | zero => simp [transportPowUVTerms, transportEvalUVTerms, transportEvalUVTerm]
  | succ n ih =>
      rw [transportPowUVTerms, transportEvalMulUVTerms, ih, pow_succ]

theorem transportEvalSubstituteLinearXTerm
    {degree : ℕ} {term : TransportXUVTerm}
    (A B : List TransportUVTerm) (U V : ℚ)
    (hi : term.1 ≤ degree) (hA : transportEvalUVTerms A U V ≠ 0) :
    transportEvalUVTerms
        (transportSubstituteLinearXTerm degree A B term) U V =
      transportEvalUVTerms A U V ^ degree *
        ((term.2.2.2 : ℚ) *
          (-transportEvalUVTerms B U V / transportEvalUVTerms A U V) ^ term.1 *
          U ^ term.2.1 * V ^ term.2.2.1) := by
  rw [transportSubstituteLinearXTerm, transportEvalMulUVTerms,
    transportEvalMulUVTerms, transportEvalPowUVTerms,
    transportEvalPowUVTerms, transportEvalNegUVTerms]
  simp only [transportEvalUVTerms, transportEvalUVTerm, neg_neg]
  rw [div_pow]
  field_simp [pow_ne_zero term.1 hA]
  rw [← pow_sub_mul_pow (transportEvalUVTerms A U V) hi]
  ring

private theorem transportEvalSubstituteLinearXTerms_fold
    (degree : ℕ) (terms : List TransportXUVTerm)
    (A B answer : List TransportUVTerm) (U V : ℚ)
    (hdegree : ∀ term ∈ terms, term.1 ≤ degree)
    (hA : transportEvalUVTerms A U V ≠ 0) :
    transportEvalUVTerms
        (terms.foldl
          (fun result term =>
            transportAddUVTerms result
              (transportSubstituteLinearXTerm degree A B term))
          answer) U V =
      transportEvalUVTerms answer U V +
        transportEvalUVTerms A U V ^ degree *
          transportEvalXUVTerms terms
            (-transportEvalUVTerms B U V / transportEvalUVTerms A U V) U V := by
  induction terms generalizing answer with
  | nil =>
      simp [transportEvalXUVTerms, transportEvalUVTerms]
  | cons term rest ih =>
      rw [List.foldl_cons, ih]
      · rw [transportEvalAddUVTerms,
          transportEvalSubstituteLinearXTerm A B U V (hdegree term (by simp)) hA]
        simp only [transportEvalXUVTerms]
        ring
      · intro item hitem
        exact hdegree item (by simp [hitem])

theorem transportEvalSubstituteLinearXTerms
    (degree : ℕ) (terms : List TransportXUVTerm)
    (A B : List TransportUVTerm) (U V : ℚ)
    (hdegree : ∀ term ∈ terms, term.1 ≤ degree)
    (hA : transportEvalUVTerms A U V ≠ 0) :
    transportEvalUVTerms
        (transportSubstituteLinearXTerms degree terms A B) U V =
      transportEvalUVTerms A U V ^ degree *
        transportEvalXUVTerms terms
          (-transportEvalUVTerms B U V / transportEvalUVTerms A U V) U V := by
  rw [transportSubstituteLinearXTerms,
    transportEvalSubstituteLinearXTerms_fold degree terms A B [] U V hdegree hA]
  simp [transportEvalUVTerms]

end Cuboid2
