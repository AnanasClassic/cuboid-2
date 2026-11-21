import Cuboid2.Main
import Lean.Util.CollectAxioms

open Lean Elab Command

example {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (cop : Nat.Coprime p q) (ne : p ≠ q) :
    Irreducible (Cuboid2.sharipovPolynomial p q : Polynomial ℤ) :=
  Cuboid2.sharipov_second_cuboid_conjecture hp hq cop ne

example (p q : ℕ) : (Cuboid2.sharipovPolynomial p q).natDegree = 10 :=
  Cuboid2.sharipovPolynomial_natDegree p q

run_cmd do
  let env ← getEnv
  let foundation := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``Cuboid2.linear_quartic_impossible, ``Cuboid2.quadratic_cubic_impossible,
      ``Cuboid2.symmetric_five_five_impossible, ``Cuboid2.sharipov_second_cuboid_conjecture] do
    let axioms ← collectAxioms name
    let mut nativeCount := 0
    for ax in axioms do
      if foundation.contains ax then continue
      unless ax.toString.contains "._native.native_decide.ax_" do
        throwError m!"Unexpected axiom {ax}"
      let some (.axiomInfo decl) := env.find? ax | throwError m!"Missing axiom {ax}"
      let type := decl.type
      let args := type.getAppArgs
      unless type.isAppOfArity ``Eq 3 && args[0]!.isConstOf ``Bool &&
          args[2]!.isConstOf ``Bool.true && args[1]!.isAppOf ``decide &&
          !type.hasFVar && !type.hasMVar && !type.hasLooseBVars do
        throwError m!"Unexpected computation certificate type for {ax}: {type}"
      nativeCount := nativeCount + 1
    logInfo m!"{name}: {axioms.size} total axioms, {nativeCount} closed decide expressions certified by native computation; foundations: {axioms.filter foundation.contains}"
