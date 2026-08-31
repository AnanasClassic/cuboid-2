import Cuboid2.DPlus.CantorTrace

/-!
# Specialized semantic Cantor arithmetic for `D+`

This is the public import for the fixed-curve presentation and the generated
exact trace identifying the stored rational Mumford output with `11D`.

The public endpoint is `dplusCantorClass_eleven_generator`.  Addition lives
only on the quotient `DPlusCantorClass`; raw `MumfordPair` values deliberately
have no synthetic group-law instance.
-/

namespace Cuboid2

namespace DPlusCantorModel

variable {G : Type*} [AddCommGroup G]

/--
Every semantic model respecting the checked fixed-curve Cantor rules
identifies the stored rational pair with eleven copies of the generator.
-/
theorem dplusElevenD_eq_eleven_generator
    (model : DPlusCantorModel G) :
    model.pairClass dplusElevenDCantorPair =
      11 • model.pairClass dplusGeneratorCantorPair := by
  rw [← model.dplusCantorLift_class,
    dplusCantorClass_eleven_generator, map_nsmul,
    model.dplusCantorLift_class]

end DPlusCantorModel

end Cuboid2
