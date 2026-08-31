import Cuboid2.FiveFive.Resultant

/-!
# Explicit Bézout certificate for the `5+5` resultant

The three expressions below are finite integer data.  The identity

`U*G₂ + V*G₃ = F`

is checked by `ring`; no correctness property of the script that generated
these coefficients is trusted.
-/

namespace Cuboid2

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- The primitive 104-term resultant factor after removing `s^2`. -/
def fiveFiveResultantFactor (s y : ℚ) : ℚ :=
  256*s^12*y^8 - 17408*s^12*y^6 + 411136*s^12*y^4 - 3916800*s^12*y^2 + 12960000*s^12 - 256*s^11*y^10
  + 13056*s^11*y^8 - 223744*s^11*y^6 + 4096*s^11*y^5 + 1459712*s^11*y^4 + 122880*s^11*y^3 + 2157312*s^11*y^2
  - 3010560*s^11*y - 30931200*s^11 + 96*s^10*y^12 - 3392*s^10*y^10 + 33696*s^10*y^8 - 4096*s^10*y^7
  + 102016*s^10*y^6 - 159744*s^10*y^5 - 4870752*s^10*y^4 + 2347008*s^10*y^3 + 23243456*s^10*y^2
  + 12288*s^10*y - 16244128*s^10 - 16*s^9*y^14 + 336*s^9*y^12 + 1264*s^9*y^10 + 2304*s^9*y^9 - 97072*s^9*y^8
  + 11264*s^9*y^7 + 1108816*s^9*y^6 - 133632*s^9*y^5 - 1995408*s^9*y^4 - 4035584*s^9*y^3 - 24547376*s^9*y^2
  + 14575872*s^9*y + 96898160*s^9 + s^8*y^16 - 8*s^8*y^14 - 708*s^8*y^12 - 384*s^8*y^11 + 13832*s^8*y^10
  + 1152*s^8*y^9 - 57306*s^8*y^8 + 13568*s^8*y^7 - 918712*s^8*y^6 + 558336*s^8*y^5 + 12098300*s^8*y^4
  - 2945920*s^8*y^3 - 33596872*s^8*y^2 - 9259392*s^8*y - 41403359*s^8 + 48*s^7*y^14 - 496*s^7*y^12
  - 10448*s^7*y^10 - 6912*s^7*y^9 + 227728*s^7*y^8 - 1024*s^7*y^7 - 1410544*s^7*y^6 - 41472*s^7*y^5
  - 3155536*s^7*y^4 + 7126016*s^7*y^3 + 54808208*s^7*y^2 - 16972544*s^7*y - 100331856*s^7 + 992*s^6*y^12
  - 11840*s^6*y^10 - 52192*s^6*y^8 - 28672*s^6*y^7 + 1855616*s^6*y^6 - 397312*s^6*y^5 - 11363808*s^6*y^4
  - 643072*s^6*y^3 + 6052288*s^6*y^2 + 17420288*s^6*y + 93598176*s^6 + 11520*s^5*y^10 - 145152*s^5*y^8
  + 160256*s^5*y^6 + 135168*s^5*y^5 + 7660032*s^5*y^4 - 3284992*s^5*y^3 - 43654912*s^5*y^2 + 3018752*s^5*y
  + 26662144*s^5 + 82176*s^4*y^8 - 1000448*s^4*y^6 + 2688512*s^4*y^4 + 1245184*s^4*y^3 + 16301056*s^4*y^2
  - 8192000*s^4*y - 61456128*s^4 + 368640*s^3*y^6 - 3907584*s^3*y^4 + 9723904*s^3*y^2 + 2359296*s^3*y
  + 14524416*s^3 + 1015808*s^2*y^4 - 8060928*s^2*y^2 + 11501568*s^2 + 1572864*s*y^2 - 6815744*s + 1048576

/-- First numerator in the exact Bézout identity. -/
def fiveFiveBezoutU (s y z : ℚ) : ℚ :=
  -64*s^9*y^6 + 384*s^9*y^5 + 3136*s^9*y^4 - 13056*s^9*y^3 - 47040*s^9*y^2 + 86400*s^9*y + 216000*s^9
  + 48*s^8*y^8 - 192*s^8*y^7 - 1600*s^8*y^6 + 64*s^8*y^5*z^2 + 3200*s^8*y^5 + 384*s^8*y^4*z + 14496*s^8*y^4
  - 2176*s^8*y^3*z^2 - 1536*s^8*y^3*z - 12480*s^8*y^3 - 4352*s^8*y^2*z + 1728*s^8*y^2 + 14400*s^8*y*z^2
  - 23040*s^8*y*z - 183040*s^8*y - 28800*s^8*z - 375120*s^8 - 12*s^7*y^10 + 24*s^7*y^9 + 228*s^7*y^8
  - 32*s^7*y^7*z^2 - 64*s^7*y^7 - 320*s^7*y^6*z + 104*s^7*y^6 + 544*s^7*y^5*z^2 + 1152*s^7*y^5*z
  - 3472*s^7*y^5 + 3264*s^7*y^4*z - 32664*s^7*y^4 - 256*s^7*y^3*z^3 - 2272*s^7*y^3*z^2 - 512*s^7*y^3*z
  + 78464*s^7*y^3 - 256*s^7*y^2*z^2 - 4544*s^7*y^2*z + 228260*s^7*y^2 - 3840*s^7*y*z^3 - 20256*s^7*y*z^2
  + 18816*s^7*y*z - 123592*s^7*y + 3840*s^7*z^2 + 31296*s^7*z - 329548*s^7 + s^6*y^12 - 6*s^6*y^10
  + 4*s^6*y^9*z^2 - 4*s^6*y^9 + 56*s^6*y^8*z - 393*s^6*y^8 - 16*s^6*y^7*z^2 + 144*s^6*y^7 - 160*s^6*y^6*z
  + 6348*s^6*y^6 + 192*s^6*y^5*z^3 - 680*s^6*y^5*z^2 - 192*s^6*y^5*z - 3416*s^6*y^5 + 576*s^6*y^4*z^2
  - 4080*s^6*y^4*z - 23873*s^6*y^4 - 128*s^6*y^3*z^3 + 7024*s^6*y^3*z^2 + 6272*s^6*y^3*z - 18672*s^6*y^3
  - 128*s^6*y^2*z^2 + 14048*s^6*y^2*z - 146342*s^6*y^2 + 2496*s^6*y*z^3 - 18620*s^6*y*z^2 + 25152*s^6*y*z
  + 440764*s^6*y - 512*s^6*z^3 - 2496*s^6*z^2 + 38776*s^6*z + 964009*s^6 + 36*s^5*y^10 - 8*s^5*y^9
  - 300*s^5*y^8 + 96*s^5*y^7*z^2 - 64*s^5*y^7 + 960*s^5*y^6*z - 3640*s^5*y^6 - 608*s^5*y^5*z^2
  - 384*s^5*y^5*z + 3120*s^5*y^5 - 3648*s^5*y^4*z + 66248*s^5*y^4 + 768*s^5*y^3*z^3 - 352*s^5*y^3*z^2
  - 512*s^5*y^3*z - 71808*s^5*y^3 + 768*s^5*y^2*z^2 - 704*s^5*y^2*z - 264684*s^5*y^2 + 3328*s^5*y*z^3
  + 32096*s^5*y*z^2 - 20608*s^5*y*z - 69992*s^5*y - 3328*s^5*z^2 - 61120*s^5*z - 146332*s^5 + 528*s^4*y^8
  - 192*s^4*y^7 - 5056*s^4*y^6 + 832*s^4*y^5*z^2 + 384*s^4*y^5 + 4992*s^4*y^4*z - 6688*s^4*y^4
  - 5760*s^4*y^3*z^2 - 1536*s^4*y^3*z + 32064*s^4*y^3 - 11520*s^4*y^2*z + 273728*s^4*y^2 - 2048*s^4*y*z^3
  + 832*s^4*y*z^2 - 4608*s^4*y*z - 278016*s^4*y + 2048*s^4*z^2 - 1664*s^4*z - 760176*s^4 + 4032*s^3*y^6
  - 1664*s^3*y^5 - 37824*s^3*y^4 + 3072*s^3*y^3*z^2 + 8448*s^3*y^3 + 6144*s^3*y^2*z + 47168*s^3*y^2
  - 13312*s^3*y*z^2 + 4096*s^3*y*z + 109952*s^3*y + 26624*s^3*z + 424896*s^3 + 16896*s^2*y^4 - 6144*s^2*y^3
  - 128000*s^2*y^2 + 4096*s^2*y*z^2 + 22528*s^2*y - 8192*s^2*z + 139776*s^2 + 36864*s*y^2 - 8192*s*y
  - 159744*s + 32768

/-- Second numerator in the exact Bézout identity. -/
def fiveFiveBezoutV (s y z : ℚ) : ℚ :=
  -256*s^9*y^6 + 8704*s^9*y^4 - 57600*s^9*y^2 + 128*s^8*y^8 - 2176*s^8*y^6 + 1024*s^8*y^4*z + 9088*s^8*y^4
  - 1024*s^8*y^3 + 15360*s^8*y^2*z + 81024*s^8*y^2 - 46080*s^8*y - 16*s^7*y^10 + 64*s^7*y^8 - 768*s^7*y^6*z
  + 2720*s^7*y^6 - 768*s^7*y^5 + 512*s^7*y^4*z - 28096*s^7*y^4 - 512*s^7*y^3 - 9984*s^7*y^2*z
  + 74480*s^7*y^2 + 2048*s^7*y*z + 29952*s^7*y - 4096*s^7 - 384*s^6*y^8 + 2432*s^6*y^6 - 3072*s^6*y^4*z
  + 1408*s^6*y^4 + 3072*s^6*y^3 - 13312*s^6*y^2*z - 128384*s^6*y^2 + 39936*s^6*y - 3328*s^5*y^6
  + 23040*s^5*y^4 + 8192*s^5*y^2*z - 3328*s^5*y^2 - 24576*s^5*y - 12288*s^4*y^4 + 53248*s^4*y^2
  - 16384*s^3*y^2

/-- Kernel-checkable multiplication-back certificate. -/
theorem fiveFive_bezout_identity (s y z : ℚ) :
    fiveFiveBezoutU s y z * fiveFiveG2 s y z +
      fiveFiveBezoutV s y z * fiveFiveG3 s y z =
        fiveFiveResultantFactor s y := by
  unfold fiveFiveBezoutU fiveFiveBezoutV fiveFiveG2 fiveFiveG3
    fiveFiveResultantFactor
  ring

/-- Every common root lies on the explicit 104-term scalar curve. -/
theorem fiveFiveResultantFactor_eq_zero_of_common_root
    {s y z : ℚ}
    (hg2 : fiveFiveG2 s y z = 0)
    (hg3 : fiveFiveG3 s y z = 0) :
    fiveFiveResultantFactor s y = 0 := by
  rw [← fiveFive_bezout_identity s y z, hg2, hg3]
  ring

/-- Every normalized `5+5` point lies on the explicit scalar curve. -/
theorem FiveFiveReducedPoint.resultantFactor_eq_zero
    {s : ℚ} (P : FiveFiveReducedPoint s) :
    fiveFiveResultantFactor s P.y = 0 :=
  fiveFiveResultantFactor_eq_zero_of_common_root P.g2 P.g3

end

end Cuboid2
