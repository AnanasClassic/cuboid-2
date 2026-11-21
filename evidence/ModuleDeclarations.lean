import Cuboid2
import Cuboid2.AxiomAudit
import Cuboid2.Capell
import Cuboid2.CapellDegree
import Cuboid2.CapellFactor
import Cuboid2.CapellQuintic
import Cuboid2.Certificates.PositiveSumSquares
import Cuboid2.DPlus.AffineClassGroup
import Cuboid2.DPlus.Basic
import Cuboid2.DPlus.Cantor
import Cuboid2.DPlus.CantorSemantics
import Cuboid2.DPlus.CantorTrace
import Cuboid2.DPlus.DirectP3
import Cuboid2.DPlus.FiniteGroup
import Cuboid2.DPlus.FormalLogP3
import Cuboid2.DPlus.GlobalBridge
import Cuboid2.DPlus.GlobalCertificateInterface
import Cuboid2.DPlus.GlobalDescent
import Cuboid2.DPlus.GlobalKummer
import Cuboid2.DPlus.GlobalMumfordCertificate
import Cuboid2.DPlus.GlobalPointClass
import Cuboid2.DPlus.LocalP3
import Cuboid2.DPlus.LocalSeries
import Cuboid2.DPlus.Mumford
import Cuboid2.DPlus.Saturation
import Cuboid2.DPlus.SquareDiskReduction
import Cuboid2.Factorization
import Cuboid2.FactorizationClassification
import Cuboid2.FiveFive.Basic
import Cuboid2.FiveFive.DiscriminantIntervals
import Cuboid2.FiveFive.DiscriminantP28Local
import Cuboid2.FiveFive.DiscriminantP28Roots
import Cuboid2.FiveFive.DiscriminantP6Roots
import Cuboid2.FiveFive.DiscriminantRoots
import Cuboid2.FiveFive.Reduction
import Cuboid2.FiveFive.Resultant
import Cuboid2.FiveFive.ResultantCertificate
import Cuboid2.FiveFive.ResultantCritical
import Cuboid2.FiveFive.ResultantPolynomial
import Cuboid2.FiveFive.RootExclusion
import Cuboid2.FiveFive.RootTransport
import Cuboid2.FiveFive.SamplePositivity
import Cuboid2.FiveFive.SamplePositivity317
import Cuboid2.FiveFive.SamplePositivity40
import Cuboid2.FiveFive.SamplePositivity63
import Cuboid2.FiveFive.SamplePositivityMore
import Cuboid2.FiveFive.SamplePositivityReal
import Cuboid2.Genus2.FiniteMumford
import Cuboid2.Genus2.Mumford
import Cuboid2.LinearQuartic.Basic
import Cuboid2.LinearQuartic.ClassificationBridge
import Cuboid2.LinearQuartic.DescentCertificates
import Cuboid2.LinearQuartic.DescentCompletion
import Cuboid2.LinearQuartic.DirectSquareReduction
import Cuboid2.LinearQuartic.FermatAuxiliary
import Cuboid2.LinearQuartic.FiniteCounts
import Cuboid2.LinearQuartic.KnownPoints
import Cuboid2.LinearQuartic.LocalP5
import Cuboid2.LinearQuartic.RootMap
import Cuboid2.LinearQuartic.SharipovCompletion
import Cuboid2.LinearQuartic.SharipovImpossibility
import Cuboid2.LinearQuartic.SignedSquareCovers
import Cuboid2.Main
import Cuboid2.Polynomial
import Cuboid2.QuadraticReduction.C012
import Cuboid2.QuadraticReduction.CharacterDescent
import Cuboid2.QuadraticReduction.Characters
import Cuboid2.QuadraticReduction.CompactBoundary
import Cuboid2.QuadraticReduction.CompactModel
import Cuboid2.QuadraticReduction.Completion
import Cuboid2.QuadraticReduction.ExceptionalFibers
import Cuboid2.QuadraticReduction.Extraction
import Cuboid2.QuadraticReduction.GaussianActualTorsion
import Cuboid2.QuadraticReduction.GaussianArithmetic
import Cuboid2.QuadraticReduction.GaussianClassification
import Cuboid2.QuadraticReduction.GaussianCompletion
import Cuboid2.QuadraticReduction.GaussianCover
import Cuboid2.QuadraticReduction.GaussianCoverOneCompletion
import Cuboid2.QuadraticReduction.GaussianCoverReductionActual
import Cuboid2.QuadraticReduction.GaussianCoverZeroIndexPair
import Cuboid2.QuadraticReduction.GaussianCoverZeroRowCompletion
import Cuboid2.QuadraticReduction.GaussianCoverZeroTranslationActual
import Cuboid2.QuadraticReduction.GaussianDescent
import Cuboid2.QuadraticReduction.GaussianDualTranslation
import Cuboid2.QuadraticReduction.GaussianE1LocalReduction
import Cuboid2.QuadraticReduction.GaussianE1Split37ReductionActual
import Cuboid2.QuadraticReduction.GaussianExactRanges
import Cuboid2.QuadraticReduction.GaussianFinite
import Cuboid2.QuadraticReduction.GaussianFiniteExponent
import Cuboid2.QuadraticReduction.GaussianFormalKernelDisk
import Cuboid2.QuadraticReduction.GaussianFormalKernelTorsion
import Cuboid2.QuadraticReduction.GaussianFormalLocal
import Cuboid2.QuadraticReduction.GaussianFraction
import Cuboid2.QuadraticReduction.GaussianGlobal
import Cuboid2.QuadraticReduction.GaussianGoodReduction
import Cuboid2.QuadraticReduction.GaussianHeight
import Cuboid2.QuadraticReduction.GaussianIndexCoprime
import Cuboid2.QuadraticReduction.GaussianIndexIndependent
import Cuboid2.QuadraticReduction.GaussianIndexIndependentReduction
import Cuboid2.QuadraticReduction.GaussianLocalMapInjective
import Cuboid2.QuadraticReduction.GaussianMordellWeil
import Cuboid2.QuadraticReduction.GaussianObstructionBridge
import Cuboid2.QuadraticReduction.GaussianP29PolynomialRootBridge
import Cuboid2.QuadraticReduction.GaussianP29SaturationActual
import Cuboid2.QuadraticReduction.GaussianP37
import Cuboid2.QuadraticReduction.GaussianP37ActualTrace
import Cuboid2.QuadraticReduction.GaussianP37Bridge
import Cuboid2.QuadraticReduction.GaussianP37IndexSaturationActual
import Cuboid2.QuadraticReduction.GaussianP37SaturationActual
import Cuboid2.QuadraticReduction.GaussianPairedFormalNorm
import Cuboid2.QuadraticReduction.GaussianPrimes
import Cuboid2.QuadraticReduction.GaussianProjectiveReduction
import Cuboid2.QuadraticReduction.GaussianProjectiveReductionHom
import Cuboid2.QuadraticReduction.GaussianRange
import Cuboid2.QuadraticReduction.GaussianRankArithmetic
import Cuboid2.QuadraticReduction.GaussianRationalFormalUniqueness
import Cuboid2.QuadraticReduction.GaussianReductionSurjective
import Cuboid2.QuadraticReduction.GaussianSaturationBridge
import Cuboid2.QuadraticReduction.GaussianSaturationFinite
import Cuboid2.QuadraticReduction.GaussianSession1Completion
import Cuboid2.QuadraticReduction.GaussianSplit
import Cuboid2.QuadraticReduction.GaussianSplit37ReductionActual
import Cuboid2.QuadraticReduction.GaussianSupport
import Cuboid2.QuadraticReduction.GaussianThreeTorsion
import Cuboid2.QuadraticReduction.GaussianTorsionNormalForm
import Cuboid2.QuadraticReduction.GaussianTorsionReduction
import Cuboid2.QuadraticReduction.GaussianTranslationSeparation
import Cuboid2.QuadraticReduction.GaussianTwoTorsion
import Cuboid2.QuadraticReduction.GaussianUFD
import Cuboid2.QuadraticReduction.GaussianVisibleReduction
import Cuboid2.QuadraticReduction.GaussianWeakMW
import Cuboid2.QuadraticReduction.ProjectionCertificate
import Cuboid2.QuadraticReduction.ProjectionCertificateNegative
import Cuboid2.QuadraticReduction.QuotientInverse
import Cuboid2.QuadraticReduction.QuotientTransport
import Cuboid2.QuadraticReduction.Reciprocal
import Cuboid2.QuadraticReduction.SignedSquare
import Cuboid2.QuadraticReduction.SquareclassDescent
import Cuboid2.QuadraticReduction.TransportCertificateData
import Cuboid2.QuadraticReduction.TransportCompletion
import Cuboid2.QuadraticReduction.TransportExceptionData
import Cuboid2.QuadraticReduction.TransportExceptions
import Cuboid2.QuadraticReduction.TransportPolynomial
import Cuboid2.QuadraticReduction.ValuationDescent
import Cuboid2.Scaling

import Lean
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut projectCount : Nat := 0
  let mut nativeCount : Nat := 0
  let mut unexpectedAxioms := #[]
  let mut opaqueDecls := #[]
  for owner in env.allImportedModuleNames do
    unless (`Cuboid2).isPrefixOf owner do continue
    let some idx := env.getModuleIdx? owner | throwError m!"Missing imported module {owner}"
    let md := env.header.moduleData[idx.toNat]!
    for name in md.constNames, info in md.constants do
      projectCount := projectCount + 1
      match info with
      | .axiomInfo decl =>
        if name.toString.contains "._native.native_decide.ax_" then
          nativeCount := nativeCount + 1
        else
          unexpectedAxioms := unexpectedAxioms.push (owner, decl.name)
      | .opaqueInfo decl => opaqueDecls := opaqueDecls.push (owner, decl.name)
      | _ => pure ()
  logInfo m!"Project-owned compiled declarations = {projectCount}. Generated native computation axioms = {nativeCount}. Other axiom declarations = {unexpectedAxioms.size}. Explicit kernel opaque declarations = {opaqueDecls.size}."
  for (owner, name) in unexpectedAxioms do logInfo m!"AXIOM {owner} {name}"
  for (owner, name) in opaqueDecls do logInfo m!"OPAQUE {owner} {name}"
