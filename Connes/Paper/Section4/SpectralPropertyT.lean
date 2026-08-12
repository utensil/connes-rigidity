/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Concrete Zhou §4 wrappers for the positive scalar spectral bridge.  The
analytic spectral measures are constructed by joint functional calculus, so
the only paper-specific input is finite spectral detection. Paper: §4.
-/
import Connes.Paper.Section4.PropertyT
import Connes.Paper.Section4.SplitExtensions
import Connes.Paper.Section4.FiniteExtensions
import Connes.Foundation.OperatorAlgebra.PositiveSpectralMeasure
import Connes.Paper.Section3.DualHaar

namespace Connes
namespace PaperSpectralPropertyT

open Construction
open Construction.PaperKernel
open PaperPropertyT

noncomputable section

/-- Borel structure on the raw compact character carrier used by §4. Paper: §4. -/
noncomputable instance paperRawCharacterMeasurableSpace :
    MeasurableSpace (DiscreteCharacterSpace PaperKernel.D) :=
  borel (DiscreteCharacterSpace PaperKernel.D)

/-- The raw compact character carrier is a Borel space. Paper: §4. -/
instance paperRawCharacterBorelSpace :
    BorelSpace (DiscreteCharacterSpace PaperKernel.D) := ⟨rfl⟩

/-- Singletons are measurable in the paper's compact character space. Paper: §4. -/
instance paperRawCharacterMeasurableSingletonClass :
    MeasurableSingletonClass (DiscreteCharacterSpace PaperKernel.D) := by
  infer_instance

/-- The first actual split extension used by the spectral argument. Paper: §4. -/
noncomputable def lambdaOneExtension :
    SplitAbelianExtension PaperKernel.D
      (lambdaOneOf PaperKernel.paperActionData) SpecialLinear.sl3Group :=
  PaperSplitExtensions.lambdaOne PaperKernel.paperActionData

/-- The second actual split extension used by the spectral argument. Paper: §4. -/
noncomputable def lambdaTwoExtension :
    SplitAbelianExtension PaperKernel.D
      (lambdaTwoOf PaperKernel.paperActionData) SpecialLinear.sl3Group :=
  PaperSplitExtensions.lambdaTwo PaperKernel.paperActionData

/-- Spectral data for the first concrete intermediate group. Paper: §4. -/
structure LambdaOneSpectralData where
  J : Finset PaperKernel.D
  c : ℝ
  c_pos : 0 < c
  detection : HasFiniteSpectralDetection lambdaOneExtension J c

/-- Spectral data for the second concrete intermediate group. Paper: §4. -/
structure LambdaTwoSpectralData where
  J : Finset PaperKernel.D
  c : ℝ
  c_pos : 0 < c
  detection : HasFiniteSpectralDetection lambdaTwoExtension J c

/-- The first concrete intermediate group is property-(T) from its spectral data. Paper: §4. -/
theorem lambdaOne_propertyT_of_spectralData
    (input : EJZKInput) (data : LambdaOneSpectralData) :
    HasKazhdanPropertyT (lambdaOneOf PaperKernel.paperActionData) := by
  exact spectral_criterion_unconditional
    lambdaOneExtension (sl3_propertyT_from_EJZK input)
      data.J data.c_pos data.detection

/-- The second concrete intermediate group is property-(T) from its spectral data. Paper: §4. -/
theorem lambdaTwo_propertyT_of_spectralData
    (input : EJZKInput) (data : LambdaTwoSpectralData) :
    HasKazhdanPropertyT (lambdaTwoOf PaperKernel.paperActionData) := by
  exact spectral_criterion_unconditional
    lambdaTwoExtension (sl3_propertyT_from_EJZK input)
      data.J data.c_pos data.detection

/-- Both concrete Zhou groups have property-(T) from the two spectral inputs. Paper: §4. -/
theorem completion_of_spectralData
    (input : EJZKInput)
    (dataOne : LambdaOneSpectralData)
    (dataTwo : LambdaTwoSpectralData) :
    HasKazhdanPropertyT
      (PaperKernel.paperGammaOneOf PaperKernel.paperActionData) ∧
      HasKazhdanPropertyT
        (PaperKernel.paperGammaTwoOf PaperKernel.paperActionData) := by
  exact ⟨
    PropertyTTransfer.hasKazhdanPropertyT_of_finiteExtension
      PaperFiniteExtensions.finiteExtensionOne
      (lambdaOne_propertyT_of_spectralData input dataOne)
      PaperPropertyT.finiteSymplecticGroup_propertyT,
    PropertyTTransfer.hasKazhdanPropertyT_of_finiteExtension
      PaperFiniteExtensions.finiteExtensionTwo
      (lambdaTwo_propertyT_of_spectralData input dataTwo)
      PaperPropertyT.finiteSymplecticGroup_propertyT⟩

end
end PaperSpectralPropertyT
end Connes
