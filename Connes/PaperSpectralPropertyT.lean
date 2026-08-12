/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Concrete Zhou §4 wrappers for the positive scalar spectral bridge.  The
analytic spectral measures are constructed by joint functional calculus, so
the only paper-specific input is finite spectral detection. Paper: §4.
-/
import Connes.PaperPropertyT
import Connes.PaperSplitExtensions
import Connes.PaperFiniteExtensions
import Connes.Foundation.OperatorAlgebra.PositiveSpectralMeasure
import Connes.Foundation.OperatorAlgebra.PaperDualHaar

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

/-- Normality of the first kernel subgroup follows from the quotient map. Paper: §4. -/
theorem lambdaOneKernelNormal :
    (lambdaOneKernelSubgroup PaperKernel.paperActionData).Normal := by
  change (SemidirectProduct.rightHom
    (N := Multiplicative PaperKernel.D)
    (G := SpecialLinear.SL3)
    (φ := PaperKernel.paperThetaOneHom.comp
      (PaperPropertyT.sl3ToActingGroup))).ker.Normal
  exact (SemidirectProduct.rightHom
    (N := Multiplicative PaperKernel.D)
    (G := SpecialLinear.SL3)
    (φ := PaperKernel.paperThetaOneHom.comp
      (PaperPropertyT.sl3ToActingGroup))).normal_ker

/-- Normality of the second kernel subgroup follows from the quotient map. Paper: §4. -/
theorem lambdaTwoKernelNormal :
    (lambdaTwoKernelSubgroup PaperKernel.paperActionData).Normal := by
  change (SemidirectProduct.rightHom
    (N := Multiplicative PaperKernel.D)
    (G := SpecialLinear.SL3)
    (φ := PaperKernel.paperThetaTwoHom.comp
      (PaperPropertyT.sl3ToActingGroup))).ker.Normal
  exact (SemidirectProduct.rightHom
    (N := Multiplicative PaperKernel.D)
    (G := SpecialLinear.SL3)
    (φ := PaperKernel.paperThetaTwoHom.comp
      (PaperPropertyT.sl3ToActingGroup))).normal_ker

/-- A group property-(T) representation supplies the relative fixed vector. Paper: §4. -/
theorem relativePropertyT_of_propertyT
    (G : CountableDiscreteGroup) (N : Subgroup G)
    (hG : HasKazhdanPropertyT G) :
    HasRelativePropertyT G N := by
  intro K _ _ _ π hπ
  obtain ⟨ξ, hξ, hinv⟩ :=
    hG K inferInstance inferInstance inferInstance π hπ
  refine ⟨ξ, hξ, ?_⟩
  intro n
  exact hinv (n : G)

/-- The first split quotient identifies with the actual SL₃ group. Paper: §4. -/
def lambdaOneQuotientEquiv :
    CountableDiscreteGroup.quotient
        (lambdaOneOf PaperKernel.paperActionData)
        (lambdaOneKernelSubgroup PaperKernel.paperActionData)
        lambdaOneKernelNormal ≃*
      SpecialLinear.sl3Group := by
  let E := lambdaOneExtension
  have hker : E.quotient.ker =
      lambdaOneKernelSubgroup PaperKernel.paperActionData := by
    rfl
  let hsurj : Function.Surjective E.quotient := by
    intro h
    exact ⟨E.splitting h,
      SplitAbelianExtension.quotient_splitting_apply E h⟩
  letI : (lambdaOneKernelSubgroup PaperKernel.paperActionData).Normal :=
    lambdaOneKernelNormal
  change ((lambdaOneOf PaperKernel.paperActionData : Type) ⧸
      lambdaOneKernelSubgroup PaperKernel.paperActionData) ≃*
    (SpecialLinear.sl3Group : Type)
  exact QuotientGroup.quotientKerEquivOfSurjective E.quotient hsurj

/-- The second split quotient identifies with the actual SL₃ group. Paper: §4. -/
def lambdaTwoQuotientEquiv :
    CountableDiscreteGroup.quotient
        (lambdaTwoOf PaperKernel.paperActionData)
        (lambdaTwoKernelSubgroup PaperKernel.paperActionData)
        lambdaTwoKernelNormal ≃*
      SpecialLinear.sl3Group := by
  let E := lambdaTwoExtension
  have hker : E.quotient.ker =
      lambdaTwoKernelSubgroup PaperKernel.paperActionData := by
    rfl
  let hsurj : Function.Surjective E.quotient := by
    intro h
    exact ⟨E.splitting h,
      SplitAbelianExtension.quotient_splitting_apply E h⟩
  letI : (lambdaTwoKernelSubgroup PaperKernel.paperActionData).Normal :=
    lambdaTwoKernelNormal
  change ((lambdaTwoOf PaperKernel.paperActionData : Type) ⧸
      lambdaTwoKernelSubgroup PaperKernel.paperActionData) ≃*
    (SpecialLinear.sl3Group : Type)
  exact QuotientGroup.quotientKerEquivOfSurjective E.quotient hsurj

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
    lambdaOneExtension input.propertyT data.J data.c_pos data.detection

/-- The second concrete intermediate group is property-(T) from its spectral data. Paper: §4. -/
theorem lambdaTwo_propertyT_of_spectralData
    (input : EJZKInput) (data : LambdaTwoSpectralData) :
    HasKazhdanPropertyT (lambdaTwoOf PaperKernel.paperActionData) := by
  exact spectral_criterion_unconditional
    lambdaTwoExtension input.propertyT data.J data.c_pos data.detection

/-- Build the first relative transfer record from its stronger spectral conclusion. Paper: §4. -/
def lambdaOneRelativeData_of_spectralData
    (input : EJZKInput) (data : LambdaOneSpectralData) :
    PropertyTTransfer.RelativeExtensionData
      (lambdaOneOf PaperKernel.paperActionData) SpecialLinear.sl3Group
      (lambdaOneKernelSubgroup PaperKernel.paperActionData) where
  normal := lambdaOneKernelNormal
  relative := relativePropertyT_of_propertyT
    (lambdaOneOf PaperKernel.paperActionData)
    (lambdaOneKernelSubgroup PaperKernel.paperActionData)
    (lambdaOne_propertyT_of_spectralData input data)
  quotientEquiv := lambdaOneQuotientEquiv

/-- Build the second relative transfer record from its stronger spectral conclusion. Paper: §4. -/
def lambdaTwoRelativeData_of_spectralData
    (input : EJZKInput) (data : LambdaTwoSpectralData) :
    PropertyTTransfer.RelativeExtensionData
      (lambdaTwoOf PaperKernel.paperActionData) SpecialLinear.sl3Group
      (lambdaTwoKernelSubgroup PaperKernel.paperActionData) where
  normal := lambdaTwoKernelNormal
  relative := relativePropertyT_of_propertyT
    (lambdaTwoOf PaperKernel.paperActionData)
    (lambdaTwoKernelSubgroup PaperKernel.paperActionData)
    (lambdaTwo_propertyT_of_spectralData input data)
  quotientEquiv := lambdaTwoQuotientEquiv

/-- Assemble the full concrete §4 transfer data from both spectral inputs. Paper: §4. -/
def propertyTData_of_spectralData
    (input : EJZKInput)
    (dataOne : LambdaOneSpectralData)
    (dataTwo : LambdaTwoSpectralData) :
    PaperPropertyT.Data PaperKernel.paperActionData where
  lambdaOne := lambdaOneRelativeData_of_spectralData input dataOne
  lambdaTwo := lambdaTwoRelativeData_of_spectralData input dataTwo
  gammaOne := PaperFiniteExtensions.finiteExtensionOne
  gammaTwo := PaperFiniteExtensions.finiteExtensionTwo

/-- Both concrete Zhou groups have property-(T) from the two spectral inputs. Paper: §4. -/
theorem completion_of_spectralData
    (input : EJZKInput)
    (dataOne : LambdaOneSpectralData)
    (dataTwo : LambdaTwoSpectralData) :
    HasKazhdanPropertyT
      (PaperKernel.paperGammaOneOf PaperKernel.paperActionData) ∧
      HasKazhdanPropertyT
        (PaperKernel.paperGammaTwoOf PaperKernel.paperActionData) := by
  exact PaperPropertyT.completion PaperKernel.paperActionData input
    (propertyTData_of_spectralData input dataOne dataTwo)

end
end PaperSpectralPropertyT
end Connes
