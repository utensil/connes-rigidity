/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Concrete finite-index extension data for the Zhou semidirect products.
Paper: §4.
-/
import Connes.Paper.Section4.SplitExtensions

namespace Connes
namespace PaperFiniteExtensions

open Construction
open Construction.PaperKernel
open PaperPropertyT

noncomputable section

abbrev N := Multiplicative PaperKernel.D
abbrev S := SpecialLinear.SL3
abbrev Q := PaperKernel.Q
abbrev FullCarrier (action : H →* MulAut N) :=
  SemidirectProduct N H action
abbrev LambdaCarrier (action : H →* MulAut N) :=
  SemidirectProduct N S (action.comp sl3ToActingGroup)

/-- The finite quotient map records the Sp₄(F₂) coordinate. Paper: §4. -/
def quotientQ (action : H →* MulAut N) : FullCarrier action →* Q :=
  (MonoidHom.snd S Q).comp
    (SemidirectProduct.rightHom (N := N) (G := H) (φ := action))

theorem quotientQ_surjective (action : H →* MulAut N) :
    Function.Surjective (quotientQ action) := by
  intro q
  refine ⟨SemidirectProduct.inr (1, q), ?_⟩
  rfl

/-- The intermediate semidirect product embeds as the kernel of the finite quotient. Paper: §4. -/
def liftLambda (action : H →* MulAut N) :
    LambdaCarrier action →* FullCarrier action :=
  SemidirectProduct.map (MonoidHom.id N) sl3ToActingGroup (by
    intro s
    rfl)

/-- The intermediate group is identified with the finite-index kernel. Paper: §4. -/
def lambdaToSubgroup (action : H →* MulAut N) :
    LambdaCarrier action ≃* (quotientQ action).ker where
  toFun x := ⟨liftLambda action x, by
    apply MonoidHom.mem_ker.mpr
    rfl⟩
  invFun x := ⟨x.1.left, x.1.right.1⟩
  left_inv x := by
    apply SemidirectProduct.ext <;> rfl
  right_inv x := by
    apply Subtype.ext
    change (⟨x.1.left, (x.1.right.1, 1)⟩ : FullCarrier action) = x.1
    apply SemidirectProduct.ext
    · rfl
    · apply Prod.ext
      · rfl
      · have hx := MonoidHom.mem_ker.mp x.property
        change x.1.right.2 = 1 at hx
        exact hx.symm
  map_mul' x y := by
    apply Subtype.ext
    exact (liftLambda action).map_mul x y

private theorem quotient_finite (action : H →* MulAut N) :
    Finite ((FullCarrier action) ⧸ (quotientQ action).ker) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective
    (quotientQ action) (quotientQ_surjective action)
  exact Finite.of_injective (fun x => e x) e.injective

/-- The first finite extension in Zhou Proposition 4.8 is concrete. Paper: §4. -/
def finiteExtensionOne :
    PropertyTTransfer.FiniteExtensionData
      (lambdaOneOf PaperKernel.paperActionData)
      (PaperKernel.paperGammaOneOf PaperKernel.paperActionData)
      finiteSymplecticGroup := by
  let Nq := (quotientQ PaperKernel.paperThetaOneHom).ker
  let hN : Nq.Normal := (quotientQ PaperKernel.paperThetaOneHom).normal_ker
  letI : Finite ((PaperKernel.paperGammaOneOf PaperKernel.paperActionData : Type) ⧸ Nq) := by
    exact quotient_finite PaperKernel.paperThetaOneHom
  have hindex : Nq.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  have hquotient :
      CountableDiscreteGroup.quotient
          (PaperKernel.paperGammaOneOf PaperKernel.paperActionData) Nq hN ≃*
        finiteSymplecticGroup := by
    change ((PaperKernel.paperGammaOneOf PaperKernel.paperActionData : Type) ⧸ Nq) ≃*
      (Q : Type)
    exact QuotientGroup.quotientKerEquivOfSurjective
      (quotientQ PaperKernel.paperThetaOneHom)
      (quotientQ_surjective PaperKernel.paperThetaOneHom)
  exact {
    subgroup := Nq
    normal := hN
    finiteIndex := hindex
    subgroupEquiv := lambdaToSubgroup PaperKernel.paperThetaOneHom
    quotientEquiv := hquotient }

/-- The second finite extension in Zhou Proposition 4.8 is concrete. Paper: §4. -/
def finiteExtensionTwo :
    PropertyTTransfer.FiniteExtensionData
      (lambdaTwoOf PaperKernel.paperActionData)
      (PaperKernel.paperGammaTwoOf PaperKernel.paperActionData)
      finiteSymplecticGroup := by
  let Nq := (quotientQ PaperKernel.paperThetaTwoHom).ker
  let hN : Nq.Normal := (quotientQ PaperKernel.paperThetaTwoHom).normal_ker
  letI : Finite ((PaperKernel.paperGammaTwoOf PaperKernel.paperActionData : Type) ⧸ Nq) := by
    exact quotient_finite PaperKernel.paperThetaTwoHom
  have hindex : Nq.FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  have hquotient :
      CountableDiscreteGroup.quotient
          (PaperKernel.paperGammaTwoOf PaperKernel.paperActionData) Nq hN ≃*
        finiteSymplecticGroup := by
    change ((PaperKernel.paperGammaTwoOf PaperKernel.paperActionData : Type) ⧸ Nq) ≃*
      (Q : Type)
    exact QuotientGroup.quotientKerEquivOfSurjective
      (quotientQ PaperKernel.paperThetaTwoHom)
      (quotientQ_surjective PaperKernel.paperThetaTwoHom)
  exact {
    subgroup := Nq
    normal := hN
    finiteIndex := hindex
    subgroupEquiv := lambdaToSubgroup PaperKernel.paperThetaTwoHom
    quotientEquiv := hquotient }

end
end PaperFiniteExtensions
end Connes
