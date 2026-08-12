/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Paper-facing non-isomorphism target for Zhou §6. The previous file used
arbitrary `Prop` fields and the legacy carrier. Here the module predicates are
the actual `k[Sp₄(F₂)]` semisimplicity predicates on the two PaperKernel
actions; the characteristic-kernel argument is an explicit module-equivalence
input until the full §6 normal-subgroup proof is formalized.
-/
import Connes.Construction.PaperActionInstances
import Connes.Foundation.GroupTheory.Sp4
import Connes.Foundation.LinearAlgebra.Semisimple

namespace Connes
namespace PaperNonisomorphism

open Construction
open Construction.PaperKernel

noncomputable section

abbrev Q := PaperKernel.Q
abbrev D := PaperKernel.D
abbrev Ring := MonoidAlgebra k Q

/-- The quotient action map `Sp₄(F₂) → SL₃(R) × Sp₄(F₂)`. Paper: §§2, 6. -/
def qToH : Q →* H where
  toFun q := (1, q)
  map_one' := by rfl
  map_mul' p q := by simp

/-- The first quotient action on the actual additive kernel. Paper: §6. -/
def qLinearActionOne (actions : PaperKernel.ActionData) :
    Q →* (D ≃ₗ[k] D) :=
  PaperKernel.paperThetaOneLinearHom.comp qToH

/-- The second quotient action on the actual additive kernel. Paper: §6. -/
def qLinearActionTwo (actions : PaperKernel.ActionData) :
    Q →* (D ≃ₗ[k] D) :=
  PaperKernel.paperThetaTwoLinearHom.comp qToH

/-- Linear representation attached to the first actual quotient action. -/
def qRepresentationOne (actions : PaperKernel.ActionData) :
    Representation k Q D where
  toFun q := (qLinearActionOne actions q).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro d
    change (qLinearActionOne actions 1) d = d
    simpa using congrArg (fun e : D ≃ₗ[k] D => e d)
      (qLinearActionOne actions).map_one
  map_mul' p q := by
    apply LinearMap.ext
    intro d
    change (qLinearActionOne actions (p * q)) d =
      (qLinearActionOne actions p) ((qLinearActionOne actions q) d)
    simpa using congrArg (fun e : D ≃ₗ[k] D => e d)
      ((qLinearActionOne actions).map_mul p q)

/-- Linear representation attached to the second actual quotient action. -/
def qRepresentationTwo (actions : PaperKernel.ActionData) :
    Representation k Q D where
  toFun q := (qLinearActionTwo actions q).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro d
    change (qLinearActionTwo actions 1) d = d
    simpa using congrArg (fun e : D ≃ₗ[k] D => e d)
      (qLinearActionTwo actions).map_one
  map_mul' p q := by
    apply LinearMap.ext
    intro d
    change (qLinearActionTwo actions (p * q)) d =
      (qLinearActionTwo actions p) ((qLinearActionTwo actions q) d)
    simpa using congrArg (fun e : D ≃ₗ[k] D => e d)
      ((qLinearActionTwo actions).map_mul p q)

/-- Pull back the second quotient action along the quotient automorphism induced
by a hypothetical group isomorphism. Paper: §6. -/
def qRepresentationTwoAlong (actions : PaperKernel.ActionData)
    (σ : Q ≃* Q) : Representation k Q D where
  toFun q := qRepresentationTwo actions (σ q)
  map_one' := by
    apply LinearMap.ext
    intro d
    change (qRepresentationTwo actions (σ 1)) d = d
    rw [map_one]
    exact congrArg (fun e : D →ₗ[k] D => e d)
      (qRepresentationTwo actions).map_one
  map_mul' p q := by
    apply LinearMap.ext
    intro d
    change (qRepresentationTwo actions (σ (p * q))) d =
      (qRepresentationTwo actions (σ p))
        ((qRepresentationTwo actions (σ q)) d)
    rw [map_mul]
    exact congrArg (fun e : D →ₗ[k] D => e d)
      ((qRepresentationTwo actions).map_mul (σ p) (σ q))

noncomputable instance representationAsModuleAddCommGroup
    (ρ : Representation k Q D) : AddCommGroup ρ.asModule :=
  inferInstanceAs (AddCommGroup D)

/-- The actual first quotient module is semisimple over the group algebra. -/
def moduleOneSemisimple (actions : PaperKernel.ActionData) : Prop :=
  IsSemisimpleModule Ring (qRepresentationOne actions).asModule

/-- The actual second quotient module is semisimple over the group algebra. -/
def moduleTwoSemisimple (actions : PaperKernel.ActionData) : Prop :=
  IsSemisimpleModule Ring (qRepresentationTwo actions).asModule

/-- Semisimplicity predicate after the quotient automorphism from §6. -/
def moduleTwoSemisimpleAlong (actions : PaperKernel.ActionData)
    (σ : Q ≃* Q) : Prop :=
  IsSemisimpleModule Ring (qRepresentationTwoAlong actions σ).asModule

namespace FiniteCocycle

abbrev W := OpenAIPort.ModTwoSpace

/-- The finite quadratic correction appearing in the second action. Paper:
§2, §6. -/
def cocycle (q : Q) (v : W) : k :=
  OpenAIPort.standardQuadraticForm (q⁻¹ • v) +
    OpenAIPort.standardQuadraticForm v

/-- Linear coboundary predicate for the finite quotient correction. Paper: §6. -/
def IsLinearCoboundary : Prop :=
  ∃ f : W →ₗ[k] k, ∀ q v,
    cocycle q v = f (q⁻¹ • v) + f v

/-- A coordinate functional on the four-dimensional quotient module. Paper: §6. -/
def coordinateFunctional (c : W) (v : W) : k :=
  ∑ i, c i * v i

private theorem no_coordinate_coboundary :
    ¬ ∃ c : W, ∀ q v,
      cocycle q v = coordinateFunctional c (q⁻¹ • v) +
        coordinateFunctional c v := by
  rintro ⟨c, hc⟩
  let s : W → k := fun v =>
    OpenAIPort.standardQuadraticForm v + coordinateFunctional c v
  have hs_invariant : ∀ q : Q, ∀ v : W, s (q⁻¹ • v) = s v := by
    intro q v
    have h := hc q v
    change
      OpenAIPort.standardQuadraticForm (q⁻¹ • v) +
          OpenAIPort.standardQuadraticForm v =
        coordinateFunctional c (q⁻¹ • v) +
          coordinateFunctional c v at h
    dsimp [s]
    calc
      OpenAIPort.standardQuadraticForm (q⁻¹ • v) +
          coordinateFunctional c (q⁻¹ • v) =
        (OpenAIPort.standardQuadraticForm (q⁻¹ • v) +
          OpenAIPort.standardQuadraticForm v) +
          (OpenAIPort.standardQuadraticForm v +
            coordinateFunctional c (q⁻¹ • v)) := by
            rw [add_assoc, ← add_assoc
              (OpenAIPort.standardQuadraticForm v),
              CharTwo.add_self_eq_zero, zero_add]
      _ = (coordinateFunctional c (q⁻¹ • v) +
          coordinateFunctional c v) +
          (OpenAIPort.standardQuadraticForm v +
            coordinateFunctional c (q⁻¹ • v)) := by rw [h]
      _ = (coordinateFunctional c (q⁻¹ • v) +
            coordinateFunctional c (q⁻¹ • v)) +
          (coordinateFunctional c v +
            OpenAIPort.standardQuadraticForm v) := by ac_rfl
      _ = OpenAIPort.standardQuadraticForm v +
          coordinateFunctional c v := by
            rw [CharTwo.add_self_eq_zero, zero_add, add_comm]
  have hs_nonzero_constant {v w : W} (hv : v ≠ 0) (hw : w ≠ 0) :
      s v = s w := by
    obtain ⟨q, hq⟩ := Sp4.transitive_on_nonzero_vectors v hv w hw
    have h := hs_invariant q⁻¹ v
    simpa [hq] using h.symm
  let e0 : W := OpenAIPort.modTwoBasis (Sum.inl 0)
  let e1 : W := OpenAIPort.modTwoBasis (Sum.inl 1)
  let f0 : W := OpenAIPort.modTwoBasis (Sum.inr 0)
  have he0 : e0 ≠ 0 := by
    intro h
    have h' := congrFun h (Sum.inl 0)
    simp [e0, OpenAIPort.modTwoBasis] at h'
  have he1 : e1 ≠ 0 := by
    intro h
    have h' := congrFun h (Sum.inl 1)
    simp [e1, OpenAIPort.modTwoBasis] at h'
  have hf0 : f0 ≠ 0 := by
    intro h
    have h' := congrFun h (Sum.inr 0)
    simp [f0, OpenAIPort.modTwoBasis] at h'
  have he01 : e0 + e1 ≠ 0 := by
    intro h
    have h' := congrFun h (Sum.inl 0)
    simp [e0, e1, OpenAIPort.modTwoBasis, Pi.single_apply] at h'
  have he0f0 : e0 + f0 ≠ 0 := by
    intro h
    have h' := congrFun h (Sum.inl 0)
    simp [e0, f0, OpenAIPort.modTwoBasis, Pi.single_apply] at h'
  have h01 := hs_nonzero_constant he0 he1
  have h0sum := hs_nonzero_constant he0 he01
  have h0f := hs_nonzero_constant he0 hf0
  have h0pair := hs_nonzero_constant he0 he0f0
  dsimp [s, e0, e1, f0] at h01 h0sum h0f h0pair
  simp [OpenAIPort.standardQuadraticForm, OpenAIPort.modTwoBasis,
    coordinateFunctional, Pi.single_apply] at h01 h0sum h0f h0pair
  have hc0 : c (Sum.inl 0) = 0 := h01.trans h0sum
  have hcf0 : c (Sum.inr 0) = 0 := h0f.symm.trans hc0
  rw [hc0, hcf0] at h0pair
  norm_num at h0pair

/-- The finite correction is not a linear coboundary. This is the proved
four-dimensional obstruction used by the §6 module argument. Paper: §6. -/
theorem not_linearCoboundary : ¬ IsLinearCoboundary := by
  intro h
  obtain ⟨f, hf⟩ := h
  let c : W := fun i => f (Pi.single i 1)
  apply no_coordinate_coboundary
  refine ⟨c, ?_⟩
  intro q v
  have hrep : ∀ w : W, f w = coordinateFunctional c w := by
    intro w
    calc
      f w = f (∑ i, w i • (Pi.single i (1 : k))) := by
        congr 1
        ext j
        simp [Pi.single_apply]
      _ = ∑ i, f (w i • (Pi.single i (1 : k))) := by
        rw [map_sum]
      _ = ∑ i, w i * f (Pi.single i (1 : k)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, smul_eq_mul]
      _ = coordinateFunctional c w := by
        simp only [c, coordinateFunctional]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_comm]
  rw [hf q v, hrep, hrep]

end FiniteCocycle

@[simp] theorem finiteCocycle_eq (q : Q) (v : FiniteCocycle.W) :
    FiniteCocycle.cocycle q v =
      OpenAIPort.standardQuadraticForm (q⁻¹ • v) +
        OpenAIPort.standardQuadraticForm v := rfl

/-- The finite correction is not a linear coboundary. Paper: §6. -/
theorem finiteCocycle_not_linearCoboundary :
    ¬ FiniteCocycle.IsLinearCoboundary :=
  FiniteCocycle.not_linearCoboundary

/-- The actual second action contains the finite quadratic correction on the
quotient fiber. Paper: §2, §6. -/
theorem thetaTwo_q_correction
    (q : Q) (c : PaperKernel.C) :
    (PaperKernel.thetaTwoLinearMap (1, q) (0, c)).1 =
      PaperKernel.delta c ⊗ₜ[k] OpenAIPort.quadraticDefectLinear q := by
  have hc : PaperKernel.sl3CAction (1 : SpecialLinear.SL3) c = c := by
    have hm := PaperKernel.sl3CActionHom.map_one
    change PaperKernel.sl3CActionEquiv (1 : SpecialLinear.SL3) =
      LinearEquiv.refl k PaperKernel.C at hm
    exact congrArg (fun e : PaperKernel.C ≃ₗ[k] PaperKernel.C => e c) hm
  change avStarAction (1 : SpecialLinear.SL3) q 0 +
      PaperKernel.delta (sl3CAction (1 : SpecialLinear.SL3) c) ⊗ₜ[k]
        OpenAIPort.quadraticDefectLinear q =
    PaperKernel.delta c ⊗ₜ[k] OpenAIPort.quadraticDefectLinear q
  rw [hc]
  simp

/-- Exact §6 inputs after the characteristic subgroup has been identified.
The module equivalence is the output expected from the characteristic-kernel
and quotient-normality argument, rather than an unconstrained implication.
Paper: §6. -/
structure Data (actions : PaperKernel.ActionData) where
  moduleOne_semisimple : moduleOneSemisimple actions
  moduleTwo_not_semisimple_under_quotient :
    ∀ σ : Q ≃* Q, ¬ moduleTwoSemisimpleAlong actions σ
  characteristic_module_equiv :
    ∀ f : PaperKernel.paperGammaOneOf actions ≃*
      PaperKernel.paperGammaTwoOf actions, ∃ σ : Q ≃* Q,
      Nonempty ((qRepresentationOne actions).asModule ≃ₗ[Ring]
        (qRepresentationTwoAlong actions σ).asModule)

/-- The actual Zhou groups are not isomorphic once §6 supplies the module
equivalence induced by a hypothetical group isomorphism. Paper: §6. -/
theorem not_isomorphic
    (actions : PaperKernel.ActionData) (data : Data actions) :
    ¬ GroupsIsomorphic
      (PaperKernel.paperGammaOneOf actions)
      (PaperKernel.paperGammaTwoOf actions) := by
  rintro ⟨f⟩
  obtain ⟨σ, ⟨e⟩⟩ := data.characteristic_module_equiv f
  apply data.moduleTwo_not_semisimple_under_quotient σ
  exact Semisimple.semisimple_invariant_under_linear_equiv e
    data.moduleOne_semisimple

end
end PaperNonisomorphism
end Connes
