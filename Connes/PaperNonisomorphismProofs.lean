/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Concrete §6 module obstruction for Zhou's nonsplit finite correction. The
extension is proved over the actual finite group algebra; the remaining
embedding into the full second kernel is handled in the companion action
file. The construction follows the paper's E_ell argument.
-/
import Connes.PaperNonisomorphism
import Connes.PaperICCOrbits

set_option maxHeartbeats 1600000

namespace Connes
namespace PaperNonisomorphism

open Construction
open Construction.PaperKernel

noncomputable section

abbrev PaperEll := PaperKernel.VStar × k

def paperEllMap (q : PaperKernel.Q) : PaperEll →ₗ[k] PaperEll where
  toFun p :=
    (qVStarActionHom q p.1 + p.2 • OpenAIPort.quadraticDefectLinear q, p.2)
  map_add' p r := by
    apply Prod.ext
    · simp [smul_add, add_smul, add_assoc, add_left_comm, add_comm]
    · simp
  map_smul' a p := by
    apply Prod.ext
    · simp [smul_add, add_smul, smul_smul]
    · simp

def paperEllRepresentation : Representation k PaperKernel.Q PaperEll where
  toFun := paperEllMap
  map_one' := by
    have hq : OpenAIPort.quadraticDefectLinear (1 : PaperKernel.Q) = 0 := by
      apply LinearMap.ext
      intro v
      simp [OpenAIPort.quadraticDefectLinear, CharTwo.add_self_eq_zero]
    apply LinearMap.ext
    rintro ⟨f, s⟩
    apply Prod.ext
    · simp [paperEllMap, hq]
    · rfl
  map_mul' p q := by
    apply LinearMap.ext
    rintro ⟨f, s⟩
    apply Prod.ext
    · change qVStarActionHom (p * q) f +
          s • OpenAIPort.quadraticDefectLinear (p * q) =
        qVStarActionHom p
            (qVStarActionHom q f + s • OpenAIPort.quadraticDefectLinear q) +
          s • OpenAIPort.quadraticDefectLinear p
      rw [map_mul, PaperKernel.quadraticDefectLinear_cocycle]
      simp [smul_add, add_smul, smul_smul, add_assoc, add_left_comm, add_comm]
    · rfl

def paperEllVStarRepresentation : Representation k PaperKernel.Q PaperKernel.VStar :=
  { toFun := fun q => (qVStarActionHom q).toLinearMap
    map_one' := by
      apply LinearMap.ext
      intro f
      simpa using congrArg (fun e : PaperKernel.VStar ≃ₗ[k] PaperKernel.VStar => e f)
        qVStarActionHom.map_one
    map_mul' := by
      intro p q
      apply LinearMap.ext
      intro f
      simpa using congrArg (fun e : PaperKernel.VStar ≃ₗ[k] PaperKernel.VStar => e f)
        (qVStarActionHom.map_mul p q) }

def paperEllScalarRepresentation : Representation k PaperKernel.Q k :=
  Representation.trivial k PaperKernel.Q k

def paperEllInclusionLinear : PaperKernel.VStar →ₗ[k] PaperEll where
  toFun f := (f, 0)
  map_add' f g := by simp
  map_smul' a f := by simp

def paperEllInclusionIntertwining :
    Representation.IntertwiningMap paperEllVStarRepresentation paperEllRepresentation :=
  paperEllInclusionLinear.intertwiningMap_of_isIntertwiningMap
    paperEllVStarRepresentation paperEllRepresentation (by
      intro q f
      apply Prod.ext
      · simp [paperEllInclusionLinear, paperEllVStarRepresentation,
          paperEllRepresentation, paperEllMap]
      · rfl)

def paperEllProjectionLinear : PaperEll →ₗ[k] k where
  toFun p := p.2
  map_add' p q := by simp
  map_smul' a p := by simp

def paperEllProjectionIntertwining :
    Representation.IntertwiningMap paperEllRepresentation paperEllScalarRepresentation :=
  paperEllProjectionLinear.intertwiningMap_of_isIntertwiningMap
    paperEllRepresentation paperEllScalarRepresentation (by
      intro q p
      rfl)

def paperEllInclusion :
    paperEllVStarRepresentation.asModule →ₗ[Ring]
      paperEllRepresentation.asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule
    paperEllVStarRepresentation paperEllRepresentation).toFun paperEllInclusionIntertwining

def paperEllProjection :
    paperEllRepresentation.asModule →ₗ[Ring]
      paperEllScalarRepresentation.asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule
    paperEllRepresentation paperEllScalarRepresentation).toFun paperEllProjectionIntertwining

theorem paperEll_projection_surjective : Function.Surjective paperEllProjection := by
  intro s
  refine ⟨(0, s), ?_⟩
  rfl

theorem paperEll_exact : Function.Exact paperEllInclusion paperEllProjection := by
  apply LinearMap.exact_of_comp_of_mem_range
  · ext p
    rfl
  · intro p hp
    refine ⟨p.1, ?_⟩
    apply Prod.ext
    · rfl
    · change p.2 = 0 at hp
      exact hp.symm

def paperEllExtension :
    Semisimple.LinearExtension Ring
      paperEllVStarRepresentation.asModule
      paperEllScalarRepresentation.asModule
      paperEllRepresentation.asModule where
  inclusion := paperEllInclusion
  projection := paperEllProjection
  exact := paperEll_exact

theorem paperEll_extension_not_splits : ¬ Semisimple.ExactSplits paperEllExtension := by
  rintro ⟨section_⟩
  refine finiteCocycle_not_linearCoboundary ?_
  let oneScalar : paperEllScalarRepresentation.asModule :=
    paperEllScalarRepresentation.asModuleEquiv.symm (1 : k)
  let lambda : PaperKernel.VStar :=
    (paperEllRepresentation.asModuleEquiv
      (section_.section_ oneScalar)).1
  refine ⟨lambda, ?_⟩
  intro q v
  have hq := section_.section_.map_smul
    (MonoidAlgebra.of k PaperKernel.Q q)
    oneScalar
  have hsource_fixed :
      paperEllScalarRepresentation.asModuleEquiv.symm
          (paperEllScalarRepresentation q (1 : k)) = oneScalar := by
    simp [paperEllScalarRepresentation, oneScalar]
  have hqsource :
      (MonoidAlgebra.of k PaperKernel.Q q) • oneScalar =
        paperEllScalarRepresentation.asModuleEquiv.symm
          (paperEllScalarRepresentation q (1 : k)) := by
    change
      (MonoidAlgebra.of k PaperKernel.Q q) •
          paperEllScalarRepresentation.asModuleEquiv.symm (1 : k) =
        paperEllScalarRepresentation.asModuleEquiv.symm
          (paperEllScalarRepresentation q (1 : k))
    exact (Representation.asModuleEquiv_symm_map_rho
      (ρ := paperEllScalarRepresentation) q (1 : k)).symm
  have hqcodomain :
      (MonoidAlgebra.of k PaperKernel.Q q) • section_.section_ oneScalar =
        paperEllRepresentation.asModuleEquiv.symm
          (paperEllRepresentation q
            (paperEllRepresentation.asModuleEquiv (section_.section_ oneScalar))) := by
    simpa using
      (Representation.asModuleEquiv_symm_map_rho
        (ρ := paperEllRepresentation) q
          (paperEllRepresentation.asModuleEquiv (section_.section_ oneScalar))).symm
  rw [hqsource, hsource_fixed, hqcodomain] at hq
  have hq' := congrArg paperEllRepresentation.asModuleEquiv hq
  rw [LinearEquiv.apply_symm_apply] at hq'
  have hfirst := congrArg Prod.fst hq'
  have hsection :=
    LinearMap.congr_fun section_.projection_section oneScalar
  have hsection' :=
    congrArg paperEllScalarRepresentation.asModuleEquiv hsection
  change (paperEllRepresentation.asModuleEquiv
      (section_.section_ oneScalar)).2 = 1 at hsection'
  have hxsecond :
      (paperEllRepresentation.asModuleEquiv (section_.section_ oneScalar)).2 = 1 := by
    exact hsection'
  have hfirst' :
      lambda = qVStarActionHom q lambda +
        (paperEllRepresentation.asModuleEquiv
          (section_.section_ oneScalar)).2 •
          OpenAIPort.quadraticDefectLinear q := by
    simpa [lambda, paperEllRepresentation, paperEllMap] using hfirst
  rw [hxsecond, one_smul] at hfirst'
  have hquad :
      OpenAIPort.quadraticDefectLinear q =
        qVStarActionHom q lambda + lambda := by
    have h := congrArg (fun z : PaperKernel.VStar => z + lambda) hfirst'
    rw [add_assoc, Connes.Construction.SymmetricTensor.add_self_eq_zero] at h
    have h' := congrArg
      (fun z : PaperKernel.VStar => z + qVStarActionHom q lambda + lambda) h
    simpa [add_assoc, add_left_comm, add_comm,
      Connes.Construction.SymmetricTensor.add_self_eq_zero] using h'.symm
  change OpenAIPort.quadraticDefectLinear q v =
    lambda (q⁻¹ • v) + lambda v
  rw [hquad]
  rfl

def paperEll_splitting_criterion :
    Semisimple.SemisimplicitySplittingCriterion paperEllExtension where
  semisimple_splits hE := by
    letI : IsSemisimpleModule Ring paperEllRepresentation.asModule := hE
    have hs : Function.Surjective paperEllProjection := paperEll_projection_surjective
    obtain ⟨section_, hsection⟩ :=
      IsSemisimpleModule.lifting_property
        (M := paperEllRepresentation.asModule)
        (N := paperEllScalarRepresentation.asModule)
        (P := paperEllScalarRepresentation.asModule)
        paperEllProjection hs
          (LinearMap.id : paperEllScalarRepresentation.asModule →ₗ[Ring]
            paperEllScalarRepresentation.asModule)
    refine ⟨{ section_ := section_, projection_section := ?_ }⟩
    change paperEllProjection ∘ₗ section_ = LinearMap.id at hsection
    exact hsection

theorem paperEll_not_semisimple :
    ¬ IsSemisimpleModule Ring paperEllRepresentation.asModule :=
  Semisimple.nonsplit_extension_not_semisimple paperEllExtension
    paperEll_extension_not_splits
    paperEll_splitting_criterion

end
end PaperNonisomorphism
end Connes
