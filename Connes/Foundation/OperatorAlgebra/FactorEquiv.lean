/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Proof transfer from OpenAI ten-proofs, ConnesRigidity.lean:13650-13699.
The source is cited for provenance only; this file has no dependency on it.
-/
import Mathlib
import Connes.Core
import Connes.Foundation.OperatorAlgebra.StarAlgEquiv

namespace Connes
namespace OpenAIPort

universe u v w

noncomputable section

/-- The identity factor witness. Paper: §3. -/
def groupFactorEquivRefl (G : CountableDiscreteGroup.{u}) :
    TracialGroupFactorEquiv G G where
  toStarAlgEquiv := StarAlgEquiv.refl ℂ (GroupVonNeumannAlgebra G)
  normal := starAlgEquiv_isNormal _
  trace_preserving := by
    intro x
    rfl

/-- The inverse of a trace-preserving factor witness. Paper: §3. -/
def groupFactorEquivSymm
    {G : CountableDiscreteGroup.{u}}
    {H : CountableDiscreteGroup.{v}}
    (e : TracialGroupFactorEquiv G H) :
    TracialGroupFactorEquiv H G where
  toStarAlgEquiv := e.toStarAlgEquiv.symm
  normal := by
    exact ⟨e.normal.2, e.normal.1⟩
  trace_preserving := by
    intro y
    have h := e.trace_preserving (e.toStarAlgEquiv.symm y)
    simpa only [StarAlgEquiv.apply_symm_apply] using h.symm

/-- The composite of trace-preserving factor witnesses. Paper: §3. -/
def groupFactorEquivTrans
    {G : CountableDiscreteGroup.{u}}
    {H : CountableDiscreteGroup.{v}}
    {J : CountableDiscreteGroup.{w}}
    (e : TracialGroupFactorEquiv G H)
    (f : TracialGroupFactorEquiv H J) :
    TracialGroupFactorEquiv G J where
  toStarAlgEquiv := e.toStarAlgEquiv.trans f.toStarAlgEquiv
  normal := by
    constructor
    · intro S p hp
      have he := e.normal.1 S p hp
      have hf := f.normal.1 (e.toStarAlgEquiv '' S) (e.toStarAlgEquiv p) he
      change
        IsProjectionSupremum
          ((fun x ↦ f.toStarAlgEquiv (e.toStarAlgEquiv x)) '' S)
          (f.toStarAlgEquiv (e.toStarAlgEquiv p))
      simpa only [Set.image_image] using hf
    · intro S p hp
      have hf := f.normal.2 S p hp
      have he :=
        e.normal.2 (f.toStarAlgEquiv.symm '' S) (f.toStarAlgEquiv.symm p) hf
      change
        IsProjectionSupremum
          ((fun x ↦ e.toStarAlgEquiv.symm (f.toStarAlgEquiv.symm x)) '' S)
          (e.toStarAlgEquiv.symm (f.toStarAlgEquiv.symm p))
      simpa only [Set.image_image] using he
  trace_preserving := by
    intro x
    change
      canonicalTrace J (f.toStarAlgEquiv (e.toStarAlgEquiv x)) =
        canonicalTrace G x
    rw [f.trace_preserving, e.trace_preserving]

/-- Symmetry of the trace-preserving factor relation. Paper: §3. -/
theorem groupFactorsIsomorphic_symm
    {G : CountableDiscreteGroup.{u}}
    {H : CountableDiscreteGroup.{v}}
    (h : TracialGroupFactorsIsomorphic G H) :
    TracialGroupFactorsIsomorphic H G := by
  obtain ⟨e⟩ := h
  exact ⟨groupFactorEquivSymm e⟩

/-- Transitivity of the trace-preserving factor relation. Paper: §3. -/
theorem groupFactorsIsomorphic_trans
    {G : CountableDiscreteGroup.{u}}
    {H : CountableDiscreteGroup.{v}}
    {J : CountableDiscreteGroup.{w}}
    (hGH : TracialGroupFactorsIsomorphic G H)
    (hHJ : TracialGroupFactorsIsomorphic H J) :
    TracialGroupFactorsIsomorphic G J := by
  obtain ⟨e⟩ := hGH
  obtain ⟨f⟩ := hHJ
  exact ⟨groupFactorEquivTrans e f⟩

end
end OpenAIPort
end Connes
