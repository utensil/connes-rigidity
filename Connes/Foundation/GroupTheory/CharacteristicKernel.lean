/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Proof transfer from OpenAI/ten-proofs archive commit 66af838,
ConnesRigidity/CharacteristicKernel.lean:24-137. This generic obstruction
layer is source-linked but independent of the Zhou construction.
-/
import Connes.Foundation.GroupTheory.CocycleExtension

namespace Connes
namespace OpenAIPort
namespace CocycleExtension

universe u v

variable {G : Type u} {A : Type v}
variable [Group G] [AddCommGroup A] [DistribMulAction G A]

private abbrev zeroCocycle : NormalizedAddCocycle G A :=
  NormalizedAddCocycle.zero

/-- Inclusion of the zero-cocycle extension. Paper: §6. -/
def zeroInr : G →* CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) where
  toFun g := ⟨0, g⟩
  map_one' := rfl
  map_mul' g h := by
    apply CocycleExtension.ext
    · simp
    · simp

/-- Coordinate form of the zero-cocycle inclusion. Paper: §6. -/
@[simp] theorem zeroInr_apply (g : G) :
    zeroInr (A := A) g = ⟨0, g⟩ := rfl

/-- Kernel preservation for a candidate extension equivalence. Paper: §6. -/
def PreservesKernel
    (c : NormalizedAddCocycle G A)
    (f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
      CocycleExtension c) : Prop :=
  ∀ x, x.snd = 1 ↔ (f x).snd = 1

/-- Quotient map induced by an extension equivalence. Paper: §6. -/
def quotientHom
    (c : NormalizedAddCocycle G A)
    (f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
      CocycleExtension c) : G →* G :=
  (rightHom c).comp (f.toMonoidHom.comp (zeroInr (A := A)))

/-- Evaluation of the induced quotient map. Paper: §6. -/
@[simp] theorem quotientHom_apply
    (c : NormalizedAddCocycle G A)
    (f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
      CocycleExtension c)
    (g : G) :
    quotientHom c f g = (f ⟨0, g⟩).snd := rfl

/-- Kernel preservation makes the induced quotient map injective. Paper: §6. -/
theorem quotientHom_injective_of_preservesKernel
    (c : NormalizedAddCocycle G A)
    (f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
      CocycleExtension c)
    (hf : PreservesKernel c f) :
    Function.Injective (quotientHom c f) := by
  intro g h hgh
  apply eq_of_mul_inv_eq_one
  have hker : quotientHom c f (g * h⁻¹) = 1 := by
    rw [map_mul, map_inv, hgh, mul_inv_cancel]
  have hsource : (⟨0, g * h⁻¹⟩ :
      CocycleExtension (zeroCocycle : NormalizedAddCocycle G A)).snd = 1 :=
    (hf ⟨0, g * h⁻¹⟩).mpr hker
  exact hsource

/-- Kernel preservation makes the induced quotient map surjective. Paper: §6. -/
theorem quotientHom_surjective_of_preservesKernel
    (c : NormalizedAddCocycle G A)
    (f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
      CocycleExtension c)
    (hf : PreservesKernel c f) :
    Function.Surjective (quotientHom c f) := by
  intro q
  let x : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) :=
    f.symm ⟨0, q⟩
  refine ⟨x.snd, ?_⟩
  have hx :
      x = (⟨x.fst, (1 : G)⟩ :
        CocycleExtension (zeroCocycle : NormalizedAddCocycle G A)) *
        (⟨(0 : A), x.snd⟩ :
        CocycleExtension (zeroCocycle : NormalizedAddCocycle G A)) := by
    apply CocycleExtension.ext
    · simp
    · simp
  have hk : (f ⟨x.fst, (1 : G)⟩).snd = 1 :=
    (hf ⟨x.fst, (1 : G)⟩).mp rfl
  have hfx : f x = ⟨0, q⟩ :=
    f.apply_symm_apply ⟨0, q⟩
  calc
    quotientHom c f x.snd = (f ⟨(0 : A), x.snd⟩).snd := rfl
    _ = (f ⟨x.fst, (1 : G)⟩ * f ⟨(0 : A), x.snd⟩).snd := by simp [hk]
    _ = (f ((⟨x.fst, (1 : G)⟩ :
        CocycleExtension (zeroCocycle : NormalizedAddCocycle G A)) *
          (⟨(0 : A), x.snd⟩ :
            CocycleExtension (zeroCocycle : NormalizedAddCocycle G A)))).snd := by
      rw [f.map_mul]
    _ = (f x).snd := by rw [← hx]
    _ = q := congr_arg CocycleExtension.snd hfx

/-- A kernel-preserving extension equivalence induces a group equivalence. Paper: §6. -/
noncomputable def quotientEquivOfPreservesKernel
    (c : NormalizedAddCocycle G A)
    (f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
      CocycleExtension c)
    (hf : PreservesKernel c f) : G ≃* G :=
  MulEquiv.ofBijective (quotientHom c f)
    ⟨quotientHom_injective_of_preservesKernel c f hf,
      quotientHom_surjective_of_preservesKernel c f hf⟩

/-- A kernel-preserving extension equivalence yields a splitting. Paper: §6. -/
noncomputable def splittingOfEquivPreservingKernel
    (c : NormalizedAddCocycle G A)
    (f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
      CocycleExtension c)
    (hf : PreservesKernel c f) :
    Splitting c := by
  let β := quotientEquivOfPreservesKernel c f hf
  let s : G →* CocycleExtension c :=
    f.toMonoidHom.comp ((zeroInr (A := A)).comp β.symm.toMonoidHom)
  refine ⟨s, ?_⟩
  ext g
  exact β.apply_symm_apply g

/-- A characteristic kernel prevents an isomorphism to a nonsplit extension. Paper: §6. -/
theorem not_isomorphic_of_kernel_characteristic
    (c : NormalizedAddCocycle G A)
    (hc : ¬c.IsCoboundary)
    (hcharacteristic :
      ∀ f : CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
        CocycleExtension c, PreservesKernel c f) :
    ¬Nonempty
      (CocycleExtension (zeroCocycle : NormalizedAddCocycle G A) ≃*
        CocycleExtension c) := by
  rintro ⟨f⟩
  exact hc (isCoboundaryOfSplitting c
    (splittingOfEquivPreservingKernel c f (hcharacteristic f)))

end CocycleExtension
end OpenAIPort
end Connes
