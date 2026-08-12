/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0
-/
import Connes.Construction.PaperActionInstances
import Connes.Foundation.GroupTheory.SpecialLinear.ICC

/-!
ICC transfer for Zhou §5. Since the acting group is
`SL₃(R) × Sp₄(F₂)`, the proof uses the paper's three-case criterion on the
concrete product quotient.
-/

namespace Connes
namespace PaperICC

open Construction
open Construction.PaperKernel

noncomputable section

abbrev N := Multiplicative PaperKernel.D
abbrev S := SpecialLinear.SL3
abbrev Q := PaperKernel.Q
abbrev H := S × Q

/-- The actual semidirect carrier for one of Zhou's actions. Paper: §2, §5. -/
abbrev Carrier (action : H →* MulAut N) := SemidirectProduct N H action

/-- Countable wrapper used by the generic three-case ICC proof. Paper: §5. -/
noncomputable def groupOf (action : H →* MulAut N) : CountableDiscreteGroup where
  Carrier := Carrier action
  group := SemidirectProduct.instGroup
  countable := by
    exact SemidirectProduct.equivProd.injective.countable

/-- Infinite SL₃ orbits of nonzero kernel elements. Paper: §5. -/
structure ActionData (action : H →* MulAut N) where
  kernel_orbit : ∀ a : N, a ≠ 1 →
    (Set.range fun s : S => action (s, 1) a).Infinite
  q_displacement : ∀ q : Q, q ≠ 1 →
    ∃ a : N,
      a * (action (1, q) a)⁻¹ ≠ 1 ∧
        (Set.range fun s : S =>
          action (s, 1) (a * (action (1, q) a)⁻¹)).Infinite

/-- The projection of the actual semidirect product to the SL₃ factor. -/
def projectionS (action : H →* MulAut N) : Carrier action →* S where
  toFun x := x.right.1
  map_one' := by rfl
  map_mul' x y := by simp [SemidirectProduct.mul_right]

private theorem section_injective (action : H →* MulAut N) :
    Function.Injective (fun s : S =>
      (SemidirectProduct.inr (s, 1) : Carrier action)) := by
  intro s t h
  exact congrArg (fun x : Carrier action => x.right.1) h

private theorem kernel_nontrivial_of_right_one
    (action : H →* MulAut N) (x : Carrier action)
    (hx : x ≠ 1) (hright : x.right = 1) :
    x.left ≠ 1 := by
  intro hleft
  apply hx
  apply SemidirectProduct.ext
  · exact hleft
  · exact hright

private theorem action_commutes_with_q
    (action : H →* MulAut N) (s : S) (q : Q) (a : N) :
    action ((1 : S), q) (action (s, (1 : Q)) a) =
      action (s, (1 : Q)) (action ((1 : S), q) a) := by
  change (action ((1 : S), q) * action (s, (1 : Q))) a =
    (action (s, (1 : Q)) * action ((1 : S), q)) a
  rw [← action.map_mul, ← action.map_mul]
  congr 1
  ext <;> simp

private theorem q_displacement_conjugate
    (action : H →* MulAut N) (x : Carrier action)
    (hs : x.right.1 = 1) (q : Q) (hqx : x.right.2 = q) (a : N) :
    ∀ s : S,
      (⟨x.left * action (s, (1 : Q))
            (a * (action ((1 : S), q) a)⁻¹), x.right⟩ : Carrier action) =
        (SemidirectProduct.inl (action (s, (1 : Q)) a) : Carrier action) * x *
          (SemidirectProduct.inl (action (s, (1 : Q)) a) : Carrier action)⁻¹ := by
  intro s
  have hxright : x.right = ((1 : S), q) := by
    apply Prod.ext
    · exact hs
    · exact hqx
  have hdisp :
      action (s, (1 : Q)) a *
          action ((1 : S), q) (action (s, (1 : Q)) a)⁻¹ =
        action (s, (1 : Q))
          (a * (action ((1 : S), q) a)⁻¹) := by
    calc
      action (s, (1 : Q)) a *
          action ((1 : S), q) (action (s, (1 : Q)) a)⁻¹ =
        action (s, (1 : Q)) a *
          (action ((1 : S), q) (action (s, (1 : Q)) a))⁻¹ := by
            congr 1
            exact map_inv (action ((1 : S), q)) _
      _ = action (s, (1 : Q)) a *
          (action (s, (1 : Q)) (action ((1 : S), q) a))⁻¹ := by
        rw [action_commutes_with_q]
      _ = action (s, (1 : Q)) a *
          action (s, (1 : Q)) ((action ((1 : S), q) a)⁻¹) := by
            congr 1
            exact (map_inv (action (s, (1 : Q))) _).symm
      _ = action (s, (1 : Q))
          (a * (action ((1 : S), q) a)⁻¹) := by
        rw [← map_mul]
  apply SemidirectProduct.ext
  ·
    simp only [SemidirectProduct.left_inl, SemidirectProduct.mul_left,
      SemidirectProduct.inv_left, SemidirectProduct.right_inl,
      SemidirectProduct.mul_right]
    simp only [one_mul, inv_one, map_one, MulAut.one_apply,
      map_mul, map_inv]
    have hdisp' :
        action (s, (1 : Q)) a *
            action (s, (1 : Q)) ((action ((1 : S), q) a)⁻¹) =
          action (s, (1 : Q))
            (a * (action ((1 : S), q) a)⁻¹) := by
      rw [← map_mul]
    calc
      x.left *
          (action (s, (1 : Q)) a *
            action (s, (1 : Q)) ((action ((1 : S), q) a)⁻¹)) =
          x.left * action (s, (1 : Q))
            (a * (action ((1 : S), q) a)⁻¹) := by rw [hdisp']
      _ = x.left *
          (action (s, (1 : Q)) a *
            action ((1 : S), q) (action (s, (1 : Q)) a)⁻¹) := by
        rw [hdisp]
      _ = action (s, (1 : Q)) a * x.left *
          action ((1 : S), q) (action (s, (1 : Q)) a)⁻¹ := by
        ac_rfl
      _ = action (s, (1 : Q)) a * x.left *
          action x.right (action (s, (1 : Q)) a)⁻¹ := by rw [hxright]
  ·
    simp only [SemidirectProduct.right_inl, SemidirectProduct.mul_right,
      SemidirectProduct.inv_right]
    simp

/-- Three-case ICC transfer for the product quotient in Zhou §5. -/
theorem isICC_of_product_quotient
    (action : H →* MulAut N) (data : ActionData action) :
    IsICC (groupOf action) := by
  change Infinite (Carrier action) ∧
    ∀ x : Carrier action, x ≠ 1 →
      Set.Infinite (conjugacyClass (groupOf action) x)
  refine ⟨?_, ?_⟩
  · letI : Infinite S := SpecialLinear.sl3_isICC.1
    exact Infinite.of_injective
      (fun s : S =>
        (SemidirectProduct.inr (N := N) (G := H) (φ := action)
          (s, (1 : Q)) : Carrier action))
      (section_injective action)
  · rintro (x : Carrier action) hx
    by_cases hs : x.right.1 ≠ 1
    · let conjugates : S → Carrier action := fun s =>
        (SemidirectProduct.inr (N := N) (G := H) (φ := action)
          (s, (1 : Q)) : Carrier action) * x *
          (SemidirectProduct.inr (N := N) (G := H) (φ := action)
            (s, (1 : Q)) : Carrier action)⁻¹
      apply Set.Infinite.of_image (projectionS action)
      apply (SpecialLinear.sl3_isICC.2 x.right.1 hs).mono
      rintro y ⟨s, rfl⟩
      refine ⟨conjugates s,
        ⟨(SemidirectProduct.inr (N := N) (G := H) (φ := action)
          (s, (1 : Q)) : Carrier action), rfl⟩, ?_⟩
      simp only [conjugates, projectionS]
      rfl
    · have hs' : x.right.1 = 1 := by exact not_ne_iff.mp hs
      by_cases hq : x.right.2 = 1
      · have hright : x.right = 1 := by
          apply Prod.ext
          · exact hs'
          · exact hq
        have hleft := kernel_nontrivial_of_right_one action x hx hright
        have horbit := data.kernel_orbit x.left hleft
        have hinfinite := horbit.image
          (SemidirectProduct.inl_injective (φ := action)).injOn
        apply hinfinite.mono
        rintro y ⟨a, ⟨s, rfl⟩, rfl⟩
        refine ⟨(SemidirectProduct.inr (N := N) (G := H) (φ := action)
          (s, (1 : Q)) : Carrier action), ?_⟩
        have hxkernel : x = SemidirectProduct.inl x.left := by
          apply SemidirectProduct.ext
          · rfl
          · exact hright
        rw [hxkernel]
        change
          (SemidirectProduct.inl (action (s, (1 : Q)) x.left) :
            Carrier action) =
            (SemidirectProduct.inr (s, (1 : Q)) : Carrier action) *
              (SemidirectProduct.inl x.left : Carrier action) *
                (SemidirectProduct.inr (s, (1 : Q)) : Carrier action)⁻¹
        simpa only [map_inv] using
          SemidirectProduct.inl_aut (φ := action) (s, (1 : Q)) x.left
      · obtain ⟨a, ha, horbit⟩ := data.q_displacement x.right.2 hq
        let displacement : N :=
          a * (action ((1 : S), x.right.2) a)⁻¹
        have hdisp : displacement ≠ 1 := by
          exact ha
        have hmul : Function.Injective (fun b : N => x.left * b) := by
          intro b c hbc
          exact mul_left_cancel hbc
        have htranslated :
            (Set.range fun s : S =>
              x.left * action (s, (1 : Q)) displacement).Infinite := by
          dsimp [displacement] at horbit ⊢
          have himage := horbit.image hmul.injOn
          have hset :
              (Set.range fun s : S =>
                x.left * action (s, (1 : Q)) displacement) =
                (fun b : N => x.left * b) ''
                  Set.range (fun s : S =>
                    action (s, (1 : Q)) displacement) := by
            ext y
            constructor
            · rintro ⟨s, rfl⟩
              exact ⟨action (s, (1 : Q)) displacement,
                ⟨s, rfl⟩, rfl⟩
            · rintro ⟨b, ⟨s, rfl⟩, rfl⟩
              exact ⟨s, rfl⟩
          rw [hset]
          exact himage
        have hinj : Function.Injective
            (fun b : N => (⟨b, x.right⟩ : Carrier action)) := by
          intro b c hbc
          exact congrArg SemidirectProduct.left hbc
        have hinfinite := htranslated.image
          hinj.injOn
        apply hinfinite.mono
        rintro y ⟨b, ⟨s, rfl⟩, rfl⟩
        exact ⟨SemidirectProduct.inl (action (s, (1 : Q)) a),
          by
            change
              (⟨x.left * action (s, (1 : Q)) displacement, x.right⟩ :
                Carrier action) =
                (SemidirectProduct.inl (action (s, (1 : Q)) a) :
                  Carrier action) * x *
                  (SemidirectProduct.inl (action (s, (1 : Q)) a) :
                    Carrier action)⁻¹
            dsimp [displacement]
            exact q_displacement_conjugate action x hs' x.right.2 rfl a s⟩

/-- ICC inputs for both actual Zhou actions. Paper: §5. -/
structure DataPair (actions : PaperKernel.ActionData) where
  thetaOne : ActionData actions.thetaOne
  thetaTwo : ActionData actions.thetaTwo

/-- ICC for the first actual Zhou group. Paper: §5. -/
theorem gammaOne_icc
    (actions : PaperKernel.ActionData) (data : DataPair actions) :
    IsICC (PaperKernel.paperGammaOneOf actions) := by
  simpa only [PaperKernel.paperGammaOneOf, groupOf] using
    isICC_of_product_quotient actions.thetaOne data.thetaOne

/-- ICC for the second actual Zhou group. Paper: §5. -/
theorem gammaTwo_icc
    (actions : PaperKernel.ActionData) (data : DataPair actions) :
    IsICC (PaperKernel.paperGammaTwoOf actions) := by
  simpa only [PaperKernel.paperGammaTwoOf, groupOf] using
    isICC_of_product_quotient actions.thetaTwo data.thetaTwo

end
end PaperICC
end Connes
