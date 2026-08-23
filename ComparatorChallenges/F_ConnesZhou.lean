/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Independent comparator challenge for connes-rigidity. The declarations below
are intentionally self-contained and are not imported from the solution.
Their vocabulary follows the public OpenAI ten-proofs challenge shape, while
the theorem statement follows Zhou, arXiv:2608.02327.
-/
import Mathlib

namespace Connes

universe u v w

/-- Countable discrete group carrier for the challenge. Paper: §7. -/
structure CountableDiscreteGroup where
  Carrier : Type u
  group : Group Carrier
  countable : Countable Carrier

namespace CountableDiscreteGroup

/-- Challenge coercion to the group carrier. Paper: §7. -/
instance : CoeSort CountableDiscreteGroup (Type u) :=
  ⟨CountableDiscreteGroup.Carrier⟩

attribute [instance] group countable

end CountableDiscreteGroup

/-- Challenge ICC predicate. Paper: §5. -/
def IsICC (G : CountableDiscreteGroup) : Prop :=
  Infinite G ∧ ∀ g : G, g ≠ 1 → Set.Infinite (conjugatesOf g)

/-- Challenge unitary-representation carrier. Paper: §4. -/
abbrev UnitaryRepresentation
    (G : Type u) [Group G]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  G →* unitary (H →L[ℂ] H)

namespace UnitaryRepresentation

variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Challenge invariant-vector predicate. Paper: §4. -/
def IsInvariant (π : UnitaryRepresentation G H) (ξ : H) : Prop :=
  ∀ g : G, (π g : H →L[ℂ] H) ξ = ξ

/-- Challenge almost-invariant-vector predicate. Paper: §4. -/
def HasAlmostInvariantUnitVectors (π : UnitaryRepresentation G H) : Prop :=
  ∀ (K : Finset G) (ε : ℝ), 0 < ε →
    ∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ g ∈ K, ‖(π g : H →L[ℂ] H) ξ - ξ‖ < ε

end UnitaryRepresentation

/-- Challenge property-(T) predicate. Paper: §4. -/
def HasKazhdanPropertyT (G : CountableDiscreteGroup.{u}) : Prop :=
  ∀ (H : Type u)
    (_ : NormedAddCommGroup H)
    (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H)
    (π : UnitaryRepresentation G H),
    π.HasAlmostInvariantUnitVectors →
      ∃ ξ : H, ξ ≠ 0 ∧ π.IsInvariant ξ

noncomputable section

open scoped NNReal ENNReal

/-- Challenge group-indexed Hilbert carrier. Paper: §3. -/
abbrev GroupL2 (G : Type u) := lp (fun _ : G ↦ ℂ) 2

/-- Challenge `ℓp` reindexing lemma. Paper: §3. -/
theorem memℓp_reindex {α : Type u} {β : Type v} {E : Type w}
    [NormedAddCommGroup E] {p : ℝ≥0∞} (e : α ≃ β) (hp : 0 < p.toReal)
    (f : lp (fun _ : α ↦ E) p) : Memℓp (fun j : β ↦ f (e.symm j)) p := by
  rw [memℓp_gen_iff hp]
  exact (e.symm.summable_iff).2 ((lp.memℓp f).summable hp)

/-- Challenge Hilbert reindexing boundary. Paper: §3. -/
def l2Reindex {α : Type u} {β : Type v} (e : α ≃ β) :
    GroupL2 α ≃ₗᵢ[ℂ] GroupL2 β where
  toLinearEquiv :=
    { toFun := fun f ↦ ⟨(fun j : β ↦ f (e.symm j)), memℓp_reindex e (by norm_num) f⟩
      invFun := fun f ↦ ⟨(fun j : α ↦ f (e j)), memℓp_reindex e.symm (by norm_num) f⟩
      left_inv := fun f ↦ by ext; simp
      right_inv := fun f ↦ by ext; simp
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
  norm_map' := by
    intro f
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    congr 1
    exact e.symm.tsum_eq (fun i ↦ ‖f i‖ ^ (2 : ℝ≥0∞).toReal)

/-- Challenge left-regular unitary boundary. Paper: §3. -/
def leftRegularUnitary {G : Type u} [Group G] (g : G) :
    unitary (GroupL2 G →L[ℂ] GroupL2 G) :=
  Unitary.linearIsometryEquiv.symm (l2Reindex (Equiv.mulLeft g))

/-- Challenge left-regular representation boundary. Paper: §3. -/
def leftRegularRepresentation (G : Type u) [Group G] :
    G →* unitary (GroupL2 G →L[ℂ] GroupL2 G) where
  toFun := leftRegularUnitary
  map_one' := by
    -- Pin `λ(g)f(h) = f(g⁻¹ * h)` before discharging the representation law.
    ext f h
    change f ((1 : G)⁻¹ * h) = f h
    simp
  map_mul' g h := by
    -- Pin the same left-action convention for multiplication.
    ext f k
    change f ((g * h)⁻¹ * k) = f (h⁻¹ * (g⁻¹ * k))
    simp [mul_assoc]

/-- Challenge von Neumann closure boundary. Paper: §3. -/
def vonNeumannClosure
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Set (H →L[ℂ] H)) :
    VonNeumannAlgebra H where
  toStarSubalgebra :=
    StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))
  centralizer_centralizer' := by
    change
      Set.centralizer
          (Set.centralizer
            ((StarSubalgebra.centralizer ℂ
              (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))) :
                Set (H →L[ℂ] H))) =
        ((StarSubalgebra.centralizer ℂ
          (StarSubalgebra.centralizer ℂ S : Set (H →L[ℂ] H))) :
            Set (H →L[ℂ] H))
    rw [StarSubalgebra.coe_centralizer_centralizer]
    exact Set.centralizer_centralizer_centralizer ((S ∪ star S).centralizer)

/-- Challenge group von Neumann algebra boundary. Paper: §3. -/
def groupVonNeumannAlgebra (G : CountableDiscreteGroup.{u}) :
    VonNeumannAlgebra (GroupL2 G) :=
  vonNeumannClosure (Set.range fun g : G ↦
    (leftRegularRepresentation G g : GroupL2 G →L[ℂ] GroupL2 G))

/-- Challenge group-factor carrier. Paper: §3. -/
abbrev GroupVonNeumannAlgebra (G : CountableDiscreteGroup.{u}) :=
  (groupVonNeumannAlgebra G).toStarSubalgebra

/-- Challenge point-mass boundary. Paper: §3. -/
def delta (G : CountableDiscreteGroup.{u}) (g : G) : GroupL2 G :=
  by
    classical
    exact lp.single 2 g 1

/-- Challenge trace boundary. Paper: §3. -/
def canonicalTrace (G : CountableDiscreteGroup.{u}) :
    GroupVonNeumannAlgebra G → ℂ :=
  fun x ↦ inner ℂ (delta G 1) ((x : GroupL2 G →L[ℂ] GroupL2 G) (delta G 1))

/-- Challenge projection-supremum boundary. Paper: §3. -/
def IsProjectionSupremum {A : Type u} [Mul A] [Star A] [LE A]
    (S : Set A) (p : A) : Prop :=
  IsStarProjection p ∧
    (∀ q ∈ S, IsStarProjection q ∧ q ≤ p) ∧
    ∀ r, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r

/-- Challenge predicate asserting preservation of projection suprema by a star-algebra
equivalence and its inverse, relative to the supplied order relations. Paper: §3. -/
def IsNormalStarAlgEquiv
    {A : Type u} {B : Type v}
    [Add A] [Mul A] [SMul ℂ A] [Star A] [LE A]
    [Add B] [Mul B] [SMul ℂ B] [Star B] [LE B]
    (e : A ≃⋆ₐ[ℂ] B) : Prop :=
  (∀ (S : Set A) (p : A),
    IsProjectionSupremum S p →
    IsProjectionSupremum (e '' S) (e p)) ∧
  ∀ (S : Set B) (p : B),
    IsProjectionSupremum S p →
    IsProjectionSupremum (e.symm '' S) (e.symm p)

/-- Challenge trace-preserving factor witness. Paper: §3. -/
structure TracialGroupFactorEquiv
    (G : CountableDiscreteGroup.{u}) (H : CountableDiscreteGroup.{v}) where
  toStarAlgEquiv :
    GroupVonNeumannAlgebra G ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra H
  normal : IsNormalStarAlgEquiv toStarAlgEquiv
  trace_preserving :
    ∀ x, canonicalTrace H (toStarAlgEquiv x) = canonicalTrace G x

/-- Challenge factor-isomorphism predicate. Paper: §3. -/
def TracialGroupFactorsIsomorphic
    (G : CountableDiscreteGroup.{u}) (H : CountableDiscreteGroup.{v}) : Prop :=
  Nonempty (TracialGroupFactorEquiv G H)

end

end Connes

namespace Connes

/- The cited EJZK input is property (T) for the elementary subgroup
`EL₃(𝔽₂[t])`; the solution proves its identification with `SL₃`. Paper: §4. -/
namespace SpecialLinear

abbrev F := ZMod 2
abbrev R := Polynomial F
abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) R

noncomputable instance : Countable R := by
  exact Countable.of_equiv (AddMonoidAlgebra F ℕ)
    (Polynomial.toFinsuppIso F).toEquiv.symm

noncomputable instance : Countable (Matrix (Fin 3) (Fin 3) R) := by
  change Countable (Fin 3 → Fin 3 → R)
  infer_instance

noncomputable instance : Countable SL3 := by
  change Countable {A : Matrix (Fin 3) (Fin 3) R // A.det = 1}
  infer_instance

/-- The subgroup generated by elementary transvections. Paper: §4. -/
noncomputable def elementarySubgroup : Subgroup SL3 :=
  Subgroup.closure {g | ∃ (i j : Fin 3) (hij : i ≠ j) (a : R),
    g = Matrix.SpecialLinearGroup.transvection hij a}

end SpecialLinear

namespace PaperPropertyT

/-- The elementary subgroup appearing in the cited EJZK theorem. Paper: §4. -/
noncomputable def elementaryGroup : CountableDiscreteGroup :=
  { Carrier := SpecialLinear.elementarySubgroup
    group := inferInstance
    countable := inferInstance }

end PaperPropertyT

/-- Comparator statement for Zhou's Theorem A at the explicit EJZK boundary.
Assuming the cited property-(T) input for `EL₃(𝔽₂[t])`, it asserts the
existence of two countable discrete ICC groups satisfying the formal
property-(T) predicate that are not isomorphic although their group von
Neumann algebras are related by a trace-preserving normal star-algebra
equivalence. The solution proves `EL₃ = SL₃` and every other certificate used in
the conclusion. Paper: §7. -/
theorem theoremA
    (hEJZK : HasKazhdanPropertyT PaperPropertyT.elementaryGroup) :
    ∃ Γ₁ Γ₂ : CountableDiscreteGroup.{0},
      HasKazhdanPropertyT Γ₁ ∧ HasKazhdanPropertyT Γ₂ ∧
      IsICC Γ₁ ∧ IsICC Γ₂ ∧
      TracialGroupFactorsIsomorphic Γ₁ Γ₂ ∧
      ¬ Nonempty (Γ₁ ≃* Γ₂) := by
  sorry

end Connes
