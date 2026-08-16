/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 42-242.
Modifications: extracted the minimal group, representation, regular-factor,
and tracial-equivalence vocabulary; changed namespace and narrowed the
interface to arXiv:2608.02327. See docs/PORT_MAP.md.
-/
import Mathlib

namespace Connes

universe u v

/-- Countable discrete group carrier. Paper: §7. -/
structure CountableDiscreteGroup where
  Carrier : Type u
  group : Group Carrier
  countable : Countable Carrier

namespace CountableDiscreteGroup

/-- Coercion from the group wrapper to its carrier. Paper: §7. -/
instance : CoeSort CountableDiscreteGroup (Type u) :=
  ⟨CountableDiscreteGroup.Carrier⟩

attribute [instance] group countable

end CountableDiscreteGroup

/-- ICC predicate boundary. Paper: §5. -/
def IsICC (G : CountableDiscreteGroup) : Prop :=
  Infinite G ∧ ∀ g : G, g ≠ 1 → Set.Infinite (conjugatesOf g)

/-- Unitary-representation carrier. Paper: §4. -/
abbrev UnitaryRepresentation
    (G : Type u) [Group G]
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  G →* unitary (H →L[ℂ] H)

namespace UnitaryRepresentation

variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Invariant-vector predicate. Paper: §4. -/
def IsInvariant (π : UnitaryRepresentation G H) (ξ : H) : Prop :=
  ∀ g : G, (π g : H →L[ℂ] H) ξ = ξ

/-- Almost-invariant-vector predicate. Paper: §4. -/
def HasAlmostInvariantUnitVectors (π : UnitaryRepresentation G H) : Prop :=
  ∀ (K : Finset G) (ε : ℝ), 0 < ε →
    ∃ ξ : H, ‖ξ‖ = 1 ∧ ∀ g ∈ K, ‖(π g : H →L[ℂ] H) ξ - ξ‖ < ε

end UnitaryRepresentation

/-- Property-(T) predicate boundary. Paper: §4. -/
def HasKazhdanPropertyT (G : CountableDiscreteGroup.{u}) : Prop :=
  ∀ (H : Type u)
    (_ : NormedAddCommGroup H)
    (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H)
    (π : UnitaryRepresentation G H),
    π.HasAlmostInvariantUnitVectors →
      ∃ ξ : H, ξ ≠ 0 ∧ π.IsInvariant ξ

/-- Relative property-(T) for a group and a subgroup. Paper: §4. -/
def HasRelativePropertyT
    (G : CountableDiscreteGroup.{u}) (N : Subgroup G) : Prop :=
  ∀ (H : Type u)
    (_ : NormedAddCommGroup H)
    (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H)
    (π : UnitaryRepresentation G H),
    π.HasAlmostInvariantUnitVectors →
      ∃ ξ : H, ξ ≠ 0 ∧
        ∀ n : N, (π (n : G) : H →L[ℂ] H) ξ = ξ

noncomputable section

open scoped NNReal ENNReal

/-- Group-indexed Hilbert carrier. Paper: §3. -/
abbrev GroupL2 (G : Type u) := lp (fun _ : G ↦ ℂ) 2

/-- Reindexing equivalence for group-indexed Hilbert spaces. Paper: §3. -/
def l2Reindex {α : Type u} {β : Type v} (e : α ≃ β) :
    GroupL2 α ≃ₗᵢ[ℂ] GroupL2 β where
  toLinearEquiv :=
    { toFun := fun f ↦ ⟨(fun j : β ↦ f (e.symm j)), by
        change Memℓp (fun j : β ↦ f (e.symm j)) 2
        rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
        exact (e.symm.summable_iff).2
          ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩
      invFun := fun f ↦ ⟨(fun j : α ↦ f (e j)), by
        change Memℓp (fun j : α ↦ f (e j)) 2
        rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
        exact e.summable_iff.mpr
          ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩
      left_inv := by
        intro f
        ext i
        change f (e.symm (e i)) = f i
        simp
      right_inv := by
        intro f
        ext j
        change f (e (e.symm j)) = f j
        simp
      map_add' := by
        intro f g
        ext j
        rfl
      map_smul' := by
        intro c f
        ext j
        rfl }
  norm_map' := by
    intro f
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    congr 1
    exact e.symm.tsum_eq (fun i ↦ ‖f i‖ ^ (2 : ℝ≥0∞).toReal)

/-- Left-regular unitary boundary. Paper: §3. -/
def leftRegularUnitary {G : Type u} [Group G] (g : G) :
    unitary (GroupL2 G →L[ℂ] GroupL2 G) :=
  Unitary.linearIsometryEquiv.symm (l2Reindex (Equiv.mulLeft g))

/-- Left-regular representation boundary. Paper: §3. -/
def leftRegularRepresentation (G : Type u) [Group G] :
    G →* unitary (GroupL2 G →L[ℂ] GroupL2 G) where
  toFun := leftRegularUnitary
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    ext h
    change f ((1 : G)⁻¹ * h) = f h
    simp
  map_mul' g h := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro f
    ext k
    change f ((g * h)⁻¹ * k) = f (h⁻¹ * (g⁻¹ * k))
    simp [mul_assoc]

/-- Von Neumann closure boundary. Paper: §3. -/
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

/-- Group von Neumann algebra boundary. Paper: §3. -/
def groupVonNeumannAlgebra (G : CountableDiscreteGroup.{u}) :
    VonNeumannAlgebra (GroupL2 G) :=
  vonNeumannClosure (Set.range fun g : G ↦
    (leftRegularRepresentation G g : GroupL2 G →L[ℂ] GroupL2 G))

/-- Group von Neumann algebra carrier. Paper: §3. -/
abbrev GroupVonNeumannAlgebra (G : CountableDiscreteGroup.{u}) :=
  (groupVonNeumannAlgebra G).toStarSubalgebra

/-- Point-mass basis vector boundary. Paper: §3. -/
def delta (G : CountableDiscreteGroup.{u}) (g : G) : GroupL2 G :=
  by
    classical
    exact lp.single 2 g 1

/-- Canonical trace boundary. Paper: §3. -/
def canonicalTrace (G : CountableDiscreteGroup.{u}) :
    GroupVonNeumannAlgebra G → ℂ :=
  fun x ↦ inner ℂ (delta G 1) ((x : GroupL2 G →L[ℂ] GroupL2 G) (delta G 1))

/-- The inherited operator order agrees with the algebraic order on group-factor projections. -/
theorem GroupVonNeumannAlgebra.projection_le_iff_mul_eq_left
    {G : CountableDiscreteGroup.{u}}
    {p q : GroupVonNeumannAlgebra G}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ p * q = p := by
  have hp' : IsStarProjection (p : GroupL2 G →L[ℂ] GroupL2 G) :=
    hp.map (groupVonNeumannAlgebra G).toStarSubalgebra.subtype
  have hq' : IsStarProjection (q : GroupL2 G →L[ℂ] GroupL2 G) :=
    hq.map (groupVonNeumannAlgebra G).toStarSubalgebra.subtype
  rw [← Subtype.coe_le_coe, hp'.le_iff_mul_eq_left hq']
  exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩

/-- A star-algebra equivalence preserves operator order between group-factor projections. -/
theorem GroupVonNeumannAlgebra.starAlgEquiv_map_le_map_iff
    {G : CountableDiscreteGroup.{u}} {H : CountableDiscreteGroup.{v}}
    (e : GroupVonNeumannAlgebra G ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra H)
    {p q : GroupVonNeumannAlgebra G}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    e p ≤ e q ↔ p ≤ q := by
  rw [projection_le_iff_mul_eq_left (hp.map e) (hq.map e),
    projection_le_iff_mul_eq_left hp hq]
  exact ⟨fun h ↦ by
      simpa only [map_mul, StarAlgEquiv.symm_apply_apply] using congrArg e.symm h,
    fun h ↦ by simpa only [map_mul] using congrArg e h⟩

/-- Projection-supremum predicate in the group-factor operator order. Paper: §3. -/
def IsProjectionSupremum {G : CountableDiscreteGroup.{u}}
    (S : Set (GroupVonNeumannAlgebra G))
    (p : GroupVonNeumannAlgebra G) : Prop :=
  IsStarProjection p ∧
    (∀ q ∈ S, IsStarProjection q ∧ q ≤ p) ∧
    ∀ r, IsStarProjection r → (∀ q ∈ S, q ≤ r) → p ≤ r

/-- A star-algebra equivalence carries a projection supremum to its image. -/
theorem IsProjectionSupremum.map_starAlgEquiv
    {G : CountableDiscreteGroup.{u}} {H : CountableDiscreteGroup.{v}}
    (e : GroupVonNeumannAlgebra G ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra H)
    {S : Set (GroupVonNeumannAlgebra G)} {p : GroupVonNeumannAlgebra G}
    (hp : IsProjectionSupremum S p) :
    IsProjectionSupremum (e '' S) (e p) := by
  refine ⟨hp.1.map e, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact ⟨(hp.2.1 q hq).1.map e,
      (GroupVonNeumannAlgebra.starAlgEquiv_map_le_map_iff
        e (hp.2.1 q hq).1 hp.1).2 (hp.2.1 q hq).2⟩
  · intro r hr hupper
    have hr' : IsStarProjection (e.symm r) := hr.map e.symm
    have hbound : ∀ q ∈ S, q ≤ e.symm r := by
      intro q hq
      have h := hupper (e q) ⟨q, hq, rfl⟩
      simpa only [StarAlgEquiv.symm_apply_apply] using
        (GroupVonNeumannAlgebra.starAlgEquiv_map_le_map_iff
          e.symm ((hp.2.1 q hq).1.map e) hr).2 h
    have h := hp.2.2 (e.symm r) hr' hbound
    have h' : e.symm (e p) ≤ e.symm r := by
      simpa only [StarAlgEquiv.symm_apply_apply] using h
    exact (GroupVonNeumannAlgebra.starAlgEquiv_map_le_map_iff
      e.symm (hp.1.map e) hr).1 h'

/-- Normal star-algebra equivalence boundary. Paper: §3. -/
def IsNormalStarAlgEquiv
    {G : CountableDiscreteGroup.{u}} {H : CountableDiscreteGroup.{v}}
    (e : GroupVonNeumannAlgebra G ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra H) : Prop :=
  (∀ (S : Set (GroupVonNeumannAlgebra G)) (p : GroupVonNeumannAlgebra G),
    IsProjectionSupremum S p →
    IsProjectionSupremum (e '' S) (e p)) ∧
  ∀ (S : Set (GroupVonNeumannAlgebra H)) (p : GroupVonNeumannAlgebra H),
    IsProjectionSupremum S p →
    IsProjectionSupremum (e.symm '' S) (e.symm p)

/-- Every star-algebra equivalence between group factors preserves projection suprema. -/
theorem GroupVonNeumannAlgebra.starAlgEquiv_isNormal
    {G : CountableDiscreteGroup.{u}} {H : CountableDiscreteGroup.{v}}
    (e : GroupVonNeumannAlgebra G ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra H) :
    IsNormalStarAlgEquiv e :=
  ⟨fun _ _ ↦ IsProjectionSupremum.map_starAlgEquiv e,
    fun _ _ ↦ IsProjectionSupremum.map_starAlgEquiv e.symm⟩

/-- Trace-preserving factor-equivalence witness. Paper: §3. -/
structure TracialGroupFactorEquiv
    (G : CountableDiscreteGroup.{u}) (H : CountableDiscreteGroup.{v}) where
  toStarAlgEquiv :
    GroupVonNeumannAlgebra G ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra H
  normal : IsNormalStarAlgEquiv toStarAlgEquiv
  trace_preserving :
    ∀ x, canonicalTrace H (toStarAlgEquiv x) = canonicalTrace G x

/-- Trace-preserving factor-isomorphism predicate. Paper: §3. -/
def TracialGroupFactorsIsomorphic
    (G : CountableDiscreteGroup.{u}) (H : CountableDiscreteGroup.{v}) : Prop :=
  Nonempty (TracialGroupFactorEquiv G H)

end

end Connes
