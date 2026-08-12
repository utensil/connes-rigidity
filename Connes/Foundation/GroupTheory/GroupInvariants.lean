/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Mechanical transfer of the group-invariant and commensurability layer from
OpenAI/ten-proofs, `ConnesRigidity.lean:13952-14028`, into the Zhou §6
directory. The declarations are generic and retain the source proof terms;
the Zhou-specific invariant is still a separate construction obligation.
-/
import Connes.Core

namespace Connes
namespace OpenAIPort

universe u

/-- Group-valued cardinal invariant interface. Paper: §6. -/
structure GroupCardinalInvariant where
  carrier : CountableDiscreteGroup.{u} → Type u
  map_mulEquiv : ∀ {G H : CountableDiscreteGroup.{u}},
    (G ≃* H) → carrier G ≃ carrier H

namespace GroupCardinalInvariant

/-- Natural-number value of a group cardinal invariant. Paper: §6. -/
noncomputable def value (I : GroupCardinalInvariant.{u})
    (G : CountableDiscreteGroup.{u}) : ℕ :=
  Nat.card (I.carrier G)

/-- Group cardinal invariants are preserved by group equivalence. Paper: §6. -/
theorem value_mulEquiv (I : GroupCardinalInvariant.{u})
    {G H : CountableDiscreteGroup.{u}} (e : G ≃* H) :
    I.value G = I.value H :=
  Nat.card_congr (I.map_mulEquiv e)

end GroupCardinalInvariant

/-- Injectivity of the power-of-two parameter used by the invariant. Paper: §6. -/
theorem paperInvariantCard_injective {m n : ℕ}
    (h : 2 ^ (4 * m) = 2 ^ (4 * n)) : m = n := by
  have hmul : 4 * m = 4 * n :=
    Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < (4 : ℕ)) hmul

/-- Injective homomorphism with a recorded finite index. Paper: §6. -/
structure ExactIndexEmbedding
    (G H : CountableDiscreteGroup.{u}) (index : ℕ) where
  hom : G →* H
  injective : Function.Injective hom
  index_eq : hom.range.index = index

namespace ExactIndexEmbedding

variable {G H : CountableDiscreteGroup.{u}} {index : ℕ}

/-- Equivalence from an injective homomorphism to its range. Paper: §6. -/
noncomputable def rangeEquiv (f : ExactIndexEmbedding G H index) :
    G ≃* f.hom.range :=
  MonoidHom.ofInjective f.injective

/-- A nonzero recorded index makes the homomorphism range finite index. Paper: §6. -/
theorem range_finiteIndex (f : ExactIndexEmbedding G H index)
    (hindex : index ≠ 0) : f.hom.range.FiniteIndex :=
  Subgroup.finiteIndex_iff.mpr (by simpa only [f.index_eq, ne_eq] using hindex)

end ExactIndexEmbedding

/-- Abstract commensurability through finite-index subgroups. Paper: §6. -/
def AbstractlyCommensurable
    (G H : CountableDiscreteGroup.{u}) : Prop :=
  ∃ (S : Subgroup G) (T : Subgroup H),
    S.FiniteIndex ∧ T.FiniteIndex ∧ Nonempty (S ≃* T)

/-- A common finite-index embedding implies abstract commensurability. Paper: §6. -/
theorem abstractlyCommensurable_of_common_embedding
    {A G H : CountableDiscreteGroup.{u}} {i j : ℕ}
    (f : ExactIndexEmbedding A G i) (g : ExactIndexEmbedding A H j)
    (hi : i ≠ 0) (hj : j ≠ 0) :
    AbstractlyCommensurable G H := by
  refine ⟨f.hom.range, g.hom.range,
    f.range_finiteIndex hi, g.range_finiteIndex hj, ?_⟩
  exact ⟨f.rangeEquiv.symm.trans g.rangeEquiv⟩

/-- Groups with and without an element of order four are not isomorphic. Paper: §6. -/
theorem not_groupsIsomorphic_of_orderFour
    {G H : CountableDiscreteGroup.{u}}
    (hG : ∃ g : G, orderOf g = 4)
    (hH : ∀ h : H, orderOf h ≠ 4) :
    ¬GroupsIsomorphic G H := by
  rintro ⟨e⟩
  obtain ⟨g, hg⟩ := hG
  exact hH (e g) (by simpa only [MulEquiv.orderOf_eq] using (e.orderOf_eq g).trans hg)

end OpenAIPort
end Connes
