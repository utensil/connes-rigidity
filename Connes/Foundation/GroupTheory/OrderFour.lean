/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Mechanical transfer of the order-four obstruction lemmas from
OpenAI/ten-proofs, `ConnesRigidity.lean:36636-36694`, into the Zhou §6
directory. These are generic group proofs and are independent of the
construction-specific invariant still open in the Zhou skeleton.
-/
import Connes.Core

namespace Connes
namespace OpenAIPort

universe u v w

/-- Absence of elements of exact order four. Paper: §6. -/
def HasNoOrderFour (G : Type u) [Group G] : Prop :=
  ∀ g : G, g ^ 4 = 1 → g ^ 2 = 1

/-- Characterization of exact order four. Paper: §6. -/
theorem orderOf_eq_four_iff {G : Type u} [Group G] (g : G) :
    orderOf g = 4 ↔ g ^ 4 = 1 ∧ g ^ 2 ≠ 1 := by
  constructor
  · intro hg
    refine ⟨?_, ?_⟩
    · simpa only [hg] using pow_orderOf_eq_one g
    · intro hsquare
      have hdiv : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hsquare
      norm_num [hg] at hdiv
  · rintro ⟨hfour, hsquare⟩
    simpa only [Nat.reduceAdd, Nat.reducePow] using
      (orderOf_eq_prime_pow (p := 2) (n := 1)
        (by simpa only [pow_one, ne_eq] using hsquare)
        (by simpa only [Nat.reduceAdd, Nat.reducePow] using hfour))

/-- Fourth-power torsion lies in the kernel of a torsion-free quotient. Paper: §6. -/
theorem mem_ker_of_pow_four_eq_one_of_no_nontrivial_torsion
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    (π : G →* Q)
    (hQ : ∀ q : Q, IsOfFinOrder q → q = 1)
    {g : G} (hg : g ^ 4 = 1) :
    g ∈ π.ker := by
  apply MonoidHom.mem_ker.mpr
  apply hQ
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨4, by norm_num, ?_⟩
  simpa only [map_pow, map_one] using congrArg π hg

/-- Quotient torsion control implies the absence of order four. Paper: §6. -/
theorem hasNoOrderFour_of_quotient_without_nontrivial_torsion
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    (π : G →* Q)
    (hQ : ∀ q : Q, IsOfFinOrder q → q = 1)
    (hker : ∀ g : G, g ∈ π.ker → g ^ 2 = 1) :
    HasNoOrderFour G := by
  intro g hg
  exact hker g
    (mem_ker_of_pow_four_eq_one_of_no_nontrivial_torsion π hQ hg)

/-- Kernel containment in an exponent-two subgroup implies no order four. Paper: §6. -/
theorem hasNoOrderFour_of_quotient_without_nontrivial_torsion_of_kernel_le_range
    {G : Type u} {Q : Type v} {N : Type w}
    [Group G] [Group Q] [Group N]
    (π : G →* Q) (ι : N →* G)
    (hQ : ∀ q : Q, IsOfFinOrder q → q = 1)
    (hker : π.ker ≤ ι.range)
    (hN : ∀ n : N, n ^ 2 = 1) :
    HasNoOrderFour G := by
  apply hasNoOrderFour_of_quotient_without_nontrivial_torsion π hQ
  intro g hg
  obtain ⟨n, hn⟩ := hker hg
  subst g
  simpa only [map_pow, map_one] using congrArg ι (hN n)

/-- Semidirect products inherit order-four control from their factors. Paper: §6. -/
theorem semidirect_hasNoOrderFour_of_no_nontrivial_torsion_of_exponentTwo
    {N : Type u} {Q : Type v} [Group N] [Group Q]
    (φ : Q →* MulAut N)
    (hQ : ∀ q : Q, IsOfFinOrder q → q = 1)
    (hN : ∀ n : N, n ^ 2 = 1) :
    HasNoOrderFour (N ⋊[φ] Q) := by
  apply hasNoOrderFour_of_quotient_without_nontrivial_torsion_of_kernel_le_range
    (SemidirectProduct.rightHom : (N ⋊[φ] Q) →* Q)
    (SemidirectProduct.inl : N →* N ⋊[φ] Q)
    hQ
  · exact le_of_eq SemidirectProduct.range_inl_eq_ker_rightHom.symm
  · exact hN

end OpenAIPort
end Connes
