/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

New standalone interfaces for the SL₃(F₂[t]) part of Zhou §§4–6. The
OpenAI/ten-proofs Connes work is cited as a public design reference at commit
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6. Modifications: this file narrows
the API to the paper's finite-field polynomial ring and leaves row reduction,
ICC, and property-(T) proofs open.
-/
import Mathlib
import Connes.Core

namespace Connes
namespace SpecialLinear

/-- Characteristic-two scalar field. Paper: §§2, 4. -/
abbrev F := ZMod 2
/-- Polynomial coefficient ring. Paper: §2. -/
abbrev R := Polynomial F
/-- Special-linear group carrier. Paper: §§2, 4. -/
abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) R

/-- Conjugacy equality is equivalent to commuting with a quotient conjugator. Paper: §5. -/
theorem conjugates_eq_iff_quotient_commutes
    {G : Type*} [Group G] (u v g : G) :
    u * g * u⁻¹ = v * g * v⁻¹ ↔ Commute (v⁻¹ * u) g := by
  constructor
  · intro h
    change (v⁻¹ * u) * g = g * (v⁻¹ * u)
    calc
      (v⁻¹ * u) * g = v⁻¹ * (u * g * u⁻¹) * u := by group
      _ = v⁻¹ * (v * g * v⁻¹) * u := by rw [h]
      _ = g * (v⁻¹ * u) := by group
  · intro h
    change (v⁻¹ * u) * g = g * (v⁻¹ * u) at h
    calc
      u * g * u⁻¹ = v * ((v⁻¹ * u) * g) * u⁻¹ := by group
      _ = v * (g * (v⁻¹ * u)) * u⁻¹ := by rw [h]
      _ = v * g * v⁻¹ := by group

/-- Transvection conjugacy equality is equivalent to a commuting relation. Paper: §5. -/
theorem transvection_conjugates_eq_iff_commutes
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    {i j : ι} (hij : i ≠ j) (a b : A)
    (g : Matrix.SpecialLinearGroup ι A) :
    Matrix.SpecialLinearGroup.transvection hij a * g *
        (Matrix.SpecialLinearGroup.transvection hij a)⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij b * g *
        (Matrix.SpecialLinearGroup.transvection hij b)⁻¹ ↔
      Commute (Matrix.SpecialLinearGroup.transvection hij (a - b)) g := by
  rw [conjugates_eq_iff_quotient_commutes,
    Matrix.SpecialLinearGroup.transvection_inv,
    ← Matrix.SpecialLinearGroup.transvection_add]
  simp only [add_comm, sub_eq_add_neg]

/-- A nonzero commuting transvection forces its matrix unit to commute. Paper: §5. -/
theorem commute_matrixUnit_of_commute_nonzero_transvection
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A] [IsDomain A]
    {i j : ι} (hij : i ≠ j) (a : A) (ha : a ≠ 0)
    (g : Matrix.SpecialLinearGroup ι A)
    (h : Commute (Matrix.SpecialLinearGroup.transvection hij a) g) :
    Commute (Matrix.single i j (1 : A)) (g : Matrix ι ι A) := by
  have hmatrix := congrArg
    (fun u : Matrix.SpecialLinearGroup ι A => (u : Matrix ι ι A)) h.eq
  change ((1 : Matrix ι ι A) + Matrix.single i j a) *
    (g : Matrix ι ι A) = (g : Matrix ι ι A) *
      ((1 : Matrix ι ι A) + Matrix.single i j a) at hmatrix
  have hsingle : Matrix.single i j a * (g : Matrix ι ι A) =
      (g : Matrix ι ι A) * Matrix.single i j a := by
    simpa only [Matrix.add_mul, one_mul, Matrix.mul_add, mul_one, add_right_inj] using hmatrix
  have hrepr : Matrix.single i j a = a • Matrix.single i j (1 : A) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hrepr, Matrix.smul_mul, Matrix.mul_smul] at hsingle
  change Matrix.single i j (1 : A) * (g : Matrix ι ι A) =
    (g : Matrix ι ι A) * Matrix.single i j (1 : A)
  ext k l
  have hentry := congrArg (fun M : Matrix ι ι A => M k l) hsingle
  simpa only [Matrix.smul_apply, smul_eq_mul] using
    (mul_left_cancel₀ ha hentry)

/-- Noncommuting matrix units make transvection conjugation injective. Paper: §5. -/
theorem transvection_conjugates_injective_of_not_commute_matrixUnit
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A] [IsDomain A]
    {i j : ι} (hij : i ≠ j)
    (g : Matrix.SpecialLinearGroup ι A)
    (hnot : ¬Commute (Matrix.single i j (1 : A)) (g : Matrix ι ι A)) :
    Function.Injective (fun a : A =>
      Matrix.SpecialLinearGroup.transvection hij a * g *
        (Matrix.SpecialLinearGroup.transvection hij a)⁻¹) := by
  intro a b hab
  by_contra hne
  apply hnot
  apply commute_matrixUnit_of_commute_nonzero_transvection hij (a - b)
    (sub_ne_zero.mpr hne) g
  exact (transvection_conjugates_eq_iff_commutes hij a b g).mp hab

/-- Scaling preserves transvection-conjugation injectivity. Paper: §5. -/
theorem scaled_transvection_conjugates_injective
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A] [IsDomain A]
    {i j : ι} (hij : i ≠ j)
    (g : Matrix.SpecialLinearGroup ι A)
    (hnot : ¬Commute (Matrix.single i j (1 : A)) (g : Matrix ι ι A))
    (c : A) (hc : c ≠ 0) :
    Function.Injective (fun a : A =>
      Matrix.SpecialLinearGroup.transvection hij (c * a) * g *
        (Matrix.SpecialLinearGroup.transvection hij (c * a))⁻¹) := by
  intro a b hab
  apply mul_left_cancel₀ hc
  exact transvection_conjugates_injective_of_not_commute_matrixUnit
    hij g hnot hab

/-- Scalar special-linear elements have bounded power. Paper: §5. -/
theorem specialLinear_scalar_pow_card_eq_one
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    (g : Matrix.SpecialLinearGroup ι A)
    (hscalar : (g : Matrix ι ι A) ∈ Set.range (Matrix.scalar ι)) :
    g ^ Fintype.card ι = 1 := by
  obtain ⟨a, ha⟩ := hscalar
  have hroot : a ^ Fintype.card ι = 1 := by
    simpa only [← ha, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ] using g.property
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((g : Matrix ι ι A) ^ Fintype.card ι) i j =
    (1 : Matrix ι ι A) i j
  rw [← ha, ← map_pow (Matrix.scalar ι), hroot, map_one]

/-- Special-linear transvections are injective in their scalar. Paper: §5. -/
theorem specialLinear_transvection_injective
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]
    {i j : ι} (hij : i ≠ j) :
    Function.Injective (Matrix.SpecialLinearGroup.transvection hij :
      A → Matrix.SpecialLinearGroup ι A) := by
  intro a b hab
  have hentry := congrArg (fun u : Matrix.SpecialLinearGroup ι A => u i j) hab
  simpa only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, ne_eq, hij,
    not_false_eq_true, Matrix.one_apply_ne, Matrix.single_apply_same, zero_add] using hentry

/-- Nontrivial special-linear subgroup elements have infinite conjugacy orbits. Paper: §5. -/
theorem specialLinear_subgroup_conjugacy_infinite
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [CommRing A]
    [IsDomain A] [Infinite A]
    (H : Subgroup (Matrix.SpecialLinearGroup ι A))
    (c : A) (hc : c ≠ 0)
    (hmem : ∀ {i j : ι} (hij : i ≠ j) (a : A),
      Matrix.SpecialLinearGroup.transvection hij (c * a) ∈ H)
    (htf : ∀ h : H, IsOfFinOrder h → h = 1)
    (g : H) (hg : g ≠ 1) :
    (Set.range fun h : H => h * g * h⁻¹).Infinite := by
  have hnot_scalar : ¬(g.val : Matrix ι ι A) ∈ Set.range (Matrix.scalar ι) := by
    intro hscalar
    have hpow : g.val ^ Fintype.card ι = 1 :=
      specialLinear_scalar_pow_card_eq_one g.val hscalar
    have hpow' : g ^ Fintype.card ι = 1 := by
      apply Subtype.ext
      exact hpow
    have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
    exact hg (htf g (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨Fintype.card ι, hcard, hpow'⟩))
  have hnot_all : ¬∀ (i j : ι), i ≠ j →
      Commute (Matrix.single i j (1 : A)) (g.val : Matrix ι ι A) := by
    intro hcomm
    exact hnot_scalar (Matrix.mem_range_scalar_of_commute_single hcomm)
  push Not at hnot_all
  obtain ⟨i, j, hij, hnot⟩ := hnot_all
  let lift (a : A) : H :=
    ⟨Matrix.SpecialLinearGroup.transvection hij (c * a), hmem hij a⟩
  have hinj : Function.Injective (fun a : A => lift a * g * (lift a)⁻¹) := by
    intro a b hab
    apply scaled_transvection_conjugates_injective
      hij g.val hnot c hc
    simpa only [Subgroup.coe_mul, InvMemClass.coe_inv] using congrArg (fun h : H => h.val) hab
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨a, rfl⟩
  exact ⟨lift a, rfl⟩

/-- Countability of the polynomial ring. Paper: §4. -/
noncomputable instance : Countable R := by
  exact Countable.of_equiv (ℕ →₀ F)
    (AddMonoidAlgebra.coeffEquiv.symm.trans (Polynomial.toFinsuppIso F).toEquiv.symm)

/-- Countability of the matrix carrier. Paper: §4. -/
noncomputable instance : Countable (Matrix (Fin 3) (Fin 3) R) := by
  change Countable (Fin 3 → Fin 3 → R)
  infer_instance

/-- Countability of the special-linear carrier. Paper: §4. -/
noncomputable instance : Countable SL3 := by
  change Countable {A : Matrix (Fin 3) (Fin 3) R // A.det = 1}
  infer_instance

/-- Elementary subgroup boundary. Paper: §4. -/
noncomputable def elementarySubgroup : Subgroup SL3 := ⊤

/-- Elementary-generation statement. Paper: §4. -/
def ElementaryGeneration : Prop :=
  ∀ g : SL3, g ∈ elementarySubgroup

/-- Elementary-generation conclusion. Paper: §4. -/
theorem sl3_eq_elementary : ElementaryGeneration := by
  sorry

/-- Countable discrete acting-group carrier. Paper: §§4, 5. -/
noncomputable def sl3Group : CountableDiscreteGroup where
  Carrier := SL3
  group := inferInstance
  countable := by infer_instance

/-- ICC boundary for the special-linear group. Paper: §5. -/
theorem sl3_isICC : IsICC sl3Group := by
  sorry

/-- Abelian-normal-subgroup obstruction boundary. Paper: §6. -/
def no_nontrivial_abelian_normal_subgroup : Prop := by
  sorry

end SpecialLinear
end Connes
