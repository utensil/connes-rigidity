/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

New standalone interfaces for the SL₃(F₂[t]) part of Zhou §§4–6. The
OpenAI/ten-proofs Connes work is cited as a public design reference at commit
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6. Modifications: this file narrows
the API to the paper's finite-field polynomial ring and adapts its elementary
row-reduction argument from four dimensions to three; property (T) remains an
external paper input.
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

/-- Elementary transvections in `SL₃(F₂[t])`. Paper: §4. -/
def elementaryTransvections : Set SL3 :=
  {g | ∃ (i j : Fin 3) (hij : i ≠ j) (a : R),
    g = Matrix.SpecialLinearGroup.transvection hij a}

/-- The subgroup generated by elementary transvections. Paper: §4. -/
noncomputable def elementarySubgroup : Subgroup SL3 :=
  Subgroup.closure elementaryTransvections

/-- Elementary-generation statement. Paper: §4. -/
def ElementaryGeneration : Prop :=
  ∀ g : SL3, g ∈ elementarySubgroup

namespace ElementaryGenerationProof

open Matrix
open scoped BigOperators

abbrev Index := Fin 3
abbrev V := Index → R

theorem transvection_mem (i j : Index) (h : i ≠ j) (c : R) :
    Matrix.SpecialLinearGroup.transvection h c ∈ elementarySubgroup :=
  Subgroup.subset_closure ⟨i, j, h, c, rfl⟩

theorem transvection_smul_same (i j : Index) (h : i ≠ j) (c : R)
    (v : V) :
    (Matrix.SpecialLinearGroup.transvection h c • v) i = v i + c * v j := by
  change ((Matrix.SpecialLinearGroup.transvection h c).val *ᵥ v) i = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, Function.update_self]

theorem transvection_smul_other (i j k : Index) (h : i ≠ j)
    (hk : k ≠ i) (c : R) (v : V) :
    (Matrix.SpecialLinearGroup.transvection h c • v) k = v k := by
  change ((Matrix.SpecialLinearGroup.transvection h c).val *ᵥ v) k = _
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
      Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, ne_eq, hk, not_false_eq_true,
    Function.update_of_ne, Pi.zero_apply, add_zero]

noncomputable def coordinateSwap (i j : Index) (h : i ≠ j) : SL3 :=
  Matrix.SpecialLinearGroup.transvection h 1 *
    Matrix.SpecialLinearGroup.transvection h.symm 1 *
    Matrix.SpecialLinearGroup.transvection h 1

theorem coordinateSwap_mem (i j : Index) (h : i ≠ j) :
    coordinateSwap i j h ∈ elementarySubgroup :=
  elementarySubgroup.mul_mem
    (elementarySubgroup.mul_mem (transvection_mem i j h 1)
      (transvection_mem j i h.symm 1))
    (transvection_mem i j h 1)

theorem coordinateSwap_smul_left (i j : Index) (h : i ≠ j) (v : V) :
    (coordinateSwap i j h • v) i = v j := by
  simp only [coordinateSwap, mul_smul]
  rw [transvection_smul_same]
  rw [transvection_smul_other j i i h.symm h]
  rw [transvection_smul_same j i]
  rw [transvection_smul_same i j]
  rw [transvection_smul_other i j j h h.symm]
  simp only [one_mul]
  calc
    v i + v j + (v j + (v i + v j)) =
        (v i + v i) + (v j + v j) + v j := by ac_rfl
    _ = v j := by simp only [CharTwo.add_self_eq_zero, zero_add]

theorem coordinateSwap_smul_right (i j : Index) (h : i ≠ j) (v : V) :
    (coordinateSwap i j h • v) j = v i := by
  simp only [coordinateSwap, mul_smul]
  rw [transvection_smul_other i j j h h.symm]
  rw [transvection_smul_same j i]
  rw [transvection_smul_same i j]
  rw [transvection_smul_other i j j h h.symm]
  simp only [one_mul]
  calc
    v j + (v i + v j) = (v j + v j) + v i := by ac_rfl
    _ = v i := by simp only [CharTwo.add_self_eq_zero, zero_add]

theorem coordinateSwap_smul_other (i j k : Index) (h : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (v : V) :
    (coordinateSwap i j h • v) k = v k := by
  simp only [coordinateSwap, mul_smul]
  rw [transvection_smul_other i j k h hki]
  rw [transvection_smul_other j i k h.symm hkj]
  rw [transvection_smul_other i j k h hki]

noncomputable def euclideanStep (i j : Index) (h : i ≠ j) (a b : R) : SL3 :=
  coordinateSwap i j h *
    Matrix.SpecialLinearGroup.transvection h.symm (b / a)

theorem euclideanStep_mem (i j : Index) (h : i ≠ j) (a b : R) :
    euclideanStep i j h a b ∈ elementarySubgroup :=
  elementarySubgroup.mul_mem (coordinateSwap_mem i j h)
    (transvection_mem j i h.symm (b / a))

theorem euclideanStep_smul_left (i j : Index) (h : i ≠ j) (v : V) :
    (euclideanStep i j h (v i) (v j) • v) i = v j % v i := by
  rw [euclideanStep, mul_smul, coordinateSwap_smul_left,
    transvection_smul_same]
  have hd := EuclideanDomain.div_add_mod (v j) (v i)
  calc
    v j + (v j / v i) * v i =
        (v i * (v j / v i) + v j % v i) + (v j / v i) * v i := by rw [hd]
    _ = (v i * (v j / v i) + v i * (v j / v i)) + v j % v i := by ac_rfl
    _ = v j % v i := by simp only [CharTwo.add_self_eq_zero, zero_add]

theorem euclideanStep_smul_right (i j : Index) (h : i ≠ j) (v : V) :
    (euclideanStep i j h (v i) (v j) • v) j = v i := by
  rw [euclideanStep, mul_smul, coordinateSwap_smul_right,
    transvection_smul_other _ _ _ h.symm h]

theorem euclideanStep_smul_other (i j k : Index) (h : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (v : V) :
    (euclideanStep i j h (v i) (v j) • v) k = v k := by
  rw [euclideanStep, mul_smul,
    coordinateSwap_smul_other i j k h hki hkj,
    transvection_smul_other _ _ _ h.symm hkj]

theorem transvection_fix_of_source_zero (i j : Index) (h : i ≠ j) (c : R)
    (w : V) (hw : w j = 0) :
    Matrix.SpecialLinearGroup.transvection h c • w = w := by
  funext k
  by_cases hk : k = i
  · subst k
    rw [transvection_smul_same i j h c w, hw]
    simp only [mul_zero, add_zero]
  · exact transvection_smul_other i j k h hk c w

theorem coordinateSwap_fix_of_pair_zero (i j : Index) (h : i ≠ j) (w : V)
    (hi : w i = 0) (hj : w j = 0) :
    coordinateSwap i j h • w = w := by
  rw [coordinateSwap, mul_smul, mul_smul,
    transvection_fix_of_source_zero i j h 1 w hj,
    transvection_fix_of_source_zero j i h.symm 1 w hi,
    transvection_fix_of_source_zero i j h 1 w hj]

theorem euclideanStep_fix_of_pair_zero (i j : Index) (h : i ≠ j)
    (a b : R) (w : V) (hi : w i = 0) (hj : w j = 0) :
    euclideanStep i j h a b • w = w := by
  rw [euclideanStep, mul_smul,
    transvection_fix_of_source_zero j i h.symm (b / a) w hi,
    coordinateSwap_fix_of_pair_zero i j h w hi hj]

theorem pair_reduce_strong (i j : Index) (h : i ≠ j) (v : V) :
    ∃ g : SL3, g ∈ elementarySubgroup ∧
      (g • v) i = EuclideanDomain.gcd (v i) (v j) ∧
      (g • v) j = 0 ∧
      (∀ k : Index, k ≠ i → k ≠ j → (g • v) k = v k) ∧
      (∀ w : V, w i = 0 → w j = 0 → g • w = w) := by
  let P : R → R → Prop := fun a b =>
    ∀ w : V, w i = a → w j = b →
      ∃ g : SL3, g ∈ elementarySubgroup ∧
        (g • w) i = EuclideanDomain.gcd a b ∧
        (g • w) j = 0 ∧
        (∀ k : Index, k ≠ i → k ≠ j → (g • w) k = w k) ∧
        (∀ z : V, z i = 0 → z j = 0 → g • z = z)
  have hp : P (v i) (v j) := by
    apply EuclideanDomain.GCD.induction (P := P) (v i) (v j)
    · intro b w hwi hwj
      refine ⟨coordinateSwap i j h, coordinateSwap_mem i j h, ?_, ?_, ?_, ?_⟩
      · rw [coordinateSwap_smul_left, hwj, EuclideanDomain.gcd_zero_left]
      · rw [coordinateSwap_smul_right, hwi]
      · intro k hki hkj
        exact coordinateSwap_smul_other i j k h hki hkj w
      · exact coordinateSwap_fix_of_pair_zero i j h
    · intro a b _ ih w hwi hwj
      let s : SL3 := euclideanStep i j h a b
      have hs : s ∈ elementarySubgroup := euclideanStep_mem i j h a b
      have hsi : (s • w) i = b % a := by
        dsimp [s]
        subst a
        subst b
        exact euclideanStep_smul_left i j h w
      have hsj : (s • w) j = a := by
        dsimp [s]
        subst a
        subst b
        exact euclideanStep_smul_right i j h w
      obtain ⟨g, hg, hgi, hgj, hgother, hgfix⟩ := ih (s • w) hsi hsj
      refine ⟨g * s, elementarySubgroup.mul_mem hg hs, ?_, ?_, ?_, ?_⟩
      · rw [mul_smul, hgi, EuclideanDomain.gcd_val a b]
      · rw [mul_smul, hgj]
      · intro k hki hkj
        rw [mul_smul, hgother k hki hkj]
        dsimp [s]
        subst a
        subst b
        exact euclideanStep_smul_other i j k h hki hkj w
      · intro z hzi hzj
        rw [mul_smul]
        have hsz : s • z = z :=
          euclideanStep_fix_of_pair_zero i j h a b z hzi hzj
        rw [hsz, hgfix z hzi hzj]
  exact hp v rfl rfl

theorem binaryPolynomial_eq_one_of_isUnit (p : R) (hp : IsUnit p) :
    p = 1 := by
  obtain ⟨a, ha, hpa⟩ := Polynomial.isUnit_iff.mp hp
  have ha' : a = 1 := by
    have hne : a ≠ 0 := ha.ne_zero
    fin_cases a <;> simp_all
  simpa only [ha', map_one] using hpa.symm

theorem matrix_mul_apply_as_smul (g A : SL3) (i j : Index) :
    (g * A) i j = (g • (fun k : Index => A k j)) i := by
  rfl

theorem first_column_reduce (A : SL3) :
    ∃ g : SL3, g ∈ elementarySubgroup ∧
      (g * A) 0 0 = 1 ∧
      (g * A) 1 0 = 0 ∧
      (g * A) 2 0 = 0 := by
  let v : V := fun i => A i 0
  obtain ⟨g₁, hg₁, _, hg₁1, _, _⟩ :=
    pair_reduce_strong (0 : Index) 1 (by decide) v
  obtain ⟨g₂, hg₂, _, hg₂2, hg₂other, _⟩ :=
    pair_reduce_strong (0 : Index) 2 (by decide) (g₁ • v)
  let g := g₂ * g₁
  have hg : g ∈ elementarySubgroup := elementarySubgroup.mul_mem hg₂ hg₁
  have h1 : (g • v) (1 : Index) = 0 := by
    dsimp [g]
    rw [mul_smul, hg₂other 1 (by decide) (by decide), hg₁1]
  have h2 : (g • v) (2 : Index) = 0 := by
    dsimp [g]
    rw [mul_smul, hg₂2]
  have hentry (i : Index) : (g * A) i 0 = (g • v) i :=
    matrix_mul_apply_as_smul g A i 0
  have hz1 : (g * A) (1 : Index) 0 = 0 := (hentry 1).trans h1
  have hz2 : (g * A) (2 : Index) 0 = 0 := (hentry 2).trans h2
  have hdet : ((g * A : SL3).val).det = 1 := (g * A).property
  rw [Matrix.det_succ_column_zero] at hdet
  change ((g.val * A.val) 1 0) = 0 at hz1
  change ((g.val * A.val) 2 0) = 0 at hz2
  have hproduct :
      (g * A) 0 0 * (((g * A : SL3).val).submatrix Fin.succ Fin.succ).det = 1 := by
    simpa only [Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, Nat.succ_eq_add_one,
      Nat.reduceAdd, Fin.sum_univ_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
      pow_zero, one_mul, Fin.succAbove_zero, Fin.val_succ, zero_add, pow_one,
      Fin.succ_zero_eq_one, hz1, mul_zero, zero_mul, even_two, Even.neg_pow,
      one_pow, Fin.succ_one_eq_two, hz2, Finset.univ_unique,
      Fin.default_eq_zero, Fin.val_eq_zero, Finset.sum_singleton,
      Fin.reduceSucc, add_zero] using hdet
  have hunit : IsUnit ((g * A) 0 0) := IsUnit.of_mul_eq_one _ hproduct
  exact ⟨g, hg, binaryPolynomial_eq_one_of_isUnit _ hunit, hz1, hz2⟩

theorem second_column_reduce (A : SL3)
    (h₁₀ : A (1 : Index) 0 = 0)
    (h₂₀ : A (2 : Index) 0 = 0) :
    ∃ p : SL3, p ∈ elementarySubgroup ∧
      (p * A) 1 0 = 0 ∧
      (p * A) 2 0 = 0 ∧
      (p * A) 2 1 = 0 := by
  let v₁ : V := fun k => A k 1
  obtain ⟨p, hp, _, hz₂₁, _, hfix⟩ :=
    pair_reduce_strong (1 : Index) 2 (by decide) v₁
  let v₀ : V := fun k => A k 0
  have hfix₀ : p • v₀ = v₀ := hfix v₀ h₁₀ h₂₀
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · change (p • v₀) (1 : Index) = 0
    rw [hfix₀]
    exact h₁₀
  · change (p • v₀) (2 : Index) = 0
    rw [hfix₀]
    exact h₂₀
  · exact hz₂₁

theorem fin_three_upperTriangular_of_three (A : SL3)
    (h10 : A (1 : Index) 0 = 0)
    (h20 : A (2 : Index) 0 = 0)
    (h21 : A (2 : Index) 1 = 0) :
    ∀ i j : Index, j < i → A i j = 0 := by
  intro i j hji
  have hval : j.val < i.val := hji
  fin_cases i
  · change j.val < 0 at hval
    omega
  · change j.val < 1 at hval
    have hj : j = 0 := Fin.ext (by omega)
    simpa only [Nat.reduceAdd, Fin.mk_one, Fin.isValue, hj] using h10
  · change j.val < 2 at hval
    have hj : j = 0 ∨ j = 1 := by
      by_cases hzero : j.val = 0
      · exact Or.inl (Fin.ext hzero)
      · exact Or.inr (Fin.ext (by omega))
    rcases hj with rfl | rfl
    · exact h20
    · exact h21

theorem upper_triangularize (A : SL3) :
    ∃ g : SL3, g ∈ elementarySubgroup ∧
      ∀ i j : Index, j < i → (g * A) i j = 0 := by
  obtain ⟨p₀, hp₀, _, h10, h20⟩ := first_column_reduce A
  obtain ⟨p₁, hp₁, h10', h20', h21⟩ :=
    second_column_reduce (p₀ * A) h10 h20
  let p : SL3 := p₁ * p₀
  have hp : p ∈ elementarySubgroup := elementarySubgroup.mul_mem hp₁ hp₀
  have hprod : p * A = p₁ * (p₀ * A) := by simp only [mul_assoc, p]
  refine ⟨p, hp, ?_⟩
  rw [hprod]
  exact fin_three_upperTriangular_of_three _ h10' h20' h21

theorem upperTriangular_diag_one (g : SL3)
    (htri : ∀ i j : Index, j < i → g i j = 0) (i : Index) :
    g i i = 1 := by
  have hblock : (g : Matrix Index Index R).BlockTriangular id := by
    intro k l hkl
    exact htri k l hkl
  have hprod : (∏ j : Index, g j j) = 1 := by
    calc
      (∏ j : Index, g j j) = (g : Matrix Index Index R).det :=
        (Matrix.det_of_upperTriangular hblock).symm
      _ = 1 := g.property
  have hdvd : g i i ∣ (∏ j : Index, g j j) :=
    Finset.dvd_prod_of_mem (fun j : Index => g j j) (Finset.mem_univ i)
  rw [hprod] at hdvd
  exact binaryPolynomial_eq_one_of_isUnit _ (isUnit_of_dvd_one hdvd)

theorem upperUnitriangular_factorization (g : SL3)
    (hu : ∀ i j : Index, j < i → g i j = 0)
    (hd : ∀ i : Index, g i i = 1) :
    g =
      Matrix.SpecialLinearGroup.transvection (show (1 : Index) ≠ 2 by decide)
        (g 1 2) *
      Matrix.SpecialLinearGroup.transvection (show (0 : Index) ≠ 2 by decide)
        (g 0 2) *
      Matrix.SpecialLinearGroup.transvection (show (0 : Index) ≠ 1 by decide)
        (g 0 1) := by
  have h00 := hd 0
  have h11 := hd 1
  have h22 := hd 2
  have h10 := hu 1 0 (by decide)
  have h20 := hu 2 0 (by decide)
  have h21 := hu 2 1 (by decide)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Matrix.add_apply, Matrix.one_apply, Fin.reduceEq, false_and,
      not_false_eq_true, Matrix.single_apply_of_ne, add_zero,
      Matrix.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, one_ne_zero, true_and,
      Fin.sum_univ_three, zero_ne_one, mul_ite, mul_one, mul_zero,
      zero_add, and_false, Finset.sum_ite_eq', and_true,
      h00, h11, h22, h10, h20, h21]

theorem upperUnitriangular_mem (g : SL3)
    (hu : ∀ i j : Index, j < i → g i j = 0)
    (hd : ∀ i : Index, g i i = 1) :
    g ∈ elementarySubgroup := by
  rw [upperUnitriangular_factorization g hu hd]
  exact elementarySubgroup.mul_mem
    (elementarySubgroup.mul_mem
      (transvection_mem 1 2 (by decide) (g 1 2))
      (transvection_mem 0 2 (by decide) (g 0 2)))
    (transvection_mem 0 1 (by decide) (g 0 1))

theorem all_mem_elementarySubgroup (A : SL3) : A ∈ elementarySubgroup := by
  obtain ⟨p, hp, hupper⟩ := upper_triangularize A
  have hunit : p * A ∈ elementarySubgroup :=
    upperUnitriangular_mem (p * A) hupper
      (upperTriangular_diag_one (p * A) hupper)
  have hA := elementarySubgroup.mul_mem (elementarySubgroup.inv_mem hp) hunit
  simpa only [inv_mul_cancel_left] using hA

end ElementaryGenerationProof

/-- Elementary-generation conclusion. Paper: §4. -/
theorem sl3_eq_elementary : ElementaryGeneration :=
  ElementaryGenerationProof.all_mem_elementarySubgroup

private theorem sl3_scalar_eq_one
    (g : SL3)
    (hscalar : (g : Matrix (Fin 3) (Fin 3) R) ∈ Set.range (Matrix.scalar (Fin 3))) :
    (g : Matrix (Fin 3) (Fin 3) R) = 1 := by
  obtain ⟨a, ha⟩ := hscalar
  have hroot : a ^ Fintype.card (Fin 3) = 1 := by
    simpa only [← ha, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
      Finset.card_univ] using g.property
  have hroot3 : a ^ 3 = 1 := by
    simpa using hroot
  have hunit : IsUnit a := IsUnit.of_pow_eq_one hroot3 (by norm_num)
  have hdegree : a.degree = 0 := Polynomial.degree_eq_zero_of_isUnit hunit
  have haC : a = Polynomial.C (a.coeff 0) :=
    Polynomial.eq_C_of_degree_eq_zero hdegree
  have hcoeff : a.coeff 0 = 1 := by
    have hrootC := hroot3
    rw [haC] at hrootC
    generalize hb : a.coeff 0 = b
    have hc : b = 0 ∨ b = 1 := by
      fin_cases b
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with hzero | hone
    · exfalso
      have hzero' : a.coeff 0 = 0 := hb.trans hzero
      simpa [hzero'] using hrootC
    · exact hone
  rw [← ha, haC, hcoeff]
  simp

/-- Countable discrete acting-group carrier. Paper: §§4, 5. -/
noncomputable def sl3Group : CountableDiscreteGroup where
  Carrier := SL3
  group := inferInstance
  countable := by infer_instance

/-- ICC boundary for the special-linear group. Paper: §5. -/
theorem sl3_isICC : IsICC sl3Group := by
  let transvection : R → SL3 :=
    Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide)
  have htrans_inj : Function.Injective transvection :=
    specialLinear_transvection_injective (i := 0) (j := 1) (by decide)
  change Infinite SL3 ∧ ∀ g : SL3, g ≠ 1 →
    Set.Infinite {h : SL3 | ∃ x : SL3, h = x * g * x⁻¹}
  constructor
  · exact Infinite.of_injective transvection htrans_inj
  · intro g hg
    have hnot_scalar :
        ¬(g.val : Matrix (Fin 3) (Fin 3) R) ∈
          Set.range (Matrix.scalar (Fin 3)) := by
      intro hscalar
      have hidentity := sl3_scalar_eq_one g hscalar
      apply hg
      apply Subtype.ext
      simpa using hidentity
    have hnot_all : ¬∀ (i j : Fin 3), i ≠ j →
        Commute (Matrix.single i j (1 : R))
          (g.val : Matrix (Fin 3) (Fin 3) R) := by
      intro hcomm
      exact hnot_scalar (Matrix.mem_range_scalar_of_commute_single hcomm)
    push Not at hnot_all
    obtain ⟨i, j, hij, hnot⟩ := hnot_all
    let lift (a : R) : SL3 :=
      Matrix.SpecialLinearGroup.transvection hij a
    have hinj : Function.Injective (fun a : R => lift a * g * (lift a)⁻¹) := by
      intro a b hab
      apply transvection_conjugates_injective_of_not_commute_matrixUnit
        hij g hnot
      simpa [lift] using hab
    apply (Set.infinite_range_of_injective hinj).mono
    rintro _ ⟨a, rfl⟩
    exact ⟨lift a, rfl⟩

/-- Finite normal-subgroup obstruction available from ICC. Paper: §6.
This is the finite-normal consequence only; the full abelian-normal theorem
still needs the paper's module action. -/
def no_nontrivial_abelian_normal_subgroup : Prop :=
  ∀ N : Subgroup SL3, (N : Set SL3).Finite → N.Normal →
    (∀ x y : N, x * y = y * x) → N = ⊥

theorem no_nontrivial_abelian_normal_subgroup_proof :
    no_nontrivial_abelian_normal_subgroup := by
  intro N hfinite hnormal _hab
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hne
  have hxne : (x : SL3) ≠ 1 := by
    intro h
    apply hne
    simpa using h
  have hICC := (sl3_isICC).2 (x : SL3) hxne
  have hsubset : conjugacyClass sl3Group (x : sl3Group) ⊆ (N : Set SL3) := by
    rintro y ⟨g, rfl⟩
    exact hnormal.conj_mem x hx g
  exact (hfinite.subset hsubset).not_infinite hICC

end SpecialLinear
end Connes
