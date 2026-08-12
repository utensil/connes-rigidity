/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

New standalone interfaces for the Boolean-polynomial part of Zhou §4. The
organization is informed by OpenAI/ten-proofs at commit
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6; no code is imported from it.
Modifications: this file exposes paper-facing definitions; the weight
estimate remains open, while chart exhaustion is stated for finite support.
-/
import Mathlib

namespace Connes
namespace BooleanPolynomial

/-- Characteristic-two scalar field. Paper: §4. -/
abbrev F := ZMod 2

/-- Characteristic-two numeral reduction. Paper: §2, source: OpenAI `ConnesRigidity.lean:15-16`. -/
@[simp] theorem two_eq_zero : (2 : F) = 0 := by
  rfl

/-- Nonzero characteristic-two scalars are one. Paper: §2, source: OpenAI `ConnesRigidity.lean:18-23`. -/
theorem eq_one_of_ne_zero (a : F) (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

/-- Boolean polynomial carrier. Paper: §4. -/
abbrev Polynomial (n : ℕ) := (Fin n → F) → F

/-- Polynomial support boundary. Paper: §4. -/
def support {n : ℕ} (P : Polynomial n) : Finset (Fin n → F) :=
  Finset.univ.filter (fun x => P x ≠ 0)

/-- Polynomial support weight. Paper: §4. -/
def weight {n : ℕ} (P : Polynomial n) : ℕ :=
  (support P).card

/-- Coefficient data for a degree-two Boolean polynomial. Paper: §4. -/
structure QuadraticPolynomial (n : ℕ) where
  constant : F
  linear : Fin n → F
  quadratic : Fin n → Fin n → F

/-- Evaluation of a degree-two Boolean polynomial. Paper: §4. -/
def QuadraticPolynomial.eval {n : ℕ} (q : QuadraticPolynomial n)
    (x : Fin n → F) : F :=
  q.constant +
    ∑ i, q.linear i * x i +
      ∑ i, ∑ j, q.quadratic i j * x i * x j

/-- Degree restriction boundary. Paper: §4. -/
def DegreeAtMostTwo {n : ℕ} (P : Polynomial n) : Prop :=
  ∃ q : QuadraticPolynomial n, ∀ x, q.eval x = P x

/-- Four-point support cover for quadratic functions. Paper: §4. -/
theorem quadratic_support_quarter
    {W : Type*} [AddCommGroup W] [Module F W] [Fintype W]
    (f : W → F) (b : W → W → F)
    (hadd : ∀ x y, f (x + y) = f x + f y + f 0 + b x y)
    (hbadd : ∀ x y z, b (x + y) z = b x z + b y z)
    (hf : ∃ x, f x ≠ 0) :
    Fintype.card W ≤
      4 * ((Finset.univ : Finset W).filter (fun x => f x ≠ 0)).card := by
  classical
  have hchar2 (x : W) : x + x = 0 := by
    rw [← two_smul F x, two_eq_zero, zero_smul]
  have hchar2F (a : F) : a + a = 0 := by
    rw [← two_smul F a, two_eq_zero, zero_smul]
  let support : Finset W := Finset.univ.filter (fun x => f x ≠ 0)
  let offset (u v : W) (c : Fin 2 × Fin 2) : W :=
    (if c.1 = 0 then 0 else u) + (if c.2 = 0 then 0 else v)
  let cover (u v : W) : (support × (Fin 2 × Fin 2)) → W :=
    fun p => p.1.1 + offset u v p.2
  have hcover_card (u v : W)
      (hsurj : Function.Surjective (cover u v)) :
      Fintype.card W ≤ 4 * support.card := by
    have hcard := Fintype.card_le_of_surjective (cover u v) hsurj
    simpa only [ge_iff_le, Fintype.card_prod, Fintype.card_coe,
      Fintype.card_fin, Nat.reduceMul, Nat.mul_comm] using hcard
  change Fintype.card W ≤ 4 * support.card
  by_cases hb : ∃ u v : W, b u v ≠ 0
  · obtain ⟨u, v, huv⟩ := hb
    have hone : b u v = 1 := eq_one_of_ne_zero _ huv
    have hsquare (x : W) :
        f x + f (x + u) + f (x + v) + f ((x + u) + v) = b u v := by
      simp only [hadd x u, hadd x v, hadd (x + u) v, hbadd x u v]
      have hx : f x + f x = 0 := hchar2F (f x)
      have hu : f u + f u = 0 := hchar2F (f u)
      have hv : f v + f v = 0 := hchar2F (f v)
      have hzero : f 0 + f 0 = 0 := hchar2F (f 0)
      have hxu : b x u + b x u = 0 := hchar2F (b x u)
      have hxv : b x v + b x v = 0 := hchar2F (b x v)
      linear_combination 2 * hx + hu + hv + 2 * hzero + hxu + hxv
    apply hcover_card u v
    intro x
    by_cases hx : f x ≠ 0
    · exact ⟨(⟨x, by simpa only [support, Finset.mem_filter, Finset.mem_univ,
        true_and] using hx⟩, (0, 0)), by simp only [Fin.isValue, ↓reduceIte,
        add_zero, cover, offset]⟩
    by_cases hxu : f (x + u) ≠ 0
    · refine ⟨(⟨x + u, by simpa only [support, Finset.mem_filter,
        Finset.mem_univ, true_and] using hxu⟩, (1, 0)), ?_⟩
      simp only [Fin.isValue, one_ne_zero, ↓reduceIte, add_zero, add_assoc,
        cover, offset]
      rw [hchar2]
      simp only [add_zero]
    by_cases hxv : f (x + v) ≠ 0
    · refine ⟨(⟨x + v, by simpa only [support, Finset.mem_filter,
        Finset.mem_univ, true_and] using hxv⟩, (0, 1)), ?_⟩
      simp only [Fin.isValue, ↓reduceIte, one_ne_zero, zero_add, add_assoc,
        add_zero, cover, offset]
      rw [hchar2]
      simp only [add_zero]
    have hxuv : f ((x + u) + v) ≠ 0 := by
      intro hz
      have hsq := hsquare x
      rw [not_ne_iff.mp hx, not_ne_iff.mp hxu, not_ne_iff.mp hxv, hz] at hsq
      simp only [add_zero, hone, zero_ne_one] at hsq
    refine ⟨(⟨(x + u) + v, by simpa only [support, Finset.mem_filter,
      Finset.mem_univ, true_and] using hxuv⟩, (1, 1)), ?_⟩
    change ((x + u) + v) + (u + v) = x
    calc
      ((x + u) + v) + (u + v) = x + (u + u) + (v + v) := by abel
      _ = x := by rw [hchar2, hchar2]; simp
  · have hbzero : ∀ u v : W, b u v = 0 := by
      intro u v
      by_contra h
      exact hb ⟨u, v, h⟩
    by_cases hnonconst : ∃ u : W, f u + f 0 ≠ 0
    · obtain ⟨u, hu⟩ := hnonconst
      apply hcover_card u 0
      intro x
      by_cases hx : f x ≠ 0
      · exact ⟨(⟨x, by simpa only [support, Finset.mem_filter,
          Finset.mem_univ, true_and] using hx⟩, (0, 0)), by
          simp only [Fin.isValue, ↓reduceIte, add_zero, cover, offset]⟩
      have hxu : f (x + u) ≠ 0 := by
        rw [hadd x u, not_ne_iff.mp hx, hbzero]
        simpa only [zero_add, add_zero] using hu
      refine ⟨(⟨x + u, by simpa only [support, Finset.mem_filter,
        Finset.mem_univ, true_and] using hxu⟩, (1, 0)), ?_⟩
      simp only [Fin.isValue, one_ne_zero, ↓reduceIte, add_zero, add_assoc,
        cover, offset]
      rw [hchar2]
      simp only [add_zero]
    · have hconst : ∀ x : W, f x = f 0 := by
        intro x
        by_contra h
        apply hnonconst
        refine ⟨x, ?_⟩
        intro hzero
        apply h
        calc
          f x = f x + 0 := by simp
          _ = f x + (f 0 + f 0) := by rw [hchar2F, add_zero]
          _ = (f x + f 0) + f 0 := by abel
          _ = f 0 := by rw [hzero]; simp
      obtain ⟨u, hu⟩ := hf
      have hzero : f 0 ≠ 0 := by simpa [hconst u] using hu
      have hsupport : support = Finset.univ := by
        ext x
        simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [hconst x] using hzero
      rw [hsupport, Finset.card_univ]
      omega

/-- Low-degree support estimate. Paper: §4. -/
theorem weight_lower_bound {n : ℕ} (P : Polynomial n)
    (hdeg : DegreeAtMostTwo P) (hP : P ≠ 0) :
    weight P ≥ 2 ^ (n - 2) := by
  classical
  obtain ⟨q, hq⟩ := hdeg
  have hchar2F (a : F) : a + a = 0 := by
    rw [← two_smul F a, two_eq_zero, zero_smul]
  let b : (Fin n → F) → (Fin n → F) → F := fun x y =>
    ∑ i, ∑ j, q.quadratic i j * (x i * y j + y i * x j)
  have hq0 : q.eval 0 = q.constant := by
    simp [QuadraticPolynomial.eval]
  have hadd (x y : Fin n → F) :
      q.eval (x + y) = q.eval x + q.eval y + q.eval 0 + b x y := by
    rw [hq0]
    simp only [QuadraticPolynomial.eval, b, Pi.add_apply, add_mul, mul_add,
      Finset.sum_add_distrib]
    have hthree : (3 : F) = 1 := by decide
    have hc3 : q.constant * 3 = q.constant := by rw [hthree, mul_one]
    ring_nf
    try rw [hc3]
    all_goals abel
  have hbadd (x y z : Fin n → F) : b (x + y) z = b x z + b y z := by
    dsimp [b]
    simp only [Pi.add_apply, add_mul, mul_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hf : ∃ x : Fin n → F, q.eval x ≠ 0 := by
    by_contra h
    apply hP
    funext x
    rw [← hq x]
    exact not_ne_iff.mp (not_exists.mp h x)
  have hcard := quadratic_support_quarter q.eval b hadd hbadd hf
  have hweight :
      ((Finset.univ : Finset (Fin n → F)).filter (fun x => q.eval x ≠ 0)).card =
        weight P := by
    unfold weight support
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hq x]
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card] at hcard
  rw [hweight] at hcard
  by_cases hn : 2 ≤ n
  · have hexp : (n - 2) + 2 = n := by omega
    have hpow : 2 ^ n = 4 * 2 ^ (n - 2) := by
      rw [← hexp, pow_add]
      norm_num [Nat.mul_comm]
    rw [hpow] at hcard
    exact Nat.le_of_mul_le_mul_left hcard (by norm_num)
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · simp only [Nat.zero_sub, pow_zero]
      obtain ⟨x, hx⟩ := hf
      have hPx : P x ≠ 0 := by simpa only [← hq x] using hx
      exact Finset.card_pos.mpr ⟨x, by
        simpa only [support, Finset.mem_filter, Finset.mem_univ, true_and] using hPx⟩
    · simp only [Nat.one_sub, pow_zero]
      obtain ⟨x, hx⟩ := hf
      have hPx : P x ≠ 0 := by simpa only [← hq x] using hx
      exact Finset.card_pos.mpr ⟨x, by
        simpa only [support, Finset.mem_filter, Finset.mem_univ, true_and] using hPx⟩

/-- Finite coefficient-chart boundary. Paper: §4. -/
def coefficientChart (N : ℕ) : Set (ℕ → F) :=
  {x | ∀ n, N ≤ n → x n = 0}

/-- Finite-support coefficient data used by the chart exhaustion. Paper: §4. -/
def FiniteSupport (x : ℕ → F) : Prop :=
  (Function.support x).Finite

/-- Chart monotonicity. Paper: §4. -/
theorem coefficientChart_mono {M N : ℕ} (hMN : M ≤ N) :
    coefficientChart M ⊆ coefficientChart N := by
  intro x hx n hN
  exact hx n (le_trans hMN hN)

/-- Chart exhaustion boundary. Paper: §4. -/
theorem coefficientCharts_cover (x : ℕ → F) (hx : FiniteSupport x) :
    ∃ N, x ∈ coefficientChart N := by
  change (Function.support x).Finite at hx
  classical
  by_cases hsupp : (Function.support x).Nonempty
  · let s : Finset ℕ := hx.toFinset
    have hs : s.Nonempty := hx.toFinset_nonempty.mpr hsupp
    refine ⟨s.max' hs + 1, ?_⟩
    intro n hn
    by_contra hxn
    have hnmem : n ∈ Function.support x := hxn
    have hnfin : n ∈ s := hx.mem_toFinset.mpr hnmem
    have hle : n ≤ s.max' hs := s.le_max' n hnfin
    omega
  · refine ⟨0, ?_⟩
    intro n _
    by_contra hxn
    exact hsupp ⟨n, hxn⟩

end BooleanPolynomial
end Connes
