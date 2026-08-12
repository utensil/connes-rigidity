/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Spectral-measure proof spine for Zhou §4. This is a small, generic port of
the public OpenAI/ten-proofs criterion: the actual Zhou detector and the
representation-specific spectral construction remain inputs, while the
measure-to-invariant-vector assembly is proved here.
-/
import Mathlib
import Connes.Core
import Connes.Foundation.GroupTheory.SplitAbelianExtension

namespace Connes

noncomputable section

universe u

open MeasureTheory
open scoped ENNReal NNReal

variable {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
variable {G H : CountableDiscreteGroup.{u}}
variable [MeasurableSpace (PontryaginDual (Multiplicative A))]
  [BorelSpace (PontryaginDual (Multiplicative A))]

/-- Pontryagin dual of a discrete additive kernel. Paper: §3--4. -/
abbrev DiscreteCharacterSpace (A : Type u)
    [AddCommGroup A] [TopologicalSpace A] :=
  PontryaginDual (Multiplicative A)

/-- Inverse-dual action of a group on the character space. Paper: §4. -/
def dualCharacterAction
    (action : H →* Multiplicative (AddAut A)) (h : H)
    (χ : DiscreteCharacterSpace A) : DiscreteCharacterSpace A where
  toFun a := χ (Multiplicative.ofAdd
    ((Multiplicative.toAdd (action h⁻¹)) (Multiplicative.toAdd a)))
  map_one' := by simp only [map_inv, toAdd_inv, toAdd_one, map_zero, ofAdd_zero, map_one]
  map_mul' a b := by
    change χ (Multiplicative.ofAdd
      ((Multiplicative.toAdd (action h⁻¹))
        (Multiplicative.toAdd a + Multiplicative.toAdd b))) = _
    rw [map_add]
    exact map_mul χ _ _
  continuous_toFun := continuous_of_discreteTopology

omit [MeasurableSpace (PontryaginDual (Multiplicative A))]
  [BorelSpace (PontryaginDual (Multiplicative A))] in
@[simp] theorem dualCharacterAction_trivial
    (action : H →* Multiplicative (AddAut A)) (h : H) :
    dualCharacterAction action h (1 : DiscreteCharacterSpace A) = 1 := by
  ext a
  rfl

/-- Invariant probability measure for the dual action. Paper: §4. -/
def IsInvariantSpectralMeasure
    (action : H →* Multiplicative (AddAut A))
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) : Prop :=
  ∀ h : H,
    (μ : Measure (DiscreteCharacterSpace A)).map
      (dualCharacterAction action h) = μ

/-- Mass of the trivial character. Paper: §4. -/
def spectralTrivialAtom
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) : ℝ :=
  (μ : Measure (DiscreteCharacterSpace A)).real {1}

/-- Spectral displacement energy of a kernel element. Paper: §4. -/
def spectralDetectionEnergy
    (μ : ProbabilityMeasure (DiscreteCharacterSpace A)) (a : A) : ℝ :=
  ∫ χ : DiscreteCharacterSpace A,
    ‖((χ (Multiplicative.ofAdd a) : Circle) : ℂ) - 1‖ ^ 2
      ∂(μ : Measure (DiscreteCharacterSpace A))

/-- A normalized vector fixed by the quotient section. Paper: §4. -/
structure QuotientFixedUnitVector
    (E : SplitAbelianExtension A G H)
    (K : Type u) [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : UnitaryRepresentation G K) where
  vector : K
  norm_one : ‖vector‖ = 1
  quotient_fixed : ∀ h : H,
    (π (E.splitting h) : K →L[ℂ] K) vector = vector

/-- Representation-specific spectral input used by the generic criterion.
Paper: §4. -/
structure SpectralMeasureInterface
    (E : SplitAbelianExtension A G H)
    (K : Type u) [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : UnitaryRepresentation G K) where
  quotient_fixed_approximation :
    HasKazhdanPropertyT H →
      π.HasAlmostInvariantUnitVectors →
        ∀ (J : Finset A) (ε : ℝ), 0 < ε →
          ∃ ξ : QuotientFixedUnitVector E K π,
            (∑ a ∈ J,
              ‖(π (E.inclusion (Multiplicative.ofAdd a)) : K →L[ℂ] K)
                  ξ.vector - ξ.vector‖ ^ 2) < ε
  measure : QuotientFixedUnitVector E K π →
    ProbabilityMeasure (DiscreteCharacterSpace A)
  measure_invariant : ∀ ξ,
    IsInvariantSpectralMeasure E.action (measure ξ)
  energy_eq : ∀ (ξ : QuotientFixedUnitVector E K π) (a : A),
    spectralDetectionEnergy (measure ξ) a =
      ‖(π (E.inclusion (Multiplicative.ofAdd a)) : K →L[ℂ] K)
          ξ.vector - ξ.vector‖ ^ 2
  positive_atom_invariant :
    ∀ ξ : QuotientFixedUnitVector E K π,
      0 < spectralTrivialAtom (measure ξ) →
        ∃ η : K, η ≠ 0 ∧
          (∀ a : A,
            (π (E.inclusion (Multiplicative.ofAdd a)) : K →L[ℂ] K) η = η) ∧
          (∀ h : H, (π (E.splitting h) : K →L[ℂ] K) η = η)

/-- Finite spectral detection inequality. Paper: §4. -/
def HasFiniteSpectralDetection
    (E : SplitAbelianExtension A G H) (J : Finset A) (c : ℝ) : Prop :=
  ∀ μ : ProbabilityMeasure (DiscreteCharacterSpace A),
    IsInvariantSpectralMeasure E.action μ →
      c * (1 - spectralTrivialAtom μ) ≤
        ∑ a ∈ J, spectralDetectionEnergy μ a

omit [BorelSpace (DiscreteCharacterSpace A)] in
theorem exists_positive_spectral_atom
    (E : SplitAbelianExtension A G H)
    {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : UnitaryRepresentation G K)
    (spectral : SpectralMeasureInterface E K π)
    (hH : HasKazhdanPropertyT H)
    (hπ : π.HasAlmostInvariantUnitVectors)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c) :
    ∃ ξ : QuotientFixedUnitVector E K π,
      0 < spectralTrivialAtom (spectral.measure ξ) := by
  obtain ⟨ξ, hsmall⟩ :=
    spectral.quotient_fixed_approximation hH hπ J c hc
  refine ⟨ξ, ?_⟩
  have hdet := hdetection (spectral.measure ξ)
    (spectral.measure_invariant ξ)
  simp_rw [spectral.energy_eq] at hdet
  nlinarith

omit [BorelSpace (DiscreteCharacterSpace A)] in
theorem spectral_criterion_representation
    (E : SplitAbelianExtension A G H)
    {K : Type u} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : UnitaryRepresentation G K)
    (spectral : SpectralMeasureInterface E K π)
    (hH : HasKazhdanPropertyT H)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c)
    (hπ : π.HasAlmostInvariantUnitVectors) :
    ∃ ξ : K, ξ ≠ 0 ∧ π.IsInvariant ξ := by
  obtain ⟨ξ, hatom⟩ :=
    exists_positive_spectral_atom E π spectral hH hπ J hc hdetection
  obtain ⟨η, hη, hkernel, hquotient⟩ :=
    spectral.positive_atom_invariant ξ hatom
  exact ⟨η, hη,
    E.invariant_of_kernel_and_quotient π η hkernel hquotient⟩

omit [BorelSpace (DiscreteCharacterSpace A)] in
theorem spectral_criterion
    (E : SplitAbelianExtension A G H)
    (hH : HasKazhdanPropertyT H)
    (J : Finset A) {c : ℝ} (hc : 0 < c)
    (hdetection : HasFiniteSpectralDetection E J c)
    (spectral : ∀ (K : Type u)
      (_ : NormedAddCommGroup K)
      (_ : InnerProductSpace ℂ K)
      (_ : CompleteSpace K)
      (π : UnitaryRepresentation G K),
        SpectralMeasureInterface E K π) :
    HasKazhdanPropertyT G := by
  intro K _ _ _ π hπ
  exact spectral_criterion_representation E π
    (spectral K inferInstance inferInstance inferInstance π)
    hH J hc hdetection hπ

end
end Connes
