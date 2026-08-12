/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Proof transfer from OpenAI/ten-proofs archive commit 66af838,
ConnesRigidity/ArithmeticCocycle.lean:246-402. This file contains the small
shear and fixed-vector calculations used by the source's arithmetic
obstruction. It remains an isolated OpenAI-shaped layer beside the Zhou API.
-/
import Connes.Foundation.LinearAlgebra.QuadraticCocycle

namespace Connes
namespace OpenAIPort

open Matrix

/- Lower block shear. Paper: §2. -/
def lowerShear (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.transpose = B) :
    IntegralSymplecticGroup :=
  ⟨Matrix.fromBlocks 1 0 B 1, by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    simp [hB]⟩

/- First coordinate shear matrix. Paper: §2. -/
def lowerShearB1 : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

/- Second coordinate shear matrix. Paper: §2. -/
def lowerShearB2 : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => if i = 1 ∧ j = 1 then 1 else 0

/- Mixed coordinate shear matrix. Paper: §2. -/
def lowerShearB12 : Matrix (Fin 2) (Fin 2) ℤ :=
  fun _ _ => 1

/- Symmetry of the first shear matrix. Paper: §2. -/
theorem lowerShearB1_symm : lowerShearB1.transpose = lowerShearB1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/- Symmetry of the second shear matrix. Paper: §2. -/
theorem lowerShearB2_symm : lowerShearB2.transpose = lowerShearB2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/- Symmetry of the mixed shear matrix. Paper: §2. -/
theorem lowerShearB12_symm : lowerShearB12.transpose = lowerShearB12 :=
  rfl

/- First lower transvection. Paper: §2. -/
def transvectionF1 : IntegralSymplecticGroup :=
  lowerShear lowerShearB1 lowerShearB1_symm

/- Second lower transvection. Paper: §2. -/
def transvectionF2 : IntegralSymplecticGroup :=
  lowerShear lowerShearB2 lowerShearB2_symm

/- Mixed lower transvection. Paper: §2. -/
def transvectionF12 : IntegralSymplecticGroup :=
  lowerShear lowerShearB12 lowerShearB12_symm

/- A finite witness for the non-coboundary calculation. Paper: §2. -/
def transvectionWitness (u : ModTwoSpace) : IntegralSymplecticGroup :=
  if u (Sum.inl 1) = 0 then transvectionF2
  else if u (Sum.inl 0) = 0 then transvectionF1
  else transvectionF12

/- The witness detects every finite vector. Paper: §2. -/
theorem transvectionWitness_ne (u : ModTwoSpace) :
    transvectionWitness u • u - u ≠
      integralQuadraticCocycle (transvectionWitness u) := by
  revert u
  decide

/- The arithmetic cocycle is not a coboundary. Paper: §2. -/
theorem integralQuadraticCocycle_not_isCoboundary :
    ¬groupCohomology.IsCoboundary₁ integralQuadraticCocycle := by
  rintro ⟨u, hu⟩
  exact transvectionWitness_ne u (hu (transvectionWitness u))

/- Upper block shear. Paper: §2. -/
def upperShear (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.transpose = B) :
    IntegralSymplecticGroup :=
  ⟨Matrix.fromBlocks 1 B 0 1, by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    simp [hB]⟩

/- First upper transvection. Paper: §2. -/
def upperTransvectionE1 : IntegralSymplecticGroup :=
  upperShear lowerShearB1 lowerShearB1_symm

/- Second upper transvection. Paper: §2. -/
def upperTransvectionE2 : IntegralSymplecticGroup :=
  upperShear lowerShearB2 lowerShearB2_symm

/- Four shears have no common nonzero fixed vector. Paper: §2. -/
theorem fixed_by_four_shears_eq_zero
    (u : ModTwoSpace)
    (hl1 : transvectionF1 • u = u)
    (hl2 : transvectionF2 • u = u)
    (hu1 : upperTransvectionE1 • u = u)
    (hu2 : upperTransvectionE2 • u = u) :
    u = 0 := by
  revert u
  decide

/- The full integral symplectic action has no nonzero fixed vector. Paper: §2. -/
theorem modTwo_fixed_by_integralSymplecticGroup_eq_zero
    (u : ModTwoSpace) (h : ∀ g : IntegralSymplecticGroup, g • u = u) :
    u = 0 :=
  fixed_by_four_shears_eq_zero u
    (h transvectionF1) (h transvectionF2)
    (h upperTransvectionE1) (h upperTransvectionE2)

/- Central negation in the integral symplectic group. Paper: §2. -/
def centralNegOne : IntegralSymplecticGroup :=
  ⟨-1, SymplecticGroup.neg_mem (by simp)⟩

/- The central element acts by negation. Paper: §2. -/
theorem centralNegOne_smul (v : IntegralLattice) :
    centralNegOne • v = -v := by
  funext i
  simp [centralNegOne]

/- The central negation commutes with the group. Paper: §2. -/
theorem centralNegOne_comm (g : IntegralSymplecticGroup) :
    centralNegOne * g = g * centralNegOne := by
  apply Subtype.ext
  simp [centralNegOne]

/- Integral one-cocycles are coboundaries. Paper: §2. -/
theorem integralOneCocycles_areCoboundaries
    (F : IntegralSymplecticGroup → IntegralLattice)
    (hF : groupCohomology.IsCocycle₁ F) :
    groupCohomology.IsCoboundary₁ F := by
  let t0 := F centralNegOne
  have htwo (g : IntegralSymplecticGroup) :
      (2 : ℕ) • F g = t0 - g • t0 := by
    have hzg := hF centralNegOne g
    have hgz := hF g centralNegOne
    rw [centralNegOne_comm] at hzg
    rw [centralNegOne_smul] at hzg
    dsimp [t0]
    rw [hgz] at hzg
    apply (eq_sub_iff_add_eq).2
    rw [two_nsmul]
    calc
      F g + F g + g • F centralNegOne =
          (g • F centralNegOne + F g) + F g := by abel
      _ = (-F g + F centralNegOne) + F g := by rw [hzg]
      _ = F centralNegOne := by abel
  have ht0fixed (g : IntegralSymplecticGroup) :
      g • reduceVector t0 = reduceVector t0 := by
    have hred := congrArg reduceVector (htwo g)
    rw [map_nsmul, map_sub, reduceVector_smul] at hred
    have hexp := modTwoSpace_exponent_two (reduceVector (F g))
    rw [hexp] at hred
    exact (sub_eq_zero.mp hred.symm).symm
  have ht0zero : reduceVector t0 = 0 :=
    modTwo_fixed_by_integralSymplecticGroup_eq_zero _ ht0fixed
  obtain ⟨u0, hu0⟩ := exists_half_of_reduceVector_eq_zero t0 ht0zero
  refine ⟨-u0, ?_⟩
  intro g
  apply two_nsmul_integralLattice_injective
  change (2 : ℕ) •
      ((DistribSMul.toAddMonoidHom IntegralLattice g) (-u0) - (-u0)) =
    (2 : ℕ) • F g
  rw [nsmul_sub, map_neg, neg_nsmul, neg_nsmul]
  have hg := map_nsmul
    (DistribSMul.toAddMonoidHom IntegralLattice g) 2 u0
  rw [← hg, hu0, htwo]
  rw [sub_neg_eq_add]
  change -(g • t0) + t0 = t0 - g • t0
  abel

end OpenAIPort
end Connes
