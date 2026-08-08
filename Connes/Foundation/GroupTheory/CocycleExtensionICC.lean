/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Proof transfer from OpenAI/ten-proofs archive commit 66af838,
ConnesRigidity/ICC.lean:13-300. This file ports the source's split-extension
conjugacy argument into the Zhou-oriented GroupTheory directory without
making it a dependency of the local placeholder groups.
-/
import Connes.Foundation.GroupTheory.CocycleExtension
import Connes.Foundation.LinearAlgebra.SymplecticShear

namespace Connes
namespace OpenAIPort

open Matrix

/- A standard lattice basis vector. Paper: §5. -/
def integralBasisVector (j : SymplecticIndex) : IntegralLattice :=
  Pi.single j 1

/- Faithfulness of the integral matrix action. Paper: §5. -/
theorem integralSymplectic_action_faithful
    (g : IntegralSymplecticGroup)
    (h : ∀ v : IntegralLattice, g • v = v) :
    g = 1 := by
  apply Subtype.ext
  ext i j
  have hij := congr_fun (h (integralBasisVector j)) i
  change g.1.mulVec (Pi.single j (1 : ℤ) : IntegralLattice) i =
    (Pi.single j (1 : ℤ) : IntegralLattice) i at hij
  rw [Matrix.mulVec_single_one] at hij
  simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using hij

/- Every nonidentity integral symplectic element moves a vector. Paper: §5. -/
theorem exists_moved_vector (g : IntegralSymplecticGroup) (hg : g ≠ 1) :
    ∃ v : IntegralLattice, g • v ≠ v := by
  by_contra h
  push Not at h
  exact hg (integralSymplectic_action_faithful g h)

/- The group identity acts trivially on the lattice. Paper: §5. -/
@[simp] theorem integralSymplectic_one_smul (v : IntegralLattice) :
    (1 : IntegralSymplecticGroup) • v = v :=
  one_smul IntegralSymplecticGroup v

/- Conjugation by a kernel element. Paper: §5. -/
theorem kernel_conjugation
    {c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice}
    (b : IntegralLattice) (x : CocycleExtension c) :
    ({ fst := b, snd := (1 : IntegralSymplecticGroup) } : CocycleExtension c) * x *
      ({ fst := b, snd := (1 : IntegralSymplecticGroup) } : CocycleExtension c)⁻¹ =
      ({ fst := x.fst + (b - x.snd • b), snd := x.snd } :
        CocycleExtension c) := by
  let kb : CocycleExtension c :=
    { fst := b, snd := (1 : IntegralSymplecticGroup) }
  apply (mul_right_cancel_iff (a := kb)).mp
  rw [mul_assoc, inv_mul_cancel, mul_one]
  dsimp [kb]
  apply CocycleExtension.ext
  · simp only [CocycleExtension.mul_fst]
    rw [c.one_left, c.one_right]
    simp only [add_zero]
    funext i
    change b i + (1 : Matrix SymplecticIndex SymplecticIndex ℤ).mulVec x.fst i =
      x.fst i + (b i - (x.snd • b) i) + (x.snd • b) i
    simp only [Matrix.one_mulVec]
    ring
  · simp

/- Conjugation of a kernel element by an extension element. Paper: §5. -/
theorem extension_conjugation_kernel
    {c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice}
    (x : CocycleExtension c) (a : IntegralLattice) :
    x * ({ fst := a, snd := (1 : IntegralSymplecticGroup) } : CocycleExtension c) * x⁻¹ =
      ({ fst := x.snd • a, snd := (1 : IntegralSymplecticGroup) } : CocycleExtension c) := by
  apply (mul_right_cancel_iff (a := x)).mp
  rw [mul_assoc, inv_mul_cancel, mul_one]
  apply CocycleExtension.ext
  · simp only [CocycleExtension.mul_fst]
    rw [c.one_right, c.one_left]
    simp only [add_zero]
    funext i
    change x.fst i + (x.snd • a) i =
      (x.snd • a) i +
        (1 : Matrix SymplecticIndex SymplecticIndex ℤ).mulVec x.fst i
    simp only [Matrix.one_mulVec]
    ring
  · simp

/- The coordinate shear matrix. Paper: §5. -/
def coordinateShearMatrix (i : Fin 2) (n : ℤ) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  fun r s => if r = i ∧ s = i then n else 0

/- Symmetry of the coordinate shear matrix. Paper: §5. -/
theorem coordinateShearMatrix_symm (i : Fin 2) (n : ℤ) :
    (coordinateShearMatrix i n).transpose = coordinateShearMatrix i n := by
  ext r s
  simp only [Matrix.transpose_apply, coordinateShearMatrix]
  by_cases hri : r = i <;> by_cases hsi : s = i <;> simp_all

/- Lower coordinate shear. Paper: §5. -/
def lowerCoordinateShear (i : Fin 2) (n : ℤ) :
    IntegralSymplecticGroup :=
  lowerShear (coordinateShearMatrix i n) (coordinateShearMatrix_symm i n)

/- Upper coordinate shear. Paper: §5. -/
def upperCoordinateShear (i : Fin 2) (n : ℤ) :
    IntegralSymplecticGroup :=
  upperShear (coordinateShearMatrix i n) (coordinateShearMatrix_symm i n)

/- Lower shear coordinate action. Paper: §5. -/
theorem lowerCoordinateShear_smul_inr
    (i : Fin 2) (n : ℤ) (v : IntegralLattice) :
    (lowerCoordinateShear i n • v) (Sum.inr i) =
      n * v (Sum.inl i) + v (Sum.inr i) := by
  fin_cases i <;>
    simp [lowerCoordinateShear, lowerShear, coordinateShearMatrix,
      Matrix.mulVec, dotProduct]

/- Upper shear coordinate action. Paper: §5. -/
theorem upperCoordinateShear_smul_inl
    (i : Fin 2) (n : ℤ) (v : IntegralLattice) :
    (upperCoordinateShear i n • v) (Sum.inl i) =
      v (Sum.inl i) + n * v (Sum.inr i) := by
  fin_cases i <;>
    simp [upperCoordinateShear, upperShear, coordinateShearMatrix,
      Matrix.mulVec, dotProduct]

/- A kernel conjugacy parametrization. Paper: §5. -/
def kernelConjugate
    {c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice}
    (x : CocycleExtension c) (b : IntegralLattice) (n : ℤ) :
    CocycleExtension c :=
  let bn := n • b
  ({ fst := bn, snd := (1 : IntegralSymplecticGroup) } : CocycleExtension c) *
    x * ({ fst := bn, snd := (1 : IntegralSymplecticGroup) } : CocycleExtension c)⁻¹

/- The kernel conjugacy parametrization is injective when the action moves b. Paper: §5. -/
theorem kernelConjugate_injective
    {c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice}
    (x : CocycleExtension c) (b : IntegralLattice)
    (hb : b - x.snd • b ≠ 0) :
    Function.Injective (kernelConjugate x b) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
  intro n m hnm
  have hform (k : ℤ) :
      kernelConjugate x b k =
        ({ fst := x.fst + k • (b - x.snd • b), snd := x.snd } :
          CocycleExtension c) := by
    rw [kernelConjugate, kernel_conjugation]
    apply CocycleExtension.ext
    · change x.fst + (k • b - x.snd • k • b) =
        x.fst + k • (b - x.snd • b)
      have hk : x.snd • (k • b) = k • (x.snd • b) :=
        map_zsmul (DistribSMul.toAddMonoidHom IntegralLattice x.snd) k b
      rw [hk]
      exact congrArg (x.fst + ·) (zsmul_sub b (x.snd • b) k).symm
    · rfl
  rw [hform n, hform m] at hnm
  have hvec :
      n • (b - x.snd • b) = m • (b - x.snd • b) := by
    exact add_left_cancel (congrArg CocycleExtension.fst hnm)
  have hcoord := congr_fun hvec i
  apply mul_right_cancel₀ hi
  simpa [zsmul_eq_mul] using hcoord

/- Every parametrized kernel conjugate lies in the conjugacy class. Paper: §5. -/
theorem kernelConjugate_mem_conjugacyClass
    {c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice}
    (x : CocycleExtension c) (b : IntegralLattice) (n : ℤ) :
    kernelConjugate x b n ∈
      {h : CocycleExtension c | ∃ y, h = y * x * y⁻¹} := by
  let bn := n • b
  exact ⟨{ fst := bn, snd := (1 : IntegralSymplecticGroup) }, rfl⟩

/- Nonidentity quotient coordinates have infinite conjugacy classes. Paper: §5. -/
theorem conjugacy_infinite_of_snd_ne_one
    {c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice}
    (x : CocycleExtension c) (hx : x.snd ≠ 1) :
    Set.Infinite {h : CocycleExtension c | ∃ y, h = y * x * y⁻¹} := by
  obtain ⟨b, hb⟩ := exists_moved_vector x.snd hx
  have hd : b - x.snd • b ≠ 0 := sub_ne_zero.mpr hb.symm
  exact (Set.infinite_range_of_injective
    (kernelConjugate_injective x b hd)).mono
      (Set.range_subset_iff.mpr (kernelConjugate_mem_conjugacyClass x b))

/- Lower shear orbit element. Paper: §5. -/
def lowerOrbitElement
    {c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice}
    (a : IntegralLattice) (i : Fin 2) (n : ℤ) :
    CocycleExtension c :=
  { fst := lowerCoordinateShear i n • a
    snd := 1 }

/- Upper shear orbit element. Paper: §5. -/
def upperOrbitElement
    {c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice}
    (a : IntegralLattice) (i : Fin 2) (n : ℤ) :
    CocycleExtension c :=
  { fst := upperCoordinateShear i n • a
    snd := 1 }

/- Lower shear orbit injectivity. Paper: §5. -/
theorem lowerOrbitElement_injective
    {c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice}
    (a : IntegralLattice) (i : Fin 2) (hi : a (Sum.inl i) ≠ 0) :
    Function.Injective (lowerOrbitElement (c := c) a i) := by
  intro n m hnm
  have hcoord := congr_fun (congrArg CocycleExtension.fst hnm) (Sum.inr i)
  change (lowerCoordinateShear i n • a) (Sum.inr i) =
    (lowerCoordinateShear i m • a) (Sum.inr i) at hcoord
  rw [lowerCoordinateShear_smul_inr, lowerCoordinateShear_smul_inr] at hcoord
  have hmul : n * a (Sum.inl i) = m * a (Sum.inl i) :=
    add_right_cancel hcoord
  exact mul_right_cancel₀ hi hmul

/- Upper shear orbit injectivity. Paper: §5. -/
theorem upperOrbitElement_injective
    {c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice}
    (a : IntegralLattice) (i : Fin 2) (hi : a (Sum.inr i) ≠ 0) :
    Function.Injective (upperOrbitElement (c := c) a i) := by
  intro n m hnm
  have hcoord := congr_fun (congrArg CocycleExtension.fst hnm) (Sum.inl i)
  change (upperCoordinateShear i n • a) (Sum.inl i) =
    (upperCoordinateShear i m • a) (Sum.inl i) at hcoord
  rw [upperCoordinateShear_smul_inl, upperCoordinateShear_smul_inl] at hcoord
  have hmul : n * a (Sum.inr i) = m * a (Sum.inr i) :=
    add_left_cancel hcoord
  exact mul_right_cancel₀ hi hmul

/- Lower shear orbit elements are conjugates. Paper: §5. -/
theorem lowerOrbitElement_mem_conjugacyClass
    {c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice}
    (x : CocycleExtension c) (hx : x.snd = 1)
    (i : Fin 2) (n : ℤ) :
    lowerOrbitElement (c := c) x.fst i n ∈
      {h : CocycleExtension c | ∃ y, h = y * x * y⁻¹} := by
  let y : CocycleExtension c :=
    { fst := 0, snd := lowerCoordinateShear i n }
  refine ⟨y, ?_⟩
  have hxrepr :
      x = ({ fst := x.fst, snd := (1 : IntegralSymplecticGroup) } :
        CocycleExtension c) := by
    apply CocycleExtension.ext
    · rfl
    · exact hx
  rw [hxrepr]
  exact (extension_conjugation_kernel y x.fst).symm

/- Upper shear orbit elements are conjugates. Paper: §5. -/
theorem upperOrbitElement_mem_conjugacyClass
    {c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice}
    (x : CocycleExtension c) (hx : x.snd = 1)
    (i : Fin 2) (n : ℤ) :
    upperOrbitElement (c := c) x.fst i n ∈
      {h : CocycleExtension c | ∃ y, h = y * x * y⁻¹} := by
  let y : CocycleExtension c :=
    { fst := 0, snd := upperCoordinateShear i n }
  refine ⟨y, ?_⟩
  have hxrepr :
      x = ({ fst := x.fst, snd := (1 : IntegralSymplecticGroup) } :
        CocycleExtension c) := by
    apply CocycleExtension.ext
    · rfl
    · exact hx
  rw [hxrepr]
  exact (extension_conjugation_kernel y x.fst).symm

/- Nonidentity kernel coordinates have infinite conjugacy classes. Paper: §5. -/
theorem conjugacy_infinite_of_snd_eq_one
    {c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice}
    (x : CocycleExtension c) (hx : x ≠ 1) (hsnd : x.snd = 1) :
    Set.Infinite {h : CocycleExtension c | ∃ y, h = y * x * y⁻¹} := by
  have hfst : x.fst ≠ 0 := by
    intro hzero
    apply hx
    apply CocycleExtension.ext
    · simpa using hzero
    · simpa using hsnd
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hfst
  rcases i with i | i
  · exact (Set.infinite_range_of_injective
      (lowerOrbitElement_injective (c := c) x.fst i hi)).mono
        (Set.range_subset_iff.mpr
          (lowerOrbitElement_mem_conjugacyClass x hsnd i))
  · exact (Set.infinite_range_of_injective
      (upperOrbitElement_injective (c := c) x.fst i hi)).mono
        (Set.range_subset_iff.mpr
          (upperOrbitElement_mem_conjugacyClass x hsnd i))

/- Every nonidentity extension element has an infinite conjugacy class. Paper: §5. -/
theorem cocycleExtension_conjugacyClass_infinite
    {c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice}
    (x : CocycleExtension c) (hx : x ≠ 1) :
    Set.Infinite {h : CocycleExtension c | ∃ y, h = y * x * y⁻¹} := by
  by_cases hsnd : x.snd = 1
  · exact conjugacy_infinite_of_snd_eq_one x hx hsnd
  · exact conjugacy_infinite_of_snd_ne_one x hsnd

/- Every split extension in this layer is infinite. Paper: §5. -/
theorem cocycleExtension_infinite
    (c : NormalizedAddCocycle IntegralSymplecticGroup IntegralLattice) :
    Infinite (CocycleExtension c) := by
  let a : IntegralLattice := integralBasisVector (Sum.inl 0)
  have ha : a (Sum.inl 0) ≠ 0 := by
    simp [a, integralBasisVector]
  exact Infinite.of_injective (lowerOrbitElement (c := c) a 0)
    (lowerOrbitElement_injective a 0 ha)

end OpenAIPort
end Connes
