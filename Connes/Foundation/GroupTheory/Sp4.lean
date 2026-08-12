/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Standalone finite proofs for the Sp₄(F₂) arguments in Zhou §§2 and 6.
Mathlib supplies the symplectic-matrix carrier and its action on the standard
four-dimensional module.
-/
import Mathlib
import Connes.Foundation.LinearAlgebra.Symplectic
import Connes.Foundation.LinearAlgebra.QuadraticCocycle

namespace Connes
namespace Sp4

/-- Characteristic-two scalar field. Paper: §§2, 6. -/
abbrev F := ZMod 2
/-- Symplectic group carrier. Paper: §§2, 6. -/
abbrev Group := Symplectic.Sp4

private abbrev Matrix4 := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F

private def allMatrices : Finset Matrix4 := Finset.univ

private def symplecticMatrices : Finset Matrix4 :=
  allMatrices.filter (fun A =>
    A * Matrix.J (Fin 2) F * A.transpose = Matrix.J (Fin 2) F)

instance : Fintype Group :=
  Fintype.subtype symplecticMatrices (by
    intro x
    simp [Group, symplecticMatrices, allMatrices, Matrix.symplecticGroup])

private abbrev V := OpenAIPort.ModTwoSpace

private def pairing (v w : V) : F :=
  OpenAIPort.modTwoSymplecticForm v w

private def transvectionMatrix (u : V) : Matrix4 :=
  1 + Matrix.vecMulVec u ((Matrix.J (Fin 2) F).mulVec u)

private theorem transvectionMatrix_mem :
    ∀ u : V, transvectionMatrix u ∈ Matrix.symplecticGroup (Fin 2) F := by
  decide

private def transvection (u : V) : Group :=
  ⟨transvectionMatrix u, transvectionMatrix_mem u⟩

private theorem transvection_apply (u v : V) :
    transvection u • v = v + pairing v u • u := by
  decide +revert

private theorem pairing_self (v : V) : pairing v v = 0 := by
  decide +revert

private theorem eq_one_of_ne_zero (a : F) (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

private theorem pairing_add_right (u v w : V) :
    pairing u (v + w) = pairing u v + pairing u w := by
  exact OpenAIPort.modTwoSymplecticForm_add_right u v w

private theorem pairing_one_bridge :
    ∀ v : V, v ≠ 0 → ∀ w : V, w ≠ 0 → pairing v w = 0 →
      ∃ z : V, pairing v z = 1 ∧ pairing z w = 1 := by
  decide

/-- Transitivity of the natural `Sp₄(F₂)` action on nonzero vectors. Paper: §2. -/
def actsOnNonzeroVectors : Prop :=
  ∀ v : OpenAIPort.ModTwoSpace, v ≠ 0 →
    ∀ w : OpenAIPort.ModTwoSpace, w ≠ 0 →
      ∃ g : Group, g • v = w

/-- Nonzero-vector transitivity. Paper: §2. -/
theorem transitive_on_nonzero_vectors : actsOnNonzeroVectors := by
  unfold actsOnNonzeroVectors
  intro v hv w hw
  by_cases hvw : pairing v w = 0
  · obtain ⟨z, hvz, hzw⟩ := pairing_one_bridge v hv w hw hvw
    refine ⟨transvection (z + w) * transvection (v + z), ?_⟩
    rw [mul_smul]
    rw [transvection_apply (v + z) v]
    rw [pairing_add_right, pairing_self, zero_add, hvz, one_smul]
    rw [show v + (v + z) = z by
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]]
    rw [transvection_apply]
    rw [pairing_add_right, pairing_self, zero_add, hzw, one_smul]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · have hvw' : pairing v w = 1 := eq_one_of_ne_zero _ hvw
    refine ⟨transvection (v + w), ?_⟩
    rw [transvection_apply, pairing_add_right, pairing_self, zero_add,
      hvw', one_smul]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- Normal-subgroup obstruction boundary. Paper: §6. -/
def no_nontrivial_normal_elementary_abelian_subgroup : Prop :=
  ∀ N : Subgroup Group, N.Normal →
    (∀ x y : N, x * y = y * x) → N = ⊥

private abbrev BVMatrix := BitVec 16
private abbrev BMatrix := Fin 4 → Fin 4 → Bool

private def bvEntry (x : BVMatrix) : BMatrix := fun i j =>
  x.getLsbD (4 * i.val + j.val)

private def boolDot (a b : BMatrix) (i j : Fin 4) : Bool :=
  (a i 0 && b 0 j) ^^ (a i 1 && b 1 j) ^^
  (a i 2 && b 2 j) ^^ (a i 3 && b 3 j)

private def boolMul (a b : BMatrix) : BMatrix := boolDot a b
private def boolTranspose (a : BMatrix) : BMatrix := fun i j => a j i

private def boolMatrixEq (a b : BMatrix) : Prop :=
  a 0 0 = b 0 0 ∧ a 0 1 = b 0 1 ∧ a 0 2 = b 0 2 ∧ a 0 3 = b 0 3 ∧
  a 1 0 = b 1 0 ∧ a 1 1 = b 1 1 ∧ a 1 2 = b 1 2 ∧ a 1 3 = b 1 3 ∧
  a 2 0 = b 2 0 ∧ a 2 1 = b 2 1 ∧ a 2 2 = b 2 2 ∧ a 2 3 = b 2 3 ∧
  a 3 0 = b 3 0 ∧ a 3 1 = b 3 1 ∧ a 3 2 = b 3 2 ∧ a 3 3 = b 3 3

private def boolMatrixEqB (a b : BMatrix) : Bool :=
  (a 0 0 == b 0 0) && (a 0 1 == b 0 1) &&
  (a 0 2 == b 0 2) && (a 0 3 == b 0 3) &&
  (a 1 0 == b 1 0) && (a 1 1 == b 1 1) &&
  (a 1 2 == b 1 2) && (a 1 3 == b 1 3) &&
  (a 2 0 == b 2 0) && (a 2 1 == b 2 1) &&
  (a 2 2 == b 2 2) && (a 2 3 == b 2 3) &&
  (a 3 0 == b 3 0) && (a 3 1 == b 3 1) &&
  (a 3 2 == b 3 2) && (a 3 3 == b 3 3)

private theorem boolMatrixEqB_eq_true_iff (a b : BMatrix) :
    boolMatrixEqB a b = true ↔ boolMatrixEq a b := by
  simp only [boolMatrixEqB, Bool.and_eq_true, beq_iff_eq, boolMatrixEq]
  tauto

private def boolOne : BMatrix := bvEntry (BitVec.ofNat 16 0x8421)
private def boolJ : BMatrix := bvEntry (BitVec.ofNat 16 0x2184)
private def boolG1 : BMatrix := bvEntry (BitVec.ofNat 16 0x13DB)
private def boolG1Inv : BMatrix := bvEntry (BitVec.ofNat 16 0x5FC8)
private def boolG2 : BMatrix := bvEntry (BitVec.ofNat 16 0x21B7)
private def boolG2Inv : BMatrix := bvEntry (BitVec.ofNat 16 0xED84)

private def boolSymplectic (x : BMatrix) : Prop :=
  boolMatrixEq (boolMul (boolMul x boolJ) (boolTranspose x)) boolJ

private def boolConj (g gi x : BMatrix) : BMatrix := boolMul (boolMul g x) gi
private def boolCommutes (a b : BMatrix) : Prop :=
  boolMatrixEq (boolMul a b) (boolMul b a)

private def boolCommutesB (a b : BMatrix) : Bool :=
  boolMatrixEqB (boolMul a b) (boolMul b a)

private def detectorCheck (x : BVMatrix) : Bool :=
  !(boolMatrixEqB (boolMul (boolMul (bvEntry x) boolJ)
      (boolTranspose (bvEntry x))) boolJ) ||
  boolMatrixEqB (bvEntry x) boolOne ||
  !(boolCommutesB (boolConj boolG1 boolG1Inv (bvEntry x)) (bvEntry x)) ||
  !(boolCommutesB (boolConj boolG2 boolG2Inv (bvEntry x)) (bvEntry x))

section KernelDetectorChunks

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

private theorem detectorChunk0 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 0 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 0 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk1 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 1 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 1 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk2 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 2 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 2 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk3 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 3 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 3 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk4 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 4 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 4 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk5 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 5 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 5 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk6 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 6 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 6 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk7 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 7 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 7 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk8 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 8 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 8 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk9 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 9 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 9 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk10 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 10 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 10 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk11 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 11 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 11 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk12 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 12 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 12 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk13 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 13 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 13 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk14 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 14 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 14 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk15 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 15 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 15 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk16 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 16 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 16 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk17 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 17 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 17 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk18 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 18 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 18 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk19 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 19 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 19 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk20 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 20 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 20 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk21 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 21 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 21 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk22 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 22 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 22 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk23 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 23 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 23 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk24 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 24 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 24 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk25 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 25 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 25 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk26 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 26 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 26 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk27 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 27 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 27 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk28 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 28 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 28 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk29 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 29 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 29 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk30 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 30 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 30 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk31 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 31 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 31 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk32 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 32 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 32 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk33 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 33 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 33 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk34 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 34 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 34 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk35 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 35 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 35 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk36 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 36 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 36 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk37 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 37 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 37 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk38 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 38 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 38 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk39 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 39 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 39 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk40 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 40 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 40 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk41 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 41 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 41 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk42 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 42 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 42 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk43 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 43 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 43 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk44 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 44 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 44 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk45 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 45 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 45 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk46 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 46 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 46 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk47 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 47 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 47 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk48 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 48 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 48 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk49 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 49 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 49 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk50 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 50 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 50 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk51 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 51 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 51 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk52 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 52 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 52 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk53 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 53 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 53 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk54 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 54 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 54 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk55 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 55 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 55 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk56 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 56 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 56 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk57 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 57 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 57 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk58 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 58 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 58 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk59 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 59 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 59 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk60 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 60 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 60 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk61 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 61 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 61 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk62 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 62 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 62 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk63 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 63 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 63 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk64 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 64 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 64 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk65 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 65 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 65 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk66 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 66 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 66 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk67 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 67 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 67 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk68 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 68 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 68 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk69 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 69 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 69 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk70 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 70 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 70 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk71 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 71 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 71 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk72 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 72 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 72 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk73 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 73 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 73 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk74 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 74 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 74 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk75 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 75 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 75 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk76 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 76 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 76 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk77 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 77 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 77 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk78 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 78 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 78 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk79 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 79 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 79 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk80 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 80 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 80 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk81 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 81 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 81 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk82 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 82 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 82 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk83 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 83 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 83 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk84 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 84 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 84 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk85 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 85 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 85 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk86 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 86 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 86 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk87 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 87 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 87 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk88 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 88 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 88 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk89 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 89 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 89 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk90 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 90 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 90 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk91 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 91 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 91 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk92 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 92 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 92 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk93 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 93 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 93 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk94 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 94 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 94 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk95 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 95 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 95 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk96 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 96 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 96 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk97 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 97 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 97 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk98 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 98 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 98 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk99 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 99 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 99 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk100 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 100 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 100 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk101 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 101 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 101 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk102 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 102 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 102 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk103 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 103 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 103 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk104 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 104 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 104 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk105 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 105 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 105 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk106 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 106 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 106 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk107 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 107 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 107 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk108 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 108 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 108 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk109 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 109 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 109 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk110 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 110 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 110 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk111 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 111 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 111 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk112 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 112 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 112 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk113 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 113 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 113 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk114 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 114 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 114 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk115 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 115 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 115 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk116 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 116 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 116 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk117 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 117 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 117 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk118 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 118 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 118 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk119 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 119 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 119 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk120 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 120 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 120 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk121 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 121 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 121 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk122 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 122 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 122 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk123 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 123 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 123 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk124 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 124 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 124 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk125 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 125 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 125 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk126 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 126 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 126 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk127 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 127 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 127 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk128 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 128 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 128 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk129 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 129 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 129 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk130 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 130 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 130 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk131 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 131 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 131 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk132 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 132 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 132 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk133 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 133 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 133 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk134 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 134 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 134 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk135 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 135 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 135 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk136 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 136 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 136 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk137 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 137 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 137 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk138 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 138 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 138 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk139 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 139 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 139 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk140 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 140 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 140 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk141 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 141 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 141 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk142 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 142 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 142 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk143 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 143 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 143 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk144 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 144 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 144 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk145 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 145 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 145 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk146 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 146 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 146 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk147 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 147 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 147 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk148 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 148 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 148 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk149 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 149 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 149 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk150 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 150 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 150 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk151 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 151 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 151 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk152 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 152 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 152 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk153 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 153 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 153 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk154 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 154 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 154 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk155 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 155 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 155 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk156 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 156 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 156 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk157 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 157 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 157 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk158 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 158 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 158 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk159 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 159 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 159 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk160 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 160 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 160 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk161 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 161 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 161 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk162 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 162 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 162 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk163 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 163 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 163 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk164 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 164 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 164 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk165 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 165 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 165 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk166 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 166 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 166 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk167 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 167 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 167 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk168 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 168 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 168 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk169 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 169 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 169 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk170 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 170 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 170 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk171 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 171 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 171 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk172 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 172 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 172 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk173 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 173 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 173 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk174 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 174 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 174 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk175 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 175 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 175 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk176 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 176 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 176 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk177 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 177 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 177 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk178 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 178 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 178 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk179 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 179 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 179 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk180 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 180 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 180 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk181 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 181 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 181 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk182 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 182 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 182 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk183 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 183 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 183 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk184 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 184 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 184 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk185 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 185 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 185 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk186 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 186 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 186 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk187 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 187 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 187 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk188 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 188 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 188 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk189 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 189 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 189 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk190 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 190 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 190 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk191 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 191 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 191 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk192 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 192 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 192 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk193 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 193 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 193 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk194 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 194 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 194 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk195 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 195 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 195 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk196 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 196 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 196 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk197 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 197 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 197 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk198 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 198 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 198 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk199 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 199 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 199 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk200 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 200 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 200 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk201 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 201 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 201 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk202 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 202 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 202 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk203 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 203 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 203 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk204 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 204 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 204 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk205 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 205 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 205 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk206 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 206 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 206 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk207 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 207 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 207 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk208 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 208 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 208 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk209 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 209 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 209 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk210 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 210 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 210 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk211 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 211 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 211 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk212 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 212 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 212 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk213 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 213 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 213 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk214 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 214 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 214 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk215 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 215 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 215 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk216 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 216 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 216 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk217 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 217 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 217 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk218 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 218 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 218 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk219 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 219 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 219 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk220 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 220 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 220 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk221 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 221 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 221 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk222 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 222 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 222 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk223 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 223 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 223 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk224 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 224 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 224 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk225 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 225 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 225 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk226 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 226 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 226 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk227 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 227 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 227 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk228 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 228 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 228 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk229 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 229 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 229 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk230 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 230 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 230 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk231 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 231 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 231 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk232 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 232 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 232 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk233 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 233 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 233 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk234 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 234 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 234 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk235 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 235 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 235 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk236 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 236 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 236 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk237 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 237 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 237 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk238 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 238 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 238 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk239 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 239 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 239 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk240 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 240 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 240 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk241 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 241 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 241 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk242 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 242 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 242 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk243 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 243 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 243 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk244 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 244 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 244 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk245 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 245 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 245 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk246 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 246 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 246 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk247 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 247 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 247 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk248 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 248 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 248 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk249 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 249 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 249 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk250 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 250 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 250 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk251 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 251 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 251 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk252 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 252 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 252 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk253 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 253 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 253 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk254 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 254 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 254 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunk255 : ∀ lo : Fin 256,
    detectorCheck (BitVec.ofNat 16 (256 * 255 + lo.val)) = true := by
  letI : DecidablePred (fun lo : Fin 256 =>
      detectorCheck (BitVec.ofNat 16 (256 * 255 + lo.val)) = true) := fun _ => inferInstance
  decide

private theorem detectorChunks (hi lo : Fin 256) :
    detectorCheck (BitVec.ofNat 16 (256 * hi.val + lo.val)) = true := by
  fin_cases hi
  · exact detectorChunk0 lo
  · exact detectorChunk1 lo
  · exact detectorChunk2 lo
  · exact detectorChunk3 lo
  · exact detectorChunk4 lo
  · exact detectorChunk5 lo
  · exact detectorChunk6 lo
  · exact detectorChunk7 lo
  · exact detectorChunk8 lo
  · exact detectorChunk9 lo
  · exact detectorChunk10 lo
  · exact detectorChunk11 lo
  · exact detectorChunk12 lo
  · exact detectorChunk13 lo
  · exact detectorChunk14 lo
  · exact detectorChunk15 lo
  · exact detectorChunk16 lo
  · exact detectorChunk17 lo
  · exact detectorChunk18 lo
  · exact detectorChunk19 lo
  · exact detectorChunk20 lo
  · exact detectorChunk21 lo
  · exact detectorChunk22 lo
  · exact detectorChunk23 lo
  · exact detectorChunk24 lo
  · exact detectorChunk25 lo
  · exact detectorChunk26 lo
  · exact detectorChunk27 lo
  · exact detectorChunk28 lo
  · exact detectorChunk29 lo
  · exact detectorChunk30 lo
  · exact detectorChunk31 lo
  · exact detectorChunk32 lo
  · exact detectorChunk33 lo
  · exact detectorChunk34 lo
  · exact detectorChunk35 lo
  · exact detectorChunk36 lo
  · exact detectorChunk37 lo
  · exact detectorChunk38 lo
  · exact detectorChunk39 lo
  · exact detectorChunk40 lo
  · exact detectorChunk41 lo
  · exact detectorChunk42 lo
  · exact detectorChunk43 lo
  · exact detectorChunk44 lo
  · exact detectorChunk45 lo
  · exact detectorChunk46 lo
  · exact detectorChunk47 lo
  · exact detectorChunk48 lo
  · exact detectorChunk49 lo
  · exact detectorChunk50 lo
  · exact detectorChunk51 lo
  · exact detectorChunk52 lo
  · exact detectorChunk53 lo
  · exact detectorChunk54 lo
  · exact detectorChunk55 lo
  · exact detectorChunk56 lo
  · exact detectorChunk57 lo
  · exact detectorChunk58 lo
  · exact detectorChunk59 lo
  · exact detectorChunk60 lo
  · exact detectorChunk61 lo
  · exact detectorChunk62 lo
  · exact detectorChunk63 lo
  · exact detectorChunk64 lo
  · exact detectorChunk65 lo
  · exact detectorChunk66 lo
  · exact detectorChunk67 lo
  · exact detectorChunk68 lo
  · exact detectorChunk69 lo
  · exact detectorChunk70 lo
  · exact detectorChunk71 lo
  · exact detectorChunk72 lo
  · exact detectorChunk73 lo
  · exact detectorChunk74 lo
  · exact detectorChunk75 lo
  · exact detectorChunk76 lo
  · exact detectorChunk77 lo
  · exact detectorChunk78 lo
  · exact detectorChunk79 lo
  · exact detectorChunk80 lo
  · exact detectorChunk81 lo
  · exact detectorChunk82 lo
  · exact detectorChunk83 lo
  · exact detectorChunk84 lo
  · exact detectorChunk85 lo
  · exact detectorChunk86 lo
  · exact detectorChunk87 lo
  · exact detectorChunk88 lo
  · exact detectorChunk89 lo
  · exact detectorChunk90 lo
  · exact detectorChunk91 lo
  · exact detectorChunk92 lo
  · exact detectorChunk93 lo
  · exact detectorChunk94 lo
  · exact detectorChunk95 lo
  · exact detectorChunk96 lo
  · exact detectorChunk97 lo
  · exact detectorChunk98 lo
  · exact detectorChunk99 lo
  · exact detectorChunk100 lo
  · exact detectorChunk101 lo
  · exact detectorChunk102 lo
  · exact detectorChunk103 lo
  · exact detectorChunk104 lo
  · exact detectorChunk105 lo
  · exact detectorChunk106 lo
  · exact detectorChunk107 lo
  · exact detectorChunk108 lo
  · exact detectorChunk109 lo
  · exact detectorChunk110 lo
  · exact detectorChunk111 lo
  · exact detectorChunk112 lo
  · exact detectorChunk113 lo
  · exact detectorChunk114 lo
  · exact detectorChunk115 lo
  · exact detectorChunk116 lo
  · exact detectorChunk117 lo
  · exact detectorChunk118 lo
  · exact detectorChunk119 lo
  · exact detectorChunk120 lo
  · exact detectorChunk121 lo
  · exact detectorChunk122 lo
  · exact detectorChunk123 lo
  · exact detectorChunk124 lo
  · exact detectorChunk125 lo
  · exact detectorChunk126 lo
  · exact detectorChunk127 lo
  · exact detectorChunk128 lo
  · exact detectorChunk129 lo
  · exact detectorChunk130 lo
  · exact detectorChunk131 lo
  · exact detectorChunk132 lo
  · exact detectorChunk133 lo
  · exact detectorChunk134 lo
  · exact detectorChunk135 lo
  · exact detectorChunk136 lo
  · exact detectorChunk137 lo
  · exact detectorChunk138 lo
  · exact detectorChunk139 lo
  · exact detectorChunk140 lo
  · exact detectorChunk141 lo
  · exact detectorChunk142 lo
  · exact detectorChunk143 lo
  · exact detectorChunk144 lo
  · exact detectorChunk145 lo
  · exact detectorChunk146 lo
  · exact detectorChunk147 lo
  · exact detectorChunk148 lo
  · exact detectorChunk149 lo
  · exact detectorChunk150 lo
  · exact detectorChunk151 lo
  · exact detectorChunk152 lo
  · exact detectorChunk153 lo
  · exact detectorChunk154 lo
  · exact detectorChunk155 lo
  · exact detectorChunk156 lo
  · exact detectorChunk157 lo
  · exact detectorChunk158 lo
  · exact detectorChunk159 lo
  · exact detectorChunk160 lo
  · exact detectorChunk161 lo
  · exact detectorChunk162 lo
  · exact detectorChunk163 lo
  · exact detectorChunk164 lo
  · exact detectorChunk165 lo
  · exact detectorChunk166 lo
  · exact detectorChunk167 lo
  · exact detectorChunk168 lo
  · exact detectorChunk169 lo
  · exact detectorChunk170 lo
  · exact detectorChunk171 lo
  · exact detectorChunk172 lo
  · exact detectorChunk173 lo
  · exact detectorChunk174 lo
  · exact detectorChunk175 lo
  · exact detectorChunk176 lo
  · exact detectorChunk177 lo
  · exact detectorChunk178 lo
  · exact detectorChunk179 lo
  · exact detectorChunk180 lo
  · exact detectorChunk181 lo
  · exact detectorChunk182 lo
  · exact detectorChunk183 lo
  · exact detectorChunk184 lo
  · exact detectorChunk185 lo
  · exact detectorChunk186 lo
  · exact detectorChunk187 lo
  · exact detectorChunk188 lo
  · exact detectorChunk189 lo
  · exact detectorChunk190 lo
  · exact detectorChunk191 lo
  · exact detectorChunk192 lo
  · exact detectorChunk193 lo
  · exact detectorChunk194 lo
  · exact detectorChunk195 lo
  · exact detectorChunk196 lo
  · exact detectorChunk197 lo
  · exact detectorChunk198 lo
  · exact detectorChunk199 lo
  · exact detectorChunk200 lo
  · exact detectorChunk201 lo
  · exact detectorChunk202 lo
  · exact detectorChunk203 lo
  · exact detectorChunk204 lo
  · exact detectorChunk205 lo
  · exact detectorChunk206 lo
  · exact detectorChunk207 lo
  · exact detectorChunk208 lo
  · exact detectorChunk209 lo
  · exact detectorChunk210 lo
  · exact detectorChunk211 lo
  · exact detectorChunk212 lo
  · exact detectorChunk213 lo
  · exact detectorChunk214 lo
  · exact detectorChunk215 lo
  · exact detectorChunk216 lo
  · exact detectorChunk217 lo
  · exact detectorChunk218 lo
  · exact detectorChunk219 lo
  · exact detectorChunk220 lo
  · exact detectorChunk221 lo
  · exact detectorChunk222 lo
  · exact detectorChunk223 lo
  · exact detectorChunk224 lo
  · exact detectorChunk225 lo
  · exact detectorChunk226 lo
  · exact detectorChunk227 lo
  · exact detectorChunk228 lo
  · exact detectorChunk229 lo
  · exact detectorChunk230 lo
  · exact detectorChunk231 lo
  · exact detectorChunk232 lo
  · exact detectorChunk233 lo
  · exact detectorChunk234 lo
  · exact detectorChunk235 lo
  · exact detectorChunk236 lo
  · exact detectorChunk237 lo
  · exact detectorChunk238 lo
  · exact detectorChunk239 lo
  · exact detectorChunk240 lo
  · exact detectorChunk241 lo
  · exact detectorChunk242 lo
  · exact detectorChunk243 lo
  · exact detectorChunk244 lo
  · exact detectorChunk245 lo
  · exact detectorChunk246 lo
  · exact detectorChunk247 lo
  · exact detectorChunk248 lo
  · exact detectorChunk249 lo
  · exact detectorChunk250 lo
  · exact detectorChunk251 lo
  · exact detectorChunk252 lo
  · exact detectorChunk253 lo
  · exact detectorChunk254 lo
  · exact detectorChunk255 lo

private theorem detectorCheck_all (x : BVMatrix) : detectorCheck x = true := by
  have hxlt : x.toNat < 65536 := by
    simpa using x.toFin.isLt
  let hi : Fin 256 := ⟨x.toNat / 256, by omega⟩
  let lo : Fin 256 := ⟨x.toNat % 256, Nat.mod_lt _ (by omega)⟩
  have hval : 256 * hi.val + lo.val = x.toNat := by
    dsimp [hi, lo]
    omega
  have hx : BitVec.ofNat 16 (256 * hi.val + lo.val) = x := by
    apply BitVec.eq_of_toNat_eq
    have hxlt' : x.toNat < 2 ^ 16 := by
      norm_num at hxlt ⊢
      exact hxlt
    rw [BitVec.toNat_ofNat, hval, Nat.mod_eq_of_lt hxlt']
  rw [← hx]
  exact detectorChunks hi lo

private theorem boolean_detector_cover : ∀ x : BVMatrix,
    boolSymplectic (bvEntry x) → ¬boolMatrixEq (bvEntry x) boolOne →
    ¬boolCommutes (boolConj boolG1 boolG1Inv (bvEntry x)) (bvEntry x) ∨
    ¬boolCommutes (boolConj boolG2 boolG2Inv (bvEntry x)) (bvEntry x) := by
  intro x hs hn
  have hc := detectorCheck_all x
  have hsB :
      boolMatrixEqB (boolMul (boolMul (bvEntry x) boolJ)
        (boolTranspose (bvEntry x))) boolJ = true :=
    (boolMatrixEqB_eq_true_iff _ _).2 hs
  have hnB : boolMatrixEqB (bvEntry x) boolOne = false := by
    cases h : boolMatrixEqB (bvEntry x) boolOne
    · rfl
    · exact (hn ((boolMatrixEqB_eq_true_iff _ _).1 h)).elim
  rw [detectorCheck, hsB, hnB] at hc
  simp only [Bool.not_true, Bool.false_or] at hc
  by_cases h1 :
      boolCommutesB (boolConj boolG1 boolG1Inv (bvEntry x)) (bvEntry x) = true
  · right
    intro hp
    have h2 :
        boolCommutesB (boolConj boolG2 boolG2Inv (bvEntry x)) (bvEntry x) = true := by
      exact (boolMatrixEqB_eq_true_iff _ _).2 hp
    simp [h1, h2] at hc
  · left
    intro hp
    exact h1 ((boolMatrixEqB_eq_true_iff _ _).2 hp)

end KernelDetectorChunks

private abbrev MatrixIndex := Fin 2 ⊕ Fin 2

private def matrixIndex (i : MatrixIndex) : Fin 4 := finSumFinEquiv i
private def boolToF (b : Bool) : F := if b then 1 else 0

private theorem boolToF_and (a b : Bool) :
    boolToF (a && b) = boolToF a * boolToF b := by
  cases a <;> cases b <;> rfl

private theorem boolToF_xor (a b : Bool) :
    boolToF (a ^^ b) = boolToF a + boolToF b := by
  cases a <;> cases b <;> rfl

private theorem boolToF_decide_eq_one (a : F) :
    boolToF (decide (a = 1)) = a := by
  fin_cases a <;> rfl

private theorem boolToF_injective : Function.Injective boolToF := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolToF]

private def decodeBoolMatrix (a : BMatrix) : Matrix4 := fun i j =>
  boolToF (a (matrixIndex i) (matrixIndex j))

private theorem decodeBoolMatrix_mul (a b : BMatrix) :
    decodeBoolMatrix (boolMul a b) = decodeBoolMatrix a * decodeBoolMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [decodeBoolMatrix, boolMul, boolDot, matrixIndex, Matrix.mul_apply,
      boolToF_and, boolToF_xor, Fin.sum_univ_two, finSumFinEquiv] <;>
    ring

private theorem decodeBoolMatrix_transpose (a : BMatrix) :
    decodeBoolMatrix (boolTranspose a) = (decodeBoolMatrix a).transpose := by
  rfl

private theorem boolMatrixEq_iff_decode_eq (a b : BMatrix) :
    boolMatrixEq a b ↔ decodeBoolMatrix a = decodeBoolMatrix b := by
  constructor
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp_all [boolMatrixEq, decodeBoolMatrix, matrixIndex, finSumFinEquiv]
  · intro h
    have hij (i j : Fin 4) : a i j = b i j := by
      have hm := congrFun (congrFun h (finSumFinEquiv.symm i))
        (finSumFinEquiv.symm j)
      apply boolToF_injective
      simpa [decodeBoolMatrix, matrixIndex] using hm
    simp only [boolMatrixEq]
    aesop

private def bvBit (n : Nat) (b : Bool) : BVMatrix :=
  (BitVec.ofBool b).setWidth 16 <<< n

private def bvBuild (f : Fin 16 → Bool) : BVMatrix :=
  bvBit 0 (f 0) ||| bvBit 1 (f 1) ||| bvBit 2 (f 2) ||| bvBit 3 (f 3) |||
  bvBit 4 (f 4) ||| bvBit 5 (f 5) ||| bvBit 6 (f 6) ||| bvBit 7 (f 7) |||
  bvBit 8 (f 8) ||| bvBit 9 (f 9) ||| bvBit 10 (f 10) ||| bvBit 11 (f 11) |||
  bvBit 12 (f 12) ||| bvBit 13 (f 13) ||| bvBit 14 (f 14) ||| bvBit 15 (f 15)

private theorem bvBuild_getLsbD (f : Fin 16 → Bool) (k : Fin 16) :
    (bvBuild f).getLsbD k.val = f k := by
  fin_cases k <;> simp [bvBuild, bvBit]

private def rowOfBit (k : Fin 16) : MatrixIndex :=
  finSumFinEquiv.symm ⟨k.val / 4, by omega⟩

private def colOfBit (k : Fin 16) : MatrixIndex :=
  finSumFinEquiv.symm ⟨k.val % 4, Nat.mod_lt _ (by omega)⟩

private def encodeMatrix (M : Matrix4) : BVMatrix :=
  bvBuild fun k => decide (M (rowOfBit k) (colOfBit k) = 1)

private theorem decode_encodeMatrix (M : Matrix4) :
    decodeBoolMatrix (bvEntry (encodeMatrix M)) = M := by
  ext i j
  let k : Fin 16 := ⟨4 * (matrixIndex i).val + (matrixIndex j).val, by omega⟩
  have hget := bvBuild_getLsbD
    (fun k => decide (M (rowOfBit k) (colOfBit k) = 1)) k
  change boolToF ((encodeMatrix M).getLsbD k.val) = M i j
  rw [show encodeMatrix M = bvBuild
      (fun k => decide (M (rowOfBit k) (colOfBit k) = 1)) by rfl, hget]
  have hrow : rowOfBit k = i := by
    have hval : k.val / 4 = (matrixIndex i).val := by
      dsimp [k]
      omega
    apply finSumFinEquiv.injective
    simp only [rowOfBit, Equiv.apply_symm_apply]
    exact Fin.ext hval
  have hcol : colOfBit k = j := by
    have hval : k.val % 4 = (matrixIndex j).val := by
      dsimp [k]
      omega
    apply finSumFinEquiv.injective
    simp only [colOfBit, Equiv.apply_symm_apply]
    exact Fin.ext hval
  rw [hrow, hcol]
  exact boolToF_decide_eq_one _

private theorem decode_boolOne : decodeBoolMatrix boolOne = (1 : Matrix4) := by
  decide

private theorem decode_boolJ :
    decodeBoolMatrix boolJ = Matrix.J (Fin 2) F := by
  decide

private def detectorOne : Group := ⟨decodeBoolMatrix boolG1, by
  change decodeBoolMatrix boolG1 * Matrix.J (Fin 2) F *
      (decodeBoolMatrix boolG1).transpose = Matrix.J (Fin 2) F
  decide⟩

private def detectorTwo : Group := ⟨decodeBoolMatrix boolG2, by
  change decodeBoolMatrix boolG2 * Matrix.J (Fin 2) F *
      (decodeBoolMatrix boolG2).transpose = Matrix.J (Fin 2) F
  decide⟩

private theorem detectorOne_inv :
    ((detectorOne⁻¹ : Group) : Matrix4) = decodeBoolMatrix boolG1Inv := by
  decide

private theorem detectorTwo_inv :
    ((detectorTwo⁻¹ : Group) : Matrix4) = decodeBoolMatrix boolG2Inv := by
  decide

private theorem encoded_symplectic (x : Group) :
    boolSymplectic (bvEntry (encodeMatrix (x : Matrix4))) := by
  unfold boolSymplectic
  apply (boolMatrixEq_iff_decode_eq _ _).2
  rw [decodeBoolMatrix_mul, decodeBoolMatrix_mul, decodeBoolMatrix_transpose,
    decode_encodeMatrix, decode_boolJ]
  exact x.property

private theorem encoded_ne_one (x : Group) (hx : x ≠ 1) :
    ¬boolMatrixEq (bvEntry (encodeMatrix (x : Matrix4))) boolOne := by
  intro h
  apply hx
  apply Subtype.ext
  have hm := (boolMatrixEq_iff_decode_eq _ _).1 h
  simpa [decode_encodeMatrix, decode_boolOne] using hm

private theorem conjugacy_detector :
    ∀ x : Group, x ≠ 1 →
      ∃ g : Group, (g * x * g⁻¹) * x ≠ x * (g * x * g⁻¹) := by
  intro x hx
  have hc := boolean_detector_cover (encodeMatrix (x : Matrix4))
    (encoded_symplectic x) (encoded_ne_one x hx)
  rcases hc with h | h
  · refine ⟨detectorOne, ?_⟩
    intro hcomm
    apply h
    unfold boolCommutes boolConj
    apply (boolMatrixEq_iff_decode_eq _ _).2
    simp only [decodeBoolMatrix_mul, decode_encodeMatrix]
    rw [show decodeBoolMatrix boolG1 = (detectorOne : Matrix4) by rfl]
    rw [← detectorOne_inv]
    exact congrArg Subtype.val hcomm
  · refine ⟨detectorTwo, ?_⟩
    intro hcomm
    apply h
    unfold boolCommutes boolConj
    apply (boolMatrixEq_iff_decode_eq _ _).2
    simp only [decodeBoolMatrix_mul, decode_encodeMatrix]
    rw [show decodeBoolMatrix boolG2 = (detectorTwo : Matrix4) by rfl]
    rw [← detectorTwo_inv]
    exact congrArg Subtype.val hcomm

theorem no_nontrivial_normal_elementary_abelian_subgroup_proof :
    no_nontrivial_normal_elementary_abelian_subgroup := by
  intro N hnormal hab
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hne
  have hxne : (x : Group) ≠ 1 := by
    intro h
    apply hne
    simpa using h
  obtain ⟨g, hcomm⟩ := conjugacy_detector x hxne
  have hy : g * (x : Group) * g⁻¹ ∈ N := hnormal.conj_mem x hx g
  let y : N := ⟨g * (x : Group) * g⁻¹, hy⟩
  have hxy := hab y ⟨x, hx⟩
  apply hcomm
  exact congrArg Subtype.val hxy

end Sp4
end Connes
