/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

The concrete spatial crossed-product bridge for Zhou §3. Character
multipliers generate the continuous-coefficient crossed closure by uniform
Stone--Weierstrass density; the fiber shear transports that closure and hence
the two regular group factors.
-/
import Connes.Paper.Section3.GroupQuotient
import Connes.Foundation.OperatorAlgebra.SemidirectClosure
import Connes.Foundation.OperatorAlgebra.CrossedProductFactorTransport
import Connes.Paper.Section3.GroupVacuum
import Connes.Foundation.OperatorAlgebra.SemidirectGeneratorTransport
import Connes.Foundation.OperatorAlgebra.FactorWitness

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace Connes
namespace PaperFactorClosure

open Construction
open Construction.PaperKernel
open PaperCrossedHaar
open PaperCrossedKernel
open PaperFourier
open PaperFourierCoordinates
open PaperDualTopology
open PaperGroupFactor
open PaperGroupQuotient
open PaperGroupVacuum
open CrossedProduct
open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

abbrev D := PaperKernel.D
abbrev H := Construction.H

local instance paperHaarProbability
    (X : HaarProbabilityAction H PaperFactorIsomorphism.DualCoordinates) :
    IsProbabilityMeasure X.measure :=
  X.probability

private theorem leftRegularRepresentation_apply_clm
    {G : Type*} [Group G] (g : G) :
    ((leftRegularRepresentation G g :
        unitary (GroupL2 G →L[ℂ] GroupL2 G)) :
      GroupL2 G →L[ℂ] GroupL2 G) =
      ((leftRegularUnitary g :
          unitary (GroupL2 G →L[ℂ] GroupL2 G)) :
        GroupL2 G →L[ℂ] GroupL2 G) := rfl

def reducedCrossedGeneratorSetOne :
    Set (CrossedOne →L[ℂ] CrossedOne) :=
  Set.range crossedKernelMultiplier ∪
    Set.range fun h : H ↦
      (crossedGroupUnitary paperHaarActionOne h).toContinuousLinearEquiv.toContinuousLinearMap

def reducedCrossedGeneratorSetTwo :
    Set (CrossedTwo →L[ℂ] CrossedTwo) :=
  (Set.range fun d : D ↦
      crossedMultiplier paperHaarActionTwo (coordinateCharacterCoefficient d)) ∪
    Set.range fun h : H ↦
      (crossedGroupUnitary paperHaarActionTwo h).toContinuousLinearEquiv.toContinuousLinearMap

theorem mem_vonNeumannClosure_mono
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    {S T : Set (E →L[ℂ] E)} (hST : S ⊆ T)
    {x : E →L[ℂ] E} (hx : x ∈ vonNeumannClosure S) :
    x ∈ vonNeumannClosure T := by
  change x ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ T : Set (E →L[ℂ] E))
  change x ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ S : Set (E →L[ℂ] E)) at hx
  simp only [StarSubalgebra.mem_centralizer_iff] at hx ⊢
  intro z hzT
  apply hx z
  intro y hyS
  apply hzT y
  rcases hyS with hyS | hyS
  · exact Or.inl (hST hyS)
  · exact Or.inr (Set.mem_star.mpr (hST (Set.mem_star.mp hyS)))

theorem paperGroupFactorUnitaryOne_generatorSet_image :
    paperGroupFactorUnitaryOne.conjStarAlgEquiv ''
        SemidirectGeneratorTransport.generatorSet
          (A := Multiplicative D) (K := H) paperThetaOneHom =
      reducedCrossedGeneratorSetOne := by
  ext T
  constructor
  · rintro ⟨S, (⟨a, rfl⟩ | ⟨h, rfl⟩), rfl⟩
    · left
      refine ⟨Multiplicative.toAdd a, ?_⟩
      simpa only [leftRegularRepresentation_apply_clm, ofAdd_toAdd] using
        (paperGroupFactorUnitaryOne_conj_inl
          (Multiplicative.toAdd a)).symm
    · right
      exact ⟨h, (paperGroupFactorUnitaryOne_conj_inr h).symm⟩
  · rintro (⟨d, rfl⟩ | ⟨h, rfl⟩)
    · refine ⟨_, Or.inl ⟨Multiplicative.ofAdd d, rfl⟩, ?_⟩
      exact paperGroupFactorUnitaryOne_conj_inl d
    · refine ⟨_, Or.inr ⟨h, rfl⟩, ?_⟩
      exact paperGroupFactorUnitaryOne_conj_inr h

theorem paperGroupFactorUnitaryTwo_generatorSet_image :
    paperGroupFactorUnitaryTwo.conjStarAlgEquiv ''
        SemidirectGeneratorTransport.generatorSet
          (A := Multiplicative D) (K := H) paperThetaTwoHom =
      reducedCrossedGeneratorSetTwo := by
  ext T
  constructor
  · rintro ⟨S, (⟨a, rfl⟩ | ⟨h, rfl⟩), rfl⟩
    · left
      refine ⟨Multiplicative.toAdd a, ?_⟩
      simpa only [leftRegularRepresentation_apply_clm, ofAdd_toAdd] using
        (paperGroupFactorUnitaryTwo_conj_inl
          (Multiplicative.toAdd a)).symm
    · right
      exact ⟨h, (paperGroupFactorUnitaryTwo_conj_inr h).symm⟩
  · rintro (⟨d, rfl⟩ | ⟨h, rfl⟩)
    · refine ⟨_, Or.inl ⟨Multiplicative.ofAdd d, rfl⟩, ?_⟩
      exact paperGroupFactorUnitaryTwo_conj_inl d
    · refine ⟨_, Or.inr ⟨h, rfl⟩, ?_⟩
      exact paperGroupFactorUnitaryTwo_conj_inr h

theorem paperGroupFactorUnitaryOne_mem_reducedClosure_iff
    (T : GroupL2 PaperGroupOne →L[ℂ] GroupL2 PaperGroupOne) :
    T ∈ vonNeumannClosure
        (Set.range fun x : PaperGroupOne ↦
          (leftRegularRepresentation PaperGroupOne x :
            GroupL2 PaperGroupOne →L[ℂ] GroupL2 PaperGroupOne)) ↔
      paperGroupFactorUnitaryOne.conjStarAlgEquiv T ∈
        vonNeumannClosure reducedCrossedGeneratorSetOne := by
  change T ∈ vonNeumannClosure
      (Set.range fun x : (Multiplicative D ⋊[paperThetaOneHom] H) ↦
        (leftRegularRepresentation (Multiplicative D ⋊[paperThetaOneHom] H) x :
          GroupL2 (Multiplicative D ⋊[paperThetaOneHom] H) →L[ℂ]
            GroupL2 (Multiplicative D ⋊[paperThetaOneHom] H))) ↔ _
  calc
    T ∈ vonNeumannClosure
        (Set.range fun x : (Multiplicative D ⋊[paperThetaOneHom] H) ↦
          (leftRegularRepresentation (Multiplicative D ⋊[paperThetaOneHom] H) x :
            GroupL2 (Multiplicative D ⋊[paperThetaOneHom] H) →L[ℂ]
              GroupL2 (Multiplicative D ⋊[paperThetaOneHom] H))) ↔
        T ∈ vonNeumannClosure
          (SemidirectGeneratorTransport.generatorSet paperThetaOneHom) :=
      Iff.of_eq (congrArg (fun M : VonNeumannAlgebra (GroupL2 PaperGroupOne) ↦
        T ∈ M) (semidirect_vonNeumannClosure_eq_inl_inr
          (A := Multiplicative D) (K := H) paperThetaOneHom))
    _ ↔ paperGroupFactorUnitaryOne.conjStarAlgEquiv T ∈
        vonNeumannClosure reducedCrossedGeneratorSetOne :=
      by
        apply mem_vonNeumannClosure_iff_of_conj_image_eq
        exact paperGroupFactorUnitaryOne_generatorSet_image

theorem paperGroupFactorUnitaryTwo_mem_reducedClosure_iff
    (T : GroupL2 PaperGroupTwo →L[ℂ] GroupL2 PaperGroupTwo) :
    T ∈ vonNeumannClosure
        (Set.range fun x : PaperGroupTwo ↦
          (leftRegularRepresentation PaperGroupTwo x :
            GroupL2 PaperGroupTwo →L[ℂ] GroupL2 PaperGroupTwo)) ↔
      paperGroupFactorUnitaryTwo.conjStarAlgEquiv T ∈
        vonNeumannClosure reducedCrossedGeneratorSetTwo := by
  change T ∈ vonNeumannClosure
      (Set.range fun x : (Multiplicative D ⋊[paperThetaTwoHom] H) ↦
        (leftRegularRepresentation (Multiplicative D ⋊[paperThetaTwoHom] H) x :
          GroupL2 (Multiplicative D ⋊[paperThetaTwoHom] H) →L[ℂ]
            GroupL2 (Multiplicative D ⋊[paperThetaTwoHom] H))) ↔ _
  calc
    T ∈ vonNeumannClosure
        (Set.range fun x : (Multiplicative D ⋊[paperThetaTwoHom] H) ↦
          (leftRegularRepresentation (Multiplicative D ⋊[paperThetaTwoHom] H) x :
            GroupL2 (Multiplicative D ⋊[paperThetaTwoHom] H) →L[ℂ]
              GroupL2 (Multiplicative D ⋊[paperThetaTwoHom] H))) ↔
        T ∈ vonNeumannClosure
          (SemidirectGeneratorTransport.generatorSet paperThetaTwoHom) :=
      Iff.of_eq (congrArg (fun M : VonNeumannAlgebra (GroupL2 PaperGroupTwo) ↦
        T ∈ M) (semidirect_vonNeumannClosure_eq_inl_inr
          (A := Multiplicative D) (K := H) paperThetaTwoHom))
    _ ↔ paperGroupFactorUnitaryTwo.conjStarAlgEquiv T ∈
        vonNeumannClosure reducedCrossedGeneratorSetTwo :=
      by
        apply mem_vonNeumannClosure_iff_of_conj_image_eq
        exact paperGroupFactorUnitaryTwo_generatorSet_image

theorem coordinateComplexCharacter_star (d : D) :
    star (coordinateComplexCharacter d) =
      coordinateComplexCharacter (-d) := by
  ext p
  change starRingEnd ℂ
      (complexCharacter d (characterCoordinatesHomeomorph.symm p)) =
    complexCharacter (-d) (characterCoordinatesHomeomorph.symm p)
  exact DFunLike.congr_fun (PaperFourier.complexCharacter_star d)
    (characterCoordinatesHomeomorph.symm p)

def coordinateCharacterSubalgebra :
    StarSubalgebra ℂ C(PaperFactorIsomorphism.DualCoordinates, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ
    (Set.range (coordinateComplexCharacter : D →
      C(PaperFactorIsomorphism.DualCoordinates, ℂ)))
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range (coordinateComplexCharacter : D →
      C(PaperFactorIsomorphism.DualCoordinates, ℂ))) ≤
        star (Algebra.adjoin ℂ
          (Set.range (coordinateComplexCharacter : D →
            C(PaperFactorIsomorphism.DualCoordinates, ℂ))))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨d, rfl⟩
    exact Algebra.subset_adjoin ⟨-d, (coordinateComplexCharacter_star d).symm⟩

theorem coordinateCharacterSubalgebra_toSubmodule :
    coordinateCharacterSubalgebra.toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (coordinateComplexCharacter : D →
        C(PaperFactorIsomorphism.DualCoordinates, ℂ))) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro z hz
  refine Submonoid.closure_induction (fun _ ↦ id) ⟨0, ?_⟩ ?_ hz
  · ext p
    simp [coordinateComplexCharacter, PaperFourier.complexCharacter]
  · rintro - - - - ⟨d, rfl⟩ ⟨e, rfl⟩
    refine ⟨d + e, ?_⟩
    ext p
    simp [coordinateComplexCharacter, PaperFourier.complexCharacter]

theorem coordinateComplexCharacter_span_closure_eq_top :
    (Submodule.span ℂ (Set.range (coordinateComplexCharacter : D →
      C(PaperFactorIsomorphism.DualCoordinates, ℂ)))).topologicalClosure = ⊤ := by
  have hsep : coordinateCharacterSubalgebra.SeparatesPoints := by
    intro p q hpq
    have hpq' : characterCoordinatesHomeomorph.symm p ≠
        characterCoordinatesHomeomorph.symm q := by
      intro h
      exact hpq (characterCoordinatesHomeomorph.symm.injective h)
    obtain ⟨d, hd⟩ := PaperFourier.complexCharacter_separates hpq'
    refine ⟨_, ⟨coordinateComplexCharacter d,
      Algebra.subset_adjoin ⟨d, rfl⟩, rfl⟩, ?_⟩
    exact hd
  rw [← coordinateCharacterSubalgebra_toSubmodule]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      coordinateCharacterSubalgebra hsep)

def crossedFiberwiseOperatorCLM
    {K : Type*} {E : Type*} [Group K]
    [NormedAddCommGroup E] [NormedSpace ℂ E] :
    (E →L[ℂ] E) →L[ℂ]
      (lp (fun _ : K ↦ E) 2 →L[ℂ] lp (fun _ : K ↦ E) 2) := by
  let F : (E →L[ℂ] E) →ₗ[ℂ]
      (lp (fun _ : K ↦ E) 2 →L[ℂ] lp (fun _ : K ↦ E) 2) :=
    { toFun := crossedFiberwiseOperator
      map_add' := by
        intro S T
        apply ContinuousLinearMap.ext
        intro ξ
        apply lp.ext
        funext k
        rfl
      map_smul' := by
        intro c T
        apply ContinuousLinearMap.ext
        intro ξ
        apply lp.ext
        funext k
        rfl }
  exact F.mkContinuous 1 (by
    intro T
    rw [one_mul]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro ξ
    calc
      ‖crossedFiberwiseOperator T ξ‖ ≤ ‖(‖T‖ : ℂ) • ξ‖ := lp.norm_mono (by norm_num) (by
        intro k
        change ‖T (ξ k)‖ ≤ ‖(‖T‖ : ℂ) • ξ k‖
        simpa only [Complex.coe_smul, norm_smul, norm_norm] using
          T.le_opNorm (ξ k))
      _ = ‖T‖ * ‖ξ‖ := by
        rw [lp.norm_const_smul (by norm_num : (2 : ℝ≥0∞) ≠ 0)]
        simp only [Complex.norm_real, norm_norm])

def continuousCrossedMultiplier
    (X : HaarProbabilityAction H PaperFactorIsomorphism.DualCoordinates) :
    C(PaperFactorIsomorphism.DualCoordinates, ℂ) →L[ℂ]
      (crossedHilbert X →L[ℂ] crossedHilbert X) :=
  (crossedFiberwiseOperatorCLM (K := H)
      (E := crossedBaseHilbert X)).comp
    (((ContinuousLinearMap.mul ℂ ℂ).holderL X.measure ⊤ 2 2).comp
      (ContinuousMap.toLp ⊤ X.measure ℂ))

@[simp] theorem continuousCrossedMultiplier_apply
    (X : HaarProbabilityAction H PaperFactorIsomorphism.DualCoordinates)
    (q : C(PaperFactorIsomorphism.DualCoordinates, ℂ)) :
    continuousCrossedMultiplier X q =
      crossedMultiplier X (ContinuousMap.toLp ⊤ X.measure ℂ q) := by
  rfl

private theorem vonNeumannClosure_coe
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (S : Set (E →L[ℂ] E)) :
    (vonNeumannClosure S : Set (E →L[ℂ] E)) =
      (S ∪ star S).centralizer.centralizer := by
  change (((StarSubalgebra.centralizer ℂ S : Set (E →L[ℂ] E)) ∪
      star (StarSubalgebra.centralizer ℂ S : Set (E →L[ℂ] E))).centralizer) = _
  rw [StarMemClass.star_coe_eq, Set.union_self]
  rfl

theorem subset_vonNeumannClosure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (S : Set (E →L[ℂ] E)) :
    S ⊆ vonNeumannClosure S := by
  intro x hx
  rw [vonNeumannClosure_coe]
  exact Set.subset_centralizer_centralizer (Or.inl hx)

theorem continuousLinearMap_mem_vonNeumannClosure_of_dense_span
    {Q E : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {I : Type*} (F : Q →L[ℂ] (E →L[ℂ] E))
    (v : I → Q)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (S : Set (E →L[ℂ] E))
    (hgen : ∀ i, F (v i) ∈ vonNeumannClosure S)
    (q : Q) : F q ∈ vonNeumannClosure S := by
  let P : Submodule ℂ Q :=
    (vonNeumannClosure S).toStarSubalgebra.toSubalgebra.toSubmodule.comap
      F.toLinearMap
  have hspan : Submodule.span ℂ (Set.range v) ≤ P := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hgen i
  have hclosed : IsClosed (P : Set Q) := by
    change IsClosed (F ⁻¹' (vonNeumannClosure S : Set (E →L[ℂ] E)))
    apply IsClosed.preimage F.continuous
    rw [vonNeumannClosure_coe]
    exact Set.isClosed_centralizer _
  have htop : (⊤ : Submodule ℂ Q) ≤ P := by
    rw [← hv]
    exact (Submodule.span ℂ (Set.range v)).topologicalClosure_minimal
      hspan hclosed
  exact htop Submodule.mem_top

theorem vonNeumannClosure_coe_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (M : VonNeumannAlgebra E) :
    vonNeumannClosure (M : Set (E →L[ℂ] E)) = M := by
  apply SetLike.coe_injective
  rw [vonNeumannClosure_coe, StarMemClass.star_coe_eq, Set.union_self,
    M.centralizer_centralizer]

@[simp] theorem continuousCrossedMultiplier_coordinate_one (d : D) :
    continuousCrossedMultiplier paperHaarActionOne
        (coordinateComplexCharacter d) = crossedKernelMultiplier d := by
  rw [continuousCrossedMultiplier_apply]
  rfl

@[simp] theorem continuousCrossedMultiplier_coordinate_two (d : D) :
    continuousCrossedMultiplier paperHaarActionTwo
        (coordinateComplexCharacter d) =
      crossedMultiplier paperHaarActionTwo (coordinateCharacterCoefficient d) := by
  rw [continuousCrossedMultiplier_apply]
  rfl

theorem vonNeumannClosure_le_of_subset
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {S T : Set (E →L[ℂ] E)}
    (hTS : T ⊆ vonNeumannClosure S) :
    (vonNeumannClosure T : Set (E →L[ℂ] E)) ⊆
      vonNeumannClosure S := by
  intro x hx
  have hx' := mem_vonNeumannClosure_mono hTS hx
  rw [vonNeumannClosure_coe_self] at hx'
  exact hx'

def continuousCrossedGeneratorSetOne :
    Set (CrossedOne →L[ℂ] CrossedOne) :=
  Set.range (continuousCrossedMultiplier paperHaarActionOne) ∪
    Set.range fun h : H ↦
      (crossedGroupUnitary paperHaarActionOne h).toContinuousLinearEquiv.toContinuousLinearMap

def continuousCrossedGeneratorSetTwo :
    Set (CrossedTwo →L[ℂ] CrossedTwo) :=
  Set.range (continuousCrossedMultiplier paperHaarActionTwo) ∪
    Set.range fun h : H ↦
      (crossedGroupUnitary paperHaarActionTwo h).toContinuousLinearEquiv.toContinuousLinearMap

theorem reducedCrossedGeneratorSetOne_subset_continuous :
    reducedCrossedGeneratorSetOne ⊆ continuousCrossedGeneratorSetOne := by
  rintro T (⟨d, rfl⟩ | ⟨h, rfl⟩)
  · refine Or.inl ⟨coordinateComplexCharacter d, ?_⟩
    exact continuousCrossedMultiplier_coordinate_one d
  · exact Or.inr ⟨h, rfl⟩

theorem reducedCrossedGeneratorSetTwo_subset_continuous :
    reducedCrossedGeneratorSetTwo ⊆ continuousCrossedGeneratorSetTwo := by
  rintro T (⟨d, rfl⟩ | ⟨h, rfl⟩)
  · refine Or.inl ⟨coordinateComplexCharacter d, ?_⟩
    exact continuousCrossedMultiplier_coordinate_two d
  · exact Or.inr ⟨h, rfl⟩

theorem continuousCrossedGeneratorSetOne_subset_reducedClosure :
    continuousCrossedGeneratorSetOne ⊆
      vonNeumannClosure reducedCrossedGeneratorSetOne := by
  rintro T (⟨q, rfl⟩ | ⟨h, rfl⟩)
  · apply continuousLinearMap_mem_vonNeumannClosure_of_dense_span
      (continuousCrossedMultiplier paperHaarActionOne)
      coordinateComplexCharacter
      coordinateComplexCharacter_span_closure_eq_top
      reducedCrossedGeneratorSetOne
    intro d
    exact subset_vonNeumannClosure reducedCrossedGeneratorSetOne
      (Or.inl ⟨d, by
        exact (continuousCrossedMultiplier_coordinate_one d).symm⟩)
  · exact subset_vonNeumannClosure reducedCrossedGeneratorSetOne
      (Or.inr ⟨h, rfl⟩)

theorem continuousCrossedGeneratorSetTwo_subset_reducedClosure :
    continuousCrossedGeneratorSetTwo ⊆
      vonNeumannClosure reducedCrossedGeneratorSetTwo := by
  rintro T (⟨q, rfl⟩ | ⟨h, rfl⟩)
  · apply continuousLinearMap_mem_vonNeumannClosure_of_dense_span
      (continuousCrossedMultiplier paperHaarActionTwo)
      coordinateComplexCharacter
      coordinateComplexCharacter_span_closure_eq_top
      reducedCrossedGeneratorSetTwo
    intro d
    exact subset_vonNeumannClosure reducedCrossedGeneratorSetTwo
      (Or.inl ⟨d, by
        exact (continuousCrossedMultiplier_coordinate_two d).symm⟩)
  · exact subset_vonNeumannClosure reducedCrossedGeneratorSetTwo
      (Or.inr ⟨h, rfl⟩)

theorem reducedClosureOne_eq_continuousClosure :
    vonNeumannClosure reducedCrossedGeneratorSetOne =
      vonNeumannClosure continuousCrossedGeneratorSetOne := by
  apply VonNeumannAlgebra.ext
  intro T
  constructor
  · exact mem_vonNeumannClosure_mono
      reducedCrossedGeneratorSetOne_subset_continuous
  · intro hT
    exact vonNeumannClosure_le_of_subset
      continuousCrossedGeneratorSetOne_subset_reducedClosure hT

theorem reducedClosureTwo_eq_continuousClosure :
    vonNeumannClosure reducedCrossedGeneratorSetTwo =
      vonNeumannClosure continuousCrossedGeneratorSetTwo := by
  apply VonNeumannAlgebra.ext
  intro T
  constructor
  · exact mem_vonNeumannClosure_mono
      reducedCrossedGeneratorSetTwo_subset_continuous
  · intro hT
    exact vonNeumannClosure_le_of_subset
      continuousCrossedGeneratorSetTwo_subset_reducedClosure hT

def fiberShearContinuousMap :
    C(PaperFactorIsomorphism.DualCoordinates,
      PaperFactorIsomorphism.DualCoordinates) :=
  ⟨PaperFactorIsomorphism.fiberShear,
    PaperDualTopology.continuous_fiberShear⟩

def shearPullback
    (q : C(PaperFactorIsomorphism.DualCoordinates, ℂ)) :
    C(PaperFactorIsomorphism.DualCoordinates, ℂ) :=
  q.comp fiberShearContinuousMap

theorem paperHaarEquiv_continuousCoefficient_pullback
    (q : C(PaperFactorIsomorphism.DualCoordinates, ℂ)) :
    Lp.compMeasurePreserving
        paperHaarEquiv.toMeasurableEquiv.symm
        (EquivariantHaarEquiv.symm paperHaarEquiv).measure_preserving
        (ContinuousMap.toLp ⊤ paperHaarActionOne.measure ℂ q) =
      ContinuousMap.toLp ⊤ paperHaarActionTwo.measure ℂ
        (shearPullback q) := by
  apply Lp.ext
  let he : MeasurePreserving
      (paperHaarEquiv.toMeasurableEquiv.symm :
        PaperFactorIsomorphism.DualCoordinates →
          PaperFactorIsomorphism.DualCoordinates)
      paperHaarActionTwo.measure paperHaarActionOne.measure :=
    (EquivariantHaarEquiv.symm paperHaarEquiv).measure_preserving
  have hcomp := Lp.coeFn_compMeasurePreserving
    (ContinuousMap.toLp ⊤ paperHaarActionOne.measure ℂ q) he
  have hq := ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℂ)
    paperHaarActionOne.measure q
  have hq' := he.quasiMeasurePreserving.tendsto_ae hq
  have htarget := ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℂ)
    paperHaarActionTwo.measure (shearPullback q)
  filter_upwards [hcomp, hq', htarget] with p hcomp hq' htarget
  rw [hcomp, htarget]
  change (ContinuousMap.toLp ⊤ paperHaarActionOne.measure ℂ q)
      (paperHaarEquiv.toMeasurableEquiv.symm p) =
    (shearPullback q) p
  rw [show (ContinuousMap.toLp ⊤ paperHaarActionOne.measure ℂ q)
      (paperHaarEquiv.toMeasurableEquiv.symm p) =
        q (paperHaarEquiv.toMeasurableEquiv.symm p) from hq']
  rfl

theorem paperHaarEquiv_continuousMultiplier_conj
    (q : C(PaperFactorIsomorphism.DualCoordinates, ℂ)) :
    (crossedHaarHilbertEquiv paperHaarEquiv).conjStarAlgEquiv
        (continuousCrossedMultiplier paperHaarActionOne q) =
      continuousCrossedMultiplier paperHaarActionTwo
        (shearPullback q) := by
  calc
    (crossedHaarHilbertEquiv paperHaarEquiv).conjStarAlgEquiv
          (continuousCrossedMultiplier paperHaarActionOne q) =
        (crossedHaarHilbertEquiv paperHaarEquiv).conjStarAlgEquiv
          (crossedMultiplier paperHaarActionOne
            (ContinuousMap.toLp ⊤ paperHaarActionOne.measure ℂ q)) :=
      congrArg (crossedHaarHilbertEquiv paperHaarEquiv).conjStarAlgEquiv
        (continuousCrossedMultiplier_apply paperHaarActionOne q)
    _ =
        crossedMultiplier paperHaarActionTwo
          (Lp.compMeasurePreserving paperHaarEquiv.toMeasurableEquiv.symm
            (EquivariantHaarEquiv.symm paperHaarEquiv).measure_preserving
            (ContinuousMap.toLp ⊤ paperHaarActionOne.measure ℂ q)) := by
      exact crossedHaarHilbertEquiv_multiplier_conj paperHaarEquiv _
    _ = crossedMultiplier paperHaarActionTwo
          (ContinuousMap.toLp ⊤ paperHaarActionTwo.measure ℂ
            (shearPullback q)) :=
      congrArg (crossedMultiplier paperHaarActionTwo)
        (paperHaarEquiv_continuousCoefficient_pullback q)
    _ = continuousCrossedMultiplier paperHaarActionTwo
          (shearPullback q) :=
      (continuousCrossedMultiplier_apply paperHaarActionTwo _).symm

@[simp] theorem shearPullback_involutive
    (q : C(PaperFactorIsomorphism.DualCoordinates, ℂ)) :
    shearPullback (shearPullback q) = q := by
  ext p
  simp only [shearPullback, ContinuousMap.comp_apply]
  change q (PaperFactorIsomorphism.fiberShear
      (PaperFactorIsomorphism.fiberShear p)) = q p
  rw [PaperFactorIsomorphism.fiberShear_involutive]

theorem paperHaarEquiv_continuousGeneratorSet_image :
    (crossedHaarHilbertEquiv paperHaarEquiv).conjStarAlgEquiv ''
        continuousCrossedGeneratorSetOne =
      continuousCrossedGeneratorSetTwo := by
  ext T
  constructor
  · rintro ⟨S, (⟨q, rfl⟩ | ⟨h, rfl⟩), rfl⟩
    · exact Or.inl ⟨shearPullback q,
        (paperHaarEquiv_continuousMultiplier_conj q).symm⟩
    · exact Or.inr ⟨h,
        (crossedHaarHilbertEquiv_group_conj paperHaarEquiv h).symm⟩
  · rintro (⟨q, rfl⟩ | ⟨h, rfl⟩)
    · refine ⟨continuousCrossedMultiplier paperHaarActionOne
          (shearPullback q), Or.inl ⟨shearPullback q, rfl⟩, ?_⟩
      calc
        (crossedHaarHilbertEquiv paperHaarEquiv).conjStarAlgEquiv
            (continuousCrossedMultiplier paperHaarActionOne
              (shearPullback q)) =
          continuousCrossedMultiplier paperHaarActionTwo
            (shearPullback (shearPullback q)) :=
          paperHaarEquiv_continuousMultiplier_conj (shearPullback q)
        _ = continuousCrossedMultiplier paperHaarActionTwo q :=
          congrArg (continuousCrossedMultiplier paperHaarActionTwo)
            (shearPullback_involutive q)
    · exact ⟨_, Or.inr ⟨h, rfl⟩,
        crossedHaarHilbertEquiv_group_conj paperHaarEquiv h⟩

theorem paperHaarEquiv_mem_continuousClosure_iff
    (T : CrossedOne →L[ℂ] CrossedOne) :
    T ∈ vonNeumannClosure continuousCrossedGeneratorSetOne ↔
      (crossedHaarHilbertEquiv paperHaarEquiv).conjStarAlgEquiv T ∈
        vonNeumannClosure continuousCrossedGeneratorSetTwo := by
  exact mem_vonNeumannClosure_iff_of_conj_image_eq
    (crossedHaarHilbertEquiv paperHaarEquiv)
    continuousCrossedGeneratorSetOne continuousCrossedGeneratorSetTwo
    paperHaarEquiv_continuousGeneratorSet_image T

/- The two paper Fourier models and the fiber shear compose to the concrete
spatial equivalence of regular Hilbert spaces. Paper: §3. -/
def paperSpatialUnitary :
    GroupL2 PaperGroupOne ≃ₗᵢ[ℂ] GroupL2 PaperGroupTwo :=
  paperGroupFactorUnitaryOne |>.trans
    (crossedHaarHilbertEquiv paperHaarEquiv) |>.trans
      paperGroupFactorUnitaryTwo.symm

/- The spatial equivalence carries the first regular group factor onto the
second. Paper: §3. -/
theorem paperSpatialUnitary_maps_group_factor
    (T : GroupL2 PaperGroupOne →L[ℂ] GroupL2 PaperGroupOne) :
    T ∈ vonNeumannClosure
        (Set.range fun x : PaperGroupOne ↦
          (leftRegularRepresentation PaperGroupOne x :
            GroupL2 PaperGroupOne →L[ℂ] GroupL2 PaperGroupOne)) ↔
      paperSpatialUnitary.conjStarAlgEquiv T ∈
        vonNeumannClosure
          (Set.range fun x : PaperGroupTwo ↦
            (leftRegularRepresentation PaperGroupTwo x :
              GroupL2 PaperGroupTwo →L[ℂ] GroupL2 PaperGroupTwo)) := by
  rw [paperGroupFactorUnitaryOne_mem_reducedClosure_iff]
  change paperGroupFactorUnitaryOne.conjStarAlgEquiv T ∈
      vonNeumannClosure reducedCrossedGeneratorSetOne ↔
    paperGroupFactorUnitaryTwo.symm.conjStarAlgEquiv
        ((crossedHaarHilbertEquiv paperHaarEquiv).conjStarAlgEquiv
          (paperGroupFactorUnitaryOne.conjStarAlgEquiv T)) ∈
      vonNeumannClosure
        (Set.range fun x : PaperGroupTwo ↦
          (leftRegularRepresentation PaperGroupTwo x :
            GroupL2 PaperGroupTwo →L[ℂ] GroupL2 PaperGroupTwo))
  let S := paperGroupFactorUnitaryOne.conjStarAlgEquiv T
  let R := (crossedHaarHilbertEquiv paperHaarEquiv).conjStarAlgEquiv S
  calc
    S ∈ vonNeumannClosure reducedCrossedGeneratorSetOne ↔
        S ∈ vonNeumannClosure continuousCrossedGeneratorSetOne := by
      rw [reducedClosureOne_eq_continuousClosure]
    _ ↔ R ∈ vonNeumannClosure continuousCrossedGeneratorSetTwo :=
      paperHaarEquiv_mem_continuousClosure_iff S
    _ ↔ R ∈ vonNeumannClosure reducedCrossedGeneratorSetTwo := by
      rw [reducedClosureTwo_eq_continuousClosure]
    _ ↔ paperGroupFactorUnitaryTwo.symm.conjStarAlgEquiv R ∈
        vonNeumannClosure
          (Set.range fun x : PaperGroupTwo ↦
            (leftRegularRepresentation PaperGroupTwo x :
              GroupL2 PaperGroupTwo →L[ℂ] GroupL2 PaperGroupTwo)) := by
      let X := paperGroupFactorUnitaryTwo.symm.conjStarAlgEquiv R
      have hR : paperGroupFactorUnitaryTwo.conjStarAlgEquiv
          X = R := by
        apply ContinuousLinearMap.ext
        intro v
        change paperGroupFactorUnitaryTwo
            (paperGroupFactorUnitaryTwo.symm
              (R (paperGroupFactorUnitaryTwo
                (paperGroupFactorUnitaryTwo.symm v)))) = R v
        calc
          paperGroupFactorUnitaryTwo
              (paperGroupFactorUnitaryTwo.symm
                (R (paperGroupFactorUnitaryTwo
                  (paperGroupFactorUnitaryTwo.symm v)))) =
            paperGroupFactorUnitaryTwo
              (paperGroupFactorUnitaryTwo.symm (R v)) :=
            congrArg (fun z ↦ paperGroupFactorUnitaryTwo
              (paperGroupFactorUnitaryTwo.symm (R z)))
              (paperGroupFactorUnitaryTwo.apply_symm_apply v)
          _ = R v := paperGroupFactorUnitaryTwo.apply_symm_apply (R v)
      calc
        R ∈ vonNeumannClosure reducedCrossedGeneratorSetTwo ↔
            paperGroupFactorUnitaryTwo.conjStarAlgEquiv X ∈
              vonNeumannClosure reducedCrossedGeneratorSetTwo :=
          Iff.of_eq (congrArg (fun Z : CrossedTwo →L[ℂ] CrossedTwo ↦
            Z ∈ vonNeumannClosure reducedCrossedGeneratorSetTwo) hR.symm)
        _ ↔ X ∈ vonNeumannClosure
            (Set.range fun x : PaperGroupTwo ↦
              (leftRegularRepresentation PaperGroupTwo x :
                GroupL2 PaperGroupTwo →L[ℂ] GroupL2 PaperGroupTwo)) :=
          (paperGroupFactorUnitaryTwo_mem_reducedClosure_iff X).symm

/- The spatial equivalence preserves the canonical group vacuum. Paper: §3. -/
theorem paperSpatialUnitary_maps_vacuum :
    paperSpatialUnitary paperIdentityOne = paperIdentityTwo := by
  change paperGroupFactorUnitaryTwo.symm
      (crossedHaarHilbertEquiv paperHaarEquiv
        (paperGroupFactorUnitaryOne paperIdentityOne)) = paperIdentityTwo
  rw [paperGroupFactorUnitaryOne_vacuum,
    crossedHaarHilbertEquiv_vacuum,
    ← paperGroupFactorUnitaryTwo_vacuum,
    paperGroupFactorUnitaryTwo.symm_apply_apply]

/- The concrete spatial witness for Zhou's pair of group factors. Paper: §3. -/
def paperSpatialWitness : FactorWitness.SpatialWitness
    (paperGammaOneOf PaperKernel.paperActionData)
    (paperGammaTwoOf PaperKernel.paperActionData) where
  unitary := by
    change GroupL2 PaperGroupOne ≃ₗᵢ[ℂ] GroupL2 PaperGroupTwo
    exact paperSpatialUnitary
  maps_group_factor := by
    intro T
    unfold groupVonNeumannAlgebra
    change T ∈ vonNeumannClosure
        (Set.range fun x : PaperGroupOne ↦
          (leftRegularRepresentation PaperGroupOne x :
            GroupL2 PaperGroupOne →L[ℂ] GroupL2 PaperGroupOne)) ↔
      paperSpatialUnitary.conjStarAlgEquiv T ∈
        vonNeumannClosure
          (Set.range fun x : PaperGroupTwo ↦
            (leftRegularRepresentation PaperGroupTwo x :
              GroupL2 PaperGroupTwo →L[ℂ] GroupL2 PaperGroupTwo))
    exact paperSpatialUnitary_maps_group_factor T
  maps_vacuum := by
    change paperSpatialUnitary paperIdentityOne = paperIdentityTwo
    exact paperSpatialUnitary_maps_vacuum

/- The two concrete paper group factors are trace-preservingly isomorphic.
Paper: §3. -/
theorem paperGroupFactors_isomorphic :
    TracialGroupFactorsIsomorphic
      (paperGammaOneOf PaperKernel.paperActionData)
      (paperGammaTwoOf PaperKernel.paperActionData) :=
  FactorWitness.tracialEquiv_of_spatialWitness paperSpatialWitness

end
end PaperFactorClosure
end Connes
