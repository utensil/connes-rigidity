/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Paper-shaped construction for Zhou §2. The declarations are new standalone
scaffolding, informed by the public OpenAI/ten-proofs Connes formalization at
commit 94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6. Modifications: Zhou's
finite-field polynomial-ring construction replaces the reference example;
the retraction remains paper-shaped, while the current identity actions are
packaged as homomorphisms so the semidirect-product API is explicit.
-/
import Mathlib
import Connes.Core
import Connes.Foundation.GroupTheory.SpecialLinear
import Connes.Foundation.GroupTheory.Sp4
import Connes.Foundation.LinearAlgebra.ArithmeticSymplectic
import Connes.Foundation.LinearAlgebra.BooleanPolynomial
import Connes.Foundation.LinearAlgebra.Symplectic
import Connes.Foundation.LinearAlgebra.Semisimple
import Connes.Foundation.GroupTheory.SemidirectICC

namespace Connes
namespace Construction

/-- Characteristic-two scalar field. Paper: §2. -/
abbrev k := ZMod 2
/-- Polynomial coefficient ring. Paper: §2. -/
abbrev R := Polynomial k
/-- Polynomial module for the construction. Paper: §2. -/
abbrev A := Fin 3 → R
/-- Finite symplectic module. Paper: §2. -/
abbrev V := Fin 4 → k
/-- Symmetric-data carrier placeholder. Paper: §2. -/
abbrev C := A × A
/-- Abelian-kernel carrier placeholder. Paper: §2. -/
abbrev D := (A × V) × C
/-- Acting-group carrier. Paper: §2. -/
abbrev H := SpecialLinear.SL3 × Symplectic.Sp4

/-- Countable discrete wrapper for the acting group. Paper: §2. -/
noncomputable def actingGroup : CountableDiscreteGroup where
  Carrier := H
  group := inferInstance
  countable := by infer_instance

/-- Multiplicative view of the additive kernel used by the semidirect product.
Paper: §2. -/
abbrev GammaKernel := Multiplicative D

/-- Countability of the multiplicative kernel. Paper: §2. -/
noncomputable instance : Countable GammaKernel := by
  change Countable D
  infer_instance

/-- Countable discrete wrapper for the kernel. Paper: §2. -/
noncomputable def kernelGroup : CountableDiscreteGroup where
  Carrier := GammaKernel
  group := inferInstance
  countable := by infer_instance

/-- Diagonal symmetric data. Paper: §2. -/
def diagonal (a : A) : C := (a, a)

/-- Retraction boundary for diagonal data. Paper: §2. -/
def delta (c : C) : A := c.1

/-- Retraction check for diagonal data. Paper: §2. -/
theorem delta_diagonal (a : A) : delta (diagonal a) = a := by
  rfl

/-- Quadratic cocycle boundary. Paper: §2. -/
def quadraticCocycle : H → C → k := fun _ _ => 0

/-- Action data for the two paper constructions. Paper: §2.

The two maps share the kernel and acting group but are supplied separately.
This keeps the eventual action formulas at an API boundary instead of making
the semidirect-product layer depend on a placeholder definition. -/
structure ActionData where
  thetaOneAction : H →* MulAut GammaKernel
  thetaTwoAction : H →* MulAut GammaKernel

private noncomputable def identityAction : H →* MulAut GammaKernel where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := by rfl

/-- Current scaffold input. Paper: §2. Replace this value with the two real
actions after the kernel and cocycle APIs are available. -/
noncomputable def placeholderActionData : ActionData where
  thetaOneAction := identityAction
  thetaTwoAction := identityAction

/-- First action homomorphism boundary. Paper: §2. -/
noncomputable abbrev thetaOneAction : H →* MulAut GammaKernel :=
  placeholderActionData.thetaOneAction

/-- Second action homomorphism boundary. Paper: §2. -/
noncomputable abbrev thetaTwoAction : H →* MulAut GammaKernel :=
  placeholderActionData.thetaTwoAction

/-- First action boundary in additive coordinates. Paper: §2. -/
noncomputable def thetaOneOf (actions : ActionData) (h : H) (d : D) : D :=
  (actions.thetaOneAction h (Multiplicative.ofAdd d)).toAdd

/-- Second action boundary in additive coordinates. Paper: §2. -/
noncomputable def thetaTwoOf (actions : ActionData) (h : H) (d : D) : D :=
  (actions.thetaTwoAction h (Multiplicative.ofAdd d)).toAdd

/-- Current scaffold action boundaries. Paper: §2. -/
noncomputable abbrev thetaOne (h : H) (d : D) : D :=
  thetaOneOf placeholderActionData h d

/-- Current scaffold action boundaries. Paper: §2. -/
noncomputable abbrev thetaTwo (h : H) (d : D) : D :=
  thetaTwoOf placeholderActionData h d

/-- First action law. Paper: §2. -/
def thetaOne_is_action : Prop :=
  (∀ d, thetaOne 1 d = d) ∧
    ∀ h₁ h₂ d, thetaOne (h₁ * h₂) d = thetaOne h₁ (thetaOne h₂ d)

/-- Second action law. Paper: §2. -/
def thetaTwo_is_action : Prop :=
  (∀ d, thetaTwo 1 d = d) ∧
    ∀ h₁ h₂ d, thetaTwo (h₁ * h₂) d = thetaTwo h₁ (thetaTwo h₂ d)

theorem thetaOne_is_action_proof : thetaOne_is_action := by
  constructor
  · intro d
    rfl
  · intro h₁ h₂ d
    rfl

theorem thetaTwo_is_action_proof : thetaTwo_is_action := by
  constructor
  · intro d
    rfl
  · intro h₁ h₂ d
    rfl

/-- First semidirect carrier for an action input. Paper: §2. -/
abbrev GammaOneCarrierOf (actions : ActionData) :=
  SemidirectProduct GammaKernel H actions.thetaOneAction

/-- Second semidirect carrier for an action input. Paper: §2. -/
abbrev GammaTwoCarrierOf (actions : ActionData) :=
  SemidirectProduct GammaKernel H actions.thetaTwoAction

/-- First group wrapper for an action input. Paper: §2. -/
noncomputable def gammaOneOf (actions : ActionData) : CountableDiscreteGroup where
  Carrier := GammaOneCarrierOf actions
  group := inferInstance
  countable := by
    exact SemidirectProduct.equivProd.injective.countable

/-- Second group wrapper for an action input. Paper: §2. -/
noncomputable def gammaTwoOf (actions : ActionData) : CountableDiscreteGroup where
  Carrier := GammaTwoCarrierOf actions
  group := inferInstance
  countable := by
    exact SemidirectProduct.equivProd.injective.countable

/-- Current scaffold carriers. Paper: §2. -/
abbrev GammaOneCarrier := GammaOneCarrierOf placeholderActionData

/-- Current scaffold carriers. Paper: §2. -/
abbrev GammaTwoCarrier := GammaTwoCarrierOf placeholderActionData

/-- Current scaffold group boundary. Paper: §2. -/
noncomputable def gammaOne : CountableDiscreteGroup :=
  gammaOneOf placeholderActionData

/-- Current scaffold group boundary. Paper: §2. -/
noncomputable def gammaTwo : CountableDiscreteGroup :=
  gammaTwoOf placeholderActionData

/-- The current placeholder action makes both group wrappers definitionally
equal. Paper: §2. -/
theorem gammaOne_eq_gammaTwo : gammaOne = gammaTwo := by
  rfl

/-- The current placeholder groups have the identity group equivalence. Paper:
§2. -/
theorem gammaOne_groupsIsomorphic_gammaTwo :
    GroupsIsomorphic gammaOne gammaTwo := by
  exact ⟨MulEquiv.refl _⟩

/-- First group countability witness. Paper: §2. -/
theorem gammaOne_countable : Countable (gammaOne : Type) := by
  infer_instance

/-- Second group countability witness. Paper: §2. -/
theorem gammaTwo_countable : Countable (gammaTwo : Type) := by
  infer_instance

namespace PaperKernel

noncomputable section

/-- Countability of tensor products with countable factors. Paper: §2. -/
noncomputable instance tensorCountable
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module k M] [Module k N] [Countable M] [Countable N] :
    Countable (TensorProduct k M N) := by
  change Countable (Quotient (addConGen (TensorProduct.Eqv k M N)).toSetoid)
  infer_instance

/-- Tensor square used by the paper's symmetric kernel. Paper: §2. -/
abbrev TensorAA := TensorProduct k A A

/-- Countability of the tensor square. Paper: §2. -/
noncomputable instance tensorAACountable : Countable TensorAA := by
  infer_instance

/-- Flip on the tensor square. Paper: §2. -/
def flip : TensorAA ≃ₗ[k] TensorAA := TensorProduct.comm k A A

/-- Flip-fixed symmetric tensor module. Paper: §2. -/
def C : Submodule k TensorAA where
  carrier := {x | flip x = x}
  zero_mem' := by simp [flip]
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, hx, hy]
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [map_smul, hx]

/-- Diagonal element of the paper's symmetric tensor module. Paper: §2. -/
def diagonal (a : A) : C :=
  ⟨a ⊗ₜ[k] a, by simp [flip, C]⟩

/-- Matrix-indexed finite symplectic module. Paper: §2. -/
abbrev PaperV := OpenAIPort.ModTwoSpace

/- The sum index records the ordered symplectic basis used by `Sp₄(F₂)`. -/
/-- Dual of the finite symplectic module. Paper: §2. -/
abbrev VStar := PaperV →ₗ[k] k

/-- Countability of the finite dual module. Paper: §2. -/
noncomputable instance vStarCountable : Countable VStar := by
  exact (show Function.Injective (fun f : PaperV →ₗ[k] k => f.toFun) from
    fun f g h => LinearMap.ext fun v => congrFun h v).countable

/-- Coefficientwise product on the polynomial module. Paper: §2. -/
noncomputable def hadamard (p q : R) : R :=
  let fp : ℕ →₀ k := AddMonoidAlgebra.coeffEquiv p.toFinsupp
  let fq : ℕ →₀ k := AddMonoidAlgebra.coeffEquiv q.toFinsupp
  Polynomial.ofFinsupp <| AddMonoidAlgebra.coeffEquiv.symm
    (Finsupp.zipWith (· * ·) (by simp) fp fq)

/-- Coefficient formula for the polynomial module product. Paper: §2. -/
@[simp] theorem coeff_hadamard (p q : R) (n : ℕ) :
    (hadamard p q).coeff n = p.coeff n * q.coeff n := by
  simp [hadamard, Polynomial.toFinsupp_apply]

/-- Additivity of the first coefficientwise product input. Paper: §2. -/
theorem hadamard_add_left (p q r : R) :
    hadamard (p + q) r = hadamard p r + hadamard q r := by
  ext n
  simp only [coeff_hadamard, Polynomial.coeff_add]
  ring

/-- Additivity of the second coefficientwise product input. Paper: §2. -/
theorem hadamard_add_right (p q r : R) :
    hadamard p (q + r) = hadamard p q + hadamard p r := by
  ext n
  simp only [coeff_hadamard, Polynomial.coeff_add]
  ring

/-- Scalar compatibility of the first coefficientwise product input. Paper: §2. -/
theorem hadamard_smul_left (c : k) (p q : R) :
    hadamard (c • p) q = c • hadamard p q := by
  ext n
  simp only [coeff_hadamard, Polynomial.coeff_smul, smul_eq_mul]
  ring

/-- Scalar compatibility of the second coefficientwise product input. Paper: §2. -/
theorem hadamard_smul_right (c : k) (p q : R) :
    hadamard p (c • q) = c • hadamard p q := by
  ext n
  simp only [coeff_hadamard, Polynomial.coeff_smul, smul_eq_mul]
  ring

/-- Squaring for the coefficientwise product over the Boolean field. Paper: §2. -/
theorem hadamard_square (p : R) : hadamard p p = p := by
  ext n
  simp only [coeff_hadamard]
  have h : p.coeff n * p.coeff n = p.coeff n := by
    generalize hc : p.coeff n = c
    fin_cases c <;> decide
  exact h

/-- Coordinatewise coefficientwise product on the polynomial module. Paper: §2. -/
def coordHadamard (a b : A) : A := fun i => hadamard (a i) (b i)

/-- Bilinear map used to construct the paper retraction. Paper: §2. -/
def coordHadamardLinear : A →ₗ[k] A →ₗ[k] A where
  toFun a :=
    { toFun := fun b => coordHadamard a b
      map_add' := by
        intro b c
        funext i
        exact hadamard_add_right _ _ _
      map_smul' := by
        intro c b
        funext i
        exact hadamard_smul_right _ _ _ }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    funext i
    change hadamard ((a + b) i) (c i) =
      hadamard (a i) (c i) + hadamard (b i) (c i)
    exact hadamard_add_left _ _ _
  map_smul' := by
    intro c a
    apply LinearMap.ext
    intro b
    funext i
    change hadamard ((c • a) i) (b i) =
      c • hadamard (a i) (b i)
    exact hadamard_smul_left _ _ _

/-- Linear map on the tensor square underlying the paper retraction. Paper: §2. -/
def deltaTensor : TensorAA →ₗ[k] A := TensorProduct.lift coordHadamardLinear

/-- Equivariant-retraction candidate on the flip-fixed tensor module. Paper: §2. -/
def delta : C →ₗ[k] A := deltaTensor.domRestrict C

/-- The retraction returns the original vector on diagonal tensors. Paper: §2. -/
theorem delta_diagonal (a : A) : delta (diagonal a) = a := by
  funext i
  change hadamard (a i) (a i) = a i
  exact hadamard_square (a i)

/-- First summand of the paper's abelian kernel. Paper: §2. -/
abbrev AVStar := TensorProduct k A VStar

/-- Countability of the tensor-dual summand. Paper: §2. -/
noncomputable instance avStarCountable : Countable AVStar := by
  infer_instance

/-- Binary product presentation of the paper's direct-sum kernel. Paper: §2. -/
abbrev D := AVStar × C

/-- Countability of the paper-shaped kernel. Paper: §2. -/
noncomputable instance dCountable : Countable D := by
  infer_instance

/-- Countability of the multiplicative paper-shaped kernel. Paper: §2. -/
noncomputable instance paperGammaKernelCountable :
    Countable (Multiplicative D) := by
  change Countable D
  infer_instance

/-- Retraction candidate before the paper equivariance check. Paper: §2. -/
structure RetractionCandidate where
  delta : C →ₗ[k] A
  delta_diagonal : ∀ a, delta (diagonal a) = a

/-- Coefficientwise retraction candidate. Paper: §2. -/
def retractionCandidate : RetractionCandidate where
  delta := delta
  delta_diagonal := delta_diagonal

/-- Action pair over the paper-shaped kernel carrier. Paper: §2. -/
structure ActionData where
  thetaOne : H →* MulAut (Multiplicative D)
  thetaTwo : H →* MulAut (Multiplicative D)

/-- Countable discrete wrapper for the paper-shaped kernel. Paper: §2. -/
noncomputable def paperKernelGroup : CountableDiscreteGroup where
  Carrier := Multiplicative D
  group := inferInstance
  countable := by infer_instance

/-- First paper-shaped semidirect group for an action input. Paper: §2. -/
noncomputable def paperGammaOneOf
    (actions : ActionData) : CountableDiscreteGroup where
  Carrier := SemidirectProduct (Multiplicative D) H actions.thetaOne
  group := inferInstance
  countable := by
    exact SemidirectProduct.equivProd.injective.countable

/-- Second paper-shaped semidirect group for an action input. Paper: §2. -/
noncomputable def paperGammaTwoOf
    (actions : ActionData) : CountableDiscreteGroup where
  Carrier := SemidirectProduct (Multiplicative D) H actions.thetaTwo
  group := inferInstance
  countable := by
    exact SemidirectProduct.equivProd.injective.countable

end
end PaperKernel

end Construction
end Connes
