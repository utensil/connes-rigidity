/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Proof transfer from OpenAI/ten-proofs archive commit 66af838,
ConnesRigidity/CocycleExtension.lean:25-290. The source is public
Apache-2.0 material and is used here as an isolated generic extension layer;
the Zhou construction remains a separate interface.
-/
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

namespace Connes
namespace OpenAIPort

universe u v

/-- Normalized additive two-cocycle data. Paper: §6. -/
structure NormalizedAddCocycle (G : Type u) (A : Type v)
    [Group G] [AddCommGroup A] [DistribMulAction G A] where
  toFun : G → G → A
  cocycle : ∀ g h k, toFun (g * h) k + toFun g h =
    g • toFun h k + toFun g (h * k)
  one_left : ∀ g, toFun 1 g = 0
  one_right : ∀ g, toFun g 1 = 0

namespace NormalizedAddCocycle

variable {G : Type u} {A : Type v}
variable [Group G] [AddCommGroup A] [DistribMulAction G A]

instance : CoeFun (NormalizedAddCocycle G A) (fun _ ↦ G → G → A) :=
  ⟨NormalizedAddCocycle.toFun⟩

/-- Equality of cocycles is pointwise equality. Paper: §6. -/
@[ext] theorem ext {c d : NormalizedAddCocycle G A} (h : ∀ g k, c g k = d g k) : c = d := by
  cases c
  cases d
  congr
  funext g k
  exact h g k

/-- The zero normalized cocycle. Paper: §6. -/
def zero : NormalizedAddCocycle G A where
  toFun := fun _ _ ↦ 0
  cocycle := by simp
  one_left := by simp
  one_right := by simp

/-- Evaluation of the zero cocycle. Paper: §6. -/
@[simp] theorem zero_apply (g h : G) : (zero : NormalizedAddCocycle G A) g h = 0 := rfl

/-- The normalized coboundary attached to a one-cochain. Paper: §6. -/
def coboundary (r : G → A) : NormalizedAddCocycle G A where
  toFun := fun g h ↦
    g • (r h - r 1) - (r (g * h) - r 1) + (r g - r 1)
  cocycle := by
    intro g h k
    simp only [smul_sub, smul_add, mul_smul, mul_assoc]
    abel
  one_left := by simp
  one_right := by simp

/-- Evaluation of a normalized coboundary. Paper: §6. -/
@[simp] theorem coboundary_apply (r : G → A) (g h : G) :
    coboundary r g h =
      g • (r h - r 1) - (r (g * h) - r 1) + (r g - r 1) := rfl

/-- Coboundary predicate in normalized coordinates. Paper: §6. -/
def IsCoboundary (c : NormalizedAddCocycle G A) : Prop :=
  ∃ r : G → A, r 1 = 0 ∧ ∀ g h, g • r h - r (g * h) + r g = c g h

/-- Comparison with Mathlib's group-cohomology coboundary predicate. Paper: §6. -/
theorem isCoboundary_iff_groupCohomology (c : NormalizedAddCocycle G A) :
    c.IsCoboundary ↔
      groupCohomology.IsCoboundary₂ (fun gh : G × G ↦ c gh.1 gh.2) := by
  constructor
  · rintro ⟨r, -, hr⟩
    exact ⟨r, hr⟩
  · rintro ⟨r, hr⟩
    have hr1 : r 1 = 0 := by
      simpa [c.one_left] using hr 1 1
    exact ⟨r, hr1, hr⟩

end NormalizedAddCocycle

/-- Carrier of the extension defined by a normalized cocycle. Paper: §6. -/
structure CocycleExtension {G : Type u} {A : Type v}
    [Group G] [AddCommGroup A] [DistribMulAction G A]
    (_c : NormalizedAddCocycle G A) where
  fst : A
  snd : G

namespace CocycleExtension

variable {G : Type u} {A : Type v}
variable [Group G] [AddCommGroup A] [DistribMulAction G A]
variable (c : NormalizedAddCocycle G A)

/-- Equality of extension elements by coordinates. Paper: §6. -/
@[ext] theorem ext {x y : CocycleExtension c}
    (hfst : x.fst = y.fst) (hsnd : x.snd = y.snd) : x = y := by
  cases x
  cases y
  simp_all

instance [Countable A] [Countable G] : Countable (CocycleExtension c) :=
  (show Function.Injective (fun x : CocycleExtension c ↦ (x.fst, x.snd)) by
    intro x y h
    exact CocycleExtension.ext c (congr_arg Prod.fst h) (congr_arg Prod.snd h)).countable

instance : One (CocycleExtension c) := ⟨⟨0, 1⟩⟩

instance : Mul (CocycleExtension c) where
  mul x y := ⟨x.fst + x.snd • y.fst + c x.snd y.snd, x.snd * y.snd⟩

instance : Inv (CocycleExtension c) where
  inv x :=
    ⟨-(x.snd⁻¹ • (x.fst + c x.snd x.snd⁻¹)), x.snd⁻¹⟩

/-- First coordinate of the extension identity. Paper: §6. -/
@[simp] theorem one_fst : (1 : CocycleExtension c).fst = 0 := rfl

/-- Second coordinate of the extension identity. Paper: §6. -/
@[simp] theorem one_snd : (1 : CocycleExtension c).snd = 1 := rfl

/-- First coordinate of extension multiplication. Paper: §6. -/
@[simp] theorem mul_fst (x y : CocycleExtension c) :
    (x * y).fst = x.fst + x.snd • y.fst + c x.snd y.snd := rfl

/-- Second coordinate of extension multiplication. Paper: §6. -/
@[simp] theorem mul_snd (x y : CocycleExtension c) :
    (x * y).snd = x.snd * y.snd := rfl

/-- First coordinate of extension inversion. Paper: §6. -/
@[simp] theorem inv_fst (x : CocycleExtension c) :
    (x⁻¹).fst = -(x.snd⁻¹ • (x.fst + c x.snd x.snd⁻¹)) := rfl

/-- Second coordinate of extension inversion. Paper: §6. -/
@[simp] theorem inv_snd (x : CocycleExtension c) :
    (x⁻¹).snd = x.snd⁻¹ := rfl

private theorem mul_assoc' (x y z : CocycleExtension c) :
    (x * y) * z = x * (y * z) := by
  apply CocycleExtension.ext
  · change
      (x.fst + x.snd • y.fst + c x.snd y.snd) + (x.snd * y.snd) • z.fst +
          c (x.snd * y.snd) z.snd =
        x.fst + x.snd • (y.fst + y.snd • z.fst + c y.snd z.snd) +
          c x.snd (y.snd * z.snd)
    calc
      _ = x.fst + x.snd • y.fst + x.snd • (y.snd • z.fst) +
          (c (x.snd * y.snd) z.snd + c x.snd y.snd) := by
            rw [mul_smul]
            abel
      _ = x.fst + x.snd • y.fst + x.snd • (y.snd • z.fst) +
          (x.snd • c y.snd z.snd + c x.snd (y.snd * z.snd)) := by
            rw [c.cocycle]
      _ = _ := by
            rw [smul_add, smul_add]
            abel
  · exact mul_assoc _ _ _

private theorem one_mul' (x : CocycleExtension c) : 1 * x = x := by
  apply CocycleExtension.ext
  · simp [c.one_left]
  · simp

private theorem inv_mul_cancel' (x : CocycleExtension c) : x⁻¹ * x = 1 := by
  apply CocycleExtension.ext
  · change
      -(x.snd⁻¹ • (x.fst + c x.snd x.snd⁻¹)) +
          x.snd⁻¹ • x.fst + c x.snd⁻¹ x.snd = 0
    have hc := c.cocycle x.snd⁻¹ x.snd x.snd⁻¹
    simp only [inv_mul_cancel, mul_inv_cancel, c.one_left, c.one_right, add_zero] at hc
    rw [smul_add, neg_add_rev]
    abel_nf at hc ⊢
    simpa [sub_eq_add_neg] using sub_eq_zero.mpr hc
  · simp

instance : Group (CocycleExtension c) :=
  Group.ofLeftAxioms (mul_assoc' c) (one_mul' c) (inv_mul_cancel' c)

/-- Inclusion of the additive kernel. Paper: §6. -/
def inl : Multiplicative A →* CocycleExtension c where
  toFun a := ⟨a.toAdd, 1⟩
  map_one' := rfl
  map_mul' a b := by
    apply CocycleExtension.ext
    · simp [c.one_right]
    · simp

/-- Coordinate form of the kernel inclusion. Paper: §6. -/
@[simp] theorem inl_apply (a : Multiplicative A) :
    inl c a = ⟨a.toAdd, 1⟩ := rfl

/-- Projection from the extension to its quotient group. Paper: §6. -/
def rightHom : CocycleExtension c →* G where
  toFun := CocycleExtension.snd
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Coordinate form of the quotient projection. Paper: §6. -/
@[simp] theorem rightHom_apply (x : CocycleExtension c) : rightHom c x = x.snd := rfl

/-- The quotient projection is surjective. Paper: §6. -/
theorem rightHom_surjective : Function.Surjective (rightHom c) :=
  fun g ↦ ⟨⟨0, g⟩, rfl⟩

/-- The kernel inclusion is injective. Paper: §6. -/
theorem inl_injective : Function.Injective (inl c) := by
  intro a b h
  exact Multiplicative.ext (congr_arg CocycleExtension.fst h)

/-- The kernel inclusion has exactly the quotient kernel as its range. Paper: §6. -/
theorem range_inl_eq_ker_rightHom :
    MonoidHom.range (inl c) = MonoidHom.ker (rightHom c) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro hx
    have hx' : x.snd = 1 := by simpa using hx
    refine ⟨Multiplicative.ofAdd x.fst, ?_⟩
    apply CocycleExtension.ext
    · rfl
    · simpa using hx'.symm

/-- A splitting of the quotient projection. Paper: §6. -/
def Splitting : Type max u v :=
  {s : G →* CocycleExtension c // (rightHom c).comp s = MonoidHom.id G}

/-- A splitting preserves the quotient coordinate. Paper: §6. -/
theorem splitting_apply_snd (s : Splitting c) (g : G) : (s.1 g).snd = g := by
  have h := DFunLike.congr_fun s.2 g
  exact h

/-- Construct a splitting from a coboundary witness. Paper: §6. -/
noncomputable def splittingOfIsCoboundary (hc : c.IsCoboundary) : Splitting c := by
  let r := Classical.choose hc
  have hr1 : r 1 = 0 := (Classical.choose_spec hc).1
  have hr : ∀ g h, g • r h - r (g * h) + r g = c g h :=
    (Classical.choose_spec hc).2
  let s : G →* CocycleExtension c :=
    { toFun := fun g ↦ ⟨-r g, g⟩
      map_one' := by
        apply CocycleExtension.ext
        · simp [hr1]
        · simp
      map_mul' := by
        intro g h
        apply CocycleExtension.ext
        · simp only [mul_fst, smul_neg]
          rw [← hr g h]
          abel
        · simp }
  exact ⟨s, by ext g; rfl⟩

/-- A splitting produces a coboundary witness. Paper: §6. -/
theorem isCoboundaryOfSplitting (s : Splitting c) : c.IsCoboundary := by
  let r : G → A := fun g ↦ -(s.1 g).fst
  refine ⟨r, ?_, ?_⟩
  · have hs1 := s.1.map_one
    exact neg_eq_zero.mpr (congr_arg CocycleExtension.fst hs1)
  · intro g h
    have hs := s.1.map_mul g h
    have hsg := splitting_apply_snd c s g
    have hsh := splitting_apply_snd c s h
    have hfst := congr_arg CocycleExtension.fst hs
    simp only [mul_fst] at hfst
    change g • (-(s.1 h).fst) - (-(s.1 (g * h)).fst) + (-(s.1 g).fst) = c g h
    rw [smul_neg]
    rw [hsg, hsh] at hfst
    rw [sub_neg_eq_add]
    rw [hfst]
    abel

/-- A quotient splitting exists exactly for a coboundary. Paper: §6. -/
theorem splitting_nonempty_iff_isCoboundary :
    Nonempty (Splitting c) ↔ c.IsCoboundary :=
  ⟨fun ⟨s⟩ ↦ isCoboundaryOfSplitting c s,
    fun hc ↦ ⟨splittingOfIsCoboundary c hc⟩⟩

/-- A non-coboundary extension has no quotient splitting. Paper: §6. -/
theorem noSplitting_of_not_isCoboundary (hc : ¬c.IsCoboundary) :
    IsEmpty (Splitting c) :=
  ⟨fun s ↦ hc (isCoboundaryOfSplitting c s)⟩

end CocycleExtension

end OpenAIPort
end Connes
