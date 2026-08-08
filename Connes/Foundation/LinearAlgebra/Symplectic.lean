/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

New standalone interfaces for the characteristic-two symplectic construction
in Zhou §2. The OpenAI/ten-proofs Connes formalization is a public reading
reference, pinned at commit 94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, and is
not a dependency of this file. Modifications: the paper's local symplectic
API is introduced independently and its difficult facts remain open.
-/
import Mathlib

namespace Connes
namespace Symplectic

abbrev F := ZMod 2
abbrev V := Fin 4 → F

def form (v w : V) : F :=
  v 0 * w 1 + v 1 * w 0 + v 2 * w 3 + v 3 * w 2

def quadraticRefinement (v : V) : F :=
  v 0 * v 1 + v 2 * v 3

def polarization (q : V → F) (v w : V) : F :=
  q (v + w) - q v - q w

theorem refinement_polarizes_to_form :
    ∀ v w : V, polarization quadraticRefinement v w = form v w := by
  sorry

abbrev Sp4 := Matrix.symplecticGroup (Fin 2) F

def cocycle (g : V ≃ₗ[F] V) : V → F :=
  fun v => quadraticRefinement (g v) - quadraticRefinement v

theorem cocycle_is_linear (g : V ≃ₗ[F] V)
    : ∃ ℓ : V →ₗ[F] F, ∀ v, ℓ v = cocycle g v := by
  sorry

theorem cocycle_identity (g h : V ≃ₗ[F] V) :
    cocycle (g.trans h) = fun v => cocycle g (h v) + cocycle h v := by
  sorry

theorem sp4_transitive_on_nonzero :
    ∀ v : V, v ≠ 0 → ∃ g : V ≃ₗ[F] V, g v = fun _ => 1 := by
  sorry

end Symplectic
end Connes
