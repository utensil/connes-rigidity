/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

New interfaces for the dual and Fourier coordinates in Zhou §3. The
fiber-shear pattern is independently re-expressed here from the public
OpenAI/ten-proofs reference.
-/
import Mathlib

namespace Connes
namespace Fourier

abbrev Character (M : Type*) [AddCommGroup M] := M →+ ZMod 2

def dual (M : Type*) [AddCommGroup M] := Character M

def evaluation {M : Type*} [AddCommGroup M] (χ : dual M) (m : M) : ZMod 2 :=
  (show Character M from χ) m

theorem dual_coordinates_exist (M : Type*) [AddCommGroup M] :
    Nonempty (dual M) := by
  sorry

def FourierTransform (M : Type*) [AddCommGroup M] :
    dual M → M → ZMod 2 := fun χ m => evaluation χ m

end Fourier
end Connes
