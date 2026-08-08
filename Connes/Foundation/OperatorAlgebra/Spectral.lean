/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

New spectral-measure interface for the relative property-(T) argument in
Zhou §4. This is a paper-shaped placeholder, not an unproved axiom in the
final design: the eventual theorem will replace the field with a formal
construction or an explicitly quantified input.
-/
import Mathlib

namespace Connes
namespace Spectral

structure SpectralInput (D H : Type*) where
  measureSpace : Prop
  representationFormula : Prop
  covariance : Prop

def detectorBound (D : Type*) : Prop := True

theorem detector_bound_of_spectralInput {D H : Type*}
    (input : SpectralInput D H) : detectorBound D := by
  sorry

end Spectral
end Connes
