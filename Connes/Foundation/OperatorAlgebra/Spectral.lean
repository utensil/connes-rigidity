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

/-- Spectral-measure input boundary. Paper: §4. -/
structure SpectralInput (D H : Type*) where
  measureSpace : Prop
  representationFormula : Prop
  covariance : Prop

/-- Detector-bound predicate boundary. Paper: §4. -/
def detectorBound (D : Type*) : Prop := True

/-- Spectral-input detector transfer. Paper: §4. -/
theorem detector_bound_of_spectralInput {D H : Type*}
    (input : SpectralInput D H) : detectorBound D := by
  trivial

end Spectral
end Connes
