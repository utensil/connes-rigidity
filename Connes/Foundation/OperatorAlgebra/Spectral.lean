/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

New spectral-measure interface for the relative property-(T) argument in
Zhou §4. This is a paper-shaped placeholder, not an unproved axiom in the
final design: the eventual theorem will replace the field with a formal
construction or an explicitly quantified input.
-/
import Mathlib
import Connes.Core

namespace Connes
namespace Spectral

/-- Spectral-measure input boundary. Paper: §4. -/
structure SpectralInput
    (G : CountableDiscreteGroup.{u}) (N : Subgroup G) where
  relativePropertyT : HasRelativePropertyT G N

/-- The analytic spectral argument is supplied at this boundary. Paper: §4. -/
theorem relative_propertyT_of_spectralInput
    {G : CountableDiscreteGroup.{u}} {N : Subgroup G}
    (input : SpectralInput G N) : HasRelativePropertyT G N :=
  input.relativePropertyT

end Spectral
end Connes
