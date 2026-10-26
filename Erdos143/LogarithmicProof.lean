import Erdos143.LogarithmicDoubleSeries
import Erdos143.LogarithmicSelection

noncomputable section
open Complex

namespace Erdos143.Logarithmic

/-- The uniform remainder bound, discharged for the actual Dirichlet Euler factors. -/
theorem remainderBound_proved : RemainderBound := by
  intro N χ u hu0 hu1 s hs
  have h := prime_logarithmic_remainder_summable_and_norm_le hu0 hu1
    (fun p : Nat.Primes => χ p * (p : ℂ) ^ (-s))
    (dirichlet_prime_factor_norm_le_reciprocal χ hs)
  exact h.2

/-- The periodic primitive-selection theorem via the revised logarithmic analytic proof. -/
theorem periodicPrimitiveSelection_logarithmic_proved : PeriodicPrimitiveSelection := by
  letI : Estimate := ⟨remainderBound_proved⟩
  exact periodicPrimitiveSelection_proved

end Erdos143.Logarithmic
