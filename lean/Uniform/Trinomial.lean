import Uniform.Comparison
import Uniform.Walks.Convolution

/-! # Nonnegative trinomial factors of binary polynomials -/

namespace Uniform

open Polynomial

/-- Theorem 1.1, for arbitrary exponents and cofactor degree. -/
theorem trinomial_factor {A B : ℝ[X]} (hA : A.Monic) (hB : B.Monic)
    (ha : NonnegativeCoeffs A) (hb : NonnegativeCoeffs B)
    (hs : A.support.card = 3) (hc : IsBinary (A*B)) : IsBinary A ∧ IsBinary B :=
  Embedded.theorem_of_global_bound Walks.global_bound A B hA hB ha hb hs hc

end Uniform
