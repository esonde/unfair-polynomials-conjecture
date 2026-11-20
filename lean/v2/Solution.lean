module

import Trinomial

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# The unfair 0–1 polynomial conjecture for trinomial factors

If the product of two monic real polynomials with nonnegative coefficients
is binary and one factor has exactly three nonzero terms, both factors
are binary. The exponents and the degree of the other factor are arbitrary.

If the sum of two independent integer-valued random variables with finite
supports is uniform on its support and either variable has three support
points, both variables are uniform on their supports.
-/

namespace UnfairTrinomial

open Polynomial MeasureTheory ProbabilityTheory

/-- Every coefficient of a binary polynomial is zero or one. -/
def IsBinary (P : ℝ[X]) : Prop :=
  ∀ n, P.coeff n = 0 ∨ P.coeff n = 1

/-- Each coefficient of the polynomial is nonnegative. -/
def NonnegativeCoeffs (P : ℝ[X]) : Prop := ∀ n, 0 ≤ P.coeff n

/-- A binary product of monic nonnegative factors with one trinomial factor
has two binary factors. -/
theorem trinomial_factor {A B : ℝ[X]} (hA : A.Monic) (hB : B.Monic)
    (ha : NonnegativeCoeffs A) (hb : NonnegativeCoeffs B)
    (hs : A.support.card = 3) (hc : IsBinary (A * B)) :
    IsBinary A ∧ IsBinary B := by
  exact Trinomial.trinomial_factor hA hB ha hb hs hc

/-- The probability that the integer-valued random variable takes the value i. -/
def atomMass {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℤ) (i : ℤ) :=
  μ (X ⁻¹' {i})

/-- A mass function is uniform on its support if all its nonzero masses agree. -/
def UniformOnSupport {ι K : Type*} [Zero K] (f : ι → K) : Prop :=
  ∀ i j, f i ≠ 0 → f j ≠ 0 → f i = f j

/-- The sum of two independent integer variables, one supported on exactly three
points, can be uniform on its support only if both variables are uniform on
their respective finite supports. -/
theorem uniform_of_independent_random_variables {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℤ)
    (hX : Measurable X) (hY : Measurable Y) (ind : IndepFun X Y μ)
    (finiteX : (Function.support (atomMass μ X)).Finite)
    (finiteY : (Function.support (atomMass μ Y)).Finite)
    (three : (Function.support (atomMass μ X)).ncard = 3 ∨
      (Function.support (atomMass μ Y)).ncard = 3)
    (flat : UniformOnSupport (atomMass μ (fun ω => X ω + Y ω))) :
    UniformOnSupport (atomMass μ X) ∧ UniformOnSupport (atomMass μ Y) := by
  exact Trinomial.uniform_of_independent_random_variables
    μ X Y hX hY ind finiteX finiteY three flat

end UnfairTrinomial
