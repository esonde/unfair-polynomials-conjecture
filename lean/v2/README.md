# The unfair 0–1 polynomial conjecture for trinomial factors

This Lean package proves Theorem 1 of [the second manuscript](../../paper/v2.pdf). If two monic real polynomials have nonnegative coefficients, their product is binary, and one factor has exactly three nonzero terms, then both factors are binary. The entry point is [Trinomial.trinomial_factor](Trinomial/Trinomial.lean). The hypotheses allow arbitrary exponents and arbitrary cofactor degree.

## Build and check

From this directory, with Elan installed, run

```sh
lake exe cache get
lake build
```

The toolchain and mathlib are pinned to v4.19.0. The package has its own Lake configuration and manifest. All project imports start with `Trinomial`. The algebraic modules adapt proofs shared with the first manuscript. The analytic proof uses mathlib's Fourier coefficients on the additive circle and the product of its normalized Haar measures.

To inspect the statements and their transitive axioms, run

```sh
lake env lean --stdin <<'LEAN'
import Trinomial
#check Trinomial.trinomial_factor
#check Trinomial.Fourier.fourier_bound
#print axioms Trinomial.trinomial_factor
#print axioms Trinomial.Fourier.fourier_bound
#print axioms Trinomial.uniform_of_independent_random_variables
LEAN
```

## Read alongside the manuscript

The names below are relative to `Trinomial`.

| Manuscript | Lean result | What to look for |
| --- | --- | --- |
| §1, normalization | [theorem_of_no_fractional_case](Trinomial/Normalization.lean) | Removing powers of X, reversing the factors, and reducing to a fractional middle coefficient with m > 2r. |
| Lemma 2, four forced rows | [FractionalCase.four_forced_rows](Trinomial/FourRows.lean) | The binary word at a drop, absence of adjacent ones, a globally widest strip of width at least five, and the four product digits through the endpoint. The [spacing proof](Trinomial/Strips.lean) counts drops in one period. |
| §2, choice of conjugate | [FractionalCase.conjugate_annulus](Trinomial/Conjugate.lean) | The algebraic norm supplies a conjugate outside the unit circle. The diameter argument supplies the upper bound of two. |
| Lemma 3, column differences | [Embedded.column_differences](Trinomial/Differences.lean) | A value of type `Four` stores the coefficients modulo y⁴. Its `step` multiplies by 1+y. The [drop-depth table](Trinomial/Embedded.lean) determines the inherited coefficients at depths two, three, and at least four. |
| Proposition 4, Fourier bound | [Fourier.fourier_bound](Trinomial/Fourier/Torus.lean) | For complex λ with 1 ≤ ‖λ‖ ≤ 2, the zero-extended quotient is continuous, and the sum of the norms of its two-variable Fourier coefficients is strictly below 25‖λ‖³. The [convolution argument](Trinomial/Fourier/Convolution.lean) applies this proposition to the cofactor differences. |
| Lemma 5, column moments | [Fourier.column_moments](Trinomial/Fourier/ColumnMoments.lean) | The three identities hold off the switch, including at b = 0. The two integer columns j and −j−1 are paired in each `HasSum` statement. |
| §4, exclusion of a widest strip | [Embedded.theorem_of_global_bound](Trinomial/Comparison.lean) | The three filtered rows include the boundary word below the old bottom. Their bounds give the [final contradiction](Trinomial/WidestStrip.lean). |
| Probabilistic formulation | [uniform_of_independent_random_variables](Trinomial/Probability.lean) | On an arbitrary probability space, either independent integer-valued variable may be the one with three support points. |

## Inside the Fourier proof

1. The [branch formulas](Trinomial/Fourier/Branches.lean) give the two geometric profiles and their derivatives, including the derivative of the zero extension at a switch. The [two-point sum](Trinomial/Fourier/TwoPoint.lean) gives the manuscript's rational function H. For the other two moments, Lean sums the differentiated geometric terms using the first three weighted powers of j+½. This evaluates the same derivatives as the manuscript's generating-function calculation.
2. On the circle of period 2π, [the angular calculation](Trinomial/Fourier/Angular.lean) applies Parseval to each profile and its angular derivative. Translation by π identifies the allowed frequencies. In original row n and column s, the angular mode is 2n+s−5.
3. [Integration by parts](Trinomial/Fourier/IntegrationByParts.lean) integrates the derivative of ℓωω′g² over a period. The three column moments give an integrable bound for the signed sums. The switching angles form a finite set of Haar measure zero. The [angular average](Trinomial/Fourier/Energy.lean) then gives (211x³ + 38x² − 107x + 542)/4, with x = ‖λ‖².
4. The [reciprocal weights](Trinomial/Fourier/Weights.lean) contribute at most 11π/10. [Weighted Cauchy–Schwarz](Trinomial/Fourier/KernelNorm.lean) combines this with the energy estimate 171‖λ‖⁶ and proves absolute summability.
5. Lean constructs the [absolutely convergent torus series](Trinomial/Fourier/Series.lean) from those coefficients. Its coefficient recurrence gives KF = P. Continuity identifies the sum with the zero-extended quotient even at singular points. The resulting theorem `Fourier.quotient_coefficient` identifies the original product-Haar Fourier coefficient, including its phase for complex λ. This establishes the coefficient identification in the reverse order from the manuscript.
