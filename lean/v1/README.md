# Lean certificate for nonnegative trinomial factors

The certificate formalizes [the v1 coefficient proof](../../paper/v1.tex) using Lean 4.19.0 and mathlib. The library entry point is `import Uniform`.

## Build and check

With Elan installed, run these commands from this directory.

```sh
lake exe cache get
lake build
```

To inspect the public theorems and their transitive axiom dependencies, run the following in the same directory.

```sh
lake env lean --stdin <<'EOF'
import Uniform
#check Uniform.trinomial_factor
#print axioms Uniform.trinomial_factor
#print axioms Uniform.Walks.global_bound
#print axioms Uniform.uniform_of_independent_random_variables
EOF
```

## Reading the proof

Start with [Trinomial.lean](Uniform/Trinomial.lean). Its proof applies the contradiction from Sections 1–5 to the global bound from Appendix A. The files directly under [Uniform/](Uniform/) cover the main text and the probability formulation. [Uniform/Walks/](Uniform/Walks/) contains the proof of the global bound.

| Paper | Lean entry point |
| --- | --- |
| Section 1 | [Polynomial.lean](Uniform/Polynomial.lean) defines binary polynomials. [Recurrence.lean](Uniform/Recurrence.lean) gives the coefficient equation. [Normalization.lean](Uniform/Normalization.lean) reduces to a fractional middle coefficient and [Conjugate.lean](Uniform/Conjugate.lean) constructs the conjugate in the annulus. |
| Section 2 | [Columns.lean](Uniform/Columns.lean), [Strips.lean](Uniform/Strips.lean), and [FourRows.lean](Uniform/FourRows.lean) prove the drop, width, and forced-digit statements. |
| Section 3 | [Embedded.lean](Uniform/Embedded.lean) transports the strip entries to the conjugate and bounds the inherited terms. [Differences.lean](Uniform/Differences.lean) computes the four row differences. |
| Section 4 | [Filter.lean](Uniform/Filter.lean) defines the filter and states Proposition 4.1. [Comparison.lean](Uniform/Comparison.lean) applies it to each step of a strip, including the last column. |
| Section 5 | [WidestStrip.lean](Uniform/WidestStrip.lean) proves that the row bounds are incompatible at width five or greater. [Comparison.lean](Uniform/Comparison.lean) applies this to a widest strip. |
| Appendix A.1 | [Polynomial.lean](Uniform/Walks/Polynomial.lean) and [Moments.lean](Uniform/Walks/Moments.lean) prove the Laurent identities and count returns. [Positivity.lean](Uniform/Walks/Positivity.lean), [Continuous.lean](Uniform/Walks/Continuous.lean), and [Differentiable.lean](Uniform/Walks/Differentiable.lean) extend the identities to the column functions. |
| Appendix A.2 | [Branches.lean](Uniform/Walks/Branches.lean) constructs the kernel. [Specialize.lean](Uniform/Walks/Specialize.lean) and [Convolution.lean](Uniform/Walks/Convolution.lean) use its equation and norm bound to prove Proposition 4.1. |
| Appendix A.3 | [Geometric.lean](Uniform/Walks/Geometric.lean) and [Pointwise.lean](Uniform/Walks/Pointwise.lean) compute the energy density. [Weights.lean](Uniform/Walks/Weights.lean) and [Energy.lean](Uniform/Walks/Energy.lean) give the two bounds combined in [KernelNorm.lean](Uniform/Walks/KernelNorm.lean). |
| Probability formulation | [FiniteLaws.lean](Uniform/FiniteLaws.lean) relates convolution on the integers to polynomial multiplication. [Probability.lean](Uniform/Probability.lean) proves the result for probability mass functions and for independent random variables on an arbitrary probability space. |

## Where the derivations differ

- In Section 2 the paper counts the drops in one period. Lean proves their total depth is $r$ in `sum_drop_depths` and excludes $r=1$ in `two_le_r`. For the width estimate, `widest_with_ratio` takes a widest strip of width $W$. Each block of $W$ steps contains a drop of depth at least two. Over $m$ such blocks periodicity gives a total drop of $Wr$, hence $2m \le Wr$. Both arguments give a strip of width at least five. [Columns.lean](Uniform/Columns.lean), [Strips.lean](Uniform/Strips.lean)
- In Section 4, `filtered_bounds` bounds the three rows at every step of a strip. Its result is written before division by the conjugate modulus to the power of the step index. The last step is the one used in the contradiction. [Comparison.lean](Uniform/Comparison.lean)
- In Appendix A.2 the paper groups the coefficients of the absolutely summable kernel by their exponent after substitution. Lean reindexes the absolutely convergent sums against a bounded function in `transfer`, then chooses that function to extract the required coefficient. [Convolution.lean](Uniform/Walks/Convolution.lean)
- In Appendix A.3 the paper computes a derivative sum by differentiating a two-variable identity. Lean sums the energy directly on each geometric branch. The resulting polynomial identity `density_sum_off_switch` holds at every point off the switch, including zero. At the switch both proofs extend the bound for each finite partial sum by continuity. [Geometric.lean](Uniform/Walks/Geometric.lean), [Pointwise.lean](Uniform/Walks/Pointwise.lean), [Energy.lean](Uniform/Walks/Energy.lean)
