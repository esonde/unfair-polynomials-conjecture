# The unfair 0–1 polynomial conjecture for trinomial factors

Let two monic polynomials with nonnegative real coefficients have a product whose coefficients are all zero or one. If one factor has exactly three nonzero terms, then every nonzero coefficient in both factors is one. The three exponents and the degree of the other factor are arbitrary.

AI generated the proof, the manuscript, and the Lean formalization.

| Version | Manuscript | Lean proof |
| --- | --- | --- |
| v2 · Fourier series | [PDF](paper/v2.pdf) · [LaTeX](paper/v2.tex) | [Reading guide](lean/v2/README.md) · [Polynomial theorem](lean/v2/Trinomial/Trinomial.lean) · [Probabilistic formulation](lean/v2/Trinomial/Probability.lean) |
| v1 · Polynomial approximation | [PDF](paper/v1.pdf) · [LaTeX](paper/v1.tex) | [Reading guide](lean/v1/README.md) · [Polynomial theorem](lean/v1/Uniform/Trinomial.lean) · [Probabilistic formulation](lean/v1/Uniform/Probability.lean) |

## Check the Lean proof

With Elan installed, run the following from the repository root for v2. For v1, use `cd lean/v1` in the first step. Both projects pin Lean and mathlib to v4.19.0.

```sh
cd lean/v2
lake exe cache get
lake build
```

## Rebuild the paper

From the repository root, run `latexmk -cd -pdf paper/v2.tex` or `latexmk -cd -pdf paper/v1.tex`. Each source includes its figure and bibliography.

The [archived v1 calculation](https://github.com/esonde/unfair-polynomials-conjecture/blob/262b868ef20140c8ec11081fe80280b79d014555/paper/check-walk-energy.py) checks the scalar identities and constants in Appendix A.3 using exact arithmetic. After downloading the script, run `python3 check-walk-energy.py` with SymPy installed.
