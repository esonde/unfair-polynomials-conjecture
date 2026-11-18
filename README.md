# The unfair 0–1 polynomial conjecture for trinomial factors

Let two monic polynomials with nonnegative real coefficients have a product whose coefficients are all zero or one. If one factor has exactly three nonzero terms, then every nonzero coefficient in both factors is one. The three exponents and the degree of the other factor are arbitrary.

AI generated the proof, the manuscript, and the Lean formalization.

- Read the [paper (PDF)](paper/trinomials-coefficients.pdf) or its [LaTeX source](paper/trinomials-coefficients.tex).
- Follow the [Lean proof section by section](lean/README.md), starting with the [polynomial theorem](lean/Uniform/Trinomial.lean). The certificate also proves the [probabilistic formulation](lean/Uniform/Probability.lean).

## Check the Lean proof

With Elan installed, run the following from the repository root. The project pins Lean and mathlib to v4.19.0.

```sh
cd lean
lake exe cache get
lake build
```

## Rebuild the paper

From the repository root, run `latexmk -cd -pdf paper/trinomials-coefficients.tex`. The source includes the figure and bibliography.

The [supplementary calculation](paper/check-walk-energy.py) checks the scalar identities and constants in Appendix A.3 using exact arithmetic. With SymPy installed, run `python3 paper/check-walk-energy.py`.
