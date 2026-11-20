module

public import Trinomial.FiniteLaws
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Set.Card
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-! # The probabilistic formulation of Theorem 1 -/

noncomputable section
namespace Trinomial

open Finset

/-- The distribution of the sum of independent integer draws with laws p and q. -/
def independentSum (p q : PMF ℤ) : PMF ℤ := p.bind (fun i => q.map (i + ·))

private theorem shifted_mass (q : PMF ℤ) (i n : ℤ) : q.map (i + ·) n = q (n-i) := by
  rw [PMF.map_apply, tsum_eq_single (n-i)]
  · simp
  · intro j hj
    exact if_neg (by omega)

private def masses (p : PMF ℤ) (h : p.support.Finite) : AddMonoidAlgebra ℝ ℤ :=
  AddMonoidAlgebra.ofCoeff <|
    Finsupp.onFinset h.toFinset (fun i => (p i).toReal) (fun i hi => h.mem_toFinset.mpr
      (by intro hz; exact hi (by simp [show p i = 0 from hz])))

private theorem mass_support (p : PMF ℤ) (h : p.support.Finite) : (masses p h).coeff.support = h.toFinset := by
  ext i
  simp only [Finsupp.mem_support_iff,masses,AddMonoidAlgebra.coeff_ofCoeff,Finsupp.onFinset_apply,Set.Finite.mem_toFinset,
    PMF.mem_support_iff,ne_eq,ENNReal.toReal_eq_zero_iff,p.apply_ne_top,or_false]

private theorem mass_nonzero (p : PMF ℤ) (h : p.support.Finite) : masses p h ≠ 0 := by
  intro hz
  obtain ⟨i,hi⟩ := p.support_nonempty
  have : i ∈ (masses p h).coeff.support := by rwa [mass_support,Set.Finite.mem_toFinset]
  simp [hz] at this

private theorem convolution_mass (p q : PMF ℤ) (hp : p.support.Finite) (hq : q.support.Finite) (n : ℤ) :
    (masses p hp * masses q hq : AddMonoidAlgebra ℝ ℤ).coeff n = ((independentSum p q) n).toReal := by
  classical
  let a := masses p hp
  let b := masses q hq
  have prod : (a*b : AddMonoidAlgebra ℝ ℤ).coeff n = ∑ i ∈ a.coeff.support, a.coeff i * b.coeff (n-i) := by
    rw [AddMonoidAlgebra.coeff_mul_apply_left]
    simp [Finsupp.sum, sub_eq_neg_add]
  rw [independentSum,PMF.bind_apply]
  simp_rw [shifted_mass]
  rw [tsum_eq_sum (s := hp.toFinset) (fun i hi => by
    rw [(p.apply_eq_zero_iff i).mpr (by simpa using hi),zero_mul])]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (p.apply_ne_top _) (q.apply_ne_top _))]
  rw [show a.coeff.support = hp.toFinset from mass_support p hp] at prod
  simpa only [a,b,masses,AddMonoidAlgebra.coeff_ofCoeff,Finsupp.onFinset_apply,ENNReal.toReal_mul] using prod

private theorem real_flat (p : PMF ℤ) :
    UniformOnSupport (fun n => (p n).toReal) ↔ UniformOnSupport p := by
  have nonzero (n : ℤ) : (p n).toReal ≠ 0 ↔ p n ≠ 0 := by simp [ENNReal.toReal_eq_zero_iff,p.apply_ne_top]
  constructor
  · intro h i j hi hj
    have eq := congrArg ENNReal.ofReal (h i j ((nonzero i).mpr hi) ((nonzero j).mpr hj))
    simpa only [ENNReal.ofReal_toReal (p.apply_ne_top _)] using eq
  · intro h i j hi hj
    exact congrArg ENNReal.toReal (h i j ((nonzero i).mp hi) ((nonzero j).mp hj))

/-- If a sum of independent finite integer laws is uniform on its support and one law
has three support points, both laws are uniform on their own supports. -/
theorem uniform_of_independent_sum (p q : PMF ℤ) (hp : p.support.Finite) (hq : q.support.Finite)
    (three : p.support.ncard = 3 ∨ q.support.ncard = 3)
    (flat : UniformOnSupport (independentSum p q)) : UniformOnSupport p ∧ UniformOnSupport q := by
  let a := masses p hp
  let b := masses q hq
  have prod : UniformOnSupport (a*b : AddMonoidAlgebra ℝ ℤ).coeff := by
    change UniformOnSupport (fun n => (a*b : AddMonoidAlgebra ℝ ℤ).coeff n)
    simpa only [a,b,convolution_mass] using (real_flat _).mpr flat
  have count (r : PMF ℤ) (hr : r.support.Finite) : (masses r hr).coeff.support.card = r.support.ncard := by
    rw [mass_support,Set.ncard_eq_toFinset_card _ hr]
  have nonneg (r : PMF ℤ) (hr : r.support.Finite) (i : ℤ) : 0 ≤ (masses r hr).coeff i := ENNReal.toReal_nonneg
  have both : UniformOnSupport a.coeff ∧ UniformOnSupport b.coeff := by
    rcases three with h|h
    · exact uniform_factors_of_convolution a b (nonneg p hp) (nonneg q hq) (mass_nonzero q hq)
        ((count p hp).trans h) prod
    · exact (uniform_factors_of_convolution b a (nonneg q hq) (nonneg p hp) (mass_nonzero p hp)
        ((count q hq).trans h) (mul_comm a b ▸ prod)).symm
  exact ⟨(real_flat p).mp both.1, (real_flat q).mp both.2⟩

/-- Dividing a nonzero binary polynomial by its value at one gives the uniform
probability law on its support, coefficient by coefficient. -/
theorem binary_uniform_law (P : Polynomial ℝ) (hp : P ≠ 0) (hb : IsBinary P) (n : ℕ) :
    P.coeff n / P.eval 1 =
      (PMF.uniformOfFinset P.support (Finset.nonempty_iff_ne_empty.mpr
        (fun h => hp (Polynomial.support_eq_empty.mp h))) n).toReal := by
  have one (i : ℕ) (hi : i ∈ P.support) : P.coeff i = 1 :=
    (hb i).resolve_left (Polynomial.mem_support_iff.mp hi)
  have mass : P.eval 1 = (P.support.card : ℝ) := by
    rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
    simp only [one_pow,mul_one]
    rw [Finset.sum_congr rfl one]
    simp
  rw [mass,PMF.uniformOfFinset_apply]
  by_cases hi : n ∈ P.support
  · simp [hi,one n hi]
  · have hz : P.coeff n = 0 := by simpa [Polynomial.mem_support_iff] using hi
    simp [hi,hz]

open MeasureTheory ProbabilityTheory

/-- The mass of an integer-valued random variable at a single integer. -/
def atomMass {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℤ) (i : ℤ) :=
  μ (X ⁻¹' {i})

private def law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℤ) (_hX : Measurable X) : PMF ℤ :=
  (μ.map X).toPMF

private theorem law_apply {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℤ) (hX : Measurable X) (n : ℤ) : law μ X hX n = atomMass μ X n :=
  Measure.map_apply hX (measurableSet_singleton n)

/-- The random-variable formulation of the theorem on any probability space. -/
theorem uniform_of_independent_random_variables {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℤ) (hX : Measurable X) (hY : Measurable Y)
    (ind : IndepFun X Y μ)
    (finiteX : (Function.support (atomMass μ X)).Finite) (finiteY : (Function.support (atomMass μ Y)).Finite)
    (three : (Function.support (atomMass μ X)).ncard = 3 ∨ (Function.support (atomMass μ Y)).ncard = 3)
    (flat : UniformOnSupport (atomMass μ (fun ω => X ω + Y ω))) :
    UniformOnSupport (atomMass μ X) ∧ UniformOnSupport (atomMass μ Y) := by
  let p := law μ X hX
  let q := law μ Y hY
  have ep : ⇑p = atomMass μ X := funext (law_apply μ X hX)
  have eq : ⇑q = atomMass μ Y := funext (law_apply μ Y hY)
  have sumMass : ⇑(independentSum p q) = atomMass μ (fun ω => X ω + Y ω) := by
    funext n
    let cells (i : ℤ) := (X ⁻¹' {i}) ∩ (Y ⁻¹' {n-i})
    have union : (⋃ i, cells i) = (fun ω => X ω + Y ω) ⁻¹' {n} := by
      ext ω
      simp only [Set.mem_iUnion,cells,Set.mem_inter_iff,Set.mem_preimage,Set.mem_singleton_iff]
      constructor
      · rintro ⟨i,h,g⟩; omega
      · intro h; exact ⟨X ω,rfl,by omega⟩
    have disjoint : Pairwise (fun i j => Disjoint (cells i) (cells j)) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro ω hi hj
      exact hij ((show X ω = i from hi.1).symm.trans hj.1)
    have measured := measure_iUnion (μ := μ) disjoint (fun i =>
      (hX (measurableSet_singleton i)).inter (hY (measurableSet_singleton (n-i))))
    rw [independentSum,PMF.bind_apply]
    simp_rw [shifted_mass]
    change _ = μ ((fun ω => X ω + Y ω) ⁻¹' {n})
    rw [← union,measured]
    exact tsum_congr (fun i => by
      rw [ep,eq]
      exact (ind.measure_inter_preimage_eq_mul {i} {n-i} (measurableSet_singleton _) (measurableSet_singleton _)).symm)
  have sp : p.support = Function.support (atomMass μ X) := congrArg Function.support ep
  have sq : q.support = Function.support (atomMass μ Y) := congrArg Function.support eq
  have h := uniform_of_independent_sum p q (sp ▸ finiteX) (sq ▸ finiteY) (sp ▸ sq ▸ three) (sumMass ▸ flat)
  exact ep ▸ eq ▸ h

end Trinomial
