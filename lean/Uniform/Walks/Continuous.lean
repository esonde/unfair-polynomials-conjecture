import Uniform.Walks.Positivity
import Uniform.Walks.Moments
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Continuous extension of the walk coefficients -/

noncomputable section
namespace Uniform.Walks

open Polynomial Set
open scoped Topology

abbrev I := Set.Icc (-2 : ℝ) 2
abbrev Functions := C(I,ℝ)
abbrev L2 := lp (fun _ : ℤ => ℝ) 2

def restrict : ℝ[X] →ₐ[ℝ] Functions := Polynomial.toContinuousMapOnAlgHom I

theorem restrict_apply (p : ℝ[X]) (x : I) : restrict p x = p.eval (x : ℝ) := rfl

theorem dense_restrict : DenseRange restrict := by
  intro f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨p,hp⟩ := exists_polynomial_near_continuousMap (-2) 2 f ε hε
  exact ⟨_,⟨p,rfl⟩,by simpa [dist_comm f,dist_eq_norm] using hp⟩

private def vector (a : Laurent) : L2 :=
  ⟨(fun d => a d),(memℓp_zero a.finite_support).of_exponent_ge (zero_le _)⟩

theorem norm_sq (a : L2) : ‖a‖^2 = ∑' d, (a d)^2 := by
  simpa [Real.norm_eq_abs] using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) a

private def vectors (p : ℝ[X]) : L2 × L2 := (vector (walk p), vector (H*walk p))

private theorem vectors_sub (p q : ℝ[X]) : vectors (p-q) = vectors p - vectors q := by
  apply Prod.ext <;> apply Subtype.ext <;> funext d
  · exact congrArg (fun a : Laurent => a d) (map_sub walk p q)
  · change (H*walk (p-q)) d = ((H*walk p)-(H*walk q)) d
    rw [map_sub,mul_sub]

@[simp] theorem moment_C (a : ℝ) : moment (C a) = a := by simp [moment]

private theorem vectors_bound (p : ℝ[X]) : ‖vectors p‖ ≤ 2*‖restrict p‖ := by
  have abs_bound {u : ℝ} (hu : u ∈ I) : |p.eval u| ≤ ‖restrict p‖ :=
    (restrict p).norm_coe_le_norm ⟨u,hu⟩
  have sq_bound {u : ℝ} (hu : u ∈ I) : (p.eval u)^2 ≤ ‖restrict p‖^2 :=
    (sq_le_sq.mpr (by simpa using abs_bound hu))
  have h₀ : moment (p^2) ≤ ‖restrict p‖^2 := by
    rw [← moment_C (‖restrict p‖^2)]
    exact moment_le (fun u hu => by simp [sq_bound hu])
  have h₁ : moment ((4-X^2)*p^2) ≤ 4*‖restrict p‖^2 := by
    rw [← moment_C (4*‖restrict p‖^2)]
    apply moment_le
    intro u hu
    simp only [eval_mul,eval_sub,eval_ofNat,eval_pow,eval_X,eval_C]
    nlinarith [sq_bound hu,mul_nonneg (sq_nonneg u) (sq_nonneg (p.eval u))]
  rw [Prod.norm_def, max_le_iff]
  have hA : ‖(vectors p).1‖^2 = moment (p^2) := (norm_sq _).trans (energy p)
  have hB : ‖(vectors p).2‖^2 = moment ((4-X^2)*p^2) := (norm_sq _).trans (difference_energy p)
  constructor <;> nlinarith [norm_nonneg (restrict p),sq_nonneg ‖restrict p‖]

private theorem vectors_dist (p q : ℝ[X]) :
    dist (vectors p) (vectors q) ≤ 2 * dist (restrict p) (restrict q) := by
  simpa only [dist_eq_norm, vectors_sub, map_sub] using vectors_bound (p-q)

private def onRange (f : Set.range restrict) := vectors f.property.choose

private theorem range_lipschitz : LipschitzWith 2 onRange := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [onRange, f.property.choose_spec, g.property.choose_spec] using
    vectors_dist f.property.choose g.property.choose

def coefficients : Functions → L2 × L2 := dense_restrict.extend onRange

@[fun_prop] theorem continuous_coefficients : Continuous coefficients :=
  (dense_restrict.uniformContinuous_extend range_lipschitz.uniformContinuous).continuous

private theorem coefficients_restrict (p : ℝ[X]) : coefficients (restrict p) = vectors p := by
  let f : Set.range restrict := ⟨restrict p, p, rfl⟩
  change dense_restrict.extend onRange f = _
  rw [dense_restrict.extend_of_ind range_lipschitz.uniformContinuous]
  apply dist_le_zero.mp
  have h := vectors_dist f.property.choose p
  simpa [f.property.choose_spec, f, onRange] using h

def b (f : Functions) (d : ℤ) : ℝ := (coefficients f).1 d
def diff (f : Functions) (d : ℤ) : ℝ := (coefficients f).2 d
def L (f : Functions) : ℝ := b f 0

@[simp] theorem b_restrict (p : ℝ[X]) (d : ℤ) : b (restrict p) d = walk p d := by
  rw [b,coefficients_restrict]; rfl

@[simp] theorem diff_restrict (p : ℝ[X]) (d : ℤ) : diff (restrict p) d = (H*walk p) d := by
  rw [diff,coefficients_restrict]; rfl

@[simp] theorem L_restrict (p : ℝ[X]) : L (restrict p) = moment p := b_restrict p 0

@[fun_prop] theorem continuous_b (d : ℤ) : Continuous (fun f => b f d) :=
  (continuous_apply d).comp (lp.uniformContinuous_coe.continuous.comp continuous_coefficients.fst)

@[fun_prop] theorem continuous_diff (d : ℤ) : Continuous (fun f => diff f d) :=
  (continuous_apply d).comp (lp.uniformContinuous_coe.continuous.comp continuous_coefficients.snd)

@[fun_prop] theorem continuous_L : Continuous L := continuous_b 0

theorem continuous_energy (f : Functions) : ∑' d, (b f d)^2 = L (f^2) := by
  change ∑' d, ((coefficients f).1 d)^2 = _
  rw [← norm_sq]
  refine dense_restrict.induction_on f (isClosed_eq (by fun_prop) (by fun_prop)) (fun p => ?_)
  rw [coefficients_restrict, ← map_pow, L_restrict, norm_sq]
  exact energy p

theorem continuous_diff_energy (f : Functions) :
    ∑' d, (diff f d)^2 = L ((4-restrict X^2)*f^2) := by
  change ∑' d, ((coefficients f).2 d)^2 = _
  rw [← norm_sq]
  refine dense_restrict.induction_on f (isClosed_eq (by fun_prop) (by fun_prop)) (fun p => ?_)
  rw [coefficients_restrict,norm_sq,← map_pow,← map_ofNat restrict,← map_sub,← map_pow,← map_mul,L_restrict]
  exact difference_energy p

theorem continuous_shift (f : Functions) (d : ℤ) :
    b (restrict X*f) d = b f (d-1)+b f (d+1) := by
  refine dense_restrict.induction_on f (isClosed_eq (by fun_prop) (by fun_prop)) (fun p => ?_)
  rw [← map_mul, b_restrict, b_restrict, b_restrict, map_mul, walk_X, shift]

theorem b_add (f g : Functions) (d : ℤ) : b (f+g) d = b f d+b g d := by
  refine dense_restrict.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) (fun p q => ?_) f g
  rw [← map_add, b_restrict, b_restrict, b_restrict, map_add, add_coeff]

theorem b_const_mul (a : ℝ) (f : Functions) (d : ℤ) :
    b (restrict (C a)*f) d = a*b f d := by
  refine dense_restrict.induction_on f (isClosed_eq (by fun_prop) (by fun_prop)) (fun p => ?_)
  rw [← map_mul,b_restrict,b_restrict,map_mul,walk_C,← LaurentPolynomial.single_eq_C,
    AddMonoidAlgebra.single_zero_mul_apply]

theorem L_nonneg (f : Functions) (h : ∀ u, 0 ≤ f u) : 0 ≤ L f := by
  let g : Functions := ⟨fun u => Real.sqrt (f u),Real.continuous_sqrt.comp f.continuous⟩
  have eq : g^2 = f := by ext u; exact Real.sq_sqrt (h u)
  rw [← eq, ← continuous_energy]; exact tsum_nonneg (fun _ => sq_nonneg _)

end Uniform.Walks
