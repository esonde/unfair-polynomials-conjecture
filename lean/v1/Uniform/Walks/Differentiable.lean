module

public import Uniform.Walks.Continuous
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! # Simultaneous approximation of a function and its derivative -/

noncomputable section
namespace Uniform.Walks

open Polynomial Set

def onI (f : ℝ → ℝ) (h : ContinuousOn f I) : Functions := ⟨fun u => f u, h.restrict⟩

@[simp] theorem onI_apply (f : ℝ → ℝ) (h : ContinuousOn f I) (u : I) :
    onI f h u = f u := rfl


private theorem primitive (q : ℝ[X]) : ∃ p : ℝ[X], p.derivative = q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨r,hr⟩ := hp
    obtain ⟨s,hs⟩ := hq
    exact ⟨r+s, by rw [derivative_add,hr,hs]⟩
  | monomial n a =>
    exact ⟨monomial (n+1) (a/(n+1)), by rw [derivative_monomial_succ]; congr 1; field_simp⟩

private theorem dense_derivatives (f g : ℝ → ℝ) (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (der : ∀ x ∈ I, HasDerivWithinAt f (g x) I x) :
    (onI f hf,onI g hg) ∈ closure (Set.range (fun p : ℝ[X] => (restrict p,restrict p.derivative))) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have epos : 0 < ε/5 := by linarith
  obtain ⟨q,hq⟩ := exists_polynomial_near_continuousMap (-2) 2 (onI g hg) (ε/5) epos
  obtain ⟨p,hp⟩ := primitive q
  let P := p+C (f (-2)-p.eval (-2))
  have dp : P.derivative = q := by simp [P,hp]
  have val : P.eval (-2) = f (-2) := by simp [P]
  have small (x : ℝ) (hx : x ∈ I) : ‖q.eval x-g x‖ ≤ ε/5 :=
    ((restrict q-onI g hg).norm_coe_le_norm ⟨x,hx⟩).trans hq.le
  have est := norm_image_sub_le_of_norm_deriv_le_segment' (a := (-2:ℝ)) (b := 2)
    (f := fun x => P.eval x-f x) (f' := fun x => q.eval x-g x)
    (fun x hx => by rw [← dp]; exact (P.hasDerivAt x).hasDerivWithinAt.sub (der x hx))
    (fun x hx => small x (Ico_subset_Icc_self hx))
  have bound : ‖restrict P-onI f hf‖ ≤ (ε/5)*4 := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    have h := est x x.property
    rw [val,sub_self,sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith [x.property.2]) epos.le)
  refine ⟨_, ⟨P,rfl⟩, ?_⟩
  rw [dist_comm,Prod.dist_eq, max_lt_iff, dist_eq_norm,dist_eq_norm]
  dsimp only
  rw [dp]
  exact ⟨by linarith, by linarith [show ‖restrict q-onI g hg‖ < ε/5 from hq]⟩

theorem weighted_identity (f g : ℝ → ℝ) (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (der : ∀ x ∈ I, HasDerivWithinAt f (g x) I x) (d : ℤ) :
    (d : ℝ)*b (onI f hf) d = diff (onI g hg) d := by
  have closed : IsClosed {p : Functions × Functions | (d:ℝ)*b p.1 d = diff p.2 d} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  apply (closure_minimal (t := {p : Functions × Functions | (d:ℝ)*b p.1 d = diff p.2 d}) _ closed)
    (dense_derivatives f g hf hg der)
  rintro _ ⟨p,rfl⟩
  exact (b_restrict p d ▸ weighted_coeff p d : (d:ℝ)*b (restrict p) d = _) |>.trans
    (diff_restrict p.derivative d).symm

theorem differentiable_energy (f g : ℝ → ℝ) (hf : ContinuousOn f I) (hg : ContinuousOn g I)
    (der : ∀ x ∈ I, HasDerivWithinAt f (g x) I x) :
    ∑' d : ℤ, ((d : ℝ)*b (onI f hf) d)^2 = L ((4-restrict X^2)*(onI g hg)^2) := by
  simp_rw [weighted_identity f g hf hg der]
  exact continuous_diff_energy _

def negI : C(I,I) :=
  ⟨fun x => ⟨-(x:ℝ), by constructor <;> linarith [x.property.1,x.property.2]⟩,
    continuous_subtype_val.neg.subtype_mk (fun x => by
      change -(x : ℝ) ∈ I
      constructor <;> linarith [x.property.1, x.property.2])⟩

theorem b_reflect (f : Functions) (d : ℤ) : b (f.comp negI) d = (-1:ℝ)^d*b f d := by
  refine dense_restrict.induction_on f ?_ ?_
  · apply isClosed_eq
    · exact (continuous_b d).comp (ContinuousMap.continuous_precomp negI)
    · exact continuous_const.mul (continuous_b d)
  · intro p
    have eq : (restrict p).comp negI = restrict (p.comp (-X)) := by
      ext x
      change p.eval (-(x:ℝ)) = (p.comp (-X)).eval (x:ℝ)
      simp
    rw [eq,b_restrict,b_restrict,reflect_coeff]

end Uniform.Walks
