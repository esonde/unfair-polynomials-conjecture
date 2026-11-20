module

public import Uniform.Walks.Pointwise
public import Uniform.Walks.Weights

@[expose] public section

/-! # The global weighted energy of the walk kernel -/

noncomputable section
namespace Uniform.Walks

open Finset Polynomial

private theorem local_cont (R : ℝ) (hR : 0 < R) (s : ℤ) :
    Continuous (localEnergy R s) := by
  unfold localEnergy w
  have hf := branch_cont R hR s
  have hg := dbranch_cont R hR s
  fun_prop

private theorem local_nonneg (R : ℝ) (s : ℤ) {u : ℝ} (hu : u ∈ I) : 0 ≤ localEnergy R s u := by
  have hw : 0 ≤ w u := by
    obtain ⟨h₁,h₂⟩ := hu
    unfold w
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2+u) (by linarith : 0 ≤ 2-u)]
  have hl : 0 < ellAt s := by cases s <;> apply ell_pos
  unfold localEnergy
  positivity

private theorem partial_density (R : ℝ) (hR : 0 < R) (n : ℕ) {u : ℝ} (hu : u ∈ I) :
    ∑ j ∈ range n, (localEnergy R (.ofNat j) u + localEnergy R (.negSucc j) u) ≤
      density (u^2) (R^2) := by
  classical
  let good := (Set.univ : Set ℝ) \ (↑({R,-R} : Finset ℝ) : Set ℝ)
  have dense : Dense good := dense_univ.diff_finset _
  let ok := {v : ℝ | ∑ j ∈ range n, (localEnergy R (.ofNat j) v + localEnergy R (.negSucc j) v)
      ≤ density (v^2) (R^2)}
  have closed : IsClosed ok := by
    apply isClosed_le
    · exact continuous_finset_sum _ (fun j _ => (local_cont R hR _).add (local_cont R hR _))
    · dsimp only [density]; fun_prop
  have sub : good ∩ Set.Ioo (-2) 2 ⊆ ok := by
    intro v hv
    have ne : v ≠ R ∧ v ≠ -R := by simpa [good, not_or] using hv.1.2
    have mem := Set.Ioo_subset_Icc_self hv.2
    exact sum_le_hasSum _ (fun j _ => add_nonneg (local_nonneg R _ mem) (local_nonneg R _ mem))
      (density_sum_off_switch hR (fun he => (sq_eq_sq_iff_eq_or_eq_neg.mp he).elim ne.1 ne.2))
  have inside : Set.Ioo (-2 : ℝ) 2 ⊆ ok :=
    fun v hv => (closure_minimal sub closed) (isOpen_Ioo.closure_inter ⟨dense v,hv⟩)
  exact (closure_minimal inside closed) ((closure_Ioo (by norm_num : (-2:ℝ) ≠ 2)).symm ▸ hu)

private def Lmap : Functions →+ ℝ where
  toFun := L
  map_zero' := by simpa [L] using b_restrict (0 : ℝ[X]) 0
  map_add' f g := b_add f g 0

private theorem L_mono {f g : Functions} (h : ∀ u, f u ≤ g u) : L f ≤ L g := by
  have hp := L_nonneg (g-f) (fun u => sub_nonneg.mpr (h u))
  change 0 ≤ Lmap (g-f) at hp
  rwa [map_sub,sub_nonneg] at hp

private def localMap (R : ℝ) (hR : 0 < R) (s : ℤ) : Functions :=
  onI _ (local_cont R hR s).continuousOn

private theorem column_bound (R : ℝ) (hR : 0 < R) (s : ℤ) (ds : Finset ℤ) :
    ∑ d ∈ ds, ellAt s * (ellAt s^2+9+(d:ℝ)^2) * kernel R hR d s^2 ≤
      L (localMap R hR s) := by
  let f := column R hR s
  let g := onI _ (dbranch_cont R hR s).continuousOn
  let a := ellAt s
  have ha : 0 < a := by cases s <;> apply ell_pos
  have der := fun (u : ℝ) (_ : u ∈ I) => (branch_hasDerivAt R hR s u).hasDerivWithinAt (s := I)
  have sqsum (v : L2) : Summable (fun d => (v d)^2) := by
    simpa [Real.norm_eq_abs] using ((lp.memℓp v).summable (by norm_num : 0 < (2 : ENNReal).toReal))
  have hs := (sqsum (coefficients f).1).sum_le_tsum ds (fun d _ => sq_nonneg _)
  change ∑ d ∈ ds, (b f d)^2 ≤ ∑' d, (b f d)^2 at hs
  rw [continuous_energy] at hs
  have ht := (sqsum (coefficients g).2).sum_le_tsum ds (fun d _ => sq_nonneg _)
  change ∑ d ∈ ds, (diff g d)^2 ≤ ∑' d, (diff g d)^2 at ht
  rw [continuous_diff_energy] at ht
  have diff_eq (d : ℤ) : diff g d = (d:ℝ)*b f d := (weighted_identity _ _ _ _ der d).symm
  simp_rw [diff_eq] at ht
  have ident : localMap R hR s = restrict (C a) *
      (restrict (C (a^2+9))*f^2 + (4-restrict X^2)*g^2) := by
    ext u
    simp [localMap,onI_apply,localEnergy,restrict_apply,f,column,g,a,w,show (4 : Functions) u = 4 from rfl]
  rw [ident, L, b_const_mul,b_add,b_const_mul]
  change _ ≤ a*((a^2+9)*L (f^2)+L ((4-restrict X^2)*g^2))
  apply le_trans _ (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ a^2+9)) ht) ha.le)
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d _
  change a*(a^2+9+(d:ℝ)^2)*b f d^2 ≤ _
  exact le_of_eq (by ring)

/-- Evaluation of the density by the six even return moments. -/
theorem density_moment (x : ℝ) :
    moment (density (X^2) (C x)) = (127*x^3+94*x^2-23*x+374)/4 := by
  let coeffs : ℕ → ℝ
    | 0 => 592*x^3+768*x^2
    | 1 => -232*x^3-528*x^2
    | 2 => 21*x^3+56*x^2+304*x+2304
    | 3 => 7*x^2-216*x-1904
    | 4 => 35*x+584
    | _ => -63
  have mon (c : ℝ) (i : ℕ) : moment (C c*X^(2*i)) = c*(2*i).choose i := by
    have h := b_const_mul c (restrict (X^(2*i))) 0
    rw [← map_mul] at h
    change L (restrict _) = c*L (restrict _) at h
    simpa only [L_restrict,even_moment] using h
  have add (p q : ℝ[X]) : moment (p+q) = moment p + moment q := by simp [moment]
  have expan : density (X^2) (C x) = ∑ i ∈ range 6, C (coeffs i/8)*X^(2*i) := by
    apply Polynomial.funext
    intro z
    norm_num [coeffs,sum_range_succ,density,Polynomial.algebraMap_eq,Polynomial.eval_finset_sum]
    ring
  rw [expan,show moment (∑ i ∈ range 6, C (coeffs i/8)*X^(2*i)) =
      ∑ i ∈ range 6, moment (C (coeffs i/8)*X^(2*i)) by
    induction (range 6 : Finset ℕ) using Finset.induction_on with
    | empty => simp [moment]
    | insert a s ha ih => simp [ha,add,ih]]
  simp only [mon,sum_range_succ,sum_range_zero,sum_empty,zero_add]
  norm_num [coeffs,Nat.choose]
  ring

/-- The weighted energy on every finite rectangle is bounded uniformly. -/
theorem energy_bound (R : ℝ) (hR : 1 ≤ R) (n : ℕ) (ds : Finset ℤ) :
    let k := kernel R (lt_of_lt_of_le zero_lt_one hR)
    ∑ j ∈ range n, ∑ d ∈ ds, weight j d*(k d (.ofNat j)^2+k d (.negSucc j)^2) ≤ 143*R^6 := by
  let hp := lt_of_lt_of_le zero_lt_one hR
  let F (j : ℕ) := localMap R hp (.ofNat j) + localMap R hp (.negSucc j)
  have rows (j : ℕ) : ∑ d ∈ ds, weight j d*(kernel R hp d (.ofNat j)^2 +
      kernel R hp d (.negSucc j)^2) ≤ L (F j) := by
    simp only [mul_add,sum_add_distrib]
    exact (add_le_add (column_bound R hp (.ofNat j) ds) (column_bound R hp (.negSucc j) ds)).trans_eq
      (b_add _ _ 0).symm
  have bound := sum_le_sum (fun j (_ : j ∈ range n) => rows j)
  change _ ≤ ∑ j ∈ range n, Lmap (F j) at bound
  rw [← map_sum] at bound
  apply bound.trans
  have cmp : L (∑ j ∈ range n, F j) ≤ L (restrict (density (X^2) (C (R^2)))) := by
    apply L_mono
    intro u
    simpa [F,ContinuousMap.sum_apply,localMap,onI_apply,restrict_apply,density,Polynomial.algebraMap_eq]
      using partial_density R hp n u.property
  apply cmp.trans
  rw [L_restrict,density_moment]
  have hx : 1 ≤ R^2 := by nlinarith [sq_nonneg (R-1)]
  have hx2 := mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ R^2)
  have hx3 := mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ (R^2)^2)
  nlinarith

end Uniform.Walks
