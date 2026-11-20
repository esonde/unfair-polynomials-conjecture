module

public import Trinomial.Fourier.Branches
public import Trinomial.Fourier.Geometric

@[expose] public section

/-! # The two-point geometric series used in Lemma 5 -/

noncomputable section
namespace Trinomial.Fourier

def H (x u : ℝ) := (u+x)/(2*(u-x)^2)
def M (h x : ℝ) := (h+x)*(h-x)^2/2

private theorem first_geometric {q : ℝ} (hq : ‖q‖ < 1) :
    HasSum (fun j => ell j*q^j) (geo1 q) := by
  have a := hasSum_geometric_of_norm_lt_one hq
  have b := hasSum_choose_mul_geometric_of_norm_lt_one 1 hq
  have hn : 1-q ≠ 0 := by
    have := lt_of_le_of_lt (le_abs_self q) (show |q| < 1 from hq)
    linarith
  convert b.sub (a.mul_left (1/2)) using 1
  · funext n; simp [ell]; ring
  · dsimp [geo1]; field_simp; ring

theorem two_point {R u v : ℝ} (hp : 0 < R)
    (same : (|u| < R ∧ |v| < R) ∨ (R < |u| ∧ R < |v|)) :
    HasSum (fun j => ell j * (g R (.ofNat j) u*g R (.ofNat j) v +
      g R (.negSucc j) u*g R (.negSucc j) v)) (base R u * base R v * H (R^2) (u*v)) := by
  rcases same with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · have h : |u*v| < R^2 := by rw [abs_mul,sq]; exact mul_lt_mul' hu.le hv (abs_nonneg _) hp
    have hd : R^2-u*v ≠ 0 := by linarith [le_abs_self (u*v)]
    have un : u^2<R^2 := by nlinarith [mul_pos (sub_pos.mpr hu) (add_pos_of_nonneg_of_pos (abs_nonneg u) hp),sq_abs u]
    have vn : v^2<R^2 := by nlinarith [mul_pos (sub_pos.mpr hv) (add_pos_of_nonneg_of_pos (abs_nonneg v) hp),sq_abs v]
    have hq : ‖u*v/R^2‖ < 1 := by rwa [Real.norm_eq_abs,abs_div,abs_of_nonneg (sq_nonneg R),div_lt_one (sq_pos_of_pos hp)]
    convert (first_geometric hq).mul_left (base R u*base R v/R^2) using 1
    · funext j
      simp only [g,cut,height,sub_pos,if_pos un,if_pos vn,if_neg un.asymm,if_neg vn.asymm,
        zero_mul,zero_add,raw,ratioTerm,div_pow,mul_pow,pow_succ R j]
      have pr : (R^2)^j = (R^j)^2 := by rw [← pow_mul,← pow_mul,mul_comm]
      rw [pr]
      have sg : (-1:ℝ)^(j*2) = 1 := by rw [Nat.mul_comm,pow_mul]; norm_num
      field_simp; ring_nf; rw [sg]; ring
    · dsimp [H,geo1]
      rw [show 1-u*v/R^2 = (R^2-u*v)/R^2 by rw [sub_div, div_self (pow_ne_zero _ hp.ne')]]
      field_simp [hp.ne',hd,show u*v-R^2 ≠ 0 by intro e; apply hd; linarith]; ring
  · have h : R^2 < |u*v| := by rw [abs_mul,sq]; exact mul_lt_mul hu hv.le hp (abs_nonneg _)
    have hn : u*v ≠ 0 := by intro eq; simp [eq] at h; linarith [sq_nonneg R]
    have hd : u*v-R^2 ≠ 0 := by intro eq; rw [sub_eq_zero.mp eq,abs_of_nonneg (sq_nonneg _)] at h; exact h.false
    have un : R^2<u^2 := by nlinarith [mul_pos (sub_pos.mpr hu) (add_pos_of_nonneg_of_pos (abs_nonneg u) hp),sq_abs u]
    have vn : R^2<v^2 := by nlinarith [mul_pos (sub_pos.mpr hv) (add_pos_of_nonneg_of_pos (abs_nonneg v) hp),sq_abs v]
    have hq : ‖R^2/(u*v)‖ < 1 := by rwa [Real.norm_eq_abs,abs_div,abs_of_nonneg (sq_nonneg R),div_lt_one (abs_pos.mpr hn)]
    convert (first_geometric hq).mul_left (base R u*base R v/(u*v)) using 1
    · funext j
      simp only [g,cut,height,sub_pos,if_pos un,if_pos vn,if_neg un.asymm,if_neg vn.asymm,
        zero_mul,add_zero,raw,ratioTerm,div_pow,mul_pow,pow_succ u j,pow_succ v j]
      have hu0 := (mul_ne_zero_iff.mp hn).1
      have hv0 := (mul_ne_zero_iff.mp hn).2
      have sg : (-1:ℝ)^(j*2) = 1 := by rw [Nat.mul_comm,pow_mul]; norm_num
      field_simp [hu0,hv0]; ring_nf; rw [sg]; ring
    · dsimp [H,geo1]
      rw [show 1-R^2/(u*v) = (u*v-R^2)/(u*v) by rw [sub_div, div_self hn]]
      have hu0 := (mul_ne_zero_iff.mp hn).1
      have hv0 := (mul_ne_zero_iff.mp hn).2
      field_simp [hn,hd,hu0,hv0] <;> ring

theorem diagonal_moment {R u : ℝ} (hp : 0 < R) (hn : u^2 ≠ R^2) :
    HasSum (fun j => ell j * (g R (.ofNat j) u^2 + g R (.negSucc j) u^2)) (M (u^2) (R^2)) := by
  have ne : |u| ≠ R := by intro eq; apply hn; rw [← sq_abs u,eq]
  have same := lt_or_gt_of_ne ne
  have s := two_point (u := u) (v := u) hp (same.imp (fun h => ⟨h,h⟩) (fun h => ⟨h,h⟩))
  simp only [← sq] at s
  convert s using 1
  unfold M H base
  field_simp [sub_ne_zero.mpr hn] <;> ring

end Trinomial.Fourier
