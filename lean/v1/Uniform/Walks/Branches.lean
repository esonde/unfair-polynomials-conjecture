import Uniform.Walks.Differentiable
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # The two decaying branches of the scalar recurrence (Appendix A.2) -/

noncomputable section
namespace Uniform.Walks

open Set Filter Polynomial
open scoped Topology

def w (u : ℝ) := 4-u^2
def base (R u : ℝ) := (u^2-R^2)^2
def numerator (R : ℝ) : ℝ[X] := (4-X^2)*(X^2-C (R^2))^2

def height (R : ℝ) : ℤ → ℝ → ℝ
  | .ofNat _, u => u^2-R^2
  | .negSucc _, u => R^2-u^2

def ratioTerm (R : ℝ) : ℤ → ℝ → ℝ
  | .ofNat j, u => (-R)^j/u^(j+1)
  | .negSucc j, u => (-u)^j/R^(j+1)

def raw (R : ℝ) (s : ℤ) (u : ℝ) := base R u * ratioTerm R s u

def slopeTerm (R : ℝ) : ℤ → ℝ → ℝ
  | .ofNat j, u => -((j:ℝ)+1)*(-R)^j/u^(j+2)
  | .negSucc j, u => -(j:ℝ)*(-u)^(j-1)/R^(j+1)

def rawD (R : ℝ) (s : ℤ) (u : ℝ) :=
  (4*u*(u^2-R^2))*ratioTerm R s u + base R u*slopeTerm R s u

def cut (h g : ℝ → ℝ) (u : ℝ) := if 0 < h u then g u else 0

def g (R : ℝ) (s : ℤ) := cut (height R s) (raw R s)
def dg (R : ℝ) (s : ℤ) := cut (height R s) (rawD R s)
def branch (R : ℝ) (s : ℤ) (u : ℝ) := w u*g R s u
def dbranch (R : ℝ) (s : ℤ) (u : ℝ) := (-2*u)*g R s u+w u*dg R s u

private theorem cut_deriv {h f : ℝ → ℝ} (hc : Continuous h)
    (hd : ∀ u, 0 ≤ h u → DifferentiableAt ℝ f u)
    (hz : ∀ u, h u = 0 → f u = 0 ∧ deriv f u = 0) (u : ℝ) :
    HasDerivAt (cut h f) (cut h (deriv f) u) u := by
  rcases lt_trichotomy (h u) 0 with hi | eq | hi
  · rw [cut, if_neg hi.asymm]
    apply (hasDerivAt_const u (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [hc.continuousAt.eventually_lt (continuousAt_const) hi] with v hv
    simp [cut,hv.asymm]
  · rw [cut,if_neg (by simp [eq])]
    have ⟨v0,d0⟩ := hz u eq
    have one : HasDerivWithinAt (cut h f) 0 {x | 0 ≤ h x} u := by
      apply (d0 ▸ (hd u eq.ge).hasDerivAt.hasDerivWithinAt : HasDerivWithinAt f 0 {x | 0 ≤ h x} u).congr
      · intro x hx
        rcases (show 0 ≤ h x from hx).eq_or_lt with he | he
        · simp [cut,he.symm,(hz x he.symm).1]
        · simp [cut,he]
      · simp [cut,eq,v0]
    have two : HasDerivWithinAt (cut h f) 0 {x | h x ≤ 0} u := by
      apply (hasDerivWithinAt_const u _ (0:ℝ)).congr
      · intro x hx; exact if_neg (not_lt_of_ge hx)
      · simp [cut,eq]
    have cover : {x | 0 ≤ h x} ∪ {x | h x ≤ 0} = univ := by ext x; simp [le_total]
    exact hasDerivWithinAt_univ.mp (cover ▸ one.union two)
  · rw [cut,if_pos hi]
    apply (hd u hi.le).hasDerivAt.congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt hc.continuousAt hi] with v hv
    simp [cut,hv]

theorem raw_hasDerivAt (R : ℝ) (hR : 0 < R) (s : ℤ) {u : ℝ} (hu : 0 ≤ height R s u) :
    HasDerivAt (raw R s) (rawD R s u) u := by
  have hb : HasDerivAt (base R) (4*u*(u^2-R^2)) u := by
    convert (((hasDerivAt_id u).pow 2).sub_const (R^2)).pow 2 using 1
    simp [base]
    ring
  apply hb.mul
  cases s with
  | ofNat j =>
    have un : u ≠ 0 := by rintro rfl; simp [height] at hu; nlinarith [sq_pos_of_pos hR]
    change HasDerivAt (fun x => (-R)^j/x^(j+1)) _ u
    convert (hasDerivAt_const u ((-R)^j)).div ((hasDerivAt_id u).pow (j+1)) (pow_ne_zero _ un) using 1
    simp only [slopeTerm,Nat.cast_succ,Nat.add_sub_cancel,id_eq,mul_one,zero_mul,zero_sub]
    field_simp [pow_succ, un]
    ring
  | negSucc j =>
    change HasDerivAt (fun x => (-x)^j/R^(j+1)) _ u
    convert (((hasDerivAt_id u).neg.pow j).div_const (R^(j+1))) using 1
    simp [slopeTerm]

private theorem height_eq (R : ℝ) (s : ℤ) {u : ℝ} (hu : height R s u = 0) : u^2-R^2 = 0 := by
  cases s <;> simp [height] at hu <;> linarith

private theorem height_cont (R : ℝ) (s : ℤ) : Continuous (height R s) := by
  cases s <;> unfold height <;> fun_prop

theorem g_hasDerivAt (R : ℝ) (hR : 0 < R) (s : ℤ) (u : ℝ) : HasDerivAt (g R s) (dg R s u) u :=
by
  have he : dg R s u = cut (height R s) (deriv (raw R s)) u := by
    unfold dg cut
    split_ifs with h
    · exact (raw_hasDerivAt R hR s h.le).deriv.symm
    · rfl
  rw [he]
  exact cut_deriv (height_cont ..) (fun x h => (raw_hasDerivAt R hR s h).differentiableAt)
    (fun x h => by
      have eq := height_eq R s h
      rw [(raw_hasDerivAt R hR s h.ge).deriv]
      simp [raw,rawD,base,eq]) u

theorem dg_cont (R : ℝ) (hR : 0 < R) (s : ℤ) : Continuous (dg R s) := by
  unfold dg cut
  apply continuous_if
  · intro u hu
    have eq := height_eq R s ((frontier_lt_subset_eq continuous_const (height_cont R s) hu).symm)
    simp [rawD,base,eq]
  · intro u hu
    have hh : 0 ≤ height R s u := closure_lt_subset_le continuous_const (height_cont R s) hu
    apply ContinuousAt.continuousWithinAt
    cases s with
    | ofNat j =>
      have un : u ≠ 0 := by rintro rfl; simp [height] at hh; nlinarith [sq_pos_of_pos hR]
      unfold rawD; simp only [base,ratioTerm,slopeTerm]; fun_prop (disch := positivity)
    | negSucc j => unfold rawD; simp only [base,ratioTerm,slopeTerm]; fun_prop
  · exact continuousOn_const

theorem branch_hasDerivAt (R : ℝ) (hR : 0 < R) (s : ℤ) (u : ℝ) :
    HasDerivAt (branch R s) (dbranch R s u) u := by
  have hw : HasDerivAt w (-2*u) u := by
    simpa [w] using (hasDerivAt_const u (4:ℝ)).sub ((hasDerivAt_id u).pow 2)
  exact hw.mul (g_hasDerivAt R hR s u)

theorem branch_cont (R : ℝ) (hR : 0 < R) (s : ℤ) : Continuous (branch R s) :=
  continuous_iff_continuousAt.mpr (fun u => (branch_hasDerivAt R hR s u).continuousAt)

theorem dbranch_cont (R : ℝ) (hR : 0 < R) (s : ℤ) : Continuous (dbranch R s) := by
  have hg : Continuous (g R s) := continuous_iff_continuousAt.mpr (fun u => (g_hasDerivAt R hR s u).continuousAt)
  have hd := dg_cont R hR s
  unfold dbranch w
  fun_prop (disch := exact dg_cont R hR s)

def column (R : ℝ) (hR : 0 < R) (s : ℤ) : Functions := onI _ (branch_cont R hR s).continuousOn
def kernel (R : ℝ) (hR : 0 < R) (d s : ℤ) := b (column R hR s) d

theorem scalar (R : ℝ) (hR : 0 < R) (s : ℤ) (u : ℝ) :
    u * branch R s u + R * branch R (s-1) u = if s=0 then w u*base R u else 0 := by
  have main : u*g R s u + R*g R (s-1) u = if s=0 then base R u else 0 := by
    cases s with
    | ofNat j =>
      cases j with
      | zero =>
        change u*g R (.ofNat 0) u + R*g R (.negSucc 0) u = base R u
        rcases lt_trichotomy (u^2) (R^2) with h | eq | h
        · simp [g,cut,height,raw,ratioTerm,sub_pos,h,h.asymm, hR.ne']; field_simp
        · simp [g,cut,height,raw,base,eq]
        · have un : u ≠ 0 := by rintro rfl; norm_num at h; nlinarith [sq_nonneg R]
          simp [g,cut,height,raw,ratioTerm,sub_pos,h,h.asymm,un]; field_simp
      | succ j =>
        rw [if_neg (by change ((j+1 : ℕ) : ℤ) ≠ 0; omega : Int.ofNat (j+1) ≠ 0), show Int.ofNat (j+1)-1 = Int.ofNat j by change ((j+1 : ℕ) : ℤ)-1 = (j : ℤ); omega]
        by_cases h : R^2 < u^2
        · have un : u ≠ 0 := by rintro rfl; norm_num at h; nlinarith [sq_nonneg R]
          simp only [g,cut,height,sub_pos,if_pos h,raw,ratioTerm]
          simp only [pow_succ]
          field_simp; ring
        · simp [g,cut,height,sub_pos,h]
    | negSucc j =>
      change u*g R (.negSucc j) u + R*g R (.negSucc (j+1)) u = 0
      by_cases h : u^2 < R^2
      · simp only [g,cut,height,sub_pos,if_pos h,raw,ratioTerm]
        simp only [pow_succ]
        field_simp; ring
      · simp [g,cut,height,sub_pos,h]
  simp only [branch]
  split_ifs at main ⊢ <;> linear_combination w u * main

theorem kernel_equation (R : ℝ) (hR : 0 < R) (d s : ℤ) :
    kernel R hR (d-1) s + kernel R hR (d+1) s + R*kernel R hR d (s-1) =
      if s=0 then walk (numerator R) d else 0 := by
  have h : restrict X*column R hR s + restrict (C R)*column R hR (s-1) =
      if s=0 then restrict (numerator R) else 0 := by
    ext u
    have he := scalar R hR s u
    split_ifs at he ⊢ <;> simpa [column,onI,restrict_apply,numerator,w,base] using he
  have hf := congrArg (fun f => b f d) h
  simp only [b_add,continuous_shift,b_const_mul] at hf
  unfold kernel
  rw [hf]
  split_ifs
  · apply b_restrict
  · have z := b_restrict (0 : ℝ[X]) d
    simpa using z

end Uniform.Walks
