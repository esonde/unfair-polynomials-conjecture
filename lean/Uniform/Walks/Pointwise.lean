import Uniform.Walks.Branches
import Uniform.Walks.Geometric

/-! # Pointwise energy of the two geometric branches (Appendix A.3) -/

noncomputable section
namespace Uniform.Walks

def ellAt : ℤ → ℝ
  | .ofNat j => ell j
  | .negSucc j => ell j

def localEnergy (R : ℝ) (s : ℤ) (u : ℝ) : ℝ :=
  ellAt s*((ellAt s^2+9)*branch R s u^2+w u*dbranch R s u^2)

set_option maxHeartbeats 3000000 in
private theorem outer_density {u x : ℝ} (hu : u ≠ 0) (hx : u^2-x ≠ 0) :
    let h := u^2
    let q := x/h
    let v := (h-x)^4/h
    let A := -2*u+w u*(4*u/(h-x)-1/(2*u))
    let B := -w u/u
    v*(w u^2*(geo3 q+9*geo1 q)+w u*(A^2*geo1 q+2*A*B*geo2 q+B^2*geo3 q)) = density h x := by
  have hq : 1-x/u^2 = (u^2-x)/u^2 := by field_simp
  dsimp only
  simp only [geo1,geo2,geo3,hq,density,w,show algebraMap ℝ ℝ = RingHom.id ℝ from rfl, RingHom.id_apply, div_pow]
  field_simp [hu,hx]; ring

set_option maxHeartbeats 3000000 in
private theorem inner_density {u x : ℝ} (hu : u ≠ 0) (hx : x ≠ 0) (hd : u^2-x ≠ 0) :
    let h := u^2
    let q := h/x
    let v := (h-x)^4/x
    let A := -2*u+w u*(4*u/(h-x)-1/(2*u))
    let B := w u/u
    v*(w u^2*(geo3 q+9*geo1 q)+w u*(A^2*geo1 q+2*A*B*geo2 q+B^2*geo3 q)) = density h x := by
  have hq : 1-u^2/x = (x-u^2)/x := by field_simp
  dsimp only
  simp only [geo1,geo2,geo3,hq,density,w,show algebraMap ℝ ℝ = RingHom.id ℝ from rfl, RingHom.id_apply, div_pow]
  have hxd : x-u^2 ≠ 0 := sub_ne_zero.mpr ((sub_ne_zero.mp hd).symm)
  field_simp [hu,hx,hd,hxd]; ring

private theorem outer_square {R u : ℝ} (j : ℕ) (hu : u ≠ 0) :
    raw R (.ofNat j) u ^2 = (u^2-R^2)^4/u^2*(R^2/u^2)^j := by
  have commutePow (b : ℝ) : (b^j)^2 = (b^2)^j := by rw [← pow_mul, mul_comm j 2, pow_mul]
  simp only [raw,base,ratioTerm,pow_succ u j,mul_pow,div_pow,commutePow,neg_sq]
  field_simp; ring

private theorem inner_square {R u : ℝ} (j : ℕ) (hR : 0 < R) :
    raw R (.negSucc j) u ^2 = (u^2-R^2)^4/R^2*(u^2/R^2)^j := by
  have commutePow (b : ℝ) : (b^j)^2 = (b^2)^j := by rw [← pow_mul, mul_comm j 2, pow_mul]
  simp only [raw,base,ratioTerm,pow_succ R j,mul_pow,div_pow,commutePow,neg_sq]
  field_simp; ring

private theorem outer_log {R u : ℝ} (j : ℕ) (hu : u ≠ 0) (hd : u^2-R^2 ≠ 0) :
    rawD R (.ofNat j) u = raw R (.ofNat j) u*(4*u/(u^2-R^2)-(j+1)/u) := by
  simp only [raw,rawD,base,ratioTerm,slopeTerm]
  rw [pow_succ u (j+1)]
  field_simp [hu,hd]; ring

private theorem inner_log {R u : ℝ} (j : ℕ) (hu : u ≠ 0) (hd : u^2-R^2 ≠ 0) (hR : 0 < R) :
    rawD R (.negSucc j) u = raw R (.negSucc j) u*(4*u/(u^2-R^2)+j/u) := by
  cases j with
  | zero => simp [raw,rawD,base,ratioTerm,slopeTerm]; field_simp; ring
  | succ j =>
    simp only [raw,rawD,base,ratioTerm,slopeTerm,Nat.add_sub_cancel,Nat.cast_succ,pow_succ (-u)]
    field_simp; ring

/-- At the origin only the value in column -1 and the derivative in column -2 contribute. -/
private theorem density_zero {R : ℝ} (hR : 0 < R) :
    HasSum (fun j => localEnergy R (.ofNat j) 0 + localEnergy R (.negSucc j) 0)
      (density 0 (R^2)) := by
  let term (j : ℕ) := localEnergy R (.ofNat j) 0 + localEnergy R (.negSucc j) 0
  have hp := sq_pos_of_pos hR
  have tail (j : ℕ) (hj : j ∉ ({0, 1} : Finset ℕ)) : term j = 0 := by
    have hn : j ≠ 0 := fun h => hj (by simp [h])
    have hm : j-1 ≠ 0 := by
      have h₁ : j ≠ 1 := fun h => hj (by simp [h])
      omega
    simp [term, localEnergy, branch, dbranch, g, dg, cut, height, raw, rawD,
      ratioTerm, slopeTerm, hp, hn, hm, hp.le]
  have total : term 0 + term 1 = density 0 (R^2) := by
    norm_num [term, localEnergy, branch, dbranch, g, dg, cut, height, raw, rawD,
      ratioTerm, slopeTerm, base, w, ellAt, ell, density, hp, hp.le,
      show algebraMap ℝ ℝ = RingHom.id ℝ from rfl]
    field_simp [hR.ne']
    ring
  simpa only [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), total] using
    (hasSum_sum_of_ne_finset_zero tail)

/-- Away from the origin and the switches the logarithmic derivatives sum geometrically. -/
theorem density_sum {R u : ℝ} (hR : 0 < R) (hu : u ≠ 0) (hd : u^2 ≠ R^2) :
    HasSum (fun j => localEnergy R (.ofNat j) u + localEnergy R (.negSucc j) u) (density (u^2) (R^2)) := by
  let x := R^2
  let h := u^2
  let A := -2*u+w u*(4*u/(h-x)-1/(2*u))
  rcases lt_or_gt_of_ne hd with hi | ho
  · let B := w u/u
    have eq := affine_energy (q := h/x) (by positivity) ((div_lt_one (sq_pos_of_pos hR)).2 hi)
      ((h-x)^4/x) (w u) A B
    rw [← inner_density hu (pow_ne_zero 2 hR.ne') (sub_ne_zero.mpr hd)]
    apply eq.congr_fun
    intro j
    simp only [localEnergy,branch,dbranch,ellAt,g,dg,cut,height,sub_pos,if_neg hi.asymm,if_pos hi,
      mul_zero,add_zero,zero_mul,zero_pow (by decide : 2 ≠ 0),zero_add]
    rw [inner_log j hu (sub_ne_zero.mpr hd) hR]
    have he : -2*u+w u*(4*u/(h-x)+j/u) = A+B*ell j := by dsimp [A,B,ell]; field_simp; ring
    symm
    change _ = ell j*((ell j^2+9)*(w u*raw R (.negSucc j) u)^2+
      w u*((-2*u)*raw R (.negSucc j) u+w u*(raw R (.negSucc j) u*(4*u/(h-x)+j/u)))^2)
    rw [show (-2*u)*raw R (.negSucc j) u+w u*(raw R (.negSucc j) u*(4*u/(h-x)+j/u)) =
      (A+B*ell j)*raw R (.negSucc j) u by rw [← he]; ring, ← inner_square j hR]
    ring
  · let B := -w u/u
    have eq := affine_energy (q := x/h) (by positivity) ((div_lt_one (sq_pos_of_ne_zero hu)).2 ho)
      ((h-x)^4/h) (w u) A B
    rw [← outer_density hu (sub_ne_zero.mpr hd)]
    apply eq.congr_fun
    intro j
    simp only [localEnergy,branch,dbranch,ellAt,g,dg,cut,height,sub_pos,if_neg ho.asymm,if_pos ho,
      mul_zero,add_zero,zero_mul,zero_pow (by decide : 2 ≠ 0)]
    rw [outer_log j hu (sub_ne_zero.mpr hd)]
    have he : -2*u+w u*(4*u/(h-x)-(j+1)/u) = A+B*ell j := by dsimp [A,B,ell]; field_simp; ring
    symm
    change _ = ell j*((ell j^2+9)*(w u*raw R (.ofNat j) u)^2+
      w u*((-2*u)*raw R (.ofNat j) u+w u*(raw R (.ofNat j) u*(4*u/(h-x)-(j+1)/u)))^2)
    rw [show (-2*u)*raw R (.ofNat j) u+w u*(raw R (.ofNat j) u*(4*u/(h-x)-(j+1)/u)) =
      (A+B*ell j)*raw R (.ofNat j) u by rw [← he]; ring, ← outer_square j hu]
    ring

/-- The full density identity of Appendix A.3 at every point off the switch. -/
theorem density_sum_off_switch {R u : ℝ} (hR : 0 < R) (hd : u^2 ≠ R^2) :
    HasSum (fun j => localEnergy R (.ofNat j) u + localEnergy R (.negSucc j) u) (density (u^2) (R^2)) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simpa using density_zero hR
  · exact density_sum hR hu hd

private def signAt : ℤ → ℝ
  | .ofNat j => (-1)^(j+1)
  | .negSucc j => (-1)^j

private theorem reflected_branch (R : ℝ) (s : ℤ) (u : ℝ) :
    branch R s (-u) = signAt s * branch R s u := by
  cases s with
  | ofNat j =>
    simp only [branch,g,cut,height,neg_sq,signAt]
    split_ifs
    · simp only [raw,base,ratioTerm,neg_sq,w]
      rw [show (-u)^(j+1) = (-1)^(j+1)*u^(j+1) by rw [← mul_pow,neg_one_mul],div_mul_eq_div_div]
      have h : ((-1:ℝ)^(j+1))⁻¹ = (-1:ℝ)^(j+1) := by rw [← inv_pow]; norm_num
      simp only [div_eq_mul_inv,h]; ring
    · ring
  | negSucc j =>
    simp only [branch,g,cut,height,neg_sq,signAt]
    split_ifs
    · simp only [raw,base,ratioTerm,neg_sq,w]
      rw [show (-u)^j = (-1)^j*u^j by rw [← mul_pow,neg_one_mul]]
      rw [neg_neg]
      have hs : ((-1:ℝ)^j)^2 = 1 := by rw [sq,← mul_pow]; norm_num
      linear_combination -((4-u^2) * (u^2-R^2)^2 * u^j/R^(j+1)) * hs
    · ring

theorem complementary (R : ℝ) (hR : 0 < R) (j : ℕ) (d : ℤ) :
    kernel R hR d (.ofNat j) = 0 ∨ kernel R hR d (.negSucc j) = 0 := by
  have prop (s : ℤ) (hne : kernel R hR d s ≠ 0) : signAt s = (-1:ℝ)^d := by
    have eq : (column R hR s).comp negI = restrict (Polynomial.C (signAt s))*column R hR s := by
      ext u
      change branch R s (-↑u) = (Polynomial.C (signAt s)).eval (u:ℝ)*branch R s u
      rw [Polynomial.eval_C]; exact reflected_branch R s u
    have he := b_reflect (column R hR s) d
    rw [eq,b_const_mul] at he
    exact mul_right_cancel₀ hne he
  classical
  by_contra! h
  have a := (prop _ h.1).trans (prop _ h.2).symm
  simp only [signAt,pow_succ,mul_neg_one] at a
  exact (pow_ne_zero j (by norm_num : (-1:ℝ) ≠ 0)) (by linarith)

end Uniform.Walks
