import Trinomial.Fourier.TwoPoint

/-! # Lemma 5. The three column moments on either side of the switch -/

noncomputable section
namespace Trinomial.Fourier

theorem outer_square {R u : ℝ} (j : ℕ) (hu : u ≠ 0) :
    raw R (.ofNat j) u ^2 = (u^2-R^2)^4/u^2*(R^2/u^2)^j := by
  have commutePow (b : ℝ) : (b^j)^2 = (b^2)^j := by rw [← pow_mul, mul_comm j 2, pow_mul]
  simp only [raw,base,ratioTerm,pow_succ u j,mul_pow,div_pow,commutePow,neg_sq]
  field_simp; ring

theorem inner_square {R u : ℝ} (j : ℕ) (hR : 0 < R) :
    raw R (.negSucc j) u ^2 = (u^2-R^2)^4/R^2*(u^2/R^2)^j := by
  have commutePow (b : ℝ) : (b^j)^2 = (b^2)^j := by rw [← pow_mul, mul_comm j 2, pow_mul]
  simp only [raw,base,ratioTerm,pow_succ R j,mul_pow,div_pow,commutePow,neg_sq]
  field_simp; ring

theorem outer_log {R u : ℝ} (j : ℕ) (hu : u ≠ 0) (hd : u^2-R^2 ≠ 0) :
    rawD R (.ofNat j) u = raw R (.ofNat j) u*(4*u/(u^2-R^2)-(j+1)/u) := by
  simp only [raw,rawD,base,ratioTerm,slopeTerm]
  rw [pow_succ u (j+1)]
  field_simp [hu,hd]; ring

theorem inner_log {R u : ℝ} (j : ℕ) (hu : u ≠ 0) (hd : u^2-R^2 ≠ 0) (hR : 0 < R) :
    rawD R (.negSucc j) u = raw R (.negSucc j) u*(4*u/(u^2-R^2)+j/u) := by
  cases j with
  | zero => simp [raw,rawD,base,ratioTerm,slopeTerm]; field_simp; ring
  | succ j =>
    simp only [raw,rawD,base,ratioTerm,slopeTerm,Nat.add_sub_cancel,Nat.cast_succ,pow_succ (-u)]
    field_simp; ring

def momentTerm (R u c₀ c₂ cD : ℝ) (j : ℕ) (s : ℤ) :=
  ell j * ((c₀ + c₂*(ell j^2-1/4))*g R s u^2 + cD*dg R s u^2)

def momentTotal (h x c₀ c₂ cD : ℝ) :=
  c₀*M h x + c₂*(3*h*x*(h+x)) + cD*(3/2*(3*h^2+x^2))

private theorem geometric_form {q : ℝ} (hq : 0 ≤ q) (h1 : q < 1) (v A B c₀ c₂ cD : ℝ) :
    HasSum (fun j => ell j * ((c₀+c₂*(ell j^2-1/4))+cD*(A+B*ell j)^2) * (v*q^j))
      (v*((c₀-c₂/4+cD*A^2)*geo1 q + 2*cD*A*B*geo2 q + (c₂+cD*B^2)*geo3 q)) := by
  obtain ⟨s₁,s₂,s₃⟩ := geom_moments hq h1
  convert (((s₁.mul_left (c₀-c₂/4+cD*A^2)).add (s₂.mul_left (2*cD*A*B))).add
    (s₃.mul_left (c₂+cD*B^2))).mul_left v using 1
  funext j; ring

private theorem at_origin {R : ℝ} (hp : 0 < R) (c₀ c₂ cD : ℝ) :
    HasSum (fun j => momentTerm R 0 c₀ c₂ cD j (.ofNat j) + momentTerm R 0 c₀ c₂ cD j (.negSucc j))
      (momentTotal 0 (R^2) c₀ c₂ cD) := by
  let f (j : ℕ) := momentTerm R 0 c₀ c₂ cD j (.ofNat j) + momentTerm R 0 c₀ c₂ cD j (.negSucc j)
  have pos := sq_pos_of_pos hp
  have tail (j : ℕ) (hj : j ∉ ({0,1} : Finset ℕ)) : f j = 0 := by
    have hn : j ≠ 0 := fun h => hj (by simp [h])
    have hm : j-1 ≠ 0 := by
      have h₁ : j ≠ 1 := fun h => hj (by simp [h])
      omega
    simp [f,momentTerm,g,dg,cut,height,raw,rawD,ratioTerm,slopeTerm,pos,hn,hm,pos.le]
  have tot : f 0 + f 1 = momentTotal 0 (R^2) c₀ c₂ cD := by
    norm_num [f,momentTerm,g,dg,cut,height,raw,rawD,ratioTerm,slopeTerm,base,ell,momentTotal,M,pos,pos.le]
    field_simp [hp.ne']; ring
  simpa only [Finset.sum_pair (by decide : (0:ℕ) ≠ 1),tot] using hasSum_sum_of_ne_finset_zero tail

set_option maxHeartbeats 4200000 in
private theorem inner_moments {R u : ℝ} (hp : 0 < R) (hu : u ≠ 0) (hr : u^2 < R^2) (c₀ c₂ cD : ℝ) :
    HasSum (fun j => momentTerm R u c₀ c₂ cD j (.ofNat j) + momentTerm R u c₀ c₂ cD j (.negSucc j))
      (momentTotal (u^2) (R^2) c₀ c₂ cD) := by
  let h := u^2
  let x := R^2
  let A := 4*u/(h-x)-1/(2*u)
  let B := 1/u
  have hd : u^2-R^2 ≠ 0 := sub_ne_zero.mpr hr.ne
  have hz : R^2-u^2 ≠ 0 := by intro z; apply hd; linarith
  have hs := geometric_form (q := h/x) (by positivity) ((div_lt_one (sq_pos_of_pos hp)).mpr hr)
    ((h-x)^4/x) A B c₀ c₂ cD
  convert hs using 1
  · funext j
    simp only [momentTerm,g,dg,cut,height,sub_pos,if_neg hr.asymm,if_pos hr,zero_pow (by decide : 2 ≠ 0),
      mul_zero,add_zero,zero_add]
    rw [inner_log j hu hd hp]
    have lin : 4*u/(u^2-R^2)+j/u = A+B*ell j := by dsimp [A,B,h,x,ell]; field_simp; ring
    rw [lin,mul_pow,inner_square j hp]
    ring
  · dsimp [h,x,A,B,geo1,geo2,geo3,momentTotal,M]
    rw [show 1-u^2/R^2 = (R^2-u^2)/R^2 by field_simp]
    field_simp [hu,hp.ne',hd,hz]
    ring

set_option maxHeartbeats 4200000 in
private theorem outer_moments {R u : ℝ} (hp : 0 < R) (hu : u ≠ 0) (hr : R^2 < u^2) (c₀ c₂ cD : ℝ) :
    HasSum (fun j => momentTerm R u c₀ c₂ cD j (.ofNat j) + momentTerm R u c₀ c₂ cD j (.negSucc j))
      (momentTotal (u^2) (R^2) c₀ c₂ cD) := by
  let h := u^2
  let x := R^2
  let A := 4*u/(h-x)-1/(2*u)
  let B := -1/u
  have hd : u^2-R^2 ≠ 0 := sub_ne_zero.mpr hr.ne'
  have hz : R^2-u^2 ≠ 0 := by intro z; apply hd; linarith
  have hs := geometric_form (q := x/h) (by positivity) ((div_lt_one (sq_pos_of_ne_zero hu)).mpr hr)
    ((h-x)^4/h) A B c₀ c₂ cD
  convert hs using 1
  · funext j
    simp only [momentTerm,g,dg,cut,height,sub_pos,if_neg hr.asymm,if_pos hr,zero_pow (by decide : 2 ≠ 0),
      mul_zero,add_zero,zero_add]
    rw [outer_log j hu hd]
    have lin : 4*u/(u^2-R^2)-(j+1)/u = A+B*ell j := by dsimp [A,B,h,x,ell]; field_simp; ring
    rw [lin,mul_pow,outer_square j hu]
    ring
  · dsimp [h,x,A,B,geo1,geo2,geo3,momentTotal,M]
    rw [show 1-R^2/u^2 = (u^2-R^2)/u^2 by field_simp]
    field_simp [hu,hp.ne',hd,hz]
    ring

private theorem differentiated_moments {R u : ℝ} (hp : 0 < R) (hd : u^2 ≠ R^2) (c₀ c₂ cD : ℝ) : HasSum (fun j => momentTerm R u c₀ c₂ cD j (.ofNat j) +
      momentTerm R u c₀ c₂ cD j (.negSucc j)) (momentTotal (u^2) (R^2) c₀ c₂ cD) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simpa using at_origin hp c₀ c₂ cD
  rcases lt_or_gt_of_ne hd with h | h
  · exact inner_moments hp hu h _ _ _
  · exact outer_moments hp hu h _ _ _

/-- The three identities are stated on paired columns, with the common half-integer weight. -/
theorem column_moments {R u : ℝ} (hp : 0 < R) (hd : u^2 ≠ R^2) :
    HasSum (fun j => ell j * (g R (.ofNat j) u^2 + g R (.negSucc j) u^2)) (M (u^2) (R^2)) ∧
    HasSum (fun j => ell j * (ell j^2-1/4) * (g R (.ofNat j) u^2 + g R (.negSucc j) u^2))
      (3*u^2*R^2*(u^2+R^2)) ∧
    HasSum (fun j => ell j * (dg R (.ofNat j) u^2 + dg R (.negSucc j) u^2))
      (3/2*(3*(u^2)^2+(R^2)^2)) := by
  refine ⟨?_,?_,?_⟩
  · exact diagonal_moment hp hd
  · simpa [momentTerm,momentTotal,mul_add,mul_assoc] using differentiated_moments hp hd 0 1 0
  · simpa [momentTerm,momentTotal,mul_add] using differentiated_moments hp hd 0 0 1

/-- Apply all three moment identities with the weights supplied by integration by parts. -/
theorem column_moment_linear {R u : ℝ} (hp : 0 < R) (hd : u^2 ≠ R^2) (A B C : ℝ) :
    HasSum (fun j => momentTerm R u A B C j (.ofNat j) + momentTerm R u A B C j (.negSucc j))
      (momentTotal (u^2) (R^2) A B C) := by
  obtain ⟨h₀,h₂,hD⟩ := column_moments hp hd
  convert ((h₀.mul_left A).add (h₂.mul_left B)).add (hD.mul_left C) using 1
  funext j; dsimp [momentTerm]; ring

end Trinomial.Fourier
