import Uniform.Walks.KernelNorm
import Uniform.Walks.Specialize

/-! # Pairing the kernel equation with product coefficients -/

noncomputable section
namespace Uniform.Walks

open Polynomial Finset

private theorem transfer (R : ℝ) (hR : 1 ≤ R) (V : ℤ × ℤ → ℂ)
    (bound : ℝ) (hb : ∀ z, ‖V z‖ ≤ bound) :
    let k (p : ℤ × ℤ) := (kernel R (lt_of_lt_of_le zero_lt_one hR) p.1 p.2 : ℂ)
    ∑' p, k p * (V (p+(1,0)) + V (p+(-1,0)) + (R:ℂ)*V (p+(0,1))) =
      ∑' d, (walk (numerator R) d : ℂ)*V (d,0) := by
  let hp := lt_of_lt_of_le zero_lt_one hR
  let k (p : ℤ × ℤ) := (kernel R hp p.1 p.2 : ℂ)
  let A (v p : ℤ × ℤ) := k (p-v)*V p
  let B (v p : ℤ × ℤ) := k p*V (p+v)
  have kn : Summable (fun p : ℤ × ℤ => ‖k p‖) := by
    simpa [k,Real.norm_eq_abs] using (kernel_norm R hR).1
  have sb (v : ℤ × ℤ) : Summable (B v) :=
    (kn.mul_right bound).of_norm_bounded _ (fun p => by
      simpa [B,norm_mul] using mul_le_mul_of_nonneg_left (hb (p+v)) (norm_nonneg (k p)))
  have ident (v p : ℤ × ℤ) : A v ((Equiv.addRight v) p) = B v p := by simp [A,B]
  have sa (v : ℤ × ℤ) : Summable (A v) := by
    apply (Equiv.addRight v).summable_iff.mp
    simpa only [Function.comp_def,ident] using sb v
  have reindex (v : ℤ × ℤ) : ∑' p, B v p = ∑' p, A v p := by
    simpa only [ident] using (Equiv.addRight v).tsum_eq (A v)
  let rhs (p : ℤ × ℤ) := if p.2 = 0 then (walk (numerator R) p.1 : ℂ)*V p else 0
  have equation (p : ℤ × ℤ) : A (1,0) p + A (-1,0) p + (R:ℂ)*A (0,1) p = rhs p := by
    obtain ⟨d,s⟩ := p
    have he := congrArg Complex.ofReal (kernel_equation R hp d s)
    dsimp [A,k,rhs]
    push_cast at he
    split_ifs at he ⊢ <;> simp only [sub_zero,sub_neg_eq_add,Complex.ofReal_zero] at he ⊢ <;>
      linear_combination V (d,s)*he
  have hs : Summable rhs := (((sa (1,0)).add (sa (-1,0))).add ((sa (0,1)).mul_left (R:ℂ))).congr equation
  calc
    _ = ∑' p, (B (1,0) p + B (-1,0) p + (R:ℂ)*B (0,1) p) := by
      apply tsum_congr; intro p; dsimp only [B,k]; ring
    _ = (∑' p, B (1,0) p) + (∑' p, B (-1,0) p) + (R:ℂ)*∑' p, B (0,1) p := by
      rw [Summable.tsum_add ((sb _).add (sb _)) ((sb _).mul_left _),Summable.tsum_add (sb _) (sb _),tsum_mul_left]
    _ = ∑' p, rhs p := by
      simp only [reindex]
      rw [← tsum_mul_left, ← Summable.tsum_add (sa _) (sa _),
        ← Summable.tsum_add ((sa _).add (sa _)) ((sa _).mul_left _)]
      exact tsum_congr equation
    _ = _ := by
      rw [hs.tsum_prod]
      apply tsum_congr; intro d
      rw [tsum_eq_single 0 (fun s hs => by simp [rhs,hs])]
      simp [rhs]

private theorem doubled_bound (P : ℂ[X]) (n : ℤ) :
    ‖doubled P n‖ ≤ ∑ i ∈ P.support, ‖P.coeff i‖ := by
  have hp : 0 ≤ ∑ i ∈ P.support, ‖P.coeff i‖ := sum_nonneg (fun i _ => norm_nonneg _)
  simp only [doubled,coeffZ]
  split_ifs <;> try simpa using hp
  by_cases hm : (n/2).toNat ∈ P.support
  · exact single_le_sum (fun i _ => norm_nonneg (P.coeff i)) hm
  · have hz : P.coeff (n/2).toNat = 0 := by simpa [Polynomial.mem_support_iff] using hm
    simpa [hz] using hp

private theorem digit_bound (r m : ℕ) (lam : ℂ) (P : ℂ[X]) (hc : IsBinary (tri r m lam*P)) (n : ℤ) :
    ‖doubled (tri r m lam*((1-X^r)*P)) n‖ ≤ 1 := by
  rw [show tri r m lam*((1-X^r)*P) = tri r m lam*P-X^r*(tri r m lam*P) by ring]
  unfold doubled
  split_ifs <;> try simp
  rw [coeffZ_sub,coeffZ_X_pow_mul]
  rcases hc.coeffZ (n/2) with h|h <;> rcases hc.coeffZ (n/2-r) with g|g <;> simp [h,g]

theorem global_bound : GlobalBound := by
  intro r m lam P _ _ hR hc N
  let R := ‖lam‖
  have hp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let η := lam / (R:ℂ)
  have hn : ‖η‖ = 1 := by simp [η,norm_div,Real.norm_eq_abs,abs_of_pos hp,R,hp.ne',show ‖lam‖ ≠ 0 from hp.ne']
  have factor : (R:ℂ)*η = lam := by
    have ne : (R:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
    dsimp only [η]; field_simp
  let F := (1-X^r)*P
  let q := 2*N-6*(m:ℤ)
  let t := 2*(r:ℤ)-m
  let idx (z : ℤ × ℤ) := q-(m:ℤ)*z.1-t*z.2
  let V (z : ℤ × ℤ) := η^z.2 * doubled F (idx z)
  have hv (z : ℤ × ℤ) : ‖V z‖ ≤ ∑ i ∈ F.support, ‖F.coeff i‖ := by
    simpa [V,norm_mul,norm_zpow,hn] using doubled_bound F (idx z)
  have act (z : ℤ × ℤ) :
      V (z+(1,0)) + V (z+(-1,0)) + (R:ℂ)*V (z+(0,1)) =
        η^z.2*doubled (tri r m lam * F) (idx z + m) := by
    rw [doubled_recurrence]
    have i₁ : idx (z+(1,0)) = idx z + m - 2*m := by dsimp [idx]; ring
    have i₂ : idx (z+(-1,0)) = idx z + m := by dsimp [idx]; ring
    have i₃ : idx (z+(0,1)) = idx z + m - 2*r := by dsimp [idx,t]; ring
    simp only [V,i₁,i₂,i₃,Prod.snd_add,add_zero,zpow_add_one₀ (show η ≠ 0 by
      intro e; simp [e] at hn)]
    linear_combination η^z.2*doubled F (idx z+m-2*r)*factor
  let k (z : ℤ × ℤ) := kernel R hp z.1 z.2
  have eq := transfer R hR V _ hv
  simp only [act] at eq
  have v0 (d : ℤ) : V (d,0) = doubled F (2*N-6*m-m*d) := by simp [V,idx,q]
  simp only [v0,numerator_test] at eq
  have est : ‖∑' z : ℤ × ℤ, (k z:ℂ)*(η^z.2*doubled (tri r m lam*F) (idx z+m))‖ ≤
      ∑' z : ℤ × ℤ, |k z| := by
    apply tsum_of_norm_bounded (kernel_norm R hR).1.hasSum
    intro z
    simp only [norm_mul,norm_zpow,hn,one_zpow,one_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (digit_bound r m lam P hc _)
  change ‖_‖ < 25*R^3
  rw [show (1-X^r)*mask (‖lam‖^2-1) (X^m)*P = mask (R^2-1) (X^m)*F by dsimp [F,R]; ring]
  change (∑' z : ℤ × ℤ, (k z:ℂ)*(η^z.2*doubled (tri r m lam*F) (idx z+m))) = _ at eq
  rw [eq,norm_neg] at est
  exact est.trans_lt (kernel_norm R hR).2

end Uniform.Walks
