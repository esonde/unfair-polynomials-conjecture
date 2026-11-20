import Trinomial.Fourier.Circle
import Trinomial.Fourier.Profiles
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Integration by parts and summation of the three column moments -/

noncomputable section
namespace Trinomial.Fourier

open MeasureTheory AddCircle Filter Finset
open scoped Topology

private theorem derivative_mean_zero {V D : Angle → ℝ}
    (der : ∀ t : ℝ, HasDerivAt (fun u : ℝ => V (u : Angle)) (D t) t) (cd : Continuous D) :
    ∫ θ, D θ ∂haar = 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := period) (fun t _ => der t)
    ((cd.comp (AddCircle.continuous_mk' period)).intervalIntegrable 0 period)
  have hh := AddCircle.intervalIntegral_preimage period 0 D
  simp only [zero_add] at hh
  rw [hh,AddCircle.coe_period,AddCircle.coe_zero,sub_self,AddCircle.volume_eq_smul_haarAddCircle,
      integral_smul_measure,ENNReal.toReal_ofReal (Fact.out : 0 < period).le,smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (Fact.out : 0 < period).ne'

private theorem velocity_deriv (t : ℝ) :
    HasDerivAt (fun u : ℝ => velocity (u : Angle)) (-b t) t := by
  simp only [velocity_coe,b_coe]
  convert (Real.hasDerivAt_sin t).const_mul (-2) using 1; ring

private def corrected (R : ℝ) (s : ℤ) (u : ℝ) :=
  let h := u^2
  let W := w u
  ellAt s * ((W^2*(ellAt s^2+16)+2*W*(W-h))*g R s u^2 + W^3*dg R s u^2)

private theorem g_cont (R : ℝ) (hp : 0 < R) (s : ℤ) : Continuous (g R s) :=
  continuous_iff_continuousAt.mpr (fun t => (g_hasDerivAt R hp s t).continuousAt)

theorem original_cont (R : ℝ) (hp : 0 < R) (s : ℤ) : Continuous (localEnergy R s) := by
  unfold localEnergy w
  have := branch_cont R hp s
  have := dbranch_cont R hp s
  fun_prop

private theorem corrected_cont (R : ℝ) (hp : 0 < R) (s : ℤ) : Continuous (corrected R s) := by
  unfold corrected w
  have := g_cont R hp s
  have := dg_cont R hp s
  fun_prop

/-- Integrate the derivative of ℓ w w' g² over the circle. -/
theorem column_integration_by_parts (R : ℝ) (hp : 0 < R) (s : ℤ) :
    ∫ θ : Angle, localEnergy R s (b θ) ∂haar = ∫ θ : Angle, corrected R s (b θ) ∂haar := by
  let V (θ : Angle) := ellAt s * (w (b θ) * ((-2)*b θ*velocity θ) * g R s (b θ)^2)
  let D (θ : Angle) := localEnergy R s (b θ) - corrected R s (b θ)
  have cd : Continuous D := ((original_cont R hp s).comp b_cont).sub ((corrected_cont R hp s).comp b_cont)
  have der (t : ℝ) : HasDerivAt (fun u : ℝ => V (u : Angle)) (D (t : Angle)) t := by
    have db := b_deriv t
    have dv := velocity_deriv t
    have dw := (hasDerivAt_const t (4:ℝ)).sub (db.pow 2)
    have dw' := ((db.const_mul (-2)).mul dv)
    have dg := (g_hasDerivAt R hp s _).comp t db
    convert (((dw.mul dw').mul (dg.pow 2)).const_mul (ellAt s)) using 1
    dsimp [D,localEnergy,corrected,branch,dbranch,w]
    simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    linear_combination (ellAt s * (4 * (b (t : Angle))^2 * g R s (b t)^2 -
      4 * b t * (4 - (b t)^2) * g R s (b t) * Trinomial.Fourier.dg R s (b t) -
      2 * (4 - (b t)^2) * g R s (b t)^2)) * (velocity_sq (t : Angle)).symm
  have h := derivative_mean_zero der cd
  rw [show (∫ θ, D θ ∂haar) = _ from integral_sub (integrable_circle ((original_cont R hp s).comp b_cont))
    (integrable_circle ((corrected_cont R hp s).comp b_cont))] at h
  exact sub_eq_zero.mp h

/-- The density displayed after integration by parts in Section 3. -/
def energyDensity {K : Type*} [CommRing K] [Algebra ℝ K] (h x : K) : K :=
  let W := 4-h
  let m := (h+x)*(h-x)^2*algebraMap ℝ K (1/2)
  W^2*(algebraMap ℝ K (65/4)*m + 3*h*x*(h+x)) +
    2*W*(W-h)*m + algebraMap ℝ K (3/2)*W^3*(3*h^2+x^2)


private def c₀ (u : ℝ) := w u^2*(65/4)+2*w u*(w u-u^2)

private def terms (R u A B C : ℝ) (j : ℕ) :=
  momentTerm R u A B C j (.ofNat j) + momentTerm R u A B C j (.negSucc j)

private def partialEnergy (R : ℝ) (n : ℕ) (θ : Angle) :=
  ∑ j ∈ range n, (corrected R (.ofNat j) (b θ) + corrected R (.negSucc j) (b θ))

private theorem paired (R u : ℝ) (j : ℕ) :
    corrected R (.ofNat j) u + corrected R (.negSucc j) u =
      terms R u (c₀ u) (w u^2) (w u^3) j := by
  unfold corrected terms momentTerm c₀
  simp only [ellAt]
  ring

private theorem switch_zero (R u A B C : ℝ) (he : u^2=R^2) (j : ℕ) : terms R u A B C j = 0 := by
  simp [terms,momentTerm,g,dg,cut,height,he]

private theorem terms_mono (R u : ℝ) (j : ℕ) {A B C A' B' C' : ℝ}
    (ha : A ≤ A') (hb : B ≤ B') (hc : C ≤ C') :
    terms R u A B C j ≤ terms R u A' B' C' j := by
  have ell0 : 0 ≤ ell j := by unfold ell; positivity
  have ell2 : 0 ≤ ell j^2-1/4 := by unfold ell; nlinarith [sq_nonneg (j:ℝ),Nat.cast_nonneg (α := ℝ) j]
  dsimp [terms,momentTerm]
  gcongr

private theorem terms_abs (R u A B C : ℝ) (j : ℕ) :
    |terms R u A B C j| ≤ terms R u |A| |B| |C| j := by
  apply abs_le.mpr
  constructor
  · have h := terms_mono R u j (neg_le_abs A) (neg_le_abs B) (neg_le_abs C)
    have eq : terms R u (-A) (-B) (-C) j = -terms R u A B C j := by unfold terms momentTerm; ring
    linarith
  · exact terms_mono R u j (le_abs_self _) (le_abs_self _) (le_abs_self _)

private theorem majorant (R : ℝ) (hp : 0 < R) (u A B C : ℝ) (n : ℕ) :
    |∑ j ∈ range n, terms R u A B C j| ≤ abs (momentTotal (u^2) (R^2) |A| |B| |C|) := by
  by_cases he : u^2=R^2
  · simp [switch_zero R u A B C he]
  · have hs := column_moment_linear hp he |A| |B| |C|
    calc
      _ ≤ ∑ j ∈ range n, |terms R u A B C j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range n, terms R u |A| |B| |C| j := sum_le_sum fun j _ => terms_abs ..
      _ ≤ momentTotal (u^2) (R^2) |A| |B| |C| := sum_le_hasSum _ (fun j _ =>
        (abs_nonneg _).trans (terms_abs R u A B C j)) hs
      _ ≤ _ := le_abs_self _

private theorem energy_total (R u : ℝ) :
    momentTotal (u^2) (R^2) (c₀ u) (w u^2) (w u^3) = energyDensity (u^2) (R^2) := by
  simp [momentTotal,energyDensity,c₀,w,M,show algebraMap ℝ ℝ = RingHom.id ℝ from rfl]
  ring

private theorem partial_cont (R : ℝ) (hp : 0 < R) (n : ℕ) : Continuous (partialEnergy R n) :=
  continuous_finset_sum _ (fun _ _ => ((corrected_cont R hp _).comp b_cont).add
    ((corrected_cont R hp _).comp b_cont))

private theorem integration_limit (R : ℝ) (hp : 0 < R) :
    Tendsto (fun n => ∫ θ : Angle, partialEnergy R n θ ∂haar) atTop
      (𝓝 (∫ θ : Angle, energyDensity (b θ^2) (R^2) ∂haar)) := by
  let bound (θ : Angle) := abs (momentTotal (b θ^2) (R^2) |c₀ (b θ)| |w (b θ)^2| |w (b θ)^3|)
  have cb : Continuous bound := by unfold bound momentTotal c₀ w M; fun_prop
  apply tendsto_integral_of_dominated_convergence bound
    (fun n => (partial_cont R hp n).aestronglyMeasurable) (integrable_circle cb)
  · intro n
    filter_upwards with θ
    simpa only [partialEnergy,bound,paired,Real.norm_eq_abs] using
      majorant R hp (b θ) (c₀ (b θ)) (w (b θ)^2) (w (b θ)^3) n
  · filter_upwards [off_switch_ae R] with θ he
    have h := (column_moment_linear hp he (c₀ (b θ)) (w (b θ)^2) (w (b θ)^3)).tendsto_sum_nat
    simpa only [partialEnergy,paired,terms,energy_total] using h

/-- The integral of each finite column sum is unchanged by integration by parts. -/
private theorem integral_partial_eq (R : ℝ) (hp : 0 < R) (m : ℕ) :
    ∑ j ∈ range m, (∫ θ : Angle, (localEnergy R (.ofNat j) (b θ) +
      localEnergy R (.negSucc j) (b θ)) ∂haar) = ∫ θ, partialEnergy R m θ ∂haar := by
  unfold partialEnergy
  rw [integral_finset_sum (f := fun j θ => corrected R (.ofNat j) (b θ) + corrected R (.negSucc j) (b θ)) _ (fun j _ => integrable_circle (((corrected_cont R hp _).comp b_cont).add
    ((corrected_cont R hp _).comp b_cont)))]
  apply sum_congr rfl
  intro j _
  rw [integral_add (f := fun θ => localEnergy R (.ofNat j) (b θ)) (g := fun θ => localEnergy R (.negSucc j) (b θ)) (integrable_circle ((original_cont R hp _).comp b_cont))
    (integrable_circle ((original_cont R hp _).comp b_cont)),
    integral_add (f := fun θ => corrected R (.ofNat j) (b θ)) (g := fun θ => corrected R (.negSucc j) (b θ)) (integrable_circle ((corrected_cont R hp _).comp b_cont))
    (integrable_circle ((corrected_cont R hp _).comp b_cont)),column_integration_by_parts R hp,
    column_integration_by_parts R hp]

/-- The limit is the full angular energy; the switch set has Haar measure zero. -/
theorem energy_limit (R : ℝ) (hp : 0 < R) :
    Tendsto (fun n => ∑ j ∈ range n, (∫ θ : Angle, (localEnergy R (.ofNat j) (b θ) +
      localEnergy R (.negSucc j) (b θ)) ∂haar)) atTop
      (𝓝 (∫ θ : Angle, energyDensity (b θ^2) (R^2) ∂haar)) := by
  simp_rw [integral_partial_eq R hp]
  exact integration_limit R hp

/-- Finite original column energies increase. Their integrals equal the signed
corrected energies after integration by parts, and the latter converge by domination. -/
theorem integrated_energy (R : ℝ) (hp : 0 < R) (n : ℕ) :
    ∑ j ∈ range n, (∫ θ : Angle, (localEnergy R (.ofNat j) (b θ) +
      localEnergy R (.negSucc j) (b θ)) ∂haar) ≤ ∫ θ : Angle, energyDensity (b θ^2) (R^2) ∂haar := by
  let e (j : ℕ) := ∫ θ : Angle, (localEnergy R (.ofNat j) (b θ)+localEnergy R (.negSucc j) (b θ)) ∂haar
  have positive (j : ℕ) : 0 ≤ e j := by
    apply integral_nonneg
    intro θ
    have hw : 0 ≤ w (b θ) := by unfold w; rw [← velocity_sq]; positivity
    have ell0 : 0 ≤ ell j := by unfold ell; positivity
    unfold localEnergy
    simp only [ellAt]
    positivity
  apply ge_of_tendsto (energy_limit R hp)
  filter_upwards [eventually_ge_atTop n] with m hm
  exact sum_le_sum_of_subset_of_nonneg (range_mono hm) (fun j _ _ => positive j)

end Trinomial.Fourier
