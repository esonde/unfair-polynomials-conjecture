module

public import Trinomial.Fourier.Circle
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.NormedSpace.FunctionSeries

@[expose] public section

/-! # Absolutely convergent Fourier series on the product of two circles -/

noncomputable section
namespace Trinomial.Fourier

open MeasureTheory AddCircle

abbrev Lattice := ℤ × ℤ
abbrev Torus := Angle × Angle

def character (i : Lattice) (t : Torus) := fourier i.1 t.1 * fourier i.2 t.2

@[fun_prop] theorem character_cont (i : Lattice) : Continuous (character i) :=
  ((fourier _).continuous.comp continuous_fst).mul ((fourier _).continuous.comp continuous_snd)

@[simp] theorem char_norm (n : ℤ) (t : Angle) : ‖fourier n t‖ = 1 := Circle.norm_coe _
@[simp] theorem character_norm (i : Lattice) (t : Torus) : ‖character i t‖ = 1 := by
  simp [character,norm_mul]

theorem character_add (i j : Lattice) (t : Torus) :
    character (i+j) t = character i t * character j t := by
  simp only [character,Prod.fst_add,Prod.snd_add,fourier_add]; ring

def synthesis (a : Lattice → ℂ) (t : Torus) := ∑' i, a i * character i t

def torusCoeff (f : Torus → ℂ) (i : Lattice) :=
  ∫ t : Torus, character (-i) t * f t ∂(haar.prod haar)

theorem synthesis_cont {a : Lattice → ℂ} (ha : Summable fun i => ‖a i‖) : Continuous (synthesis a) :=
  continuous_tsum (fun i => continuous_const.mul (character_cont i)) ha (fun i t => by simp [norm_mul])

theorem character_mean (i : Lattice) :
    ∫ t : Torus, character i t ∂(haar.prod haar) = if i=0 then 1 else 0 := by
  have row (n : ℤ) : ∫ θ : Angle, fourier n θ ∂haar = if n=0 then 1 else 0 := by
    by_cases h : n=0
    · subst n; simp [fourier_zero]
    · rw [if_neg h]
      exact integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index h (Fact.out : 0 < period))
  unfold character
  rw [integral_prod_mul,row,row]
  rcases i with ⟨p,s⟩
  by_cases hp : p=0 <;> by_cases hs : s=0 <;> simp [hp,hs,Prod.ext_iff]

theorem coeff_synthesis {a : Lattice → ℂ} (ha : Summable fun i => ‖a i‖) (j : Lattice) :
    torusCoeff (synthesis a) j = a j := by
  let F (i : Lattice) (t : Torus) := a i * character (-j+i) t
  have eq (i : Lattice) : ∫ t, F i t ∂(haar.prod haar) = if i=j then a i else 0 := by
    rw [show (∫ t, F i t ∂(haar.prod haar)) = a i * ∫ t, character (-j+i) t ∂(haar.prod haar)
      from integral_const_mul ..,character_mean]
    by_cases e : i=j <;> simp_all [neg_add_eq_zero,eq_comm]
  have h := hasSum_integral_of_summable_integral_norm (μ := haar.prod haar) (F := F)
    (fun i => (continuous_const.mul (character_cont (-j+i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (by simpa [F,norm_mul] using ha)
  rw [torusCoeff]
  have eq' (t : Torus) : character (-j) t * synthesis a t = ∑' i, F i t := by
    rw [synthesis,← tsum_mul_left]
    apply tsum_congr; intro i; dsimp [F]; rw [character_add]; ring
  simp_rw [eq']
  rw [← h.tsum_eq]
  simp_rw [eq]
  rw [tsum_eq_single j (fun i hi => if_neg hi),if_pos rfl]

/-- Multiplying a Fourier series by a character shifts its coefficient array. -/
theorem synthesis_shift (a : Lattice → ℂ) (v : Lattice) (t : Torus) :
    synthesis (fun i => a (i-v)) t = character v t * synthesis a t := by
  rw [synthesis,← (Equiv.addRight v).tsum_eq]
  simp only [Equiv.coe_addRight,add_sub_cancel_right,character_add]
  rw [synthesis,← tsum_mul_left]
  apply tsum_congr; intro i; ring

end Trinomial.Fourier
