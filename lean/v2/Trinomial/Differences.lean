module

public import Trinomial.Embedded
public import Trinomial.WidestStrip

@[expose] public section

/-! # Successive differences in the first four rows (Sections 2 and 4) -/

noncomputable section
namespace Trinomial

/-- Coefficients in increasing order modulo y^4. -/
@[ext] structure Four where
  c0 : ℂ
  c1 : ℂ
  c2 : ℂ
  c3 : ℂ

namespace Four

def scale (s : ℂ) (x : Four) : Four := ⟨s*x.c0,s*x.c1,s*x.c2,s*x.c3⟩
def step (x : Four) : Four := ⟨x.c0,x.c1+x.c0,x.c2+x.c1,x.c3+x.c2⟩

theorem step_injective : Function.Injective step := by
  intro x y e
  obtain ⟨a,b,c,d⟩ := Four.ext_iff.mp e
  ext <;> simp only [step] at a b c d <;> first
    | linear_combination a | linear_combination b-a | linear_combination c-b+a | linear_combination d-c+b-a

/-- Multiplication by (1+y)⁻¹ modulo y⁴. -/
def unstep (x : Four) : Four :=
  ⟨x.c0,x.c1-x.c0,x.c2-x.c1+x.c0,x.c3-x.c2+x.c1-x.c0⟩

@[simp] theorem step_unstep (x : Four) : (unstep x).step = x := by
  ext <;> simp [unstep,step]

/-- The four coefficients of (1+y)⁻ᵏ times the starting column. -/
def inversePower (k : ℕ) (x : Four) : Four := unstep^[k] x

@[simp] theorem step_inversePower_succ (k : ℕ) (x : Four) : (inversePower (k+1) x).step = inversePower k x := by
  simp [inversePower,Function.iterate_succ_apply']

def filter (t : ℝ) (x : Four) : Four :=
  let s : ℂ := t
  ⟨x.c0, x.c1-2*s*x.c0, x.c2-2*s*x.c1+(s^2+2*s)*x.c0,
    x.c3-2*s*x.c2+(s^2+2*s)*x.c1-2*(1+s^2)*x.c0⟩

theorem step_scale (a : ℂ) (x : Four) : (scale a x).step = scale a x.step := by
  ext <;> simp [scale,step] <;> ring

theorem filter_scale (t : ℝ) (a : ℂ) (x : Four) : filter t (scale a x) = scale a (filter t x) := by
  ext <;> simp [scale,filter] <;> ring

theorem filter_step (t : ℝ) (x : Four) : (filter t x).step = filter t x.step := by
  ext <;> simp [step,filter] <;> ring

theorem scale_scale (a b : ℂ) (x : Four) : scale a (scale b x) = scale (a*b) x := by
  ext <;> simp [scale, mul_assoc]

def formula (t : ℝ) (U V : ℂ) (k : ℕ) : Four :=
  ⟨1,-(k+2*(t : ℂ)), (quad t k : ℂ)+U, -(cubic t k : ℂ)-(k+2*(t : ℂ))*U+V⟩

theorem formula_zero (t : ℝ) (U V : ℂ) : formula t U V 0 = filter t ⟨1,0,U,V⟩ := by
  ext <;> simp [formula, filter, quad, cubic] <;> ring

theorem formula_succ (t : ℝ) (U V : ℂ) (k : ℕ) : (formula t U V (k+1)).step = formula t U V k := by
  ext <;> simp [step, formula, quad, cubic] <;> ring

end Four

namespace Embedded
variable {c : FractionalCase}

def delta (E : Embedded c) (S : c.Strip) (k : ℕ) : Four :=
  let a j := E.v S j (k+1) - E.v S j k
  ⟨a 0, a 1, a 2, a 3⟩

private theorem rows (E : Embedded c) (S : c.Strip) (k : ℕ) (hk : k+1 ≤ S.width) :
    (E.v S 0 (k+1)+E.lam*E.v S 0 k = 1) ∧
    (E.v S 1 (k+1)+E.v S 0 (k+1)+E.lam*E.v S 1 k = 1) ∧
    (E.v S 2 (k+1)+E.v S 1 (k+1)+E.lam*E.v S 2 k = 1) ∧
    (E.v S 3 (k+1)+E.v S 2 (k+1)+E.lam*E.v S 3 k = 1) := by
  obtain ⟨a,b,d,e⟩ := S.four_digits hk
  have h := E.row a
  norm_num only at h
  rw [E.transport_zero (S.lower_neighbor hk), add_zero] at h
  exact ⟨h,E.row b,E.row d,E.row e⟩

theorem delta_initial (E : Embedded c) (S : c.Strip) :
    (E.delta S 0).step = Four.scale (-E.lam) ⟨1,0,E.U S,E.V S⟩ := by
  obtain ⟨a,b,d,e⟩ := E.rows S 0 S.positive
  have h₀ := E.transport_one S.initial.1
  have h₁ := E.transport_zero S.initial.2
  simp only [h₀,h₁,mul_one,mul_zero,add_zero] at a b
  ext <;> simp only [Four.step,delta,Four.scale,U,V,h₀,h₁,mul_one,mul_zero] <;>
    field_simp [E.ne_zero]
  · linear_combination a
  · linear_combination b
  · linear_combination d
  · linear_combination e

theorem delta_step (E : Embedded c) (S : c.Strip) {k : ℕ} (hk : k+2 ≤ S.width) :
    (E.delta S (k+1)).step = Four.scale (-E.lam) (E.delta S k) := by
  obtain ⟨a,b,d,e⟩ := E.rows S k (by omega)
  obtain ⟨a',b',d',e'⟩ := E.rows S (k+1) hk
  ext <;> simp only [Four.step,delta,Four.scale]
  · linear_combination a'-a
  · linear_combination b'-b
  · linear_combination d'-d
  · linear_combination e'-e

/-- Lemma 3, before the mask is applied. Index k represents the difference at step k+1. -/
theorem column_difference (E : Embedded c) (S : c.Strip) {k : ℕ} (hk : k+1 ≤ S.width) :
    E.delta S k = Four.scale ((-E.lam)^(k+1)) (Four.inversePower (k+1) ⟨1,0,E.U S,E.V S⟩) := by
  induction k with
  | zero =>
    apply Four.step_injective
    rw [E.delta_initial,Four.step_scale,Four.step_inversePower_succ,pow_one]
    rfl
  | succ k ih =>
    apply Four.step_injective
    rw [E.delta_step S hk,ih (by omega),Four.scale_scale,Four.step_scale,Four.step_inversePower_succ,
      pow_succ (-E.lam) (k+1),mul_comm (-E.lam)]

/-- Both inherited bounds and the difference formula on one strip. -/
theorem column_differences (E : Embedded c) {P S : c.Strip} (adj : P.start+P.width = S.start) :
    ‖E.U S‖ ≤ ‖E.lam‖^P.width ∧ ‖E.V S‖ ≤ P.width*‖E.lam‖^P.width ∧
    ∀ k : ℕ, k+1 ≤ S.width → E.delta S k =
      Four.scale ((-E.lam)^(k+1)) (Four.inversePower (k+1) ⟨1,0,E.U S,E.V S⟩) :=
  ⟨(E.inherited adj).1,(E.inherited adj).2,fun _ h => E.column_difference S h⟩

/-- The coefficients after applying the filter and omitting rows below the old bottom. -/
theorem filtered_delta (E : Embedded c) (S : c.Strip) (t : ℝ) {k : ℕ} (hk : k+1 ≤ S.width) :
    Four.filter t (E.delta S k) =
    Four.scale ((-E.lam)^(k+1)) (Four.formula t (E.U S) (E.V S) (k+1)) := by
  have filtered (j : ℕ) : Four.filter t (Four.inversePower j ⟨1,0,E.U S,E.V S⟩) =
      Four.formula t (E.U S) (E.V S) j := by
    induction j with
    | zero => exact (Four.formula_zero ..).symm
    | succ j ih =>
      apply Four.step_injective
      rw [Four.filter_step,Four.step_inversePower_succ,Four.formula_succ,ih]
  rw [E.column_difference S hk,Four.filter_scale,filtered]

end Embedded
end Trinomial
