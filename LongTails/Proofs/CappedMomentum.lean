import Mathlib.Tactic
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

namespace LongTails.Proofs.CappedMomentum

open MeasureTheory

lemma capped_radius {r s G : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hG : 0 ≤ G) :
    min G r * (G * s + r ^ 2) ≤ s * (G * s + r ^ 2) + 2 * G * r ^ 2 := by
  by_cases hrs : r ≤ s
  · have h := mul_le_mul_of_nonneg_right ((min_le_right G r).trans hrs)
      (show 0 ≤ G * s + r ^ 2 by positivity)
    nlinarith
  · have hsr : s ≤ r := le_of_lt (lt_of_not_ge hrs)
    by_cases hrG : r ≤ G
    · rw [min_eq_right hrG]
      have h₁ := mul_le_mul_of_nonneg_left hsr (mul_nonneg hG hr)
      have h₂ := mul_le_mul_of_nonneg_right hrG (sq_nonneg r)
      nlinarith [mul_nonneg hs (show 0 ≤ G * s + r ^ 2 by positivity)]
    · rw [min_eq_left (le_of_lt (lt_of_not_ge hrG))]
      have h₂ : G * s ≤ r ^ 2 := by
        nlinarith [mul_le_mul (le_of_lt (lt_of_not_ge hrG)) hsr hs hr]
      have h₃ := mul_le_mul_of_nonneg_left h₂ hG
      nlinarith [mul_nonneg hs (show 0 ≤ G * s + r ^ 2 by positivity)]

lemma tilted_drift {r s G α : ℝ} (hr : 0 ≤ r) (hs : 0 < s)
    (hG : 0 < G) (hα : 0 ≤ α) :
    Real.exp (α / (4 * G) * (min G r - 5 * s)) *
      (1 + α * (s ^ 2 - r ^ 2) / (G * s + r ^ 2)) ≤ 1 := by
  have hd : 0 < G * s + r ^ 2 := by positivity
  have hc := capped_radius hr hs.le hG.le
  have hn : (min G r - 5 * s) * (G * s + r ^ 2) +
      4 * G * (s ^ 2 - r ^ 2) ≤ 0 := by
    nlinarith [mul_nonneg hs.le (sq_nonneg r), mul_nonneg hG.le (sq_nonneg r)]
  have he : α / (4 * G) * (min G r - 5 * s) +
      α * (s ^ 2 - r ^ 2) / (G * s + r ^ 2) ≤ 0 := by
    have hid : α / (4 * G) * (min G r - 5 * s) +
        α * (s ^ 2 - r ^ 2) / (G * s + r ^ 2) =
        α * ((min G r - 5 * s) * (G * s + r ^ 2) +
          4 * G * (s ^ 2 - r ^ 2)) / (4 * G * (G * s + r ^ 2)) := by
      field_simp
    rw [hid]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hα hn)
      (by positivity)
  calc
    _ ≤ Real.exp (α / (4 * G) * (min G r - 5 * s)) *
        Real.exp (α * (s ^ 2 - r ^ 2) / (G * s + r ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [add_comm] using Real.add_one_le_exp
        (α * (s ^ 2 - r ^ 2) / (G * s + r ^ 2))
    _ = Real.exp (α / (4 * G) * (min G r - 5 * s) +
        α * (s ^ 2 - r ^ 2) / (G * s + r ^ 2)) := (Real.exp_add _ _).symm
    _ ≤ 1 := Real.exp_le_one_iff.mpr he

lemma potential_drift {r s G α q : ℝ} (hr : 0 ≤ r) (hs : 0 < s)
    (hG : 0 < G) (hα : 0 ≤ α)
    (hq : q ≤ (1 - α) * r ^ 2 + α * s ^ 2) :
    Real.exp (α / (4 * G) * min G r) * (1 + q / (G * s)) ≤
      Real.exp (α / (4 * G) * (5 * s)) * (1 + r ^ 2 / (G * s)) := by
  have hd : 0 < G * s + r ^ 2 := by positivity
  have hv : 0 ≤ 1 + r ^ 2 / (G * s) := by positivity
  have he := mul_le_mul_of_nonneg_right (tilted_drift hr hs hG hα) hv
  have hid : (1 + α * (s ^ 2 - r ^ 2) / (G * s + r ^ 2)) *
      (1 + r ^ 2 / (G * s)) = 1 + ((1 - α) * r ^ 2 + α * s ^ 2) / (G * s) := by
    field_simp
    ring
  rw [mul_assoc, hid, one_mul] at he
  have hq' := div_le_div_of_nonneg_right hq (mul_pos hG hs).le
  have hsmall : Real.exp (α / (4 * G) * (min G r - 5 * s)) * (1 + q / (G * s)) ≤
      1 + r ^ 2 / (G * s) :=
    (mul_le_mul_of_nonneg_left (show 1 + q / (G * s) ≤
      1 + ((1 - α) * r ^ 2 + α * s ^ 2) / (G * s) by linarith)
      (Real.exp_pos _).le).trans he
  have hh := mul_le_mul_of_nonneg_left hsmall
    (Real.exp_pos (α / (4 * G) * (5 * s))).le
  have hex : Real.exp (α / (4 * G) * (5 * s)) *
      Real.exp (α / (4 * G) * (min G r - 5 * s)) =
      Real.exp (α / (4 * G) * min G r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hex] at hh
  exact hh

lemma weighted_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : ℕ → Ω → ℝ} {V : Ω → ℝ} {τ G : ℝ}
    (hτ : 0 ≤ τ) (hZ : ∀ i, Measurable (Z i))
    (hbound : ∀ i ω, Z i ω ≤ G) (hV : Integrable V P) (n : ℕ) :
    Integrable (fun ω => Real.exp (τ * ∑ i ∈ Finset.range n, Z i ω) * V ω) P := by
  apply hV.bdd_mul
    (((Finset.measurable_sum _ (fun i _ => hZ i)).const_mul τ).exp.aestronglyMeasurable)
    (c := Real.exp (τ * (n * G)))
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, Real.abs_exp]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hτ
  simpa using Finset.sum_le_sum (s := Finset.range n) (fun i _ => hbound i ω)

lemma weighted_exp_integral {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ → MeasurableSpace Ω}
    (hm : ∀ n, m n ≤ m₀) {Z V : ℕ → Ω → ℝ} {τ G c : ℝ}
    (hτ : 0 ≤ τ) (hZ : ∀ i, Measurable (Z i))
    (hbound : ∀ i ω, Z i ω ≤ G) (hV : ∀ i, Integrable (V i) P)
    (hpast : ∀ n, StronglyMeasurable[m n]
      (fun ω => Real.exp (τ * ∑ i ∈ Finset.range (n + 1), Z i ω)))
    (hstep : ∀ n, ∀ᵐ ω ∂P,
      Real.exp (τ * Z n ω) * P[V (n + 1) | m n] ω ≤ Real.exp (τ * c) * V n ω)
    (hinit : (∫ ω, V 0 ω ∂P) ≤ 1) (n : ℕ) :
    (∫ ω, Real.exp (τ * ∑ i ∈ Finset.range n, Z i ω) * V n ω ∂P) ≤
      Real.exp (τ * c * n) := by
  induction n with
  | zero => simpa using hinit
  | succ n ih =>
    have hi := weighted_exp_integrable hτ hZ hbound (hV (n + 1)) (n + 1)
    have hprev := weighted_exp_integrable hτ hZ hbound (hV n) n
    have hp := condExp_mul_of_stronglyMeasurable_left (hpast n) hi (hV (n + 1))
    have hb : ∀ᵐ ω ∂P,
        P[(fun u => Real.exp (τ * ∑ i ∈ Finset.range (n + 1), Z i u) * V (n + 1) u) | m n] ω ≤
        Real.exp (τ * c) * (Real.exp (τ * ∑ i ∈ Finset.range n, Z i ω) * V n ω) := by
      filter_upwards [hp, hstep n] with ω hp hs
      simp only [Pi.mul_apply] at hp
      change P[(fun u => Real.exp (τ * ∑ i ∈ Finset.range (n + 1), Z i u) *
        V (n + 1) u) | m n] ω =
        Real.exp (τ * ∑ i ∈ Finset.range (n + 1), Z i ω) *
          P[V (n + 1) | m n] ω at hp
      rw [hp, Finset.sum_range_succ, mul_add, Real.exp_add]
      have hh := mul_le_mul_of_nonneg_left hs
        (Real.exp_pos (τ * ∑ i ∈ Finset.range n, Z i ω)).le
      nlinarith only [hh]
    have hh := integral_mono_ae integrable_condExp (hprev.const_mul (Real.exp (τ * c))) hb
    rw [integral_condExp (hm n), integral_const_mul] at hh
    calc
      _ ≤ Real.exp (τ * c) *
          (∫ ω, Real.exp (τ * ∑ i ∈ Finset.range n, Z i ω) * V n ω ∂P) := hh
      _ ≤ Real.exp (τ * c) * Real.exp (τ * c * n) :=
        mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; push_cast; ring

lemma weighted_tail {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ → MeasurableSpace Ω}
    (hm : ∀ n, m n ≤ m₀) {Z V : ℕ → Ω → ℝ} {τ G c : ℝ}
    (hτ : 0 < τ) (hZ : ∀ i, Measurable (Z i))
    (hbound : ∀ i ω, Z i ω ≤ G) (hV : ∀ i, Integrable (V i) P)
    (hVone : ∀ i ω, 1 ≤ V i ω)
    (hpast : ∀ n, StronglyMeasurable[m n]
      (fun ω => Real.exp (τ * ∑ i ∈ Finset.range (n + 1), Z i ω)))
    (hstep : ∀ n, ∀ᵐ ω ∂P,
      Real.exp (τ * Z n ω) * P[V (n + 1) | m n] ω ≤ Real.exp (τ * c) * V n ω)
    (hinit : (∫ ω, V 0 ω ∂P) ≤ 1) (n : ℕ) (u : ℝ) :
    P.real {ω | c * n + u / τ ≤ ∑ i ∈ Finset.range n, Z i ω} ≤ Real.exp (-u) := by
  have hi : Integrable (fun ω => Real.exp (τ * ∑ i ∈ Finset.range n, Z i ω)) P := by
    simpa using weighted_exp_integrable hτ.le hZ hbound
      (integrable_const (1 : ℝ)) n
  have hb := weighted_exp_integral hm hτ.le hZ hbound hV hpast hstep hinit n
  have hmono := integral_mono hi (weighted_exp_integrable hτ.le hZ hbound (hV n) n)
    (fun ω => le_mul_of_one_le_right (Real.exp_pos _).le (hVone n ω))
  have hmgf : ProbabilityTheory.mgf (fun ω => ∑ i ∈ Finset.range n, Z i ω) P τ ≤
      Real.exp (τ * c * n) := hmono.trans hb
  have ht := ProbabilityTheory.measure_ge_le_exp_mul_mgf (c * n + u / τ) hτ.le hi
  calc
    _ ≤ Real.exp (-τ * (c * n + u / τ)) *
        ProbabilityTheory.mgf (fun ω => ∑ i ∈ Finset.range n, Z i ω) P τ := ht
    _ ≤ Real.exp (-τ * (c * n + u / τ)) * Real.exp (τ * c * n) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; field_simp; ring

lemma capped_tail {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ → MeasurableSpace Ω}
    (hm : ∀ n, m n ≤ m₀) {r : ℕ → Ω → ℝ} {α s G : ℝ}
    (hα : 0 < α) (hs : 0 < s) (hG : 0 < G)
    (hr : ∀ n ω, 0 ≤ r n ω) (hrm : ∀ n, Measurable (r n))
    (hri : ∀ n, Integrable (fun ω => r n ω ^ 2) P)
    (hpast : ∀ n i, i ≤ n → StronglyMeasurable[m n] (r i))
    (hzero : ∀ ω, r 0 ω = 0)
    (hsecond : ∀ n, ∀ᵐ ω ∂P, P[(fun u => r (n + 1) u ^ 2) | m n] ω ≤
      (1 - α) * r n ω ^ 2 + α * s ^ 2) (n : ℕ) (u : ℝ) :
    P.real {ω | 5 * s * n + (4 * G / α) * u ≤
      ∑ i ∈ Finset.range n, min G (r i ω)} ≤ Real.exp (-u) := by
  let V : ℕ → Ω → ℝ := fun i ω => 1 + r i ω ^ 2 / (G * s)
  let Z : ℕ → Ω → ℝ := fun i ω => min G (r i ω)
  let τ := α / (4 * G)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hV : ∀ i, Integrable (V i) P := fun i =>
    (integrable_const 1).add ((hri i).div_const (G * s))
  have hZ : ∀ i, Measurable (Z i) := fun i => measurable_const.min (hrm i)
  have hstep : ∀ i, ∀ᵐ ω ∂P,
      Real.exp (τ * Z i ω) * P[V (i + 1) | m i] ω ≤
        Real.exp (τ * (5 * s)) * V i ω := by
    intro i
    have ha := condExp_add (μ := P) (integrable_const (1 : ℝ))
      ((hri (i + 1)).div_const (G * s)) (m i)
    have hb := condExp_smul (μ := P) (G * s)⁻¹ (fun ω => r (i + 1) ω ^ 2) (m i)
    filter_upwards [ha, hb, hsecond i] with ω ha hb hc
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, condExp_const (hm i)] at ha hb
    change P[(fun v => (G * s)⁻¹ * r (i + 1) v ^ 2) | m i] ω =
      (G * s)⁻¹ * P[(fun v => r (i + 1) v ^ 2) | m i] ω at hb
    have hv : P[V (i + 1) | m i] ω =
        1 + P[(fun v => r (i + 1) v ^ 2) | m i] ω / (G * s) := by
      have hb' : P[(fun v => r (i + 1) v ^ 2 / (G * s)) | m i] ω =
          P[(fun v => r (i + 1) v ^ 2) | m i] ω / (G * s) := by
        simpa only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using hb
      change P[(fun v => 1 + r (i + 1) v ^ 2 / (G * s)) | m i] ω = _
      change P[(fun v => 1 + r (i + 1) v ^ 2 / (G * s)) | m i] ω =
        1 + P[(fun v => r (i + 1) v ^ 2 / (G * s)) | m i] ω at ha
      exact ha.trans (congrArg (fun z : ℝ => 1 + z) hb')
    rw [hv]
    exact potential_drift (hr i ω) hs hG hα.le hc
  have hp : ∀ i, StronglyMeasurable[m i]
      (fun ω => Real.exp (τ * ∑ j ∈ Finset.range (i + 1), Z j ω)) := by
    intro i
    apply Real.continuous_exp.comp_stronglyMeasurable
    apply stronglyMeasurable_const.mul
    have hsum := Finset.stronglyMeasurable_sum (Finset.range (i + 1)) (fun j hj =>
      ((show Measurable[m i] (fun _ : Ω => G) from measurable_const).min (hpast i j
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).measurable).stronglyMeasurable)
    convert hsum using 1
    ext ω
    simp [Z]
  have hVo : ∀ i ω, 1 ≤ V i ω := by
    intro i ω
    dsimp [V]
    have hv : 0 ≤ r i ω ^ 2 / (G * s) := by positivity
    linarith
  have hh := weighted_tail hm hτ hZ (fun i ω => min_le_left G (r i ω)) hV
    hVo hp hstep
    (by simp [V, hzero]) n u
  convert hh using 1
  dsimp [τ, Z]
  congr 2
  field_simp

end LongTails.Proofs.CappedMomentum
