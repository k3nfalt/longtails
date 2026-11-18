import LongTails.Proofs.AdditiveFixedPointProcess

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.AdditiveFixedPointBatch

variable {ι : Type*} [Fintype ι] [Nonempty ι]

noncomputable def mass (x : ι → ℝ) := ∑ i, Real.exp (x i)

noncomputable def potential (x : ι → ℝ) := Real.log (mass x)

noncomputable def weight (x : ι → ℝ) (i : ι) := Real.exp (x i) / mass x

lemma mass_pos (x : ι → ℝ) : 0 < mass x :=
  Finset.sum_pos (fun i _ => Real.exp_pos (x i)) Finset.univ_nonempty

lemma weights_sum (x : ι → ℝ) : ∑ i, weight x i = 1 := by
  simp only [weight, ← Finset.sum_div]
  exact div_self (mass_pos x).ne'

omit [Nonempty ι] in
lemma potential_lower (x : ι → ℝ) (i : ι) : x i ≤ potential x := by
  rw [potential, ← Real.log_exp (x i)]
  exact Real.log_le_log (Real.exp_pos _) (Finset.single_le_sum
    (fun j _ => (Real.exp_pos (x j)).le) (Finset.mem_univ i))

lemma potential_shift (x y : ι → ℝ) : potential (x+y) ≤ potential x + ‖y‖ := by
  have h (i : ι) : Real.exp ((x+y) i) ≤ Real.exp (x i) * Real.exp ‖y‖ := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (add_le_add (le_refl _) ((le_abs_self _).trans (norm_le_pi_norm y i)))
  have hs := Real.log_le_log (mass_pos (x+y)) (Finset.sum_le_sum (fun i _ => h i))
  rw [← Finset.sum_mul] at hs
  change Real.log (mass (x+y)) ≤ Real.log (mass x * Real.exp ‖y‖) at hs
  rwa [Real.log_mul (mass_pos x).ne' (Real.exp_pos _).ne', Real.log_exp] at hs


omit [Nonempty ι] in
lemma potential_zero : potential (0 : ι → ℝ) = Real.log (Fintype.card ι) := by simp [potential, mass]

lemma potential_continuous : Continuous (potential (ι := ι)) :=
  (continuous_finsetSum _ (fun i _ => Real.continuous_exp.comp (continuous_apply i))).log
    (fun x => (mass_pos x).ne')

lemma potential_drift (x y : ι → ℝ) :
    potential (x+y) ≤ potential x + (∑ i, weight x i * y i) + 2 * ‖y‖ ^ 2 := by
  have hy (i : ι) : |y i| ≤ ‖y‖ := norm_le_pi_norm y i
  have hw (i : ι) : 0 ≤ weight x i := div_nonneg (Real.exp_pos _).le (mass_pos x).le
  by_cases h : ‖y‖ ≤ 1
  · have hterm (i : ι) : Real.exp (y i) ≤ 1 + y i + ‖y‖ ^ 2 := by
      have ht := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le ((hy i).trans h))).2
      nlinarith [sq_le_sq' (abs_le.mp (hy i)).1 (abs_le.mp (hy i)).2]
    have hrat : mass (x+y) / mass x = ∑ i, weight x i * Real.exp (y i) := by
      simp only [mass, Pi.add_apply, Real.exp_add, weight, ← Finset.sum_div,
        div_mul_eq_mul_div]
    have hlog := Real.log_le_sub_one_of_pos (div_pos (mass_pos (x+y)) (mass_pos x))
    rw [Real.log_div (mass_pos (x+y)).ne' (mass_pos x).ne', hrat] at hlog
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hw i))
    simp only [mul_add, mul_one, Finset.sum_add_distrib, ← Finset.sum_mul, weights_sum, one_mul] at hsum
    change Real.log (mass (x+y)) ≤ Real.log (mass x) + _ + _
    linarith [sq_nonneg ‖y‖]
  · have hlo := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (abs_le.mp (hy i)).1 (hw i))
    rw [← Finset.sum_mul, weights_sum, one_mul] at hlo
    nlinarith [potential_shift x y, mul_nonneg (sub_nonneg.mpr (le_of_not_ge h)) (norm_nonneg y)]

def signed (x : ι → ℝ) (i : ι × Bool) : ℝ := if i.2 then x i.1 else -x i.1

omit [Fintype ι] [Nonempty ι] in
lemma signed_add (x y : ι → ℝ) : signed (x+y) = signed x + signed y := by
  funext i
  cases i with | mk j b => cases b <;> simp [signed, add_comm]

omit [Nonempty ι] in
lemma signed_norm (x : ι → ℝ) : ‖signed x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  rintro ⟨i,b⟩
  cases b <;> simpa [signed] using norm_le_pi_norm x i

lemma norm_le_potential (x : ι → ℝ) : ‖x‖ ≤ potential (signed x) := by
  have hp (i : ι) : |x i| ≤ potential (signed x) := by
    rw [abs_le]
    constructor
    · have := potential_lower (signed x) (i,false)
      simp only [signed, Bool.false_eq_true, ↓reduceIte] at this
      linarith
    · simpa [signed] using potential_lower (signed x) (i,true)
  exact (pi_norm_le_iff_of_nonneg ((abs_nonneg _).trans (hp (Classical.arbitrary ι)))).mpr hp

omit [Fintype ι] [Nonempty ι] in
lemma signed_continuous : Continuous (signed (ι := ι)) := by
  apply continuous_pi
  rintro ⟨i,b⟩
  cases b
  · exact (continuous_apply i).neg
  · exact continuous_apply i

variable {d : ℕ} [NeZero d]
local notation "E" => Fin d → ℝ

lemma expected_step (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z => z) μ) (hz : (∫ z, z ∂μ) = 0)
    (hi2 : Integrable (fun z => ‖z‖^2) μ) (a : ℝ) (x : E) :
    Integrable (fun z => potential (signed (x + a • z))) μ ∧
    (∫ z, potential (signed (x + a • z)) ∂μ) ≤ potential (signed x) +
      2 * a^2 * (∫ z, ‖z‖^2 ∂μ) := by
  let w := weight (signed x)
  let c := fun (i : Fin d × Bool) => if i.2 then w i * a else -(w i * a)
  have hm : Measurable fun z : E => potential (signed (x + a • z)) :=
    potential_continuous.measurable.comp (signed_continuous.measurable.comp (by fun_prop))
  have hnn (z : E) : 0 ≤ potential (signed (x + a • z)) := (norm_nonneg _).trans (norm_le_potential _)
  have hpoint (z : E) : potential (signed (x + a • z)) ≤
      potential (signed x) + ∑ i, c i * z i.1 + 2 * a ^ 2 * ‖z‖^2 := by
    rw [signed_add]
    have h := potential_drift (signed x) (signed (a • z))
    have hid (i : Fin d × Bool) : weight (signed x) i * signed (a • z) i = c i * z i.1 := by
      obtain ⟨i,b⟩ := i
      cases b <;> simp [signed, c, w] <;> ring
    simp_rw [hid] at h
    apply h.trans
    apply add_le_add (le_refl _)
    have hnorm := signed_norm (a • z)
    rw [norm_smul, Real.norm_eq_abs] at hnorm
    nlinarith [sq_le_sq₀ (norm_nonneg (signed (a • z))) (mul_nonneg (abs_nonneg a) (norm_nonneg z)) |>.mpr hnorm,
      show (|a| * ‖z‖)^2 = a^2 * ‖z‖^2 by rw [mul_pow, sq_abs]]
  have hc (i : Fin d × Bool) : Integrable (fun z : E => c i * z i.1) μ := (hi.eval i.1).const_mul _
  have hb := ((integrable_const (potential (signed x))).add (integrable_finsetSum Finset.univ (fun i _ => hc i))).add
    (hi2.const_mul (2 * a^2))
  have hf := hb.mono' hm.aestronglyMeasurable (ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn z)]; exact hpoint z))
  refine ⟨hf, (integral_mono hf hb hpoint).trans_eq ?_⟩
  simp only [Pi.add_apply]
  erw [integral_add ((integrable_const (potential (signed x))).add (integrable_finsetSum Finset.univ (fun i _ => hc i)))
    (hi2.const_mul _), integral_add (integrable_const _) (integrable_finsetSum Finset.univ (fun i _ => hc i))]
  simp only [integral_const, probReal_univ, one_smul, integral_finsetSum Finset.univ (fun i _ => hc i), integral_const_mul]
  have hzero (i : Fin d) : ∫ z : E, z i ∂μ = 0 := by
    have := congrFun hz i
    rwa [eval_integral (f := fun z : E => z) (fun j => hi.eval j) i] at this
  simp [hzero]

open HeavyTailedProductProcess

lemma accumulated_potential (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z => z) μ) (hz : (∫ z, z ∂μ) = 0)
    (hi2 : Integrable (fun z => ‖z‖^2) μ) (a : ℝ) (n : ℕ) (x : E) :
    let P := Measure.infinitePi fun _ : ℕ => μ
    let step := fun (x z : E) => x + a • z
    Integrable (fun ξ => potential (signed (trajectory step n x ξ))) P ∧
    (∫ ξ, potential (signed (trajectory step n x ξ)) ∂P) ≤ potential (signed x) +
      n * (2 * a^2 * (∫ z, ‖z‖^2 ∂μ)) := by
  let P := Measure.infinitePi fun _ : ℕ => μ
  let step := fun (x z : E) => x + a • z
  let C := 2 * a^2 * (∫ z, ‖z‖^2 ∂μ)
  have hstep : Measurable step.uncurry := by unfold step; fun_prop
  induction n generalizing x with
  | zero => simp [trajectory]
  | succ n ih =>
    let F := fun z : E × (ℕ → E) => potential (signed (trajectory step n (step x z.1) z.2))
    have hF : Measurable F := potential_continuous.measurable.comp (signed_continuous.measurable.comp
      ((trajectory_measurable hstep n).comp
        (((hstep.comp measurable_prodMk_left).comp measurable_fst).prodMk measurable_snd)))
    have hfirst := expected_step μ hi hz hi2 a x
    have hb := WeakGradientConvolution.nonnegative_fiber_integral_bound hF.stronglyMeasurable
      (fun z => (norm_nonneg _).trans (norm_le_potential _))
      (ae_of_all μ (fun z => (ih (step x z)).1))
      (hfirst.1.add (integrable_const (μ := μ) ((n : ℝ)*C)))
      (ae_of_all μ (fun z => (ih (step x z)).2))
    have hpres := head_tail_preserving μ
    refine ⟨hpres.integrable_comp_of_integrable hb.1, ?_⟩
    change (∫ ξ, F (ξ 0, fun j => ξ (j+1)) ∂P) ≤ _
    have heq : (∫ ξ, F (ξ 0, fun j => ξ (j+1)) ∂P) = ∫ z, F z ∂μ.prod P := by
      have hh := integral_map (μ := P) hpres.measurable.aemeasurable hF.aestronglyMeasurable
      rw [hpres.map_eq] at hh
      exact hh.symm
    rw [heq]
    apply hb.2.trans
    simp only [Pi.add_apply, integral_add hfirst.1 (integrable_const _), integral_const,
      probReal_univ, one_smul, Nat.cast_succ]
    dsimp only [C]
    linarith [hfirst.2]

def sampleSum (n : ℕ) (ξ : ℕ → E) : E := ∑ i ∈ Finset.range n, ξ i

omit [NeZero d] in
lemma trajectory_sum (a : ℝ) (n : ℕ) (ξ : ℕ → E) :
    trajectory (fun (x z : E) => x + a • z) n 0 ξ = a • sampleSum n ξ := by
  induction n with
  | zero => simp [trajectory, sampleSum]
  | succ n ih => rw [trajectory_succ_last, ih]; simp [sampleSum, Finset.sum_range_succ, smul_add]

lemma batch_accuracy (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun z => z) μ) (hz : (∫ z, z ∂μ) = 0)
    (hi2 : Integrable (fun z => ‖z‖^2) μ) {σ τ : ℝ} (hσ : ∫ z, ‖z‖^2 ∂μ ≤ σ^2)
    (hτ : 0 < τ) {n : ℕ} (hn : 0 < n) (hb : 8 * Real.log (2*d) * σ^2 ≤ n * τ^2) :
    let P := Measure.infinitePi fun _ : ℕ => μ
    Integrable (fun ξ => ‖sampleSum n ξ‖ / n) P ∧
    (∫ ξ, ‖sampleSum n ξ‖ / n ∂P) ≤ τ := by
  let P := Measure.infinitePi fun _ : ℕ => μ
  let L := Real.log (2*d)
  have hd : (1:ℝ) ≤ d := by exact_mod_cast NeZero.one_le
  have hL : 0 < L := Real.log_pos (by linarith)
  let a := 2 * L / (n * τ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hh := accumulated_potential μ hi hz hi2 a n 0
  simp_rw [trajectory_sum] at hh
  have hiS : Integrable (fun ξ => sampleSum n ξ) P := by
    apply integrable_finsetSum
    intro i _
    have hp : MeasurePreserving (fun ξ : ℕ → E => ξ i) P μ :=
      ⟨measurable_pi_apply i, (OracleTemplate.StochasticGeneralized.infinitePi_iid μ).marginal i⟩
    exact hp.integrable_comp_of_integrable hi
  have hh' := integral_mono ((hiS.smul a).norm) hh.1 (fun ξ => norm_le_potential (a • sampleSum n ξ))
  have hzero : signed (0 : E) = 0 := by funext i; simp [signed]
  rw [hzero, potential_zero] at hh
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat] at hh
  have hsum : a * (∫ ξ, ‖sampleSum n ξ‖ ∂P) ≤ L + n * (2 * a^2 * σ^2) := by
    change (∫ ξ, ‖a • sampleSum n ξ‖ ∂P) ≤ _ at hh'
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, integral_const_mul] at hh'
    apply hh'.trans (hh.2.trans ?_)
    dsimp only [L]
    rw [mul_comm (d : ℝ) 2]
    gcongr
  refine ⟨hiS.norm.div_const _, ?_⟩
  rw [integral_div, div_le_iff₀ (by exact_mod_cast hn)]
  apply le_of_mul_le_mul_left (a := a) _ ha
  apply hsum.trans
  dsimp only [a]
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hb hL.le]

end LongTails.Proofs.AdditiveFixedPointBatch
