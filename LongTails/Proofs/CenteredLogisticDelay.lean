import LongTails.Proofs.CenteredLogisticSlowTrajectory
import LongTails.Proofs.CenteredLogisticComparison

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CenteredLogisticDelay

open LongTails.Setups.CenteredLogisticClassification
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift margin)
open LongTails.Setups.ManySampleConvolutionalPerceptron (Space)
open CenteredLogisticGeometry CenteredLogisticPairs CenteredLogisticComparison
open CenteredLogisticSteps CenteredLogisticSlowDynamics CenteredLogisticSlowTrajectory

variable {n : ℕ+} {d : ℕ}

noncomputable def level (μ : ℝ) (i : Fin ((n : ℕ) + n)) := label i * (1 + μ / 2) - μ / 2

lemma sample_components (e : Features d) (u : Fin n → Features d) (μ : ℝ)
    (i : Fin ((n : ℕ) + n)) :
    samples e u μ i = level μ i • e + μ • duplicate u i := by
  change (label i * (1 + μ / 2)) • e + duplicate (offset e u μ) i = _
  unfold offset
  rw [dup_apply u (fun z => μ • (z - (1 / 2 : ℝ) • e)) i]
  unfold level
  module

lemma level_range {μ : ℝ} (hμ : 0 < μ) (i : Fin ((n : ℕ) + n)) :
    1 ≤ |level μ i| ∧ |level μ i| ≤ 1 + μ := by
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j <;> simp only [level, label, at_pair, Sum.elim_inl, Sum.elim_inr] <;>
    rw [abs_le] <;> constructor <;> first | constructor <;> linarith | exact le_abs_self _ | exact le_trans (by linarith) (neg_le_abs _) | simp

lemma level_mean (μ : ℝ) : (𝔼 i : Fin ((n : ℕ) + n), level μ i) = -μ / 2 := by
  simp only [level, Finset.expect_sub_distrib, ← Finset.expect_mul, label_balance,
    Fintype.expect_const, zero_mul, zero_sub, neg_div]

lemma scale_bounds (e : Features d) (u : Fin n → Features d) {μ : ℝ}
    (he : ‖e‖ = 1) (hc : ∀ j, ⟪e,u j⟫ = 0) (hu : ∀ j, ‖u j‖ ≤ 2 / 3)
    (hμ : 0 < μ) (G : Geometry (params d n) (samples e u μ)) :
    1 ≤ G.R ∧ G.R ≤ 1 + 2 * μ := by
  let D := samples e u μ
  have henergy : (𝔼 i, ‖D i‖ ^ 2) = G.R ^ 2 := by
    change (𝔼 i, ‖samples e u μ i‖ ^ 2) = _
    simp_rw [row_scale G, norm_smul, Real.norm_eq_abs, abs_of_pos G.scale_pos, mul_pow]
    rw [← Finset.mul_expect, row_energy G, mul_one]
  have hnorm (i : Fin ((n : ℕ) + n)) : 1 ≤ ‖D i‖ ∧ ‖D i‖ ≤ 1 + 2 * μ := by
    have hx := bounds_pair (P := fun v => ‖v‖ ≤ 2 / 3) u hu i
    have ho := bounds_pair (P := fun v => ⟪e,v⟫ = 0) u hc i
    have hp := abs_real_inner_le_norm e (D i)
    change |⟪e,samples e u μ i⟫| ≤ ‖e‖ * ‖D i‖ at hp
    rw [sample_components, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, he, one_pow, mul_one, ho, mul_zero, add_zero, one_mul] at hp
    refine ⟨(level_range hμ i).1.trans hp, ?_⟩
    change ‖samples e u μ i‖ ≤ _
    rw [sample_components]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, he, mul_one, abs_of_pos hμ]
    linarith [(level_range hμ i).2, mul_le_mul_of_nonneg_left hx hμ.le]
  have hl : 1 ≤ 𝔼 i, ‖D i‖ ^ 2 := Finset.le_expect Finset.univ_nonempty
    (fun i _ => by nlinarith [(hnorm i).1, sq_nonneg (‖D i‖ - 1)])
  have hh : (𝔼 i, ‖D i‖ ^ 2) ≤ (1 + 2 * μ) ^ 2 := Finset.expect_le Finset.univ_nonempty
    (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hnorm i).2 _)
  rw [henergy] at hl hh
  constructor <;> nlinarith [G.scale_pos]

noncomputable def slowCloud (e : Features d) (u : Fin n → Features d) {μ : ℝ}
    (he : ‖e‖ = 1) (hfix : shift e = e) (hc : ∀ j, ⟪e,u j⟫ = 0) (hu : ∀ j, ‖u j‖ ≤ 2 / 3)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 64) (G : Geometry (params d n) (samples e u μ)) :
    Cloud (params d n) (fun i => G.R⁻¹ • samples e u μ i) (μ / G.R) := by
  have hR := scale_bounds e u he hc hu hμ G
  have hr := G.scale_pos
  let A (i : Fin ((n : ℕ) + n)) := level μ i / G.R
  have hA (i : Fin ((n : ℕ) + n)) : 7 / 8 ≤ |A i| ∧ |A i| ≤ 9 / 8 := by
    dsimp only [A]
    rw [abs_div, abs_of_pos hr]
    exact ⟨(le_div_iff₀ hr).mpr (by linarith [(level_range hμ i).1, hR.2]),
      (div_le_iff₀ hr).mpr (by linarith [(level_range hμ i).2, hR.1])⟩
  refine ⟨e,A,duplicate u,he,hfix,fun i => bounds_pair (P := fun v => ⟪e,v⟫ = 0) u hc i,
    fun i => (bounds_pair (P := fun v => ‖v‖ ≤ 2 / 3) u hu i).trans (by norm_num),
    fun i => (hA i).2, ?_, ?_, ?_, ?_, ?_⟩
  · change (𝔼 i : Fin ((n : ℕ) + n), level μ i / G.R) = _
    rw [← Finset.expect_div, level_mean]; ring
  · apply Finset.le_expect Finset.univ_nonempty
    intro i _
    have h := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 7 / 8) (hA i).1
    nlinarith [sq_abs (A i)]
  · apply Finset.expect_le Finset.univ_nonempty
    intro i _
    have h := mul_self_le_mul_self (abs_nonneg _) (hA i).2
    nlinarith [sq_abs (A i)]
  · refine ⟨finSumFinEquiv (Sum.inl (⟨0,n.pos⟩ : Fin n)), ?_⟩
    change 3 / 4 ≤ (label (finSumFinEquiv (Sum.inl (⟨0,n.pos⟩ : Fin n))) * (1 + μ / 2) - μ / 2) / G.R
    simp only [label, at_pair, Sum.elim_inl, one_mul]
    apply (le_div_iff₀ hr).mpr
    linarith [hR.2]
  · intro i
    change Fin ((n : ℕ) + n) at i
    rw [sample_components, smul_add, smul_smul, smul_smul]
    simp [A, div_eq_inv_mul]

lemma physical_delay (e : Features d) (u : Fin n → Features d) {μ η : ℝ}
    (he : ‖e‖ = 1) (hfix : shift e = e) (hc : ∀ j, ⟪e,u j⟫ = 0) (hu : ∀ j, ‖u j‖ ≤ 2 / 3)
    (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 64) (G : Geometry (params d n) (samples e u μ))
    (hη : 1 ≤ η) (hη' : η ≤ 2) (t : ℕ) (ht : (t : ℝ) * μ ≤ 1 / 2048) :
    let D := samples e u μ
    ∃ i, margin .conv d (D i) ((step D (η / G.R))^[t] ((Real.sqrt G.R)⁻¹ • initialPoint d)) ≤ 0 := by
  let X (i : Fin ((n : ℕ) + n)) := G.R⁻¹ • samples e u μ i
  have hr := G.scale_pos
  have hs := Real.sq_sqrt hr.le
  have hR := (scale_bounds e u he hc hu hμ G).1
  have hβ : μ / G.R ≤ μ := (div_le_iff₀ hr).mpr (by nlinarith [mul_le_mul_of_nonneg_left hR hμ.le])
  have hfail := slow_failure (slowCloud e u he hfix hc hu hμ hμ1 G) (div_pos hμ hr)
    (hβ.trans hμ1) hη hη' t ((mul_le_mul_of_nonneg_left hβ (Nat.cast_nonneg t)).trans ht)
  obtain ⟨i,hi⟩ := hfail
  refine ⟨i,?_⟩
  have hrow (j : Fin ((n : ℕ) + n)) : samples e u μ j = (Real.sqrt G.R) ^ 2 • X j := by
    dsimp only [X]
    rw [hs, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hstep (θ : Space d) : step (samples e u μ) (η / G.R) ((Real.sqrt G.R)⁻¹ • θ) =
      (Real.sqrt G.R)⁻¹ • step (p := params d n) X η θ :=
    (congrArg₂ (fun Z s => step (p := params d n) Z s ((Real.sqrt G.R)⁻¹ • θ)) (funext hrow)
      (show η / G.R = η / (Real.sqrt G.R) ^ 2 by rw [hs])).trans (scaled_step _ _ η (Real.sqrt_pos.mpr hr))
  have hiter (k : ℕ) : (step (samples e u μ) (η / G.R))^[k] ((Real.sqrt G.R)⁻¹ • initialPoint d) =
      (Real.sqrt G.R)⁻¹ • (step (p := params d n) X η)^[k] (initialPoint d) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hstep]
  dsimp only
  rw [hiter, hrow i, margin_scale, ← mul_pow, mul_inv_cancel₀ (Real.sqrt_pos.mpr hr).ne', one_pow, one_mul]
  exact hi

end LongTails.Proofs.CenteredLogisticDelay
