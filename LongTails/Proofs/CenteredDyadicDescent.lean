import LongTails.Proofs.CenteredDyadicMoments
import LongTails.Proofs.DyadicHolderDescent

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.CenteredDyadic

open OracleTemplate.NormalizedStorm OracleTemplate.DyadicHolder

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {F : E → ℝ} {g : E → Ω → E} {L M ν σ : ℝ}

local notation "P" => Measure.infinitePi fun _ : ℕ => p

omit [SecondCountableTopology E] in
lemma Hyp.descent (H : Hyp p F g L M ν σ) {η : ℝ} (hη : 0 ≤ η) (x d : E) :
    F (stormStep η x d) ≤ F x - η * ‖gradient F x‖ + 2 * η * ‖d - gradient F x‖ +
      L / 2 * η ^ 2 := by
  have H0 : OracleTemplate.DyadicHolder.Hyp p F (fun x _ => gradient F x) L (L ^ 2) 1 0 :=
    { grad := H.grad
      lip := H.lip
      meas := H.grad_continuous.measurable.comp measurable_fst
      int := fun _ => integrable_const _
      mean := fun _ => by simp
      var_int := fun _ => by simp
      var := fun _ => by simp
      diff_int := fun _ _ => integrable_const _
      msh := fun x y => by
        have h := pow_le_pow_left₀ (norm_nonneg _) (H.lip x y) 2
        simpa [mul_pow, Real.rpow_two] using h
      L_pos := H.L_pos
      M_nn := sq_nonneg _
      ν_pos := zero_lt_one }
  exact H0.descent hη x d

omit [SecondCountableTopology E] in
lemma Hyp.path_sum (H : Hyp p F g L M ν σ) (cfg : DyadicConfig) (x0 : E) (hη : 0 ≤ cfg.η)
    {Δ : ℝ} (hgap : ∀ x, F x0 - F x ≤ Δ) (ξ : ℕ → Ω) (n : ℕ) :
    cfg.η * ∑ k ∈ Finset.range n, ‖gradient F (X cfg g x0 0 ξ k)‖ ≤
      Δ + ∑ k ∈ Finset.range n, (2 * cfg.η * ‖err cfg g F x0 ξ k‖ + L / 2 * cfg.η ^ 2) := by
  have hstep : ∀ m, F (X cfg g x0 0 ξ m) + cfg.η * ∑ k ∈ Finset.range m,
      ‖gradient F (X cfg g x0 0 ξ k)‖ ≤
      F x0 + ∑ k ∈ Finset.range m, (2 * cfg.η * ‖err cfg g F x0 ξ k‖ + L / 2 * cfg.η ^ 2) := by
    intro m
    induction m with
    | zero => simp [X_zero]
    | succ m ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, X_succ]
        have hd := H.descent hη (X cfg g x0 0 ξ m) (D cfg g x0 0 ξ m)
        simp only [err] at ih ⊢
        nlinarith
  have := hstep n
  have := hgap (X cfg g x0 0 ξ n)
  linarith

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma Hyp.grad_bound (H : Hyp p F g L M ν σ) (cfg : DyadicConfig) (x0 : E) (hη : 0 ≤ cfg.η)
    (ξ : ℕ → Ω) (k : ℕ) :
    ‖gradient F (X cfg g x0 0 ξ k)‖ ≤ ‖gradient F x0‖ + L * (k * cfg.η) := by
  have h1 := H.lip (X cfg g x0 0 ξ k) x0
  have h2 := X_dist (cfg := cfg) (g := g) (x0 := x0) (τ := 0) (ξ := ξ) hη 0 k
  simp only [zero_add, X_zero] at h2
  have h3 : ‖gradient F (X cfg g x0 0 ξ k)‖ ≤ ‖gradient F x0‖ +
      ‖gradient F (X cfg g x0 0 ξ k) - gradient F x0‖ := by
    have := norm_sub_norm_le (gradient F (X cfg g x0 0 ξ k)) (gradient F x0)
    linarith
  have := H.L_pos
  nlinarith

lemma Hyp.integrable_grad (H : Hyp p F g L M ν σ) (cfg : DyadicConfig) (x0 : E) (hη : 0 ≤ cfg.η)
    (k : ℕ) : Integrable (fun ξ : ℕ → Ω => ‖gradient F (X cfg g x0 0 ξ k)‖) P := by
  refine Integrable.of_bound (C := ‖gradient F x0‖ + L * (k * cfg.η))
    ((H.grad_continuous.measurable.comp (measurable_X H.meas x0 0 k)).norm.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact H.grad_bound cfg x0 hη ξ k

lemma Hyp.master_lintegral (H : Hyp p F g L M ν σ) (cfg : DyadicConfig) (x0 : E)
    (hη : 0 < cfg.η) (hbA : 1 ≤ cfg.bA) (hb : ∀ j, 1 ≤ cfg.b j) {β V Δ ε : ℝ}
    (hβ : ∀ j, j < cfg.J → M * (2 ^ j * cfg.η) ^ (2 * ν) / cfg.b j ≤ β)
    (hV : σ ^ 2 / cfg.bA + β * cfg.J ≤ V) (hgap : ∀ x, F x0 - F x ≤ Δ)
    (hacc : Δ / (cfg.η * (cfg.K + 1)) + 2 * Real.sqrt V + L / 2 * cfg.η ≤ ε) :
    ∫⁻ ω, ENNReal.ofReal ‖gradient F (X cfg g x0 0 ω.2 ω.1.val)‖
      ∂((PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure.prod P) ≤ ENNReal.ofReal ε := by
  set K := cfg.K
  set η := cfg.η
  have herr : ∀ k, Integrable (fun ξ => ‖err cfg g F x0 ξ k‖) P ∧
      ∫ ξ, ‖err cfg g F x0 ξ k‖ ∂P ≤ Real.sqrt V := by
    intro k
    obtain ⟨hI, hle⟩ := H.err_moment cfg x0 hη.le hbA hb hβ k
    have hm := (H.measurable_err cfg x0 k).aestronglyMeasurable (μ := P)
    have hL2 : MemLp (fun ξ => err cfg g F x0 ξ k) 2 P :=
      (TwoSidedPL.memLp_two_iff_sq hm).mpr hI
    refine ⟨hL2.integrable one_le_two |>.norm, ?_⟩
    refine (integral_norm_le_sqrt hm hI).trans (Real.sqrt_le_sqrt ?_)
    refine hle.trans (le_trans ?_ hV)
    have hβ0 : ∀ j, j < cfg.J → 0 ≤ β := fun j hj =>
      le_trans (by have := H.M_nn; positivity) (hβ j hj)
    split_ifs with hk
    · rcases Nat.eq_zero_or_pos cfg.J with h0 | h0
      · simp [h0]
      · have := hβ0 0 h0
        have : 0 ≤ β * cfg.J := mul_nonneg this (Nat.cast_nonneg _)
        linarith
    · have hl := cfg.level_lt hk
      have := hβ0 _ hl
      have : (0 : ℝ) ≤ (cfg.level k : ℝ) := Nat.cast_nonneg _
      nlinarith
  have hgi := fun k => H.integrable_grad (p := p) cfg x0 hη.le k
  have hsum : η * ∑ k ∈ Finset.range (K + 1), ∫ ξ, ‖gradient F (X cfg g x0 0 ξ k)‖ ∂P ≤
      Δ + (K + 1) * (2 * η * Real.sqrt V + L / 2 * η ^ 2) := by
    have hpath := fun ξ => H.path_sum cfg x0 hη.le hgap ξ (K + 1)
    set f : ℕ → (ℕ → Ω) → ℝ := fun k ξ => 2 * cfg.η * ‖err cfg g F x0 ξ k‖ + L / 2 * cfg.η ^ 2
    have hfi : ∀ k ∈ Finset.range (K + 1), Integrable (f k) P :=
      fun k _ => ((herr k).1.const_mul _).add (integrable_const _)
    have hint1 : Integrable (fun ξ => cfg.η * ∑ k ∈ Finset.range (K + 1),
        ‖gradient F (X cfg g x0 0 ξ k)‖) P :=
      (integrable_finsetSum (Finset.range (K + 1))
        (f := fun k ξ => ‖gradient F (X cfg g x0 0 ξ k)‖) fun k _ => hgi k).const_mul _
    have hS : Integrable (fun ξ => ∑ k ∈ Finset.range (K + 1), f k ξ) P :=
      integrable_finsetSum (Finset.range (K + 1)) hfi
    have hint2 : Integrable (fun ξ => Δ + ∑ k ∈ Finset.range (K + 1), f k ξ) P :=
      (integrable_const _).add hS
    have hmono := integral_mono hint1 hint2 hpath
    rw [integral_const_mul, integral_finsetSum (Finset.range (K + 1))
      (f := fun k ξ => ‖gradient F (X cfg g x0 0 ξ k)‖) fun k _ => hgi k] at hmono
    rw [integral_add (integrable_const _) hS, integral_const,
      integral_finsetSum (Finset.range (K + 1)) hfi] at hmono
    simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
    have hterm : ∀ k ∈ Finset.range (K + 1), ∫ ξ, f k ξ ∂P ≤
        2 * η * Real.sqrt V + L / 2 * η ^ 2 := by
      intro k _
      simp only [f]
      rw [integral_add ((herr k).1.const_mul _) (integrable_const _), integral_const_mul,
        integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      have := (herr k).2
      have : 0 ≤ 2 * η := by linarith
      nlinarith
    have := Finset.sum_le_sum hterm
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    push_cast at this
    linarith
  set Q := Measure.infinitePi fun _ : ℕ => p
  have hm : Measurable (fun ω : Fin (K + 1) × (ℕ → Ω) =>
      ENNReal.ofReal ‖gradient F (X cfg g x0 0 ω.2 ω.1.val)‖) :=
    ENNReal.measurable_ofReal.comp ((H.grad_continuous.measurable.comp
      (measurable_from_prod_countable_right fun τ => measurable_X H.meas x0 0 τ.val)).norm)
  rw [lintegral_prod _ hm.aemeasurable, lintegral_fintype]
  simp only [PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _), Fintype.card_fin]
  have hc : ∀ τ : Fin (K + 1), (Fintype.card ({τ} : Set (Fin (K + 1))) : ℝ≥0∞) = 1 := by
    intro τ; simp
  simp only [hc, one_div]
  have hj : ∀ τ : Fin (K + 1), ∫⁻ ξ, ENNReal.ofReal ‖gradient F (X cfg g x0 0 ξ τ.val)‖ ∂Q =
      ENNReal.ofReal (∫ ξ, ‖gradient F (X cfg g x0 0 ξ τ.val)‖ ∂Q) := by
    intro τ
    rw [ofReal_integral_eq_lintegral_ofReal (hgi τ.val)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
  simp_rw [hj]
  rw [← Finset.sum_mul,
    ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg fun _ => norm_nonneg _)]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∫ ξ, ‖gradient F (X cfg g x0 0 ξ k)‖ ∂Q)]
  have hT : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hbound : ∑ k ∈ Finset.range (K + 1), ∫ ξ, ‖gradient F (X cfg g x0 0 ξ k)‖ ∂Q ≤
      ((K : ℝ) + 1) * ε := by
    have h2 : Δ + (K + 1) * (2 * η * Real.sqrt V + L / 2 * η ^ 2) ≤ η * (((K : ℝ) + 1) * ε) := by
      have hηK : 0 < η * ((K : ℝ) + 1) := by positivity
      have := mul_le_mul_of_nonneg_left hacc hηK.le
      rw [mul_add, mul_add, mul_div_cancel₀ _ hηK.ne'] at this
      nlinarith
    exact le_of_mul_le_mul_left (hsum.trans h2) hη
  have hinv : (((K + 1 : ℕ) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / ((K : ℝ) + 1)) := by
    rw [ENNReal.ofReal_div_of_pos hT, ENNReal.ofReal_one, one_div]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]
    simp
  rw [hinv,
    ← ENNReal.ofReal_mul (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_one_div, div_le_iff₀ hT]
  linarith

end OracleTemplate.CenteredDyadic
