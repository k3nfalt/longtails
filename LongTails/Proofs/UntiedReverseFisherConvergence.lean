import LongTails.Proofs.UntiedReverseFisherExecution
import LongTails.Proofs.UntiedReverseFisherBudget
import LongTails.Proofs.SymmetricReverseFisherInitialization

open MeasureTheory OracleTemplate Set WithLp
open scoped RealInnerProductSpace

namespace LongTails.Proofs.UntiedReverseFisherConvergence

open LongTails.Setups.UntiedGaussianReverseFisher
open LongTails.Algorithms.UntiedReverseFisherGD
open LongTails.Proofs.UntiedReverseFisherLoss
open LongTails.Proofs.UntiedReverseFisherGradient
open LongTails.Proofs.UntiedReverseFisherDynamics
open LongTails.Proofs.UntiedReverseFisherBranches
open LongTails.Proofs.UntiedReverseFisherBudget
open LongTails.Proofs.UntiedReverseFisherExecution

lemma half_norm {p : Params} (μ : Means p) : ‖half μ‖ = ‖μ 0 - μ 1‖ / 2 := by
  unfold half
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  ring

lemma iterations_cast_le {d s B δ ε x : ℝ} (h : x ≤ 10 ^ 16 / max (s ^ 2) ε *
    Real.log (logArgument d B δ ε)) {n : ℕ} (hn : (n : ℝ) ≤ x) : n ≤ iterations d s B δ ε := by
  have h2 : (n : ℝ) ≤ (⌈10 ^ 16 / max (s ^ 2) ε * Real.log (logArgument d B δ ε)⌉₊ : ℝ) :=
    hn.trans (h.trans (Nat.le_ceil _))
  unfold iterations
  exact Nat.cast_le.mp h2

lemma iteration_bound_aux {M Λ : ℝ} (hM : 0 < M) (hM1 : M ≤ 1) (hΛ : 0 ≤ Λ) :
    74 * Λ ≤ 10 ^ 16 / M * Λ := by
  apply mul_le_mul_of_nonneg_right _ hΛ
  rw [le_div_iff₀ hM]; nlinarith

set_option maxHeartbeats 1000000 in
lemma oriented_success (p : Params) (hp : spec.valid p) (μ : Means p)
    (hlow : p.lower ≤ ‖μ 0 - μ 1‖) (hup : ‖μ 0 - μ 1‖ ≤ 1) (hc : ‖centre μ‖ ≤ p.centre)
    (seed : Fin p.dimension → ℝ) (e : Space p) (he : ‖e‖ = 1)
    (hb : half μ = ‖half μ‖ • e)
    (hgood : p.accuracy / 10 ^ 5 < ‖half μ‖ ^ 2 →
      p.failure / (p.dimension : ℝ) ≤ ⟪direction p seed, e⟫) :
    matchingError μ ((gdMap μ)^[iterations p.dimension p.lower p.centre p.failure p.accuracy]
      (initial p seed)) ≤ p.accuracy := by
  rcases hp with ⟨hB, hs, -, hε, hε1, hδ, hδ1⟩
  have hd : 1 ≤ (p.dimension : ℝ) := by exact_mod_cast p.dimension.pos
  set a := ‖half μ‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have ha1 : a ≤ 1 / 2 := by rw [ha, half_norm]; linarith
  have hsa : p.lower ≤ 2 * a := by rw [ha, half_norm]; linarith
  set K := iterations p.dimension p.lower p.centre p.failure p.accuracy with hK
  set q := LongTails.Proofs.UntiedReverseFisherGradient.tiedParams p
  set y : ℕ → SSpace q × SSpace q :=
    fun k => (pairStep (q := q) (a • e))^[k] (coordinates μ (initial p seed)) with hydef
  have hy : ∀ k, y (k + 1) = pairStep (a • e) (y k) := fun k => Function.iterate_succ_apply' _ _ _
  set out := (gdMap μ)^[K] (initial p seed)
  have hyK : coordinates μ out = y K := by
    simp only [out, hydef]
    rw [coordinates_iterate, ← hb]
  have h0 := initial_coordinates μ seed
  have hv0 : ‖(y 0).2‖ = 1 := by
    simp only [hydef, Function.iterate_zero, id, h0]; exact direction_norm p seed
  have hw0 : ‖(y 0).1‖ ≤ p.centre := by
    simp only [hydef, Function.iterate_zero, id, h0]; exact (le_of_eq (norm_neg _)).trans hc
  have hme := matchingError_le μ out
  have hc1 : centre out - centre μ = (y K).1 := congrArg Prod.fst hyK
  have hc2 : half out = (y K).2 := congrArg Prod.snd hyK
  rw [hc1, hc2, hb] at hme
  have hΛ := log_main_ge hd hB hδ hδ1 hε hε1
  have hMpos : 0 < max (p.lower ^ 2) p.accuracy := lt_of_lt_of_le hε (le_max_right _ _)
  have hM1 : max (p.lower ^ 2) p.accuracy ≤ 1 := by
    apply max_le _ hε1; nlinarith [mul_self_le_mul_self hs hsa]
  have hcen : ‖(y K).1‖ ^ 2 ≤ p.accuracy / 4 :=
    centre_final he ha0 ha1 hy hB hε hw0 (k := K) (iterations_cast_le
      ((centre_le hd hB hδ hδ1 hε hε1).trans (iteration_bound_aux hMpos hM1 (by linarith)))
      le_rfl)
  by_cases hsmall : a ^ 2 ≤ p.accuracy / 10 ^ 5
  · have hv := small_branch he ha0 ha1 hy hε hε1 hsmall hv0 (k := K)
      (iterations_cast_le (small_le hd hB hδ hδ1 hε hε1 hs hsa hsmall) le_rfl)
    have key := add_le_add (mul_le_mul_of_nonneg_left hcen (by norm_num : (0:ℝ) ≤ 2))
      (mul_le_mul_of_nonneg_left hv (by norm_num : (0:ℝ) ≤ 2))
    exact hme.trans (key.trans (by linarith))
  · push Not at hsmall
    have hu := hgood hsmall
    have hapos : 0 < a := by
      by_contra h; push Not at h
      have : a = 0 := le_antisymm h ha0
      rw [this] at hsmall; nlinarith
    have hu0 : 0 < p.failure / (p.dimension : ℝ) := by positivity
    have hu01 : p.failure / (p.dimension : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hU0 : p.failure / (p.dimension : ℝ) ≤ ⟪(y 0).2, e⟫ := by
      simp only [hydef, Function.iterate_zero, id, h0]; exact hu
    have hv := positive_branch he hapos ha1 hy hε hu0 hu01 hB hv0 hw0 hU0 (k := K)
      (iterations_cast_le (positive_le hd hB hδ hδ1 hε hε1 hs hsa ha1 hsmall) le_rfl)
    have key := add_le_add (mul_le_mul_of_nonneg_left hcen (by norm_num : (0:ℝ) ≤ 2))
      (mul_le_mul_of_nonneg_left hv (by norm_num : (0:ℝ) ≤ 2))
    exact hme.trans (key.trans (by linarith))

lemma iterate_success (p : Params) (hp : spec.valid p) (μ : Means p)
    (hlow : p.lower ≤ ‖μ 0 - μ 1‖) (hup : ‖μ 0 - μ 1‖ ≤ 1) (hc : ‖centre μ‖ ≤ p.centre)
    (seed : Fin p.dimension → ℝ) (e : Space p) (he : ‖e‖ = 1)
    (hb : half μ = ‖half μ‖ • e)
    (hgood : p.accuracy / 10 ^ 5 < ‖half μ‖ ^ 2 →
      p.failure / (p.dimension : ℝ) ≤ |⟪direction p seed, e⟫|) :
    matchingError μ ((gdMap μ)^[iterations p.dimension p.lower p.centre p.failure p.accuracy]
      (initial p seed)) ≤ p.accuracy := by
  by_cases hpos : 0 ≤ ⟪direction p seed, e⟫
  · exact oriented_success p hp μ hlow hup hc seed e he hb
      (fun h => (hgood h).trans (le_of_eq (abs_of_nonneg hpos)))
  · push Not at hpos
    have hsw := oriented_success p hp (swapMeans μ)
      (by rw [swap_zero, swap_one, norm_sub_rev]; exact hlow)
      (by rw [swap_zero, swap_one, norm_sub_rev]; exact hup)
      (by rw [centre_swap]; exact hc) seed (-e) (by rw [norm_neg, he])
      (by rw [half_swap, norm_neg, hb, smul_neg, norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_norm])
      (fun h => by
        rw [half_swap, norm_neg] at h
        rw [inner_neg_right]
        exact (hgood h).trans (le_of_eq (abs_of_neg hpos)))
    rw [matchingError_swap, gdMap_swap] at hsw
    exact hsw

lemma exists_unit (p : Params) : ∃ e : Space p, ‖e‖ = 1 :=
  ⟨EuclideanSpace.single ⟨0, p.dimension.pos⟩ 1, by simp⟩

theorem output_success (p : Params) (hp : spec.valid p) (μ : Means p)
    (oracle : Oracle (Means p) (Means p)) (ho : spec.admissible p μ oracle) :
    spec.successful p μ
      (fun z : (algorithm p).Seed × ((k : ℕ) → oracle.Seed k) =>
        output p oracle (iterations p.dimension p.lower p.centre p.failure p.accuracy) z.1 z.2)
      ⟨((algorithm p).law : Measure _).prod (oracle.law : Measure _), inferInstance⟩ := by
  rcases ho with ⟨hlow, hup, hc, horacle⟩
  have hc' : ‖centre μ‖ ≤ p.centre := hc
  set K := iterations p.dimension p.lower p.centre p.failure p.accuracy
  refine ⟨output_measurable p μ oracle horacle K, ?_⟩
  change ENNReal.ofReal (1 - p.failure) ≤
    ((Measure.pi (fun _ : Fin p.dimension =>
      (LongTails.Algorithms.SymmetricReverseFisherGD.coordinateLaw : Measure ℝ))).prod
        (oracle.law : Measure _))
      {z | matchingError μ (output p oracle K z.1 z.2) ≤ p.accuracy}
  obtain ⟨e, he, hb⟩ : ∃ e : Space p, ‖e‖ = 1 ∧ half μ = ‖half μ‖ • e := by
    by_cases h0 : half μ = 0
    · obtain ⟨e, he⟩ := exists_unit p
      exact ⟨e, he, by rw [h0, norm_zero, zero_smul]⟩
    · refine ⟨‖half μ‖⁻¹ • half μ, ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]
      · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h0), one_smul]
  let S : Set (Fin p.dimension → ℝ) :=
    {z | p.failure / (p.dimension : ℝ) ≤ |⟪direction p z, e⟫|}
  have hsubset : S ×ˢ (univ : Set ((k : ℕ) → oracle.Seed k)) ⊆
      {z | matchingError μ (output p oracle K z.1 z.2) ≤ p.accuracy} := by
    rintro ⟨z, ξ⟩ ⟨hz, _⟩
    rw [mem_ofPred_eq, output_eq_iterate p μ oracle horacle K]
    exact iterate_success p hp μ hlow hup hc' z e he hb (fun _ => hz)
  have hm := measure_mono (μ := (Measure.pi (fun _ : Fin p.dimension =>
    (LongTails.Algorithms.SymmetricReverseFisherGD.coordinateLaw : Measure ℝ))).prod
      (oracle.law : Measure _)) hsubset
  rw [Measure.prod_prod, measure_univ, mul_one] at hm
  have hδ : 0 < p.failure := hp.2.2.2.2.2.1
  exact (LongTails.Proofs.SymmetricReverseFisherInitialization.initial_projection_probability
    (p := LongTails.Algorithms.UntiedReverseFisherGD.tiedParams p) e he hδ).trans hm

end LongTails.Proofs.UntiedReverseFisherConvergence
