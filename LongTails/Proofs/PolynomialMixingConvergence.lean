import LongTails.Proofs.PolynomialMixingAmplification
import LongTails.Proofs.PolynomialMixingSampling

open MeasureTheory

namespace LongTails.Proofs.PolynomialMixingConvergence

open LongTails.Setups.PolynomialMixingSubgradient LongTails.Algorithms.PolynomialMixingSelection
open LongTails.Proofs.PolynomialMixingTraining LongTails.Proofs.PolynomialMixingAccuracy
open LongTails.Proofs.PolynomialMixingExecution LongTails.Proofs.PolynomialMixingSelectionLaw
open LongTails.Proofs.PolynomialMixingBlocks PolynomialMixingBudget PolynomialMixingAmplification
open PolynomialMixingSampling OracleTemplate

lemma observations_measurable (c : Schedule) : Measurable (observations c) :=
  Measurable.of_eval fun _ => Measurable.of_eval fun _ => measurable_slice _ _

lemma bad_output (q : Params) (hp : spec.valid q) (P : ProbabilityMeasure Path)
    (hr : AbsolutelyRegular P q.τ q.β) {g : Point q → ℝ → Space q} {f : Space q → ℝ}
    (h : SubgradientOracle q f g ((P : Measure Path).map (fun z => z 0)))
    (hc : ConvexOn ℝ (Domain q) f) (u : Point q) :
    (P : Measure Path).real {z | q.ε < f (selected g (schedule q) (observations (schedule q) z)).val - f u.val} ≤ q.δ := by
  obtain ⟨_, hR, hG, hp1, hp2, hβ, hτ, hε, _, hd, hd'⟩ := hp
  let c := schedule q
  let π := (P : Measure Path).map (fun z => z 0)
  let : IsProbabilityMeasure π := (Measure.isProbabilityMeasure_map_iff
    (measurable_pi_apply 0).aemeasurable).mpr inferInstance
  let I := Measure.infinitePi (fun _ : ℕ => π)
  let Q := blockLaw P c
  have hn : (32768 * (q.G * q.R) / q.ε) ^ (q.p / (q.p - 1)) ≤ c.samples := by
    rw [← mul_assoc]; exact Nat.le_ceil _
  obtain ⟨hn', _⟩ := sample_tuning (mul_pos hG hR) hε hp1 hn
  obtain ⟨_, hk, _, ht⟩ := trial_bounds hd hd'
  change 0 < c.trials at hk
  change ((c.trials : ℝ) + 1) * (1/2 : ℝ)^c.trials ≤ q.δ/2 at ht
  have hn1 : (1 : ℝ) ≤ c.samples := by exact_mod_cast hn'
  have hτ' : 0 < q.τ := by linarith
  have hini : q.τ * (256 * (c.samples : ℝ)) ^ (1 / q.β) ≤ c.innerSkip := Nat.le_ceil _
  have hs := bridge (show 1 ≤ 256 * (c.samples : ℝ) by linarith) hτ' hβ
    (t := c.innerSkip+1) (by push_cast; linarith)
  have hsmall : c.samples * (1 + ((c.innerSkip+1 : ℕ) : ℝ) / q.τ) ^ (-q.β) ≤ 1 / 256 := by
    apply (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg c.samples)).trans
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (by positivity : (c.samples : ℝ) ≠ 0)]; norm_num
  have hf := measurable_objective (π := π) h hp1 hG.le
  have htransfer (A : Set Path) (hA : MeasurableSet A) (he : (trim c.samples) ⁻¹' A = A) :
      (Q : Measure Path).real A ≤ I.real A + 1/256 := by
    have hh := (abs_le.mp (inner_transfer P c hr A hA)).2
    rw [map_measureReal_apply (measurable_trim _) hA, he] at hh
    change (Q : Measure Path).real A - I.real A ≤ _ at hh
    linarith
  have ha : (Q : Measure Path).real {w | q.ε/2 < f (average g c.samples w).val - f u.val} ≤ 1/16 := by
    have h₁ := htransfer {w | q.ε/2 < f (average g c.samples w).val - f u.val} (measurableSet_lt measurable_const ((hf.comp (measurable_average h.measurable c.samples)).sub_const _))
      (by ext w; simp only [Set.mem_preimage, Set.mem_ofPred_eq, average_trim])
    have h₂ := iid_train (π := π) h hc hR hG hp1 hp2 hε u _ hn
    change I.real _ ≤ _ at h₂
    linarith
  have hv (x : Point q) : (Q : Measure Path).real {w | q.ε/12 < |score g x c.samples w - (f x.val - f 0)|} ≤ 1/16 := by
    have hm : Measurable (score g x c.samples) := measurable_score_at (q := q) (g := g) h.measurable c.samples x
    have h₁ := htransfer {w | q.ε/12 < |score g x c.samples w - (f x.val - f 0)|} (measurableSet_lt measurable_const (continuous_abs.measurable.comp (hm.sub_const _)))
      (by ext w; simp only [Set.mem_preimage, Set.mem_ofPred_eq, score_trim])
    have h₂ := iid_score (π := π) h hR hG hp1 hp2 hε x _ hn
    change I.real _ ≤ _ at h₂
    linarith
  let A := {v | q.ε < f (selected g c v).val - f u.val}
  have hA : MeasurableSet A := measurableSet_lt measurable_const ((hf.comp (measurable_selected h.measurable _)).sub_const _)
  have hprod := amplified (Q : Measure Path) c u h.measurable hf hk ha hv
  have houter := (abs_le.mp (outer_transfer P c hr A hA)).2
  have hm : Measurable (fun z i j => trim c.samples (observations c z i j)) :=
    Measurable.of_eval fun _ => Measurable.of_eval fun _ => (measurable_trim _).comp (measurable_slice _ _)
  rw [map_measureReal_apply hm hA] at houter
  have he : (fun z i j => trim c.samples (observations c z i j)) ⁻¹' A =
      {z | q.ε < f (selected g c (observations c z)).val - f u.val} := by
    ext z; simp only [A, Set.mem_preimage, Set.mem_ofPred_eq, selected_trim]
  rw [he] at houter
  let J := (c.trials : ℝ) * (c.trials+1)
  have hk1 : (1 : ℝ) ≤ c.trials := by exact_mod_cast hk
  have hJ : 1 ≤ J := by dsimp [J]; nlinarith
  have ho : q.τ * (4 * J / q.δ) ^ (1 / q.β) ≤ c.outerSkip := by
    dsimp only [J]; rw [← mul_assoc]; exact Nat.le_ceil _
  have hb := bridge (show 1 ≤ 4 * J / q.δ from (le_div_iff₀ hd).mpr (by linarith)) hτ' hβ ho
  have hgap : J * (1 + (c.outerSkip : ℝ) / q.τ) ^ (-q.β) ≤ q.δ/4 := by
    apply (mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ J)).trans
    rw [inv_div]; field_simp [show J ≠ 0 by linarith]; rfl
  push_cast at houter
  change _ - (Measure.pi fun _ : Fin c.trials => Measure.pi fun _ : Fin (c.trials+1) => (Q : Measure Path)).real A ≤ J * _ at houter
  change (Measure.pi fun _ : Fin c.trials => Measure.pi fun _ : Fin (c.trials+1) => (Q : Measure Path)).real A ≤ _ at hprod
  linarith

lemma success (q : Params) (hp : spec.valid q) (f : Space q → ℝ) (O : Oracle (Point q) (Space q))
    (h : spec.admissible q f O) (K : ℕ) (hk : cost (schedule q) ≤ K) :
    spec.successful q f (fun w : (method q).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (method q) (fun _ => K) w.1 w.2) ⟨((method q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨g, P, rfl, hr, hc, ⟨u, hu, hmin⟩, hg⟩ := h
  let u' : Point q := ⟨u,hu⟩
  let c := schedule q
  let output := fun z => selected g c (observations c z)
  have hm : Measurable output := (measurable_selected hg.measurable c).comp (observations_measurable c)
  let O' : Oracle (Point q) (Space q) := ⟨fun _ => ℝ, P, fun _ (_, x) v => g x v⟩
  let run : Unit × Path → Point q := fun w => execute O' (method q) (fun _ => K) w.1 w.2
  have hrun : run = output ∘ Prod.snd := funext fun w => execute_output g P K hk w.1 w.2
  refine ⟨?_, u, hu, hmin, ?_⟩
  · change Measurable run
    rw [hrun]
    exact hm.comp measurable_snd
  let π := (P : Measure Path).map (fun z => z 0)
  let : IsProbabilityMeasure π := (Measure.isProbabilityMeasure_map_iff
    (measurable_pi_apply 0).aemeasurable).mpr inferInstance
  have hf := measurable_objective (π := π) hg hp.2.2.2.1 hp.2.2.1.le
  let good := {z | f (output z).val - f u ≤ q.ε}
  have hgood : MeasurableSet good := measurableSet_le ((hf.comp hm).sub_const _) measurable_const
  have hh := bad_output q hp P hr hg hc u'
  have he : goodᶜ = {z | q.ε < f (output z).val - f u} := by
    ext z
    change (¬ f (output z).val - f u ≤ q.ε) ↔ _
    exact not_le
  rw [← he, measureReal_compl hgood, probReal_univ] at hh
  let μ : Measure Unit := Measure.dirac ()
  have hs : (μ.prod (P : Measure Path)).real (Prod.snd ⁻¹' good) = (P : Measure Path).real good :=
    real_preimage measurePreserving_snd hgood
  change (μ.prod (P : Measure Path)).real {w | f (run w).val - f u ≤ q.ε} ≥ _
  rw [hrun]
  change (μ.prod (P : Measure Path)).real (Prod.snd ⁻¹' good) ≥ _
  linarith

end LongTails.Proofs.PolynomialMixingConvergence
