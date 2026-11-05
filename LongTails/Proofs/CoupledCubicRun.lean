import LongTails.Proofs.CoupledCubicExecution
import LongTails.Proofs.CoupledCubicConcentration
import LongTails.Proofs.CoupledCubicStability
import LongTails.Proofs.CoupledCubicBatch
import LongTails.Proofs.CoupledCubicDescent

open scoped RealInnerProductSpace
open Classical

namespace LongTails.Proofs.CoupledCubicRun

open LongTails.Setups.StrongGrowthFiniteSumSecondOrder
open LongTails.Algorithms.CoupledCubicTournament
open LongTails.Proofs.CoupledCubicConcentration
open LongTails.Proofs.CoupledCubicExecution
open LongTails.Proofs.CoupledCubicSelection

noncomputable def transition (p : Params) (b K : ℕ) (g : Fin p.n × p.E → Model p)
    (state : p.E × Bool) (ξ : Fin K → Fin b → Fin p.n) : p.E × Bool :=
  nextState p state (sampledModels p b K g state.1 ξ)

lemma runState_invariant (p : Params) (b K : ℕ) (g : Fin p.n × p.E → Model p)
    (F : p.E → ℝ) (accurate : p.E → Prop) (δ : ℝ)
    (good : (p.E × Bool) → (Fin K → Fin b → Fin p.n) → Prop)
    (hstep : ∀ state ξ, good state ξ → (state.2 = true → accurate state.1) →
      ((transition p b K g state ξ).2 = true → accurate (transition p b K g state ξ).1) ∧
      ((transition p b K g state ξ).2 = false → state.2 = false ∧
        δ ≤ F state.1 - F (transition p b K g state ξ).1))
    (T : ℕ) (state : p.E × Bool) (ξ : Seeds p b K T)
    (hinit : state.2 = true → accurate state.1)
    (hpath : goodPath (transition p b K g) good T state ξ) :
    ((runState p b K g T state ξ).2 = true → accurate (runState p b K g T state ξ).1) ∧
    ((runState p b K g T state ξ).2 = false → state.2 = false ∧
      (T : ℝ) * δ ≤ F state.1 - F (runState p b K g T state ξ).1) := by
  induction T generalizing state with
  | zero =>
    refine ⟨hinit, ?_⟩
    intro hh
    exact ⟨hh, by simp [runState]⟩
  | succ T ih =>
    obtain ⟨hfirst, htail⟩ := hpath
    have hlocal := hstep state (ξ 0) hfirst hinit
    have hrest := ih (transition p b K g state (ξ 0)) (fun i => ξ i.succ) hlocal.1 htail
    change ((runState p b K g T (transition p b K g state (ξ 0)) (fun i => ξ i.succ)).2 = true → _) ∧ _
    refine ⟨hrest.1, ?_⟩
    intro hactive
    obtain ⟨hnext, hledger⟩ := hrest.2 hactive
    obtain ⟨hstate, hdrop⟩ := hlocal.2 hnext
    refine ⟨hstate, ?_⟩
    change ((T + 1 : ℕ) : ℝ) * δ ≤ F state.1 -
      F (runState p b K g T (transition p b K g state (ξ 0)) (fun i => ξ i.succ)).1
    rw [Nat.cast_add, Nat.cast_one]
    linarith

lemma runState_forced_accuracy (p : Params) (b K : ℕ) (g : Fin p.n × p.E → Model p)
    (F : p.E → ℝ) (accurate : p.E → Prop) (δ : ℝ)
    (good : (p.E × Bool) → (Fin K → Fin b → Fin p.n) → Prop)
    (hstep : ∀ state ξ, good state ξ → (state.2 = true → accurate state.1) →
      ((transition p b K g state ξ).2 = true → accurate (transition p b K g state ξ).1) ∧
      ((transition p b K g state ξ).2 = false → state.2 = false ∧
        δ ≤ F state.1 - F (transition p b K g state ξ).1))
    (hgap : ∀ y, F p.x0 - F y ≤ p.Δ) (T : ℕ) (hT : p.Δ < (T : ℝ) * δ)
    (ξ : Seeds p b K T) (hpath : goodPath (transition p b K g) good T (p.x0, false) ξ) :
    accurate (output p b K T g ξ) := by
  have hi := runState_invariant p b K g F accurate δ good hstep T (p.x0, false) ξ
    (by simp) hpath
  have hstop : (runState p b K g T (p.x0, false) ξ).2 = true := by
    by_contra hh
    have hf : (runState p b K g T (p.x0, false) ξ).2 = false := Bool.eq_false_iff.mpr hh
    have hl := (hi.2 hf).2
    have hg := hgap (runState p b K g T (p.x0, false) ξ).1
    linarith
  rw [CoupledCubicExecution.output_eq_runState]
  exact hi.1 hstop

lemma threshold_decrease (ρ ε t : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (ht : Real.sqrt (ε / ρ) / 5 < t) :
    ε * Real.sqrt ε / (16000 * Real.sqrt ρ) < ρ * t ^ 3 / 128 := by
  have hs : ρ * (Real.sqrt (ε / ρ)) ^ 2 = ε := by
    rw [Real.sq_sqrt (div_nonneg hε.le hρ.le)]
    field_simp
  have he : ρ * (Real.sqrt (ε / ρ) / 5) ^ 3 / 128 =
      ε * Real.sqrt ε / (16000 * Real.sqrt ρ) := by
    calc
      _ = (ρ * (Real.sqrt (ε / ρ)) ^ 2) * Real.sqrt (ε / ρ) / 16000 := by ring
      _ = ε * Real.sqrt (ε / ρ) / 16000 := by rw [hs]
      _ = _ := by rw [Real.sqrt_div hε.le]; ring
  have hp := pow_lt_pow_left₀ ht (by positivity : 0 ≤ Real.sqrt (ε / ρ) / 5)
    (by decide : (3 : ℕ) ≠ 0)
  have hm := mul_lt_mul_of_pos_left hp hρ
  rw [← he]
  linarith

def jointAccurate (p : Params) (F : p.E → ℝ) (x : p.E) : Prop :=
  ‖gradient F x‖ ≤ p.ε ∧ ∀ v : p.E, -Real.sqrt (p.ρ * p.ε) * ‖v‖ ^ 2 ≤
    ⟪v, fderiv ℝ (gradient F) x v⟫

def stepCertificate (p : Params) (F : p.E → ℝ) (x u : p.E) : Prop :=
  ‖gradient F (x + u)‖ ≤ 20 * p.ρ * ‖u‖ ^ 2 ∧
    (∀ v : p.E, -5 * p.ρ * ‖u‖ * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient F) (x + u) v⟫) ∧
    F (x + u) ≤ F x - p.ρ * ‖u‖ ^ 3 / 128

lemma certificate_transition (p : Params) (b K : ℕ) (g : Fin p.n × p.E → Model p)
    (F : p.E → ℝ) (hρ : 0 < p.ρ) (hε : 0 < p.ε)
    (state : p.E × Bool) (ξ : Fin K → Fin b → Fin p.n)
    (hcert : stepCertificate p F state.1 (selectedStep p (sampledModels p b K g state.1 ξ)))
    (hinit : state.2 = true → jointAccurate p F state.1) :
    ((transition p b K g state ξ).2 = true → jointAccurate p F (transition p b K g state ξ).1) ∧
      ((transition p b K g state ξ).2 = false → state.2 = false ∧
        p.ε * Real.sqrt p.ε / (16000 * Real.sqrt p.ρ) ≤
          F state.1 - F (transition p b K g state ξ).1) := by
  by_cases hstop : state.2 = true
  · simp only [transition, nextState, hstop, ite_true]
    exact ⟨fun _ => hinit hstop, fun hh => by simp at hh⟩
  · have hfalse : state.2 = false := Bool.eq_false_iff.mpr hstop
    let u := selectedStep p (sampledModels p b K g state.1 ξ)
    have he : transition p b K g state ξ =
        (state.1 + u, decide (‖u‖ ≤ Real.sqrt (p.ε / p.ρ) / 5)) := by
      simp [transition, nextState, hfalse, u]
    rw [he]
    constructor
    · intro hh
      have ht : ‖u‖ ≤ Real.sqrt (p.ε / p.ρ) / 5 := of_decide_eq_true hh
      have ha := CoupledCubicStability.stopping_accuracy p.ρ p.ε ‖u‖ hρ hε (norm_nonneg u) ht
      refine ⟨hcert.1.trans ha.1, ?_⟩
      intro v
      have hm := mul_le_mul_of_nonneg_right ha.2 (sq_nonneg ‖v‖)
      have hc := hcert.2.1 v
      change -Real.sqrt (p.ρ * p.ε) * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient F) (state.1 + u) v⟫
      change -5 * p.ρ * ‖u‖ * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient F) (state.1 + u) v⟫ at hc
      linarith
    · intro hh
      have ht : Real.sqrt (p.ε / p.ρ) / 5 < ‖u‖ := lt_of_not_ge (of_decide_eq_false hh)
      have hd := threshold_decrease p.ρ p.ε ‖u‖ hρ hε ht
      refine ⟨hfalse, ?_⟩
      have hc := hcert.2.2
      change F (state.1 + u) ≤ F state.1 - p.ρ * ‖u‖ ^ 3 / 128 at hc
      change p.ε * Real.sqrt p.ε / (16000 * Real.sqrt p.ρ) ≤ F state.1 - F (state.1 + u)
      linarith

def certifiedRound (p : Params) (b K : ℕ) (g : Fin p.n × p.E → Model p)
    (F : p.E → ℝ) (state : p.E × Bool) (ξ : Fin K → Fin b → Fin p.n) : Prop :=
  stepCertificate p F state.1 (selectedStep p (sampledModels p b K g state.1 ξ))

lemma output_accuracy_of_certificates (p : Params) (b K : ℕ) (g : Fin p.n × p.E → Model p)
    (F : p.E → ℝ) (hρ : 0 < p.ρ) (hε : 0 < p.ε)
    (hgap : ∀ y, F p.x0 - F y ≤ p.Δ) (T : ℕ)
    (hT : p.Δ < (T : ℝ) * (p.ε * Real.sqrt p.ε / (16000 * Real.sqrt p.ρ)))
    (ξ : Seeds p b K T)
    (hpath : goodPath (transition p b K g) (certifiedRound p b K g F) T (p.x0, false) ξ) :
    jointAccurate p F (output p b K T g ξ) :=
  runState_forced_accuracy p b K g F (jointAccurate p F)
    (p.ε * Real.sqrt p.ε / (16000 * Real.sqrt p.ρ)) (certifiedRound p b K g F)
    (fun state ξ hcert hinit => certificate_transition p b K g F hρ hε state ξ hcert hinit)
    hgap T hT ξ hpath

lemma majority_certified (p : Params) (b K : ℕ) (g : Fin p.n × p.E → Model p)
    (F : p.E → ℝ) (hf : ContDiff ℝ 2 F) (hρ : 0 < p.ρ)
    (hLip : ∀ y z, ‖fderiv ℝ (gradient F) y - fderiv ℝ (gradient F) z‖ ≤ p.ρ * ‖y - z‖)
    (state : p.E × Bool) (ξ : Fin K → Fin b → Fin p.n)
    (hsym : ∀ i, (g (i, state.1)).2.toLinearMap.IsSymmetric)
    (href : (fderiv ℝ (gradient F) state.1).toLinearMap.IsSymmetric)
    (η : ℝ) (hη0 : 0 ≤ η) (hη : 56 * η ≤ 1 / 1000000)
    (hmajor : K < 2 * ((Finset.univ : Finset (Fin K)).filter (fun j =>
      relativeModelAccurate p (gradient F state.1, fderiv ℝ (gradient F) state.1)
        (sampledModel p b g state.1 (ξ j)) href η)).card) :
    certifiedRound p b K g F state ξ := by
  classical
  let reference : Model p := (gradient F state.1, fderiv ℝ (gradient F) state.1)
  let models := sampledModels p b K g state.1 ξ
  let G := (Finset.univ : Finset (Fin K)).filter (fun j =>
    relativeModelAccurate p reference (sampledModel p b g state.1 (ξ j)) href η)
  let good := G.image Fin.val
  have hlen : models.length = K := by simp [models, sampledModels]
  have hcard : good.card = G.card := Finset.card_image_of_injective G Fin.val_injective
  have hsub : good ⊆ Finset.range models.length := by
    intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (by rw [hlen]; exact k.isLt)
  have hgood (j : ℕ) (hj : j ∈ good) : relativeModelAccurate p reference (modelAt p models j) href η := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    have he := modelAt_sampledModels p b K g state.1 ξ k
    change modelAt p models k = _ at he
    rw [he]
    exact (Finset.mem_filter.mp hk).2
  have hsym' (j : ℕ) (hj : j ∈ good) : (modelAt p models j).2.toLinearMap.IsSymmetric :=
    sampledModels_symmetric p b K g state.1 ξ hsym j (Finset.mem_range.mp (hsub hj))
  have hm : models.length < 2 * good.card := by rw [hlen, hcard]; exact hmajor
  obtain ⟨hindex, haccurate⟩ := selected_model_accurate p reference models good η hρ hη0 hη
    href hsym' hsub hm hgood
  have hselected := sampledModels_symmetric p b K g state.1 ξ hsym (selectedIndex p models) hindex
  exact CoupledCubicDescent.accurate_step p F hf hρ hLip state.1
    (modelAt p models (selectedIndex p models)) (η + 28 / 1000000)
    (by linarith) (by linarith) href hselected haccurate

lemma objective_round_failure (p : Params) (f : Fin p.n → p.E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hκ : 1 ≤ p.κ) (hρ : 0 < p.ρ)
    (hSGC : ∀ y, (p.n : ℝ)⁻¹ * ∑ i, ‖gradient (f i) y‖ ^ 2 ≤
      p.κ * ‖gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) y‖ ^ 2)
    (hRMS : ∀ y z, (p.n : ℝ)⁻¹ * ∑ i,
      ‖fderiv ℝ (gradient (f i)) y - fderiv ℝ (gradient (f i)) z‖ ^ 2 ≤
        p.ρ ^ 2 * ‖y - z‖ ^ 2) (b K : ℕ) (hb : 0 < b)
    (hbudget : 1024 * ((Module.finrank ℝ p.E + 1 : ℕ) : ℝ) * p.κ ≤
      (b : ℝ) * (1 / 100000000 : ℝ) ^ 2) (state : p.E × Bool) :
    let F := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
    let replies : Fin p.n × p.E → Model p := fun ix =>
      (gradient (f ix.1) ix.2, fderiv ℝ (gradient (f ix.1)) ix.2)
    (PMF.uniformOfFintype (Fin K → Fin b → Fin p.n)).toMeasure
      {ξ | ¬certifiedRound p b K replies F state ξ} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ K) := by
  let F := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let replies : Fin p.n × p.E → Model p := fun ix =>
    (gradient (f ix.1) ix.2, fderiv ℝ (gradient (f ix.1)) ix.2)
  have hF : ContDiff ℝ 2 F := CoupledCubicPopulation.objective_contDiff_two f hf
  have href := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hF state.1
  let good : (Fin b → Fin p.n) → Prop := fun ζ =>
    relativeModelAccurate p (gradient F state.1, fderiv ℝ (gradient F) state.1)
      (sampledModel p b replies state.1 ζ) href (1 / 100000000)
  have hbad : (PMF.uniformOfFintype (Fin b → Fin p.n)).toMeasure.real {ζ | ¬good ζ} ≤ 1 / 16 := by
    rw [finite_uniform_measure_product]
    have ht := CoupledCubicBatch.objective_batch_failure p f hf hκ hρ hSGC hRMS state.1
      href (1 / 100000000) (by norm_num) b hb
    apply ht.trans
    apply (div_le_iff₀ (show 0 < (b : ℝ) * (1 / 100000000 : ℝ) ^ 2 by positivity)).mpr
    nlinarith
  have hm := finite_uniform_majority_failure good hbad K
  apply (MeasureTheory.measure_mono ?_).trans hm
  intro ξ hbad hmajor
  apply hbad
  exact majority_certified p b K replies F hF hρ
    (CoupledCubicPopulation.objective_hessian_lipschitz f hf p.ρ hρ.le hRMS)
    state ξ (fun i => OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric (hf i) state.1)
    href (1 / 100000000) (by norm_num) (by norm_num) hmajor

lemma objective_output_failure (p : Params) (f : Fin p.n → p.E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hκ : 1 ≤ p.κ) (hρ : 0 < p.ρ) (hε : 0 < p.ε)
    (hSGC : ∀ y, (p.n : ℝ)⁻¹ * ∑ i, ‖gradient (f i) y‖ ^ 2 ≤
      p.κ * ‖gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) y‖ ^ 2)
    (hRMS : ∀ y z, (p.n : ℝ)⁻¹ * ∑ i,
      ‖fderiv ℝ (gradient (f i)) y - fderiv ℝ (gradient (f i)) z‖ ^ 2 ≤
        p.ρ ^ 2 * ‖y - z‖ ^ 2)
    (hgap : ∀ y, LongTails.Setups.FiniteSumSmoothAndConvex.objective f p.x0 -
      LongTails.Setups.FiniteSumSmoothAndConvex.objective f y ≤ p.Δ)
    (b K T : ℕ) (hb : 0 < b)
    (hbudget : 1024 * ((Module.finrank ℝ p.E + 1 : ℕ) : ℝ) * p.κ ≤
      (b : ℝ) * (1 / 100000000 : ℝ) ^ 2)
    (hT : p.Δ < (T : ℝ) * (p.ε * Real.sqrt p.ε / (16000 * Real.sqrt p.ρ))) :
    let F := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
    let replies : Fin p.n × p.E → Model p := fun ix =>
      (gradient (f ix.1) ix.2, fderiv ℝ (gradient (f ix.1)) ix.2)
    (PMF.uniformOfFintype (Seeds p b K T)).toMeasure
      {ξ | ¬jointAccurate p F (output p b K T replies ξ)} ≤
        (T : ENNReal) * ENNReal.ofReal ((1 / 2 : ℝ) ^ K) := by
  let F := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let replies : Fin p.n × p.E → Model p := fun ix =>
    (gradient (f ix.1) ix.2, fderiv ℝ (gradient (f ix.1)) ix.2)
  have hround (state : p.E × Bool) :=
    objective_round_failure p f hf hκ hρ hSGC hRMS b K hb hbudget state
  have hp := finite_uniform_adaptive_failure (transition p b K replies)
    (certifiedRound p b K replies F) (ENNReal.ofReal ((1 / 2 : ℝ) ^ K)) hround T (p.x0, false)
  apply (MeasureTheory.measure_mono ?_).trans hp
  intro ξ hbad hpath
  exact hbad (output_accuracy_of_certificates p b K replies F hρ hε hgap T hT ξ hpath)

end LongTails.Proofs.CoupledCubicRun
