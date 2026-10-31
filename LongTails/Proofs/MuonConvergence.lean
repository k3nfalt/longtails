import LongTails.Proofs.MuonTraining
import LongTails.Proofs.MuonValidation
import LongTails.Proofs.MuonContract
import LongTails.Proofs.MuonTuning

namespace LongTails.Proofs.MuonConvergence

open MeasureTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.ValidatedMuon

lemma execution_accuracy {m n : ℕ} {f : Space m n → ℝ} {s L Δ fmin e a D H γ : ℝ}
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    (P : ProbabilityMeasure (ℕ → model.Ω))
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) (P : Measure _))
    (hL : 0 < L) (hs : 0 ≤ s) (hΔ : 0 < Δ) (he : 0 < e)
    (ha : 1 ≤ a) (hD : 1 ≤ D) (hH : 1 ≤ H) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hscale : L * Δ = D * e ^ 2) (hnoise : 4096 * s ^ 2 ≤ a * e ^ 2)
    (hexp : Real.exp H = 1073741824 * a * D / γ)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (hmin : ∀ x, fmin ≤ f x) (x0 : Space m n) (hgap : f x0 - fmin ≤ Δ)
    {T q b k N : ℕ}
    (hT : T + 1 = ⌈1048576 * a * (D + Real.sqrt D * H ^ 2)⌉₊)
    (hq : q + 1 = ⌈Real.log (1 / γ) / Real.log 2⌉₊)
    (hb : b = max 1 ⌈144 * s ^ 2 / e ^ 2⌉₊)
    (hk : k + 1 = ⌈8 * Real.log (((q + 1 : ℕ) : ℝ) / γ)⌉₊)
    (hN : (b * (k + 1)) * (q + 1) + (T + 1) ≤ N) :
    let η := Δ / (e * (T + 1))
    let A := validatedMuon (1 / a) η (2 * e / 3) T b k q x0
    let O : Oracle (Space m n) (Space m n) :=
      { Seed := fun _ => model.Ω, law := P, answer := fun _ (_, x) ω => model.sample x ω }
    let output := fun z : A.Seed × (ℕ → model.Ω) => execute O A (fun _ => N) z.1 z.2
    Measurable output ∧ ((A.law : Measure _).prod (P : Measure _)).real
      {z | 8 * e < nuclearNorm (gradient f (output z))} ≤ 3 * γ := by
  let η := Δ / (e * (T + 1))
  let X := fun ξ (i : Fin (T + 1)) => (trajectory (1 / a) η model.sample ξ (x0, 0) 0 i.val).1
  have hX (i : Fin (T + 1)) : Measurable[MuonProcess.past (T + 1)] (fun ξ => X ξ i) := by
    have hh := (MuonProcess.adapted_trajectory (1 / a) η model.sample
      model.jointly_measurable (x0, 0) 0 i.val).fst
    rw [Nat.zero_add] at hh
    exact hh.mono (MuonProcess.past_mono i.isLt.le) le_rfl
  have htrain := MuonTraining.training_tuned_tail model h hL hs hΔ he ha hD hH hγ hγ1.le
    hscale hnoise hexp hgrad hlip hmin x0 hgap
  dsimp only at htrain
  rw [← hT] at htrain
  have htraining : (P : Measure _).real {ξ | (T + 1) * (4 * e) / 2 <
      ∑ i : Fin (T + 1), nuclearNorm (gradient f (X ξ i))} ≤ γ := by
    have hsum (ξ : ℕ → model.Ω) : (∑ i : Fin (T + 1), nuclearNorm (gradient f (X ξ i))) =
        ∑ t ∈ Finset.range (T + 1),
          nuclearNorm (gradient f (trajectory (1 / a) η model.sample ξ (x0, 0) 0 t).1) :=
      Fin.sum_univ_eq_sum_range (fun t =>
        nuclearNorm (gradient f (trajectory (1 / a) η model.sample ξ (x0, 0) 0 t).1)) (T + 1)
    simp_rw [hsum]
    simpa only [η, Nat.cast_add, Nat.cast_one, show ((T : ℝ) + 1) * (4 * e) / 2 =
      2 * e * ((T : ℝ) + 1) by ring] using htrain
  have hbnds := MuonTuning.validation_batch_bounds he ha hnoise
  rw [← hb] at hbnds
  have hraw := MuonValidation.random_validation_tail (q := q) (k := k) model h hbnds.1 hX
    (show 0 < 4 * e by positivity) (show 0 < e / 3 by positivity) hbnds.2.1 htraining
  let output := fun z : (Fin (q + 1) → Fin (T + 1)) × (ℕ → model.Ω) =>
    execute { Seed := fun _ => model.Ω, law := P, answer := fun _ (_, x) ω => model.sample x ω }
      (validatedMuon (1 / a) η (2 * e / 3) T b k q x0) (fun _ => N) z.1 z.2
  let outputPlan := fun z : (Fin (q + 1) → Fin (T + 1)) × (ℕ → model.Ω) =>
    QueryPlan.sampledEval model.sample z.2
      (validationPlan (2 * (e / 3)) b k q (fun i => X z.2 (z.1 i))) (T + 1)
  have hout : output = outputPlan := by
    funext z
    dsimp [output, outputPlan, X]
    rw [ValidatedMuonExecution.execute_validatedMuon P model.sample _ _ _ _ _ _ _ _ _ _ _ hN,
      MuonProcess.sampledEval_trainingPlan]
    congr 2
    ring
  have hdraw := MuonTuning.validation_draw_bounds ha hD hH hγ hγ1 hexp
  rw [← hq] at hdraw
  have hblock := MuonTuning.validation_block_bounds ha hD hH hγ hγ1
    (Nat.succ_pos q) hdraw.2.1 hexp
  rw [← hk] at hblock
  change Measurable output ∧
    (((PMF.uniformOfFintype (Fin (q + 1) → Fin (T + 1))).toMeasure).prod (P : Measure _)).real
      {z | 8 * e < nuclearNorm (gradient f (output z))} ≤ 3 * γ
  rw [hout]
  refine ⟨hraw.1, ?_⟩
  have hsub : {z | 8 * e < nuclearNorm (gradient f (outputPlan z))} ⊆
      {z | 4 * e + 6 * (e / 3) < nuclearNorm (gradient f (outputPlan z))} := by
    intro z hz
    dsimp only [Set.mem_ofPred_eq] at hz ⊢
    linarith
  have hm := measureReal_mono (μ := ((PMF.uniformOfFintype
    (Fin (q + 1) → Fin (T + 1))).toMeasure).prod (P : Measure _)) hsub (by finiteness)
  exact hm.trans (hraw.2.trans (by linarith [hdraw.2.2, hblock.2.2]))

lemma finiteVarianceMuon_allowed (p : LongTails.Setups.FiniteVarianceSpectralSmooth.Public)
    (hp : LongTails.Setups.FiniteVarianceSpectralSmooth.spec.valid p) :
    LongTails.Setups.FiniteVarianceSpectralSmooth.MuonFamily p
      (finiteVarianceMuon p.L p.Δ p.s p.ε p.δ p.x0) := by
  classical
  rcases hp with ⟨hL, hΔ, _hs, hε, hδ, hδ1⟩
  by_cases hcase : 2 * p.L * p.Δ ≤ p.ε ^ 2
  · have hh : LongTails.Setups.FiniteVarianceSpectralSmooth.MuonFamily p (returnInitial p.x0) :=
      Or.inl ⟨hcase, fun _ => rfl⟩
    simpa only [finiteVarianceMuon, ite_eq_left hcase] using hh
  · let e := p.ε / 8
    let γ := p.δ / 4
    let D := p.L * p.Δ / e ^ 2
    let a := max 1 (4096 * p.s ^ 2 / e ^ 2)
    let H := Real.log (1073741824 * a * D / γ)
    let T := ⌈1048576 * a * (D + Real.sqrt D * H ^ 2)⌉₊
    let q := ⌈Real.log (1 / γ) / Real.log 2⌉₊
    let b := max 1 ⌈144 * p.s ^ 2 / e ^ 2⌉₊
    let k := ⌈8 * Real.log ((q : ℝ) / γ)⌉₊
    have hbnds := MuonTuning.hard_parameter_bounds (s := p.s) hL hΔ hε hδ hδ1 (lt_of_not_ge hcase)
    have ha : 1 ≤ a := hbnds.2.2.2.1
    have hD : 1 ≤ D := hbnds.2.2.1
    have hH : 1 ≤ H := hbnds.2.2.2.2.1
    have hT : 0 < T := (MuonTuning.training_count_bounds ha hD hH).1
    have ht : 0 < (T : ℝ) := by exact_mod_cast hT
    have he : 0 < e := by dsimp [e]; positivity
    have ha0 : 0 < a := by linarith
    have hα : 0 < 1 / a := by positivity
    have hα1 : 1 / a ≤ 1 := (div_le_one ha0).mpr ha
    have hη : 0 < p.Δ / (e * T) := div_pos hbnds.2.1 (by positivity)
    have hρ : 0 < 2 * e / 3 := by positivity
    have hb : 0 < b := lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)
    have hh : LongTails.Setups.FiniteVarianceSpectralSmooth.MuonFamily p
        (validatedMuon (1 / a) (p.Δ / (e * T)) (2 * e / 3) (T - 1) b (k - 1) (q - 1) p.x0) :=
      Or.inr ⟨1 / a, p.Δ / (e * T), 2 * e / 3, T - 1, b, k - 1, q - 1,
        hα, hα1, hη, hρ, hb, MuonContract.validatedMuon_follows _ _ _ _ _ _ _ _ hb⟩
    simpa only [finiteVarianceMuon, ite_eq_right hcase] using hh

lemma initial_success (p : LongTails.Setups.FiniteVarianceSpectralSmooth.Public)
    (O : Oracle (Space p.m p.n) (Space p.m p.n)) {f : Space p.m p.n → ℝ} {fmin : ℝ}
    (hL : 0 ≤ p.L) (hε : 0 < p.ε)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ p.L * spectralNorm (x - y))
    (hmin : ∀ x, fmin ≤ f x) (hgap : f p.x0 - fmin ≤ p.Δ)
    (hcase : 2 * p.L * p.Δ ≤ p.ε ^ 2) :
    LongTails.Setups.FiniteVarianceSpectralSmooth.spec.successful p f
      (fun z : (returnInitial p.x0).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (returnInitial p.x0) (fun _ => 0) z.1 z.2)
      ⟨((returnInitial p.x0).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hg := MatrixSmooth.gradient_self_bound_nonnegative hgrad hlip hL hmin p.x0
  have hh := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * p.L by positivity)
  have hn : nuclearNorm (gradient f p.x0) ≤ p.ε := by
    nlinarith [LongTails.Algorithms.MatrixPolar.nuclearNorm_nonneg (gradient f p.x0)]
  have hout : (fun z : (returnInitial p.x0).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (returnInitial p.x0) (fun _ => 0) z.1 z.2) = fun _ => p.x0 := by
    funext z
    rw [execute_indexed]
    rfl
  change Measurable _ ∧ _
  rw [hout]
  refine ⟨measurable_const, ?_⟩
  simp only [not_lt.mpr hn, Set.ofPred_false, measure_empty]
  exact bot_le

end LongTails.Proofs.MuonConvergence
