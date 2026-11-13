import LongTails.Proofs.GatedEscapeLook
import LongTails.Proofs.GatedEscapeStream
import LongTails.Proofs.IIDBlocks

namespace LongTails.Proofs.GatedEscapeFinal

open MeasureTheory ProbabilityTheory OracleTemplate LongTails.Algorithms.GatedPerturbedEscape
  LongTails.Proofs.GatedEscapeProcess LongTails.Proofs.GatedEscapeMoments
  LongTails.Proofs.GatedEscapePhases LongTails.Proofs.GatedEscapeMeasurable
  LongTails.Proofs.GatedEscapeEscape LongTails.Proofs.GatedEscapeGlobal
  LongTails.Proofs.GatedEscapeLookahead LongTails.Proofs.GatedEscapeLook
  LongTails.Proofs.GatedEscapeSaddle LongTails.Proofs.GatedEscapeStream
  LongTails.Proofs.StrongGrowthAgdBlocks LongTails.Proofs.ComparisonTrustTaylor
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω]
variable (cfg : Config) (d : ℕ) (g : E → Ω → E) (f : E → ℝ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma astep_zs (u : State E) (z : ℕ → E) (y : (Fin cfg.b → Ω) × E) :
    astep cfg d g { u with zs := z } y = { astep cfg d g u y with zs := z } := by
  cases u with
  | mk i acc t ph j x store g0 v w att found dx done zs =>
    cases done
    · cases ph <;> simp only [astep, stepBlock, blockUpdate, queryPoint, endAttempt,
        Bool.false_eq_true, ↓reduceIte] <;> (try split_ifs) <;> first | rfl | simp only [*, ↓reduceIte]
    · simp [astep]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma run_zs (u : State E) (z : ℕ → E) (β : ℕ → (Fin cfg.b → Ω) × E) :
    ∀ N, run (astep cfg d g) { u with zs := z } β N = { run (astep cfg d g) u β N with zs := z } := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih => rw [run_succ, run_succ, ih, astep_zs]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma Gg_cases (γ : ℝ) (s : State E) (y : (Fin cfg.b → Ω) × E) :
    Gg cfg d g f γ s y = 0 ∨ Gg cfg d g f γ s y = 1 := by
  unfold Gg testBad GescG harm
  split_ifs <;> simp

noncomputable def Xs (q : (ℕ → E) × (ℕ → Ω)) : ℕ → (Fin cfg.b → Ω) × E :=
  fun n => (blocks cfg q.2 n, q.1 n)

omit [BorelSpace E] in
theorem Xs_preserving (P0 : Measure Ω) [IsProbabilityMeasure P0] (P : Measure (ℕ → Ω))
    [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) P0 P) :
    MeasurePreserving (Xs cfg) ((Measure.infinitePi fun _ : ℕ => stdGaussian E).prod P)
      (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => P0).prod (stdGaussian E)) := by
  have hb : MeasurePreserving (blocks cfg) P (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin cfg.b => P0) :=
    OracleTemplate.FiniteVariance.infinite_block_law P0 P hIID.independent hIID.marginal cfg.b
  have h1 : MeasurePreserving (Prod.swap : (ℕ → E) × (ℕ → Ω) → (ℕ → Ω) × (ℕ → E))
      ((Measure.infinitePi fun _ : ℕ => stdGaussian E).prod P) (P.prod (Measure.infinitePi fun _ : ℕ => stdGaussian E)) :=
    Measure.measurePreserving_swap
  have h2 := hb.prod (MeasurePreserving.id (Measure.infinitePi fun _ : ℕ => stdGaussian E))
  have h3 := zip_preserving (Measure.pi fun _ : Fin cfg.b => P0) (stdGaussian E)
  have := h3.comp (h2.comp h1)
  exact this

noncomputable def keyState (q : Bool × Phase × ℕ × ℕ) : State E :=
  { (initState (0 : E) (fun _ => 0)) with
    done := q.1
    ph := q.2.1
    j := q.2.2.1
    att := q.2.2.2 }

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma rem_measurable : Measurable (rem cfg (E := E)) := by
  have hkey : Measurable (fun s : State E => (s.done, s.ph, s.j, s.att)) :=
    measurable_done.prodMk (measurable_ph.prodMk (measurable_j.prodMk measurable_att))
  have hR : Measurable (fun q : Bool × Phase × ℕ × ℕ => rem cfg (keyState (E := E) q)) :=
    measurable_of_countable _
  have : rem cfg (E := E) = (fun q : Bool × Phase × ℕ × ℕ => rem cfg (keyState (E := E) q)) ∘
      (fun s : State E => (s.done, s.ph, s.j, s.att)) := by
    funext s; rfl
  rw [this]
  exact hR.comp hkey

lemma Gg_measurable {L ρ : ℝ} (hsm : Smooth f L ρ) (hg : Measurable (Function.uncurry g)) (γ : ℝ) :
    Measurable (Function.uncurry (Gg cfg d g f γ (Ω := Ω))) := by
  classical
  have hgf : Continuous (gradient f) :=
    LipschitzWith.continuous (K := ⟨|L|, abs_nonneg L⟩) (LipschitzWith.of_dist_le_mul fun y z => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hsm.lip y z).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)))
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hsm.hf x).continuousAt
  have hstep := measurable_astep cfg d g hg
  have hsad : MeasurableSet {s : State E | sadS f γ s.x} :=
    measurable_x (sadS_open f hsm.hess γ).measurableSet
  have hGescm : Measurable (GescG cfg f γ (E := E)) := by
    unfold GescG harm
    refine Measurable.ite (measurableSet_eq_fun measurable_done measurable_const)
      (Measurable.ite hsad measurable_const measurable_const) ?_
    refine Measurable.ite (measurableSet_lt ?_ ?_) measurable_const measurable_const
    · exact (hfc.measurable.comp (measurable_x.sub measurable_dx)).sub_const _
    · exact hfc.measurable.comp ((measurable_x.sub measurable_dx).add measurable_dx)
  have hbm : Measurable (fun q : State E × ((Fin cfg.b → Ω) × E) => bmean cfg g q.1.x q.2.1) :=
    (bmean_measurable_joint cfg hg (q := fun s : State E => s.x) measurable_x).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have htest : Measurable (fun q : State E × ((Fin cfg.b → Ω) × E) => testBad cfg g f q.1 q.2) := by
    unfold testBad
    refine Measurable.ite (measurableSet_lt measurable_const ?_) measurable_const measurable_const
    have hupd : Measurable (fun q : State E × ((Fin cfg.b → Ω) × E) =>
        Function.update q.1.store q.1.j (bmean cfg g q.1.x q.2.1)) :=
      measurable_update_nat (measurable_store.comp measurable_fst) (measurable_j.comp measurable_fst) hbm
    exact (((measurable_select (β := E) cfg.M cfg.τg).comp hupd).sub
      (hgf.measurable.comp (measurable_x.comp measurable_fst))).norm
  unfold Gg
  refine Measurable.ite ((measurable_done.comp measurable_fst) (measurableSet_singleton true))
    measurable_const ?_
  refine Measurable.ite ((measurable_ph.comp measurable_fst) (measurableSet_singleton _)) htest ?_
  exact hGescm.comp hstep

theorem final_success {L ρ ε δ Δ σ : ℝ} (x0 : E) (hdE : d = Module.finrank ℝ E)
    (H : SHyp cfg L ρ (Real.sqrt (ρ * ε)) σ d) (hsm : Smooth f L ρ)
    (P0 : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
      (P0 : Measure Ω) (P : Measure (ℕ → Ω)))
    (hN : Noise g (gradient f) (P0 : Measure Ω) σ) (hσ : 0 ≤ σ) (hΔ : ∀ x, f x0 - f x ≤ Δ)
    (hM : 0 < cfg.M) (hk : 0 < cfg.k) (hM6 : (19 / 32 : ℝ) ^ cfg.M ≤ 1 / 20)
    (hτq : 0 < cfg.τq) (h3τq : 3 * cfg.τq ≤ 3 * cfg.θ / 8)
    (hvar0 : σ ^ 2 / cfg.b / cfg.τ0 ^ 2 ≤ 1 / 16) (hvarq : σ ^ 2 / cfg.b / (cfg.r * cfg.τq) ^ 2 ≤ 1 / 16)
    (hτg : 0 < cfg.τg) (hvarg : σ ^ 2 / cfg.b / cfg.τg ^ 2 ≤ 1 / 16) (hgth : cfg.gth = ε / 2)
    (h3τg : 3 * cfg.τg ≤ ε / 8) {ϱ : ℝ} (hϱ : 0 < ϱ) (hgd : (cfg.M : ℝ) ≤ ε ^ 2 / (16 * L) / ϱ)
    (hesc : ((cfg.M + cfg.k * alen cfg : ℕ) : ℝ) ≤ cfg.r ^ 2 * cfg.θ / 5 / ϱ) (N : ℕ)
    (hNbig : Δ / ϱ + ((cfg.M + cfg.k * alen cfg : ℕ) : ℝ) < N)
    (hδ : ((1 / 4) ^ cfg.k + cfg.k * (2 * (19 / 32) ^ cfg.M)) * (1 + N / cfg.M + (cfg.k * alen cfg) / cfg.M) ≤ δ) :
    Measurable (fun ω : (ℕ → E) × (ℕ → Ω) =>
      execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) seed => g x seed } : Oracle E E)
        (method cfg x0) (fun _ => N * cfg.b) ω.1 ω.2) ∧
    ENNReal.ofReal (1 - δ) ≤ ((Measure.infinitePi fun _ : ℕ => stdGaussian E).prod (P : Measure (ℕ → Ω)))
      {ω | ‖gradient f (execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) seed => g x seed } :
          Oracle E E) (method cfg x0) (fun _ => N * cfg.b) ω.1 ω.2)‖ ≤ ε ∧
        ∀ v, -Real.sqrt (ρ * ε) * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient f) (execute
          ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) seed => g x seed } : Oracle E E)
          (method cfg x0) (fun _ => N * cfg.b) ω.1 ω.2) v⟫} := by
  classical
  set γ := Real.sqrt (ρ * ε)
  set ν := (Measure.pi fun _ : Fin cfg.b => (P0 : Measure Ω)).prod (stdGaussian E)
  set s0 : State E := initState x0 (fun _ => 0)
  set out : (ℕ → (Fin cfg.b → Ω) × E) → E := fun β => (run (astep cfg d g) s0 β N).x with hout
  have hstep := measurable_astep cfg d g hN.meas
  have hgf : Continuous (gradient f) :=
    LipschitzWith.continuous (K := ⟨|L|, abs_nonneg L⟩) (LipschitzWith.of_dist_le_mul fun y z => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hsm.lip y z).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _)))
  have houtm : Measurable out := measurable_x.comp (run_measurable _ s0 hstep N)
  have hexec : ∀ ω : (ℕ → E) × (ℕ → Ω),
      execute ({ Seed := fun _ => Ω, law := P, answer := fun _ (_, x) seed => g x seed } : Oracle E E)
        (method cfg x0) (fun _ => N * cfg.b) ω.1 ω.2 = out (Xs cfg ω) := by
    intro ω
    rw [execute_method cfg x0 g ω.2 P H.hb N ω.1, ← hdE, traj_eq_run cfg d x0 g ω.1 ω.2 N]
    have : initState x0 ω.1 = { s0 with zs := ω.1 } := rfl
    rw [this, run_zs]
    rfl
  simp_rw [hexec]
  have hXs := Xs_preserving cfg (E := E) (P0 : Measure Ω) (P : Measure (ℕ → Ω)) hIID
  refine ⟨houtm.comp hXs.measurable, ?_⟩
  set Good : Set (ℕ → (Fin cfg.b → Ω) × E) := {β | ‖gradient f (out β)‖ ≤ ε ∧
    ∀ v, -γ * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient f) (out β) v⟫} with hGood
  have hHc : Continuous (fun x => fderiv ℝ (gradient f) x) :=
    LipschitzWith.continuous (K := ⟨|ρ|, abs_nonneg ρ⟩) (LipschitzWith.of_dist_le_mul fun y z => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (hsm.hess y z).trans (mul_le_mul_of_nonneg_right (le_abs_self ρ) (norm_nonneg _)))
  have hSOSPm : MeasurableSet {x : E | ‖gradient f x‖ ≤ ε ∧ ∀ v, -γ * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient f) x v⟫} := by
    rw [Set.ofPred_and]
    refine (measurableSet_le hgf.measurable.norm measurable_const).inter ?_
    have : {x : E | ∀ v, -γ * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient f) x v⟫} = {x | sadS f γ x}ᶜ := by
      ext x; simp [sadS]
    rw [this]
    exact (sadS_open f hsm.hess γ).measurableSet.compl
  have hGoodm : MeasurableSet Good := houtm hSOSPm
  have hpre : (Xs cfg) ⁻¹' Good = {ω | ‖gradient f (out (Xs cfg ω))‖ ≤ ε ∧
      ∀ v, -γ * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient f) (out (Xs cfg ω)) v⟫} := rfl
  rw [← hpre, hXs.measure_preimage hGoodm.nullMeasurableSet]
  have hL := H.hL
  have hg : ∀ x, HasGradientAt f (gradient f x) x := fun x => (hsm.hf x).differentiableAt.hasGradientAt
  have hT := H.hT
  have hs0d : s0.done = false := rfl
  have hs0ph : s0.ph = .test := rfl
  have hs0j : s0.j = 0 := rfl
  set flow := f x0 - Δ with hflowdef
  have hflow : ∀ x, flow ≤ f x := fun x => by rw [hflowdef]; linarith [hΔ x]
  have hend01 : ∀ (s : State E) (tail : ℕ → (Fin cfg.b → Ω) × E),
      endBad (rem cfg) (Gg cfg d g f γ) s tail = 0 ∨ endBad (rem cfg) (Gg cfg d g f γ) s tail = 1 := by
    intro s tail; unfold endBad; split_ifs
    · exact Gg_cases cfg d g f γ s (tail 0)
    · left; rfl
  have hend0 : ∀ (s : State E) (tail : ℕ → (Fin cfg.b → Ω) × E), 0 ≤ endBad (rem cfg) (Gg cfg d g f γ) s tail := by
    intro s tail; rcases hend01 s tail with h | h <;> simp [h]
  have hpt : ∀ β, Goodᶜ.indicator (fun _ => (1 : ℝ)) β ≤
      ∑ e ∈ Finset.range N, endBad (rem cfg) (Gg cfg d g f γ) (run (astep cfg d g) s0 β e) (shift e β) := by
    intro β
    by_cases hβ : β ∈ Good
    · rw [Set.indicator_of_notMem (by simpa using hβ)]
      exact Finset.sum_nonneg fun e _ => hend0 _ _
    · rw [Set.indicator_of_mem (by simpa using hβ)]
      by_contra hlt
      push Not at hlt
      have hall : ∀ e < N, endBad (rem cfg) (Gg cfg d g f γ) (run (astep cfg d g) s0 β e) (shift e β) = 0 := by
        intro e he
        rcases hend01 (run (astep cfg d g) s0 β e) (shift e β) with h | h
        · exact h
        · exfalso
          have := Finset.single_le_sum (f := fun e => endBad (rem cfg) (Gg cfg d g f γ)
            (run (astep cfg d g) s0 β e) (shift e β)) (fun e _ => hend0 _ _) (Finset.mem_range.mpr he)
          rw [h] at this; linarith
      obtain ⟨⟨_, hdone, _⟩, hlive⟩ := good_run cfg d g f hM hT hk hL hg hsm.lip hϱ H.hη hgth h3τg
        (flow := flow) hgd hesc s0 hs0d hs0ph hs0j β N hall N le_rfl
      apply hβ
      by_cases hdn : (run (astep cfg d g) s0 β N).done = true
      · obtain ⟨h1, h2⟩ := hdone hdn
        refine ⟨h1, fun v => ?_⟩
        by_contra hv; push Not at hv; exact h2 ⟨v, hv⟩
      · exfalso
        have hdn' : (run (astep cfg d g) s0 β N).done = false := by simpa using hdn
        have hΦ := hlive hdn'
        have hΦ0 : Φ cfg f ϱ flow s0 = Δ / ϱ + ((cfg.M + cfg.k * alen cfg : ℕ) : ℝ) := by
          have hx0 : s0.x = x0 := rfl
          unfold Φ; rw [ite_eq_left hs0ph, hs0j, hflowdef, hx0, Nat.sub_zero]; ring
        have hΦN : 0 ≤ Φ cfg f ϱ flow (run (astep cfg d g) s0 β N) := by
          unfold Φ
          have := hflow (run (astep cfg d g) s0 β N).x
          have : 0 ≤ (f (run (astep cfg d g) s0 β N).x - flow) / ϱ := div_nonneg (by linarith) hϱ.le
          positivity
        rw [hΦ0] at hΦ
        linarith
  have hcount := global_count cfg d g f (ν := ν) hM hT hk hstep (rem_measurable cfg) γ
    (Gg_measurable cfg d g f hsm hN.meas γ) (p := (1 / 4) ^ cfg.k + cfg.k * (2 * (19 / 32) ^ cfg.M))
    (ε := (19 / 32) ^ cfg.M) (pE := (1 / 4) ^ cfg.k + cfg.k * (2 * (19 / 32) ^ cfg.M)) (by positivity)
    (by
      have : (1 : ℝ) ≤ cfg.k := by exact_mod_cast hk
      have h0 : (0 : ℝ) ≤ (19 / 32) ^ cfg.M := by positivity
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) cfg.k])
    le_rfl
    (fun s hd hph hj => look_test cfg d g f H.hb hN hM hτg hvarg γ s hd hph hj)
    (fun s hs ha hf => look_escape cfg d g f H hdE hsm hN hσ hM hk hM6 hτq h3τq hvar0 hvarq s hs ha hf)
    s0 hs0d hs0ph hs0j N
  have hind_int : Integrable (Goodᶜ.indicator (fun _ => (1 : ℝ))) (Measure.infinitePi fun _ : ℕ => ν) :=
    (integrable_const (1 : ℝ)).indicator hGoodm.compl
  have hDm : Measurable (Function.uncurry (endBad (rem cfg) (Gg cfg d g f γ (Ω := Ω)))) := by
    unfold endBad
    refine Measurable.ite ?_ ?_ measurable_const
    · exact ((rem_measurable cfg).comp measurable_fst) (measurableSet_singleton 1)
    · exact (Gg_measurable cfg d g f hsm hN.meas γ).comp
        (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  have hterm_int : ∀ e, Integrable (fun β => endBad (rem cfg) (Gg cfg d g f γ)
      (run (astep cfg d g) s0 β e) (shift e β)) (Measure.infinitePi fun _ : ℕ => ν) := by
    intro e
    refine Integrable.of_bound (C := 1)
      (hDm.comp ((run_measurable _ s0 hstep e).prodMk (shift_measurable e))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun β => ?_)
    rcases hend01 (run (astep cfg d g) s0 β e) (shift e β) with h | h <;> simp [h]
  have hsum_int := integrable_finsetSum (Finset.range N) (fun e _ => hterm_int e)
  have hbad : ((Measure.infinitePi fun _ : ℕ => ν) Goodᶜ).toReal ≤ δ := by
    have h1 := integral_mono hind_int hsum_int hpt
    rw [integral_indicator_const _ hGoodm.compl, smul_eq_mul, mul_one, measureReal_def,
      integral_finsetSum _ (fun e _ => hterm_int e)] at h1
    have hMr : (0 : ℝ) < cfg.M := by exact_mod_cast hM
    have e2 : (1 / 4 : ℝ) ^ cfg.k + cfg.k * (2 * (19 / 32) ^ cfg.M) +
        N * (((1 / 4) ^ cfg.k + cfg.k * (2 * (19 / 32) ^ cfg.M)) / cfg.M) +
        (cfg.k * alen cfg) * (((1 / 4) ^ cfg.k + cfg.k * (2 * (19 / 32) ^ cfg.M)) / cfg.M) =
        ((1 / 4) ^ cfg.k + cfg.k * (2 * (19 / 32) ^ cfg.M)) * (1 + N / cfg.M + (cfg.k * alen cfg) / cfg.M) := by
      field_simp
    push_cast at hcount
    rw [e2] at hcount
    linarith
  have hδ0 : 0 ≤ δ := le_trans (by positivity) hδ
  have hne : (Measure.infinitePi fun _ : ℕ => ν) Goodᶜ ≤ ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal hbad
  have hc := prob_compl_eq_one_sub (μ := Measure.infinitePi fun _ : ℕ => ν) hGoodm.compl
  rw [compl_compl] at hc
  rw [hc, ENNReal.ofReal_sub _ hδ0, ENNReal.ofReal_one]
  exact tsub_le_tsub_left hne 1

end LongTails.Proofs.GatedEscapeFinal
