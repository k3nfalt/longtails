import LongTails.Setups.MeanSquaredSmoothPL
import LongTails.Proofs.StagewiseSarahSupermartingale
import LongTails.Proofs.StagewiseSarahCost

open MeasureTheory
open scoped ENNReal

namespace OracleTemplate.StagewiseSarah

open LongTails.Setups.MeanSquaredSmoothPL

section Regularity

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type} [MeasurableSpace Ω]
variable {p : Measure Ω} {f : E → ℝ} {g : E → Ω → E} {L Lbar μ σ fstar : ℝ}

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.continuous_f (H : Hyp p f g L Lbar μ σ fstar) : Continuous f :=
  continuous_iff_continuousAt.mpr (fun x => (H.grad x).continuousAt)

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.continuous_grad (H : Hyp p f g L Lbar μ σ fstar) : Continuous (gradient f) := by
  have hLip : LipschitzWith (Real.toNNReal L) (gradient f) :=
    LipschitzWith.of_dist_le_mul (fun x y => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (H.smooth x y).trans
        (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _)))
  exact hLip.continuous

lemma pot_measurable (H : Hyp p f g L Lbar μ σ fstar) (c : Ctl) :
    Measurable (fun z : E × E => ENNReal.ofReal (pot f fstar μ σ c z)) := by
  obtain ⟨todo, i⟩ := c
  have hf : Measurable (fun z : E × E => f z.1) :=
    H.continuous_f.measurable.comp measurable_fst
  have hg : Measurable (fun z : E × E => gradient f z.1) :=
    H.continuous_grad.measurable.comp measurable_fst
  cases todo with
  | nil => exact (hf.sub_const fstar).ennreal_ofReal
  | cons e rest =>
    apply Measurable.ennreal_ofReal
    have hfun : pot f fstar μ σ ⟨e :: rest, i⟩ = fun z : E × E =>
        slope μ rest * gain μ e * epochPot f fstar μ σ e i z + after μ σ rest 0 :=
      funext (fun z => pot_cons z)
    rw [hfun]
    refine ((?_ : Measurable (fun z : E × E => epochPot f fstar μ σ e i z)).const_mul _).add_const _
    unfold epochPot
    by_cases hA : i < e.B
    · simp only [hA, ↓reduceIte]
      exact (hf.sub_const _).add
        ((((measurable_snd.sub (hg.const_smul (i : ℝ))).norm.pow_const 2).add_const _).const_mul _)
    · simp only [hA, ↓reduceIte]
      exact ((hf.sub_const _).div_const _).add
        (((measurable_snd.sub hg).norm.pow_const 2).const_mul _)

omit [CompleteSpace E] in
lemma sampleNext_measurable (hg : Measurable (Function.uncurry g)) (c : Ctl) :
    Measurable (Function.uncurry (sampleNext g c)) := by
  obtain ⟨todo, i⟩ := c
  cases todo with
  | nil => exact measurable_fst
  | cons e rest =>
    have hx : Measurable (fun w : (E × E) × Ω => w.1.1) := measurable_fst.comp measurable_fst
    have hw : Measurable (fun w : (E × E) × Ω => w.1.2) := measurable_snd.comp measurable_fst
    have hgx : Measurable (fun w : (E × E) × Ω => g w.1.1 w.2) :=
      hg.comp (hx.prodMk measurable_snd)
    have hx' : Measurable (fun w : (E × E) × Ω => w.1.1 - e.η • w.1.2) :=
      hx.sub (hw.const_smul _)
    have hgx' : Measurable (fun w : (E × E) × Ω => g (w.1.1 - e.η • w.1.2) w.2) :=
      hg.comp (hx'.prodMk measurable_snd)
    by_cases hA : i < e.B
    · by_cases h1 : i + 1 < e.B
      · have he : Function.uncurry (sampleNext g ⟨e :: rest, i⟩) =
            fun w : (E × E) × Ω => (w.1.1, w.1.2 + g w.1.1 w.2) := by
          funext ⟨⟨x, w⟩, ω⟩
          exact sampleNext_anchor_acc hA h1
        rw [he]
        exact hx.prodMk (hw.add hgx)
      · by_cases h2 : i + 1 < e.B + e.m
        · have he : Function.uncurry (sampleNext g ⟨e :: rest, i⟩) =
              fun w : (E × E) × Ω => (w.1.1, (1 / (e.B : ℝ)) • (w.1.2 + g w.1.1 w.2)) := by
            funext ⟨⟨x, w⟩, ω⟩
            exact sampleNext_anchor_done hA h1 h2
          rw [he]
          exact hx.prodMk ((hw.add hgx).const_smul _)
        · have he : Function.uncurry (sampleNext g ⟨e :: rest, i⟩) =
              fun w : (E × E) × Ω =>
                (w.1.1 - e.η • ((1 / (e.B : ℝ)) • (w.1.2 + g w.1.1 w.2)), (0 : E)) := by
            funext ⟨⟨x, w⟩, ω⟩
            exact sampleNext_anchor_final hA h1 h2
          rw [he]
          exact (hx.sub (((hw.add hgx).const_smul _).const_smul _)).prodMk measurable_const
    · by_cases h2 : i + 1 < e.B + e.m
      · have he : Function.uncurry (sampleNext g ⟨e :: rest, i⟩) =
            fun w : (E × E) × Ω =>
              (w.1.1 - e.η • w.1.2, w.1.2 + (g (w.1.1 - e.η • w.1.2) w.2 - g w.1.1 w.2)) := by
          funext ⟨⟨x, w⟩, ω⟩
          exact sampleNext_inner hA h2
        rw [he]
        exact hx'.prodMk (hw.add (hgx'.sub hgx))
      · have he : Function.uncurry (sampleNext g ⟨e :: rest, i⟩) =
            fun w : (E × E) × Ω =>
              (w.1.1 - e.η • w.1.2 -
                e.η • (w.1.2 + (g (w.1.1 - e.η • w.1.2) w.2 - g w.1.1 w.2)), (0 : E)) := by
          funext ⟨⟨x, w⟩, ω⟩
          exact sampleNext_inner_final hA h2
        rw [he]
        exact (hx'.sub ((hw.add (hgx'.sub hgx)).const_smul _)).prodMk measurable_const

end Regularity

def Inv (L Lbar μ : ℝ) (c : Ctl) : Prop :=
  (∀ e ∈ c.todo, Good L Lbar μ e) ∧ ∀ e rest, c.todo = e :: rest → c.i < e.B + e.m

lemma inv_next {L Lbar μ : ℝ} (c : Ctl) (h : Inv L Lbar μ c) : Inv L Lbar μ (ctlNext c) := by
  obtain ⟨todo, i⟩ := c
  cases todo with
  | nil => exact h
  | cons e rest =>
    by_cases h1 : i + 1 < e.B + e.m
    · rw [ctlNext_cons_lt h1]
      refine ⟨h.1, ?_⟩
      intro e' rest' heq
      cases heq
      exact h1
    · rw [ctlNext_cons_ge h1]
      refine ⟨fun e' he' => h.1 e' (List.mem_cons_of_mem _ he'), ?_⟩
      intro e' rest' heq
      have hmem : e' ∈ rest := by
        change rest = e' :: rest' at heq
        rw [heq]
        exact List.mem_cons_self
      have := (h.1 e' (List.mem_cons_of_mem _ hmem)).hB
      change 0 < e'.B + e'.m
      omega

theorem execution_successful (q : Params) (hq : spec.valid q) (N : ℕ)
    (hN : cost (schedule q.L q.Lbar q.μ q.σ q.Δ q.ε) ≤ N) (f : q.E → ℝ)
    (O : Oracle (q.E × q.E) (q.E × q.E)) (hadm : spec.admissible q f O) :
    spec.successful q f
      (fun seed : (sarah (schedule q.L q.Lbar q.μ q.σ q.Δ q.ε) q.x0).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (sarah (schedule q.L q.Lbar q.μ q.σ q.Δ q.ε) q.x0) (fun _ => N) seed.1 seed.2)
      ⟨((sarah (schedule q.L q.Lbar q.μ q.σ q.Δ q.ε) q.x0).law : Measure _).prod
        (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hμ, hL, hLbar, hσ, hΔ, hε⟩ := hq
  obtain ⟨g, p, P, hIID, rfl, hgrad, hsmooth, ⟨xstar, hmin, hgap, hpl⟩, hgm, hint, hmean, hvi,
    hvar, hmi, hmss⟩ := hadm
  have hlower : ∀ x, f xstar ≤ f x := fun x => isMinOn_iff.mp hmin x (Set.mem_univ x)
  have H : Hyp (p : Measure q.Ω) f g q.L q.Lbar q.μ q.σ (f xstar) :=
    ⟨hμ, hgrad, hsmooth, hlower, hpl, hgm, hint, hmean, hvi, hvar, hmi, hmss⟩
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω) := by
    have := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans this
  set sched := schedule q.L q.Lbar q.μ q.σ q.Δ q.ε with hsched
  have hgoodS : ∀ e ∈ sched, Good q.L q.Lbar q.μ e := schedule_good hμ hL hLbar q.σ q.Δ q.ε
  have hBS : ∀ e ∈ sched, 1 ≤ e.B := fun e he => (hgoodS e he).hB
  let X : (ℕ → q.Ω) → q.E := fun ξ =>
    (zrun ctlNext (sampleNext g) N ⟨sched, 0⟩ (q.x0, (0 : q.E)) ξ).1
  have hmX : Measurable X :=
    measurable_fst.comp ((zrun_measurable ctlNext (sampleNext g) (sampleNext_measurable hgm) N
      ⟨sched, 0⟩).comp (measurable_const.prodMk measurable_id))
  have hout : (fun seed : (sarah sched q.x0).Seed × ((k : ℕ) → q.Ω) =>
      execute
        ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
          Oracle (q.E × q.E) (q.E × q.E))
        (sarah sched q.x0) (fun _ => N) seed.1 seed.2) = fun seed => X seed.2 := by
    funext seed
    exact execute_sarah g P sched q.x0 N seed.1 seed.2
  have hinv0 : Inv q.L q.Lbar q.μ ⟨sched, 0⟩ := by
    refine ⟨hgoodS, ?_⟩
    intro e rest heq
    have hmem : e ∈ sched := by
      change sched = e :: rest at heq
      rw [heq]
      exact List.mem_cons_self
    have := hBS e hmem
    change 0 < e.B + e.m
    omega
  have hlin := zrun_lintegral (p : Measure q.Ω) ctlNext (sampleNext g)
    (sampleNext_measurable hgm) (Inv q.L q.Lbar q.μ) inv_next
    (fun c z => ENNReal.ofReal (pot f (f xstar) q.μ q.σ c z)) (pot_measurable H)
    (fun c z hc => pot_step H c z hc.1 hc.2) N ⟨sched, 0⟩ (q.x0, (0 : q.E)) hinv0
  rw [ctlNext_iterate_cost sched hBS N hN, pot_fresh f (f xstar) q.μ q.σ sched hBS] at hlin
  have hstart : after q.μ q.σ sched (f q.x0 - f xstar) ≤ q.ε :=
    after_schedule_le hμ hL hLbar hε q.σ _ (sub_nonneg.mpr (hlower q.x0)) hgap
  have hbound : ∫⁻ ξ, ENNReal.ofReal (f (X ξ) - f xstar) ∂(P : Measure (ℕ → q.Ω)) ≤
      ENNReal.ofReal q.ε := by
    rw [hP]
    exact hlin.trans (ENNReal.ofReal_le_ofReal hstart)
  have hmg : Measurable (fun ξ : ℕ → q.Ω => f (X ξ) - f xstar) :=
    (H.continuous_f.measurable.comp hmX).sub_const _
  refine ⟨?_, xstar, hmin, ?_⟩
  · erw [hout]
    exact hmX.comp measurable_snd
  have hfun : (fun seed : (sarah sched q.x0).Seed × ((k : ℕ) → q.Ω) =>
      f (execute
        ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
          Oracle (q.E × q.E) (q.E × q.E))
        (sarah sched q.x0) (fun _ => N) seed.1 seed.2) - f xstar) =
      fun seed => f (X seed.2) - f xstar := by
    funext seed
    rw [execute_sarah g P sched q.x0 N seed.1 seed.2]
  erw [hfun]
  let Pfull : Measure ((sarah sched q.x0).Seed × (ℕ → q.Ω)) :=
    ((sarah sched q.x0).law : Measure _).prod (P : Measure (ℕ → q.Ω))
  have hmap : Pfull.map Prod.snd = (P : Measure (ℕ → q.Ω)) := by
    dsimp only [Pfull]
    rw [Measure.map_snd_prod]
    simp
  have hmg' : Measurable (fun seed : (sarah sched q.x0).Seed × (ℕ → q.Ω) =>
      f (X seed.2) - f xstar) := hmg.comp measurable_snd
  have hL' : ∫⁻ seed, ENNReal.ofReal (f (X seed.2) - f xstar) ∂Pfull ≤ ENNReal.ofReal q.ε := by
    have h1 : ∫⁻ seed, ENNReal.ofReal (f (X seed.2) - f xstar) ∂Pfull =
        ∫⁻ ξ, ENNReal.ofReal (f (X ξ) - f xstar) ∂(Pfull.map Prod.snd) :=
      (lintegral_map hmg.ennreal_ofReal measurable_snd).symm
    rw [h1, hmap]
    exact hbound
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL'
  have hnn : ∀ seed : (sarah sched q.x0).Seed × (ℕ → q.Ω), 0 ≤ f (X seed.2) - f xstar :=
    fun seed => sub_nonneg.mpr (hlower _)
  change Integrable (fun seed : (sarah sched q.x0).Seed × (ℕ → q.Ω) =>
      f (X seed.2) - f xstar) Pfull ∧
    ∫ seed, (f (X seed.2) - f xstar) ∂Pfull ≤ q.ε
  refine ⟨?_, ?_⟩
  · have := integrable_toReal_of_lintegral_ne_top hmg'.ennreal_ofReal.aemeasurable hfin
    simpa [ENNReal.toReal_ofReal (hnn _)] using this
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
      hmg'.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hL'

end OracleTemplate.StagewiseSarah
