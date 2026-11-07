import LongTails.Proofs.ChiSquareConstants
import LongTails.Proofs.ChiSquareSelection
import LongTails.Proofs.ChiSquareObjective
import LongTails.Proofs.AdaptiveIID

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ChiSquareDro

open LongTails.Setups.ChiSquareConstrainedDro
open OracleTemplate.StochasticGeneralized (splitStream splitStream_preserving)
open OracleTemplate.SampledConvex (extend measurable_extend extend_agree)

variable {q : Params} {I : Instance q} {proj : q.E → q.E}

noncomputable def xAvg (q : Params) (proj : q.E → q.E) (I : Instance q) (j : ℕ) (ζ : ℕ → q.Ξ) : q.E :=
  avgX (cfg q j) proj I.loss I.sub (start q j) (sgdSteps q) ζ

noncomputable def eAvg (q : Params) (proj : q.E → q.E) (I : Instance q) (j : ℕ) (ζ : ℕ → q.Ξ) : ℝ :=
  avgE (cfg q j) proj I.loss I.sub (start q j) (sgdSteps q) ζ

noncomputable def sAvg (q : Params) (proj : q.E → q.E) (I : Instance q) (j : ℕ) (ζ : ℕ → q.Ξ) : ℝ :=
  avgS (cfg q j) proj I.loss I.sub (start q j) (sgdSteps q) ζ

noncomputable def sHat (q : Params) (proj : q.E → q.E) (I : Instance q) (j : ℕ) (ζ : ℕ → q.Ξ) : ℝ :=
  Real.sqrt ((∑ i ∈ Finset.range (selectionSamples q), max (I.loss (proj (xAvg q proj I j ζ))
    (ζ (sgdSteps q + i)) - eAvg q proj I j ζ) 0 ^ 2) / selectionSamples q)

noncomputable def sErr (q : Params) (proj : q.E → q.E) (I : Instance q) (j : ℕ) (ζ : ℕ → q.Ξ) : ℝ :=
  sHat q proj I j ζ - nrm (I.law : Measure q.Ξ) (I.loss (xAvg q proj I j ζ)) (eAvg q proj I j ζ)

lemma fhat_eq (j : ℕ) (ξ : ℕ → q.Ξ) :
    fhat q proj I.loss I.sub j ξ = eAvg q proj I j (block q j ξ) + radius q * sHat q proj I j (block q j ξ) :=
  rfl

lemma xbar_eq (j : ℕ) (ξ : ℕ → q.Ξ) :
    xbar q proj I.loss I.sub j ξ = xAvg q proj I j (block q j ξ) := rfl

lemma measurable_block (j : ℕ) : Measurable (block q j) :=
  Measurable.of_eval fun i => measurable_pi_apply (j * bracketLength q + i)

lemma integral_snd_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    [IsProbabilityMeasure μ] (ν : Measure β) [SFinite ν] {F : β → ℝ} (hF : Integrable F ν) :
    Integrable (fun w : α × β => F w.2) (μ.prod ν) ∧ (∫ w, F w.2 ∂(μ.prod ν)) = ∫ ξ, F ξ ∂ν := by
  have hsnd : MeasurePreserving (Prod.snd : α × β → β) (μ.prod ν) ν := measurePreserving_snd
  refine ⟨integrable_of_preserving hsnd hF, ?_⟩
  have := integral_map (μ := μ.prod ν) hsnd.measurable.aemeasurable (f := F)
    (by rw [hsnd.map_eq]; exact hF.aestronglyMeasurable)
  rw [hsnd.map_eq] at this
  exact this.symm

section Measurability

variable (h : Adm q I proj)
include h

lemma measurable_avgs (j : ℕ) :
    Measurable (xAvg q proj I j) ∧ Measurable (eAvg q proj I j) ∧ Measurable (sAvg q proj I j) := by
  have hz := measurable_run (k := cfg q j) h.proj_meas h.loss_meas h.sub_meas (start q j)
  refine ⟨?_, ?_, ?_⟩
  · exact (Finset.measurable_sum _ fun t _ => h.proj_meas.comp (measurable_fst.comp (hz t))).const_smul _
  · exact measurable_const.mul (Finset.measurable_sum _ fun t _ =>
      measurable_fst.comp (measurable_snd.comp (hz t)))
  · exact measurable_const.mul (Finset.measurable_sum _ fun t _ =>
      measurable_snd.comp (measurable_snd.comp (hz t)))

lemma measurable_sHat (j : ℕ) : Measurable (sHat q proj I j) := by
  obtain ⟨hx, he, -⟩ := measurable_avgs h j
  unfold sHat
  refine ((Finset.measurable_sum _ fun i _ => ?_).div_const _).sqrt
  have hl : Measurable (fun ζ : ℕ → q.Ξ => I.loss (proj (xAvg q proj I j ζ)) (ζ (sgdSteps q + i))) :=
    h.loss_meas.comp ((h.proj_meas.comp hx).prodMk (measurable_pi_apply _))
  exact ((hl.sub he).max measurable_const).pow_const 2

lemma measurable_nrm_joint :
    Measurable (fun w : q.E × ℝ => nrm (I.law : Measure q.Ξ) (I.loss w.1) w.2) := by
  have hT : Measurable (fun z : (q.E × ℝ) × q.Ξ => tail (I.loss z.1.1) z.1.2 z.2 ^ 2) := by
    unfold tail
    exact (((h.loss_meas.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub
      (measurable_snd.comp measurable_fst)).max measurable_const).pow_const 2
  have := (hT.stronglyMeasurable.integral_prod_right' (ν := (I.law : Measure q.Ξ))).measurable
  exact this.sqrt

lemma measurable_sErr (j : ℕ) : Measurable (sErr q proj I j) := by
  obtain ⟨hx, he, -⟩ := measurable_avgs h j
  exact (measurable_sHat h j).sub ((measurable_nrm_joint h).comp (hx.prodMk he))

lemma measurable_best : ∀ n, Measurable (fun ξ => best q proj I.loss I.sub ξ n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hx : Measurable (fun ξ => xbar q proj I.loss I.sub n ξ) :=
      (measurable_avgs h n).1.comp (measurable_block n)
    have hf : Measurable (fun ξ => fhat q proj I.loss I.sub n ξ) := by
      simp_rw [fhat_eq]
      exact ((measurable_avgs h n).2.1.comp (measurable_block n)).add
        (measurable_const.mul ((measurable_sHat h n).comp (measurable_block n)))
    have hset : MeasurableSet {ξ | n = 0 ∨ fhat q proj I.loss I.sub n ξ <
        (best q proj I.loss I.sub ξ n).2} := by
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, false_or]
        exact measurableSet_lt hf (measurable_snd.comp ih)
    simp only [best]
    exact Measurable.ite hset (hx.prodMk hf) ih

end Measurability

lemma best_spec (ξ : ℕ → q.Ξ) : ∀ n, 0 < n → ∃ i < n,
    best q proj I.loss I.sub ξ n = (xbar q proj I.loss I.sub i ξ, fhat q proj I.loss I.sub i ξ) ∧
      ∀ i' < n, fhat q proj I.loss I.sub i ξ ≤ fhat q proj I.loss I.sub i' ξ := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h0 : n = 0
    · subst h0
      refine ⟨0, by omega, by simp [best], fun i' hi' => ?_⟩
      have : i' = 0 := by omega
      rw [this]
    · obtain ⟨i, hi, hb, hmin⟩ := ih (Nat.pos_of_ne_zero h0)
      simp only [best, h0, false_or]
      rw [hb]
      split_ifs with hlt
      · refine ⟨n, by omega, rfl, fun i' hi' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h' | h'
        · exact hlt.le.trans (hmin i' h')
        · rw [h']
      · replace hlt := not_lt.mp hlt
        refine ⟨i, by omega, rfl, fun i' hi' => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h' | h'
        · exact hmin i' h'
        · rw [h']; exact hlt

lemma block_preserving (j : ℕ) :
    MeasurePreserving (block q j) (Measure.infinitePi fun _ : ℕ => (I.law : Measure q.Ξ))
      (Measure.infinitePi fun _ : ℕ => (I.law : Measure q.Ξ)) :=
  measurePreserving_snd.comp (splitStream_preserving (I.law : Measure q.Ξ) (j * bracketLength q))

section Analysis

variable (h : Adm q I proj) (hρ : 0 < q.ρ) (hG : 0 < q.G) (hB : 0 < q.B) (hε : 0 < q.ε)
include h hρ hG hB hε

omit hG hε in
lemma nrm_le_tail {x : q.E} (hx : x ∈ I.domain) {η : ℝ} (hη : etaLow q ≤ η) :
    nrm (I.law : Measure q.Ξ) (I.loss x) η ≤ tailBound q := by
  have hb : ∀ ξ, tail (I.loss x) η ξ ≤ tailBound q := fun ξ => by
    unfold tail; rw [← B_sub_etaLow]
    exact max_le (by linarith [(h.bounds ξ x hx).2]) (by linarith [etaLow_le hρ hB])
  have hsq : sq (I.law : Measure q.Ξ) (I.loss x) η ≤ tailBound q ^ 2 := by
    unfold sq
    have := integral_mono_of_nonneg (μ := (I.law : Measure q.Ξ))
      (ae_of_all _ fun ξ => sq_nonneg (tail (I.loss x) η ξ)) (integrable_const (tailBound q ^ 2))
      (ae_of_all _ fun ξ => pow_le_pow_left₀ (tail_nonneg _ _ _) (hb ξ) 2)
    simpa using this
  unfold nrm
  calc Real.sqrt _ ≤ Real.sqrt (tailBound q ^ 2) := Real.sqrt_le_sqrt hsq
    _ = tailBound q := Real.sqrt_sq (tailBound_pos hρ hB).le

lemma avg_props (j : ℕ) (ζ : ℕ → q.Ξ) :
    xAvg q proj I j ζ ∈ I.domain ∧ eAvg q proj I j ζ ∈ Icc (etaLow q) q.B ∧
      sAvg q proj I j ζ ∈ Icc (scaleLow q j) (4 * scaleLow q j) := by
  have hy := hyp_cfg h hρ hG hB hε j
  have hT := sgdSteps_pos (q := q)
  have he0 : (start q j).2.1 ∈ Icc (cfg q j).elo (cfg q j).ehi := zero_mem_eta hρ hB
  have hs0 : (start q j).2.2 ∈ Icc (cfg q j).slo (cfg q j).shi :=
    ⟨le_rfl, by change scaleLow q j ≤ 4 * scaleLow q j; linarith [scaleLow_pos hρ hε j]⟩
  refine ⟨avgX_mem hy h.convex hT _ ζ, ?_, ?_⟩
  · exact avg_mem_Icc hT _ fun t => (run_mem hy he0 hs0 ζ t).1
  · exact avg_mem_Icc hT _ fun t => (run_mem hy he0 hs0 ζ t).2

lemma sErr_sq_integral (j : ℕ) :
    Integrable (fun ζ => sErr q proj I j ζ ^ 2) (Measure.infinitePi fun _ : ℕ => (I.law : Measure q.Ξ)) ∧
    (∫ ζ, sErr q proj I j ζ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => (I.law : Measure q.Ξ))) ≤
      tailBound q ^ 2 / selectionSamples q := by
  set p := (I.law : Measure q.Ξ)
  set PP := Measure.infinitePi fun _ : ℕ => p
  set T := sgdSteps q
  set m := selectionSamples q
  have hm : 0 < m := selectionSamples_pos q
  have hb := tailBound_pos hρ hB
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  have hcong : ∀ ζ : ℕ → q.Ξ, xAvg q proj I j ζ = xAvg q proj I j (extend ω0 (fun i : Fin T => ζ i)) ∧
      eAvg q proj I j ζ = eAvg q proj I j (extend ω0 (fun i : Fin T => ζ i)) := by
    intro ζ
    have hr : ∀ t ∈ Finset.range T, run (cfg q j) proj I.loss I.sub (start q j) ζ t =
        run (cfg q j) proj I.loss I.sub (start q j) (extend ω0 (fun i : Fin T => ζ i)) t := by
      intro t ht
      refine run_congr _ t fun i hi => ?_
      exact (extend_agree ω0 ζ i (lt_trans hi (Finset.mem_range.mp ht))).symm
    constructor
    · unfold xAvg avgX; rw [Finset.sum_congr rfl fun t ht => by rw [hr t ht]]
    · unfold eAvg avgE; rw [Finset.sum_congr rfl fun t ht => by rw [hr t ht]]
  let Y : (Fin T → q.Ξ) → q.Ξ → ℝ := fun u ω =>
    tail (I.loss (xAvg q proj I j (extend ω0 u))) (eAvg q proj I j (extend ω0 u)) ω
  let H : (Fin T → q.Ξ) × (ℕ → q.Ξ) → ℝ := fun z =>
    (Real.sqrt ((∑ i : Fin m, Y z.1 (z.2 i) ^ 2) / m) - Real.sqrt (∫ ω, Y z.1 ω ^ 2 ∂p)) ^ 2
  have hfix : ∀ u : Fin T → q.Ξ, proj (xAvg q proj I j (extend ω0 u)) =
      xAvg q proj I j (extend ω0 u) := fun u =>
    proj_fix h.proj_vi (avg_props h hρ hG hB hε j _).1
  have hpt : ∀ ζ, sErr q proj I j ζ ^ 2 = H (splitStream T ζ) := by
    intro ζ
    obtain ⟨hx, he⟩ := hcong ζ
    unfold sErr sHat nrm sq
    rw [hx, he, hfix, Finset.sum_range]
    rfl
  have hXm : Measurable (fun u : Fin T → q.Ξ => xAvg q proj I j (extend ω0 u)) :=
    (measurable_avgs h j).1.comp (measurable_extend ω0)
  have hEm : Measurable (fun u : Fin T → q.Ξ => eAvg q proj I j (extend ω0 u)) :=
    (measurable_avgs h j).2.1.comp (measurable_extend ω0)
  have hYm : Measurable (fun z : (Fin T → q.Ξ) × q.Ξ => Y z.1 z.2) := by
    exact (h.loss_meas.comp ((hXm.comp measurable_fst).prodMk measurable_snd)).sub
      (hEm.comp measurable_fst) |>.max measurable_const
  have hY0 : ∀ u ω, 0 ≤ Y u ω := fun u ω => tail_nonneg _ _ _
  have hYb : ∀ u ω, Y u ω ≤ tailBound q := fun u ω => by
    obtain ⟨hx, he, -⟩ := avg_props h hρ hG hB hε j (extend ω0 u)
    unfold Y tail; rw [← B_sub_etaLow]
    exact max_le (by linarith [(h.bounds ω _ hx).2, he.1]) (by linarith [etaLow_le hρ hB])
  have hHm : Measurable H := by
    have h1 : Measurable (fun z : (Fin T → q.Ξ) × (ℕ → q.Ξ) => ∑ i : Fin m, Y z.1 (z.2 i) ^ 2) :=
      Finset.measurable_sum _ fun i _ =>
        (hYm.comp (measurable_fst.prodMk ((measurable_pi_apply (i : ℕ)).comp measurable_snd))).pow_const 2
    have h2 : Measurable (fun z : (Fin T → q.Ξ) × (ℕ → q.Ξ) => ∫ ω, Y z.1 ω ^ 2 ∂p) := by
      have := ((hYm.pow_const 2).stronglyMeasurable.integral_prod_right' (ν := p)).measurable
      exact this.comp measurable_fst
    exact ((h1.div_const _).sqrt.sub h2.sqrt).pow_const 2
  have hYu : ∀ u : Fin T → q.Ξ, Measurable (Y u) := fun u =>
    measurable_tail (measurable_section h.loss_meas _) _
  have hHb : ∀ z, ‖H z‖ ≤ tailBound q ^ 2 := by
    intro z
    have hsum' : ∑ i : Fin m, Y z.1 (z.2 i) ^ 2 ≤ ∑ _i : Fin m, tailBound q ^ 2 :=
      Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hY0 z.1 (z.2 i)) (hYb z.1 (z.2 i)) 2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum'
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hsum : (∑ i : Fin m, Y z.1 (z.2 i) ^ 2) / m ≤ tailBound q ^ 2 := by
      rw [div_le_iff₀ hm0]; linarith
    have hint : (∫ ω, Y z.1 ω ^ 2 ∂p) ≤ tailBound q ^ 2 := by
      have := integral_mono_of_nonneg (μ := p) (ae_of_all _ fun ω => sq_nonneg (Y z.1 ω))
        (integrable_const (tailBound q ^ 2))
        (ae_of_all _ fun ω => pow_le_pow_left₀ (hY0 z.1 ω) (hYb z.1 ω) 2)
      rwa [integral_const, probReal_univ, one_smul] at this
    have ha := Real.sqrt_le_sqrt hsum
    have hc := Real.sqrt_le_sqrt hint
    rw [Real.sqrt_sq hb.le] at ha hc
    have ha0 := Real.sqrt_nonneg ((∑ i : Fin m, Y z.1 (z.2 i) ^ 2) / m)
    have hc0 := Real.sqrt_nonneg (∫ ω, Y z.1 ω ^ 2 ∂p)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hab : |Real.sqrt ((∑ i : Fin m, Y z.1 (z.2 i) ^ 2) / m) - Real.sqrt (∫ ω, Y z.1 ω ^ 2 ∂p)| ≤
        tailBound q := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    have := pow_le_pow_left₀ (abs_nonneg _) hab 2
    rwa [sq_abs] at this
  have hHi : Integrable H ((Measure.pi fun _ : Fin T => p).prod PP) :=
    Integrable.of_bound hHm.aestronglyMeasurable (tailBound q ^ 2) (ae_of_all _ hHb)
  have hS := splitStream_preserving p T
  have hfun : (fun ζ => sErr q proj I j ζ ^ 2) = fun ζ => H (splitStream T ζ) := funext hpt
  have hinner : ∀ u, (∫ τ, H (u, τ) ∂PP) ≤ tailBound q ^ 2 / m := by
    intro u
    have hfst : MeasurePreserving (fun τ : ℕ → q.Ξ => fun i : Fin m => τ i) PP
        (Measure.pi fun _ : Fin m => p) :=
      measurePreserving_fst.comp (splitStream_preserving p m)
    have hGm : Measurable (fun v : Fin m → q.Ξ =>
        (Real.sqrt ((∑ i : Fin m, Y u (v i) ^ 2) / m) - Real.sqrt (∫ ω, Y u ω ^ 2 ∂p)) ^ 2) := by
      have : Measurable (fun v : Fin m → q.Ξ => ∑ i : Fin m, Y u (v i) ^ 2) :=
        Finset.measurable_sum _ fun i _ => ((hYu u).comp (measurable_pi_apply i)).pow_const 2
      exact ((this.div_const _).sqrt.sub_const _).pow_const 2
    change (∫ τ, (fun v : Fin m → q.Ξ =>
        (Real.sqrt ((∑ i : Fin m, Y u (v i) ^ 2) / m) - Real.sqrt (∫ ω, Y u ω ^ 2 ∂p)) ^ 2)
        (fun i : Fin m => τ i) ∂PP) ≤ _
    have key := integral_map (μ := PP) hfst.measurable.aemeasurable
      (f := fun v : Fin m → q.Ξ =>
        (Real.sqrt ((∑ i : Fin m, Y u (v i) ^ 2) / m) - Real.sqrt (∫ ω, Y u ω ^ 2 ∂p)) ^ 2)
      (by rw [hfst.map_eq]; exact hGm.aestronglyMeasurable)
    rw [hfst.map_eq] at key
    rw [← key]
    exact (sqrt_mean_dev p (hYu u) (hY0 u) (hYb u) hm).2
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact integrable_of_preserving hS hHi
  · rw [hfun, hS.integral_comp' H, integral_prod H hHi]
    have := integral_mono hHi.integral_prod_left (integrable_const (tailBound q ^ 2 / m)) hinner
    rwa [integral_const, probReal_univ, one_smul] at this

omit hG in
lemma pot_le {xs : q.E} (hR : ‖q.x0 - xs‖ ≤ q.R) {es : ℝ}
    (hes : es ∈ Icc (etaLow q) q.B) {j : ℕ} {ss : ℝ} (hss : ss ∈ Icc (scaleLow q j) (4 * scaleLow q j))
    (h2 : radius q ^ 2 * scaleLow q j ^ 2 ≤ q.ε ^ 2 / 64 + radius q ^ 2 * tailBound q ^ 2) :
    potential (cfg q j) proj xs es ss (start q j) / sgdSteps q ≤ q.ε / 8 := by
  have hc := radius_pos hρ
  have hc1 := radius_ge_one hρ
  have hs := scaleLow_pos hρ hε j
  have hb := tailBound_pos hρ hB
  have hT := sgdSteps_ge (q := q)
  have hT0 : (0 : ℝ) < sgdSteps q := by exact_mod_cast sgdSteps_pos (q := q)
  set c := radius q with hcdef
  set sl := scaleLow q j with hsdef
  set b := tailBound q with hbdef
  set W := q.B ^ 2 * (1 + 1 / q.ρ)
  have hW : b ^ 2 ≤ 2 * W := tailBound_sq_le hρ
  have hc2 : c ^ 2 = 1 + 2 * q.ρ := radius_sq hρ
  have hx0 : proj q.x0 = q.x0 := proj_fix h.proj_vi h.x0_mem
  have hW0 : 0 ≤ W := by have := hρ.le; positivity
  unfold potential
  rw [div_le_iff₀ hT0]
  change ‖proj q.x0 - xs‖ ^ 2 / stepX q + (0 - es) ^ 2 / stepEta q + (sl - ss) ^ 2 / stepScale q j ≤
    q.ε / 8 * sgdSteps q
  rw [hx0]
  have t1 : ‖q.x0 - xs‖ ^ 2 / stepX q ≤ q.R ^ 2 * (128 * c ^ 2 * q.G ^ 2) / q.ε := by
    have e : ‖q.x0 - xs‖ ^ 2 / stepX q = ‖q.x0 - xs‖ ^ 2 * (128 * c ^ 2 * q.G ^ 2) / q.ε := by
      unfold stepX; rw [← hcdef]; field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hR 2) (by positivity)) hε.le
  have hes2 : es ^ 2 ≤ b ^ 2 := by
    have hlo : -b ≤ es := by
      have := hes.1; unfold etaLow at this; unfold b tailBound; linarith
    have hhi : es ≤ b := by
      have := hes.2; unfold b tailBound
      have : 0 ≤ q.B / Real.sqrt q.ρ := by have := Real.sqrt_pos.mpr hρ; positivity
      linarith
    nlinarith
  have t2 : (0 - es) ^ 2 / stepEta q ≤ b ^ 2 * (768 * c ^ 2) / q.ε := by
    have e : (0 - es) ^ 2 / stepEta q = es ^ 2 * (128 * (2 + 4 * c ^ 2)) / q.ε := by
      unfold stepEta; rw [← hcdef]; field_simp; ring
    rw [e]
    apply div_le_div_of_nonneg_right _ hε.le
    have : 128 * (2 + 4 * c ^ 2) ≤ 768 * c ^ 2 := by nlinarith
    exact mul_le_mul hes2 this (by positivity) (sq_nonneg _)
  have t3 : (sl - ss) ^ 2 / stepScale q j ≤ (9 * q.ε ^ 2 + 1728 * c ^ 2 * b ^ 2) / q.ε := by
    have e : (sl - ss) ^ 2 / stepScale q j =
        (sl - ss) ^ 2 / sl ^ 2 * (128 * c ^ 2 * (sl ^ 2 / 2 + b ^ 2)) / q.ε := by
      unfold stepScale; rw [← hcdef, ← hsdef, ← hbdef]; field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hε.le
    have hq : (sl - ss) ^ 2 / sl ^ 2 ≤ 9 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [hss.1, hss.2]
    calc (sl - ss) ^ 2 / sl ^ 2 * (128 * c ^ 2 * (sl ^ 2 / 2 + b ^ 2)) ≤
        9 * (128 * c ^ 2 * (sl ^ 2 / 2 + b ^ 2)) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
      _ = 576 * (c ^ 2 * sl ^ 2) + 1152 * c ^ 2 * b ^ 2 := by ring
      _ ≤ 576 * (q.ε ^ 2 / 64 + c ^ 2 * b ^ 2) + 1152 * c ^ 2 * b ^ 2 := by nlinarith
      _ = 9 * q.ε ^ 2 + 1728 * c ^ 2 * b ^ 2 := by ring
  have hsum : q.R ^ 2 * (128 * c ^ 2 * q.G ^ 2) / q.ε + b ^ 2 * (768 * c ^ 2) / q.ε +
      (9 * q.ε ^ 2 + 1728 * c ^ 2 * b ^ 2) / q.ε =
      (128 * (c ^ 2 * q.G ^ 2 * q.R ^ 2) + 2496 * (c ^ 2 * b ^ 2) + 9 * q.ε ^ 2) / q.ε := by
    field_simp; ring
  have hrhs : q.ε / 8 * (2 ^ 16 * (1 + 2 * q.ρ) * (q.G ^ 2 * q.R ^ 2 + W) / q.ε ^ 2 + 144) =
      (8192 * (c ^ 2 * q.G ^ 2 * q.R ^ 2) + 8192 * (c ^ 2 * W) + 18 * q.ε ^ 2) / q.ε := by
    rw [← hc2]; field_simp; ring
  have hcmp : (128 * (c ^ 2 * q.G ^ 2 * q.R ^ 2) + 2496 * (c ^ 2 * b ^ 2) + 9 * q.ε ^ 2) / q.ε ≤
      (8192 * (c ^ 2 * q.G ^ 2 * q.R ^ 2) + 8192 * (c ^ 2 * W) + 18 * q.ε ^ 2) / q.ε := by
    apply div_le_div_of_nonneg_right _ hε.le
    have : c ^ 2 * b ^ 2 ≤ 2 * (c ^ 2 * W) := by
      have := mul_le_mul_of_nonneg_left hW (sq_nonneg c); linarith
    have hA : 0 ≤ c ^ 2 * q.G ^ 2 * q.R ^ 2 := by positivity
    have hcW : 0 ≤ c ^ 2 * W := by positivity
    linarith [sq_nonneg q.ε]
  have hT' := mul_le_mul_of_nonneg_left hT (show 0 ≤ q.ε / 8 by positivity)
  calc _ ≤ q.R ^ 2 * (128 * c ^ 2 * q.G ^ 2) / q.ε + b ^ 2 * (768 * c ^ 2) / q.ε +
        (9 * q.ε ^ 2 + 1728 * c ^ 2 * b ^ 2) / q.ε := add_le_add (add_le_add t1 t2) t3
    _ = _ := hsum
    _ ≤ _ := hcmp
    _ = _ := hrhs.symm
    _ ≤ _ := hT'

lemma phi_good_bracket {xs : q.E} (hxs : xs ∈ I.domain)
    (hmin : IsMinOn (objective I) I.domain xs) (hR : ‖q.x0 - xs‖ ≤ q.R) :
    ∃ j0 < numBrackets q,
      Integrable (fun ζ => PhiX (I.law : Measure q.Ξ) (cfg q j0) I.loss (xAvg q proj I j0 ζ)
        (eAvg q proj I j0 ζ) (sAvg q proj I j0 ζ))
        (Measure.infinitePi fun _ : ℕ => (I.law : Measure q.Ξ)) ∧
      (∫ ζ, PhiX (I.law : Measure q.Ξ) (cfg q j0) I.loss (xAvg q proj I j0 ζ)
        (eAvg q proj I j0 ζ) (sAvg q proj I j0 ζ)
        ∂(Measure.infinitePi fun _ : ℕ => (I.law : Measure q.Ξ))) - objective I xs ≤
        9 * q.ε / 32 := by
  set p := (I.law : Measure q.Ξ)
  set V := objective I xs
  have hlm : ∀ x, Measurable (I.loss x) := fun x => measurable_section h.loss_meas x
  have hL : ∀ x ∈ I.domain, ∀ η, V ≤ η + (cfg q 0).c * nrm p (I.loss x) η := by
    intro x hx η
    have h1 : V ≤ objective I x := hmin hx
    have h2 := objective_le I hρ.le (hlm x) (fun ξ => (h.bounds ξ x hx).1)
      (fun ξ => (h.bounds ξ x hx).2) η
    exact h1.trans h2
  obtain ⟨es, hes, hdual⟩ := dual_attained I hρ hB (hlm xs) (fun ξ => (h.bounds ξ xs hxs).1)
    (fun ξ => (h.bounds ξ xs hxs).2)
  set st := nrm p (I.loss xs) es
  have hst0 : 0 ≤ st := nrm_nonneg _ _ _
  have hstB : st ≤ tailBound q := nrm_le_tail h hρ hB hxs hes.1
  obtain ⟨j0, hj0, ss, hss, h1, h2⟩ := good_bracket hρ hε hst0 hstB
  refine ⟨j0, hj0, ?_, ?_⟩
  · have hy := hyp_cfg h hρ hG hB hε j0
    have hm := (measurable_PhiX' p (k := cfg q j0) h.loss_meas).comp
      ((measurable_avgs h j0).1.prodMk ((measurable_avgs h j0).2.1.prodMk (measurable_avgs h j0).2.2))
    refine Integrable.of_bound hm.aestronglyMeasurable (phiBound (cfg q j0) q.B)
      (ae_of_all _ fun ζ => ?_)
    obtain ⟨hx, he, hs⟩ := avg_props h hρ hG hB hε j0 ζ
    rw [Real.norm_eq_abs]
    exact PhiX_abs_le p hy hx he hs
  · have hy := hyp_cfg h hρ hG hB hε j0
    have hss' : ss ∈ Icc (cfg q j0).slo (cfg q j0).shi := hss
    have he0 : (start q j0).2.1 ∈ Icc (cfg q j0).elo (cfg q j0).ehi := zero_mem_eta hρ hB
    have hs0 : (start q j0).2.2 ∈ Icc (cfg q j0).slo (cfg q j0).shi :=
      ⟨le_rfl, by change scaleLow q j0 ≤ 4 * scaleLow q j0; linarith [scaleLow_pos hρ hε j0]⟩
    have hbb := bracket_bound p hy h.convex h.proj_meas h.loss_meas h.sub_meas he0 hs0 hxs
      hes hss' (L := V) (fun x hx η => hL x hx η) (noiseSlope_le hρ hG hε j0)
      (sgdSteps_pos (q := q))
    rw [noiseConst_eq hρ hG hε j0] at hbb
    have hpot := pot_le h hρ hB hε hR hes hss h2
    have hΦ : PhiX p (cfg q j0) I.loss xs es ss - V ≤ q.ε / 16 := by
      rw [PhiX_eq p hy h.loss_meas hxs es ss]
      have hsq : sq p (I.loss xs) es = st ^ 2 := (nrm_sq _ _ _).symm
      rw [hsq]
      have hss0 : 0 < ss := lt_of_lt_of_le (scaleLow_pos hρ hε j0) hss.1
      have e : radius q * st ^ 2 / (2 * ss) + radius q * ss / 2 - radius q * st =
          radius q * (ss - st) ^ 2 / (2 * ss) := by
        field_simp; ring
      have hd : es + radius q * st ≤ V := hdual
      change es + radius q * st ^ 2 / (2 * ss) + radius q * ss / 2 - V ≤ q.ε / 16
      linarith
    unfold xAvg eAvg sAvg
    linarith

lemma pointwise_gap {j0 : ℕ} (hj0 : j0 < numBrackets q) (ξ : ℕ → q.Ξ) {a : ℝ} (ha : 0 < a) :
    objective I (best q proj I.loss I.sub ξ (numBrackets q)).1 ≤
      PhiX (I.law : Measure q.Ξ) (cfg q j0) I.loss (xAvg q proj I j0 (block q j0 ξ))
        (eAvg q proj I j0 (block q j0 ξ)) (sAvg q proj I j0 (block q j0 ξ)) +
      radius q * ((∑ j ∈ Finset.range (numBrackets q), sErr q proj I j (block q j ξ) ^ 2) / a + a) := by
  set p := (I.law : Measure q.Ξ)
  have hN : 0 < numBrackets q := lt_of_le_of_lt (Nat.zero_le _) hj0
  obtain ⟨i, hi, hb, hmin⟩ := best_spec (proj := proj) (I := I) ξ (numBrackets q) hN
  rw [hb]
  simp only
  rw [xbar_eq]
  set ζi := block q i ξ
  set ζ0 := block q j0 ξ
  obtain ⟨hxi, hei, -⟩ := avg_props h hρ hG hB hε i ζi
  obtain ⟨hx0, he0, hs0⟩ := avg_props h hρ hG hB hε j0 ζ0
  have hlm : ∀ x, Measurable (I.loss x) := fun x => measurable_section h.loss_meas x
  have hobj := objective_le I hρ.le (hlm _) (fun ξ => (h.bounds ξ _ hxi).1)
    (fun ξ => (h.bounds ξ _ hxi).2) (eAvg q proj I i ζi)
  have hf := hmin j0 hj0
  rw [fhat_eq, fhat_eq] at hf
  have hy := hyp_cfg h hρ hG hB hε j0
  have hphi := PhiX_ge p hy h.loss_meas hx0 (lt_of_lt_of_le (scaleLow_pos hρ hε j0) hs0.1)
    (L := eAvg q proj I j0 ζ0 + (cfg q j0).c * nrm p (I.loss (xAvg q proj I j0 ζ0))
      (eAvg q proj I j0 ζ0)) le_rfl
  have hc : (cfg q j0).c = radius q := rfl
  rw [hc] at hphi
  have hsum : sErr q proj I i ζi ^ 2 ≤ ∑ j ∈ Finset.range (numBrackets q), sErr q proj I j (block q j ξ) ^ 2 :=
    Finset.single_le_sum (f := fun j => sErr q proj I j (block q j ξ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_range.mpr hi)
  have hsum0 : sErr q proj I j0 ζ0 ^ 2 ≤ ∑ j ∈ Finset.range (numBrackets q), sErr q proj I j (block q j ξ) ^ 2 :=
    Finset.single_le_sum (f := fun j => sErr q proj I j (block q j ξ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_range.mpr hj0)
  have a1 := abs_le_amgm (x := sErr q proj I i ζi) ha
  have a2 := abs_le_amgm (x := sErr q proj I j0 ζ0) ha
  have hS : |sErr q proj I i ζi| + |sErr q proj I j0 ζ0| ≤
      (∑ j ∈ Finset.range (numBrackets q), sErr q proj I j (block q j ξ) ^ 2) / a + a := by
    have e : (∑ j ∈ Finset.range (numBrackets q), sErr q proj I j (block q j ξ) ^ 2) / a =
        2 * ((∑ j ∈ Finset.range (numBrackets q), sErr q proj I j (block q j ξ) ^ 2) / (2 * a)) := by
      field_simp
    have b1 : sErr q proj I i ζi ^ 2 / (2 * a) ≤
        (∑ j ∈ Finset.range (numBrackets q), sErr q proj I j (block q j ξ) ^ 2) / (2 * a) :=
      div_le_div_of_nonneg_right hsum (by positivity)
    have b2 : sErr q proj I j0 ζ0 ^ 2 / (2 * a) ≤
        (∑ j ∈ Finset.range (numBrackets q), sErr q proj I j (block q j ξ) ^ 2) / (2 * a) :=
      div_le_div_of_nonneg_right hsum0 (by positivity)
    linarith
  have hcr := radius_pos hρ
  have hS' := mul_le_mul_of_nonneg_left hS hcr.le
  unfold sErr at hS' ⊢
  have l1 := neg_abs_le (sHat q proj I i ζi - nrm p (I.loss (xAvg q proj I i ζi)) (eAvg q proj I i ζi))
  have l2 := le_abs_self (sHat q proj I j0 ζ0 - nrm p (I.loss (xAvg q proj I j0 ζ0)) (eAvg q proj I j0 ζ0))
  nlinarith [mul_le_mul_of_nonneg_left l1 hcr.le, mul_le_mul_of_nonneg_left l2 hcr.le]

omit hB hε in
lemma measurable_objective_comp {Ω : Type*} [MeasurableSpace Ω] {f : Ω → q.E} (hf : Measurable f)
    (hfD : ∀ ω, f ω ∈ I.domain) : Measurable (fun ω => objective I (f ω)) := by
  have hlip : LipschitzWith (Real.toNNReal q.G) (fun x => objective I (proj x)) := by
    refine LipschitzWith.of_le_add_mul' q.G fun x y => ?_
    have h1 := objective_lipschitz I hρ.le h.loss_meas h.subgrad h.sub_le h.bounds
      (h.proj_mem x) (h.proj_mem y)
    have h2 := proj_nonexpansive h.proj_mem h.proj_vi x y
    rw [dist_eq_norm]
    nlinarith [mul_le_mul_of_nonneg_left h2 hG.le]
  have he : (fun ω => objective I (f ω)) = fun ω => objective I (proj (f ω)) := by
    funext ω; rw [proj_fix h.proj_vi (hfD ω)]
  rw [he]
  exact hlip.continuous.measurable.comp hf

lemma best_mem (ξ : ℕ → q.Ξ) : (best q proj I.loss I.sub ξ (numBrackets q)).1 ∈ I.domain := by
  have hN : 0 < numBrackets q := by unfold numBrackets; omega
  obtain ⟨i, -, hb, -⟩ := best_spec (proj := proj) (I := I) ξ (numBrackets q) hN
  rw [hb]
  exact (avg_props h hρ hG hB hε i (block q i ξ)).1

lemma expected_gap {xs : q.E} (hxs : xs ∈ I.domain)
    (hmin : IsMinOn (objective I) I.domain xs) (hR : ‖q.x0 - xs‖ ≤ q.R) :
    Integrable (fun ξ => objective I (best q proj I.loss I.sub ξ (numBrackets q)).1 - objective I xs)
      (Measure.infinitePi fun _ : ℕ => (I.law : Measure q.Ξ)) ∧
    (∫ ξ, objective I (best q proj I.loss I.sub ξ (numBrackets q)).1 - objective I xs
      ∂(Measure.infinitePi fun _ : ℕ => (I.law : Measure q.Ξ))) ≤ q.ε := by
  set p := (I.law : Measure q.Ξ)
  set PP := Measure.infinitePi fun _ : ℕ => p
  set V := objective I xs
  set N := numBrackets q
  set T := sgdSteps q
  set c := radius q
  obtain ⟨j0, hj0, hPi, hPb⟩ := phi_good_bracket h hρ hG hB hε hxs hmin hR
  have hc := radius_pos hρ
  set a := q.ε / (16 * c)
  have ha : 0 < a := by positivity
  set F : (ℕ → q.Ξ) → ℝ := fun ζ => PhiX p (cfg q j0) I.loss (xAvg q proj I j0 ζ)
    (eAvg q proj I j0 ζ) (sAvg q proj I j0 ζ)
  have hbp := block_preserving (q := q) (I := I) j0
  have hg1 : Integrable (fun ξ => F (block q j0 ξ)) PP := integrable_of_preserving hbp hPi
  have hg1E : (∫ ξ, F (block q j0 ξ) ∂PP) = ∫ ζ, F ζ ∂PP := by
    have := integral_map (μ := PP) hbp.measurable.aemeasurable
      (show AEStronglyMeasurable F (PP.map (block q j0)) by rw [hbp.map_eq]; exact hPi.aestronglyMeasurable)
    rw [hbp.map_eq] at this
    exact this.symm
  have hg2 : ∀ j, Integrable (fun ξ => sErr q proj I j (block q j ξ) ^ 2) PP := fun j =>
    integrable_of_preserving (block_preserving j) (sErr_sq_integral h hρ hG hB hε j).1
  have hg2E : ∀ j, (∫ ξ, sErr q proj I j (block q j ξ) ^ 2 ∂PP) ≤ tailBound q ^ 2 / selectionSamples q := by
    intro j
    have hbj := block_preserving (q := q) (I := I) j
    have hi := (sErr_sq_integral h hρ hG hB hε j)
    have := integral_map (μ := PP) hbj.measurable.aemeasurable
      (show AEStronglyMeasurable (fun ζ => sErr q proj I j ζ ^ 2) (PP.map (block q j)) by
        rw [hbj.map_eq]; exact hi.1.aestronglyMeasurable)
    rw [hbj.map_eq] at this
    rw [← this]; exact hi.2
  have hout : Measurable (fun ξ => (best q proj I.loss I.sub ξ N).1) := (measurable_best h N).fst
  have hom : Measurable (fun ξ => objective I (best q proj I.loss I.sub ξ N).1) :=
    measurable_objective_comp h hρ hG hout (best_mem h hρ hG hB hε)
  have hlm : ∀ x, Measurable (I.loss x) := fun x => measurable_section h.loss_meas x
  have hLi : Integrable (fun ξ => objective I (best q proj I.loss I.sub ξ N).1 - V) PP := by
    refine Integrable.of_bound (hom.sub_const V).aestronglyMeasurable (q.B + |V|)
      (ae_of_all _ fun ξ => ?_)
    have hx := best_mem h hρ hG hB hε ξ
    have h0 := objective_nonneg I hρ.le (hlm _) (fun ζ => (h.bounds ζ _ hx).1) (fun ζ => (h.bounds ζ _ hx).2)
    have h1 := objective_le_bound I hρ.le (hlm _) (fun ζ => (h.bounds ζ _ hx).1)
      (fun ζ => (h.bounds ζ _ hx).2)
    rw [Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg h0]; linarith
  refine ⟨hLi, ?_⟩
  have hsumI : Integrable (fun ξ => ∑ j ∈ Finset.range N, sErr q proj I j (block q j ξ) ^ 2) PP :=
    integrable_finsetSum _ fun j _ => hg2 j
  have hRi : Integrable (fun ξ => F (block q j0 ξ) - V +
      c * ((∑ j ∈ Finset.range N, sErr q proj I j (block q j ξ) ^ 2) / a + a)) PP :=
    (hg1.sub (integrable_const V)).add (((hsumI.div_const a).add (integrable_const a)).const_mul c)
  have hmono := integral_mono hLi hRi fun ξ => by
    have := pointwise_gap h hρ hG hB hε hj0 ξ ha
    simp only [F]
    linarith
  have hR1 : Integrable (fun ξ => F (block q j0 ξ) - V) PP := hg1.sub (integrable_const V)
  have hR3 : Integrable (fun ξ => (∑ j ∈ Finset.range N, sErr q proj I j (block q j ξ) ^ 2) / a) PP :=
    hsumI.div_const a
  have hR4 : Integrable (fun ξ => (∑ j ∈ Finset.range N, sErr q proj I j (block q j ξ) ^ 2) / a + a) PP :=
    hR3.add (integrable_const a)
  have hR2 : Integrable (fun ξ => c * ((∑ j ∈ Finset.range N, sErr q proj I j (block q j ξ) ^ 2) / a + a))
      PP := hR4.const_mul c
  have hval : (∫ ξ, F (block q j0 ξ) - V +
      c * ((∑ j ∈ Finset.range N, sErr q proj I j (block q j ξ) ^ 2) / a + a) ∂PP) =
      ((∫ ζ, F ζ ∂PP) - V) +
        c * ((∑ j ∈ Finset.range N, ∫ ξ, sErr q proj I j (block q j ξ) ^ 2 ∂PP) / a + a) := by
    rw [integral_add hR1 hR2, integral_sub hg1 (integrable_const V), integral_const_mul,
      integral_add hR3 (integrable_const a), integral_div, integral_finsetSum _ fun j _ => hg2 j, hg1E]
    simp only [integral_const, probReal_univ, one_smul]
  refine hmono.trans (le_of_eq_of_le hval ?_)
  have hsumb : ∑ j ∈ Finset.range N, (∫ ξ, sErr q proj I j (block q j ξ) ^ 2 ∂PP) ≤
      N * (tailBound q ^ 2 / selectionSamples q) := by
    have := Finset.sum_le_sum fun j (_ : j ∈ Finset.range N) => hg2E j
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  have hT0 : (0 : ℝ) < T := by exact_mod_cast sgdSteps_pos (q := q)
  have hN0 : (0 : ℝ) < N := by unfold N numBrackets; positivity
  have hm : (selectionSamples q : ℝ) = N * T := by unfold selectionSamples; push_cast; rfl
  have hNb : N * (tailBound q ^ 2 / selectionSamples q) = tailBound q ^ 2 / T := by
    rw [hm]; field_simp
  rw [hNb] at hsumb
  have hW := tailBound_sq_le hρ
  have hTg := sgdSteps_ge (q := q)
  have hc2 := radius_sq hρ
  have hTb : 256 * (c ^ 2 * tailBound q ^ 2) ≤ T * q.ε ^ 2 := by
    have h1 : 2 ^ 16 * (1 + 2 * q.ρ) * (q.B ^ 2 * (1 + 1 / q.ρ)) / q.ε ^ 2 ≤ T := by
      have : 0 ≤ 2 ^ 16 * (1 + 2 * q.ρ) * (q.G ^ 2 * q.R ^ 2) / q.ε ^ 2 := by
        have := hρ.le; positivity
      have e : 2 ^ 16 * (1 + 2 * q.ρ) * (q.G ^ 2 * q.R ^ 2 + q.B ^ 2 * (1 + 1 / q.ρ)) / q.ε ^ 2 =
          2 ^ 16 * (1 + 2 * q.ρ) * (q.G ^ 2 * q.R ^ 2) / q.ε ^ 2 +
            2 ^ 16 * (1 + 2 * q.ρ) * (q.B ^ 2 * (1 + 1 / q.ρ)) / q.ε ^ 2 := by ring
      linarith
    rw [div_le_iff₀ (by positivity)] at h1
    rw [← hc2] at h1
    have : 0 ≤ c ^ 2 * (q.B ^ 2 * (1 + 1 / q.ρ)) := by have := hρ.le; positivity
    nlinarith [mul_le_mul_of_nonneg_left hW (sq_nonneg c)]
  have hfin : c * (tailBound q ^ 2 / T / a + a) ≤ q.ε / 8 := by
    have hc0 : c ≠ 0 := hc.ne'
    have hε0 : q.ε ≠ 0 := hε.ne'
    have hT00 : (T : ℝ) ≠ 0 := hT0.ne'
    have e1 : c * a = q.ε / 16 := by simp only [a]; field_simp; try ring
    have e2 : c * (tailBound q ^ 2 / T / a) = 16 * (c ^ 2 * tailBound q ^ 2) / (T * q.ε) := by
      simp only [a]; field_simp; try ring
    rw [mul_add, e1, e2]
    have : 16 * (c ^ 2 * tailBound q ^ 2) / (T * q.ε) ≤ q.ε / 16 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hmid : c * ((∑ j ∈ Finset.range N, ∫ ξ, sErr q proj I j (block q j ξ) ^ 2 ∂PP) / a + a) ≤
      c * (tailBound q ^ 2 / T / a + a) := by
    apply mul_le_mul_of_nonneg_left _ hc.le
    linarith [div_le_div_of_nonneg_right hsumb ha.le]
  have : (∫ ζ, F ζ ∂PP) - V ≤ 9 * q.ε / 32 := hPb
  linarith

end Analysis


lemma bracket_successful (q : Params) (hq : spec.valid q) (I : Instance q)
    (O : Oracle q.E (q.E × ℝ × q.E)) (hadm : spec.admissible q I O) {K : ℕ}
    (hK : numBrackets q * bracketLength q ≤ K) :
    spec.successful q I
      (fun w : (bracketAlgorithm q).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (bracketAlgorithm q) (fun _ => K) w.1 w.2)
      ⟨((bracketAlgorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hρ, hG, hB, -, hε⟩ := hq
  obtain ⟨proj, P, hiid, rfl, hconv, -, hx0, hpm, hpmem, hpvi, hlm, hsm, hsub, hbd, hsg, xs, hxs,
    hmin, hR⟩ := hadm
  have h : Adm q I proj := ⟨hconv, hx0, hpm, hpmem, hpvi, hlm, hsm, hsub, hbd, hsg⟩
  have he : (fun w : (bracketAlgorithm q).Seed × ((k : ℕ) → (sampleOracle I proj P).Seed k) =>
      execute (sampleOracle I proj P) (bracketAlgorithm q) (fun _ => K) w.1 w.2) =
      fun w => (best q proj I.loss I.sub w.2 (numBrackets q)).1 := by
    funext w
    exact execute_eq q proj I P w.2 hK
  have hPlaw : (P : Measure (ℕ → q.Ξ)) = Measure.infinitePi fun _ => (I.law : Measure q.Ξ) := by
    have hh := hiid.stream_law.map_eq
    change (P : Measure (ℕ → q.Ξ)).map id = _ at hh
    simpa only [Measure.map_id] using hh
  obtain ⟨hI, hE⟩ := expected_gap h hρ hG hB hε hxs hmin hR
  rw [← hPlaw] at hI hE
  obtain ⟨hI', hE'⟩ := integral_snd_eq (α := (bracketAlgorithm q).Seed)
    ((bracketAlgorithm q).law : Measure (bracketAlgorithm q).Seed) (P : Measure (ℕ → q.Ξ)) hI
  change Measurable _ ∧ _ ∧ _
  rw [he]
  refine ⟨(measurable_best h _).fst.comp measurable_snd,
    fun w => best_mem h hρ hG hB hε w.2, xs, hxs, hmin, hI', ?_⟩
  exact hE'.le.trans hE

lemma bracket_budget (q : Params) :
    numBrackets q * bracketLength q ≤
      (Nat.clog 2 ⌈8 * Real.sqrt (1 + 2 * q.ρ) * (q.B + q.B / Real.sqrt q.ρ) / q.ε⌉₊ + 2) ^ 2 *
        (⌈2 ^ 16 * (1 + 2 * q.ρ) * (q.G ^ 2 * q.R ^ 2 + q.B ^ 2 * (1 + 1 / q.ρ)) / q.ε ^ 2⌉₊ + 144) := by
  have hN : Nat.clog 2 ⌈8 * Real.sqrt (1 + 2 * q.ρ) * (q.B + q.B / Real.sqrt q.ρ) / q.ε⌉₊ + 2 =
      numBrackets q + 1 := rfl
  have hT : ⌈2 ^ 16 * (1 + 2 * q.ρ) * (q.G ^ 2 * q.R ^ 2 + q.B ^ 2 * (1 + 1 / q.ρ)) / q.ε ^ 2⌉₊ + 144 =
      sgdSteps q := rfl
  rw [hN, hT]
  unfold bracketLength selectionSamples
  calc numBrackets q * (sgdSteps q + numBrackets q * sgdSteps q) =
        (numBrackets q * numBrackets q + numBrackets q) * sgdSteps q := by ring
    _ ≤ (numBrackets q * numBrackets q + numBrackets q + (numBrackets q + 1)) * sgdSteps q :=
        Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    _ = (numBrackets q + 1) ^ 2 * sgdSteps q := by ring

end OracleTemplate.ChiSquareDro
