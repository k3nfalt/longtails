import LongTails.Proofs.HeavyTailedPLProcess

open MeasureTheory
open scoped RealInnerProductSpace
open OracleTemplate.ContinuizedSimilarQuasar OracleTemplate.TerminalClipping

namespace OracleTemplate.HeavyTailedPL

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma stopped_time_le {f : E → ℝ} {g : E → Ω → E} {P0 : Measure Ω} {μ lam M : ℝ} {t0 T : ℕ}
    (n : ℕ) (s : State E) (ξ : Fin n → Ω) :
    (iterateSamples (transition f g P0 μ lam M t0 T) n s ξ).1 ≤ s.1 + n := by
  classical
  induction n generalizing s with
  | zero => simp [iterateSamples]
  | succ n ih =>
    have h := ih (transition f g P0 μ lam M t0 T s (ξ 0)) (fun i => ξ i.succ)
    have hs : (transition f g P0 μ lam M t0 T s (ξ 0)).1 ≤ s.1 + 1 := by
      unfold transition stopUnless
      split_ifs
      · simp [sgdStep]
      · omega
    change (iterateSamples (transition f g P0 μ lam M t0 T) n
      (transition f g P0 μ lam M t0 T s (ξ 0)) (fun i => ξ i.succ)).1 ≤ s.1 + (n + 1)
    omega

omit [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma sgdStep_plain {f : E → ℝ} {g : E → Ω → E} {P0 : Measure Ω} {μ lam M : ℝ} {t0 : ℕ}
    (n : ℕ) (s : State E) (ξ : Fin n → Ω) :
    ((iterateSamples (sgdStep f g P0 μ lam M t0) n s ξ).1,
      (iterateSamples (sgdStep f g P0 μ lam M t0) n s ξ).2.1) =
      iterateSamples (plainStep g μ t0) n (s.1, s.2.1) ξ := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih _ _

section Tails

variable {f : E → ℝ} {g : E → Ω → E} (P0 : ProbabilityMeasure Ω)

lemma tail_martingale (hg : Measurable (Function.uncurry g)) (hgm : Measurable (gradient f))
    {μ lam M σ : ℝ} {t0 T : ℕ} (hlam : 0 ≤ lam) (hM : 0 ≤ M)
    (hdr : ∀ t, 0 ≤ drift μ t0 t)
    (h2i : ∀ x, Integrable (fun ω => ‖noise f g x ω‖ ^ 2) (P0 : Measure Ω))
    (hvar : ∀ x, ∫ ω, ‖noise f g x ω‖ ^ 2 ∂(P0 : Measure Ω) ≤ σ ^ 2)
    (hcomp : ∀ t ≤ T, lam * drift μ t0 t * σ ^ 2 ≤ 1 / 8)
    (s : State E) (hs : s.2.2.1 = 0) (Λ : ℝ) :
    (Measure.pi fun _ : Fin T => (P0 : Measure Ω))
      {ξ | Λ < (iterateSamples (transition f g P0 μ lam M t0 T) T s ξ).2.2.1} ≤
      ENNReal.ofReal (Real.exp (-Λ)) := by
  have hV : Measurable (fun z : State E => z.2.2.1) := measurable_snd.snd.fst
  have h := stopped_exponential_tail (good_measurableSet hgm μ lam M t0 T)
    (sgdStep_measurable hg hgm (P0 : Measure Ω) μ lam M t0) hV P0 le_rfl ?_ T s Λ
  · have he : s.2.2.1 + (T : ℝ) * 0 - Λ = -Λ := by rw [hs]; ring
    rw [he] at h
    exact h
  · intro z hz
    obtain ⟨hzT, hsmall⟩ := hz
    have hm := martingale_step_mgf (P0 := (P0 : Measure Ω)) hg hgm hlam hM (hdr z.1) (h2i z.2.1)
      (hvar z.2.1) hsmall (hcomp z.1 hzT)
    simp only [sgdStep, Real.exp_add, add_zero]
    refine ⟨hm.1.const_mul _, ?_⟩
    rw [integral_const_mul]
    simpa using mul_le_mul_of_nonneg_left hm.2 (Real.exp_nonneg z.2.2.1)

lemma tail_square (hg : Measurable (Function.uncurry g)) (hgm : Measurable (gradient f))
    {μ lam M σ : ℝ} {t0 T : ℕ} (hM : 0 < M)
    (h2i : ∀ x, Integrable (fun ω => ‖noise f g x ω‖ ^ 2) (P0 : Measure Ω))
    (hvar : ∀ x, ∫ ω, ‖noise f g x ω‖ ^ 2 ∂(P0 : Measure Ω) ≤ σ ^ 2)
    (s : State E) (hs : s.2.2.2.1 = 0) (Λ : ℝ) :
    (Measure.pi fun _ : Fin T => (P0 : Measure Ω))
      {ξ | T * (2 * σ ^ 2 / M ^ 2) + Λ <
        (iterateSamples (transition f g P0 μ lam M t0 T) T s ξ).2.2.2.1} ≤
      ENNReal.ofReal (Real.exp (-Λ)) := by
  have hV : Measurable (fun z : State E => z.2.2.2.1) := measurable_snd.snd.snd.fst
  have h := stopped_exponential_tail (good_measurableSet hgm μ lam M t0 T)
    (sgdStep_measurable hg hgm (P0 : Measure Ω) μ lam M t0) hV P0
    (show 0 ≤ 2 * σ ^ 2 / M ^ 2 by positivity) ?_ T s (T * (2 * σ ^ 2 / M ^ 2) + Λ)
  · have he : s.2.2.2.1 + T * (2 * σ ^ 2 / M ^ 2) - (T * (2 * σ ^ 2 / M ^ 2) + Λ) = -Λ := by
      rw [hs]; ring
    rwa [he] at h
  · intro z _
    have hm := square_step_mgf (P0 := (P0 : Measure Ω)) hg hgm hM (h2i z.2.1) (hvar z.2.1)
    simp only [sgdStep, Real.exp_add]
    refine ⟨hm.1.const_mul _, ?_⟩
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hm.2 (Real.exp_nonneg _)

lemma tail_exceed (hg : Measurable (Function.uncurry g)) (hgm : Measurable (gradient f))
    {μ lam M ν q : ℝ} {t0 T : ℕ} (hM : 0 < M) (hν : 0 < ν) (hq : 0 < q)
    (hqi : ∀ x, Integrable (fun ω => ‖noise f g x ω‖ ^ q) (P0 : Measure Ω))
    (hqm : ∀ x, ∫ ω, ‖noise f g x ω‖ ^ q ∂(P0 : Measure Ω) ≤ ν ^ q)
    (s : State E) (hs : s.2.2.2.2 = 0) :
    (Measure.pi fun _ : Fin T => (P0 : Measure Ω))
      {ξ | 1 ≤ |(iterateSamples (transition f g P0 μ lam M t0 T) T s ξ).2.2.2.2|} ≤
      ENNReal.ofReal (T * (ν ^ q / M ^ q)) := by
  classical
  set p := ν ^ q / M ^ q with hpdef
  have hp : 0 ≤ p := div_nonneg (Real.rpow_pos_of_pos hν q).le (Real.rpow_pos_of_pos hM q).le
  have ha := transition_measurable hg hgm (P0 : Measure Ω) μ lam M t0 T
  have hV : Measurable (fun z : State E => |z.2.2.2.2|) :=
    continuous_abs.measurable.comp measurable_snd.snd.snd.snd
  have hstep : ∀ z : State E,
      Integrable (fun ω => |(transition f g P0 μ lam M t0 T z ω).2.2.2.2|) (P0 : Measure Ω) ∧
      (∫ ω, |(transition f g P0 μ lam M t0 T z ω).2.2.2.2| ∂(P0 : Measure Ω)) ≤
        1 * |z.2.2.2.2| + p := by
    intro z
    by_cases hz : Good f μ lam M t0 T z
    · have he := exceed_step (P0 := (P0 : Measure Ω)) hg hgm hM hq (hqi z.2.1) (hqm z.2.1)
      have hx0 (ω : Ω) : 0 ≤ exceed M (noise f g z.2.1 ω) := by
        unfold exceed; split_ifs <;> norm_num
      have hle (ω : Ω) : |(transition f g P0 μ lam M t0 T z ω).2.2.2.2| ≤
          |z.2.2.2.2| + exceed M (noise f g z.2.1 ω) := by
        simp only [transition, stopUnless, hz, ↓reduceIte, sgdStep]
        exact (abs_add_le _ _).trans (by rw [abs_of_nonneg (hx0 ω)])
      have hmeas : Measurable (fun ω => |(transition f g P0 μ lam M t0 T z ω).2.2.2.2|) :=
        hV.comp (ha.comp (measurable_const.prodMk measurable_id))
      have hint : Integrable (fun ω => |(transition f g P0 μ lam M t0 T z ω).2.2.2.2|)
          (P0 : Measure Ω) :=
        ((integrable_const |z.2.2.2.2|).add he.1).mono' hmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun ω => by
            rw [Real.norm_eq_abs, abs_abs]; exact hle ω))
      refine ⟨hint, ?_⟩
      have hm := integral_mono hint ((integrable_const |z.2.2.2.2|).add he.1) hle
      simp only [Pi.add_apply] at hm
      rw [integral_add (integrable_const _) he.1] at hm
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hm
      linarith [he.2]
    · simp only [transition, stopUnless, hz, ↓reduceIte]
      refine ⟨integrable_const _, ?_⟩
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      linarith
  have hint := GapStrongGrowth.iterateSamples_measurable_integral ha P0
    (fun z : State E => |z.2.2.2.2|) hV (fun _ => abs_nonneg _) zero_le_one hstep T s
  simp only [one_pow, hs, abs_zero, mul_zero, zero_add, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at hint
  have hmk := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall
    (fun ξ => abs_nonneg ((iterateSamples (transition f g P0 μ lam M t0 T) T s ξ).2.2.2.2)))
    hint.1 1
  rw [one_mul] at hmk
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  apply ENNReal.ofReal_le_ofReal
  linarith [hint.2]

end Tails

omit [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma final_state_bound {f : E → ℝ} {m μ L lam M β start Λ σ : ℝ} {t0 T : ℕ} (z : State E)
    (hμ : 0 < μ) (hL : 0 < L) (hlam : 0 < lam) (hM : 0 < M) (ht0 : 3 ≤ t0) (hβ : 0 ≤ β)
    (hgrad : ∀ x, ‖gradient f x‖ ^ 2 ≤ 2 * L * (f x - m))
    (hinv : Invariant f m μ L lam M β start t0 z)
    (hA : z.2.2.1 ≤ Λ) (hB : z.2.2.2.1 ≤ T * (2 * σ ^ 2 / M ^ 2) + Λ)
    (hC : |z.2.2.2.2| < 1) (hT : z.1 ≤ T)
    (hburn : start + Λ / lam + 16 * L / μ ^ 2 * M ^ 2 * (T * (2 * σ ^ 2 / M ^ 2) + Λ) +
      8 * (T : ℝ) * ((T : ℝ) + t0) * β / μ < μ ^ 2 / (256 * L * lam ^ 2 * M ^ 2)) :
    Good f μ lam M t0 T z ∧ weight t0 z.1 * (f z.2.1 - m) ≤
      start + Λ / lam + 16 * L / μ ^ 2 * M ^ 2 * (T * (2 * σ ^ 2 / M ^ 2) + Λ) +
        8 * (T : ℝ) * ((T : ℝ) + t0) * β / μ := by
  obtain ⟨hC0, hC01, hbound⟩ := hinv
  have hCz : z.2.2.2.2 = 0 := by
    rcases hC01 with h | h
    · exact h
    · rw [abs_of_nonneg hC0] at hC; linarith
  have hb := hbound hCz
  have hK : 0 ≤ 16 * L / μ ^ 2 * M ^ 2 := by positivity
  have hAl : z.2.2.1 / lam ≤ Λ / lam := div_le_div_of_nonneg_right hA hlam.le
  have hBl := mul_le_mul_of_nonneg_left hB hK
  have hTr : (z.1 : ℝ) ≤ T := by exact_mod_cast hT
  have hz0 : (0 : ℝ) ≤ z.1 := z.1.cast_nonneg
  have ht0r : (3 : ℝ) ≤ t0 := by exact_mod_cast ht0
  have htl : 8 * (z.1 : ℝ) * ((z.1 : ℝ) + t0) * β / μ ≤ 8 * (T : ℝ) * ((T : ℝ) + t0) * β / μ := by
    apply div_le_div_of_nonneg_right _ hμ.le
    apply mul_le_mul_of_nonneg_right _ hβ
    have := mul_le_mul hTr (add_le_add_right hTr (t0 : ℝ)) (by positivity) (by positivity)
    nlinarith
  have hfinal : weight t0 z.1 * (f z.2.1 - m) ≤
      start + Λ / lam + 16 * L / μ ^ 2 * M ^ 2 * (T * (2 * σ ^ 2 / M ^ 2) + Λ) +
        8 * (T : ℝ) * ((T : ℝ) + t0) * β / μ := by linarith
  refine ⟨⟨hT, ?_⟩, hfinal⟩
  by_contra hbad
  push Not at hbad
  have hn3 : (3 : ℝ) ≤ (z.1 : ℝ) + t0 := by linarith
  have haμ : drift μ t0 z.1 * μ = 4 * ((z.1 : ℝ) + t0 - 1) := by
    simp only [drift]; rw [div_mul_cancel₀ _ hμ.ne']
  have hgr := hgrad z.2.1
  have hG0 : 0 ≤ ‖gradient f z.2.1‖ := norm_nonneg _
  have hwlow : ((z.1 : ℝ) + t0 - 1) ^ 2 / 2 ≤ weight t0 z.1 := by
    simp only [weight]; nlinarith
  generalize ‖gradient f z.2.1‖ = G at hbad hgr hG0
  generalize drift μ t0 z.1 = a at hbad haμ
  generalize f z.2.1 - m = r at hgr hfinal
  generalize weight t0 z.1 = w at hfinal hwlow
  generalize (z.1 : ℝ) + t0 = n at hn3 haμ hwlow
  have hr0 : 0 ≤ r := by
    have h2Lr : 0 ≤ 2 * L * r := (sq_nonneg G).trans hgr
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg (by positivity : (0 : ℝ) < 2 * L) hneg
    linarith
  have hs1 : (1 : ℝ) < (2 * (lam * a) * M * G) ^ 2 := by
    have := mul_lt_mul'' hbad hbad zero_le_one zero_le_one
    rw [sq]; linarith
  have hs2 : (2 * (lam * a) * M * G) ^ 2 ≤ 8 * L * lam ^ 2 * M ^ 2 * r * a ^ 2 := by
    have e : (2 * (lam * a) * M * G) ^ 2 = 4 * (lam ^ 2 * a ^ 2 * M ^ 2) * G ^ 2 := by ring
    have hk4 : (0 : ℝ) ≤ 4 * (lam ^ 2 * a ^ 2 * M ^ 2) := by positivity
    have hm := mul_le_mul_of_nonneg_left hgr hk4
    have e2 : 4 * (lam ^ 2 * a ^ 2 * M ^ 2) * (2 * L * r) = 8 * L * lam ^ 2 * M ^ 2 * r * a ^ 2 := by
      ring
    rw [e]; linarith
  have hs3 : μ ^ 2 < 8 * L * lam ^ 2 * M ^ 2 * r * (a * μ) ^ 2 := by
    have h := mul_lt_mul_of_pos_right (hs1.trans_le hs2) (by positivity : (0 : ℝ) < μ ^ 2)
    have e : 8 * L * lam ^ 2 * M ^ 2 * r * a ^ 2 * μ ^ 2 = 8 * L * lam ^ 2 * M ^ 2 * r * (a * μ) ^ 2 := by
      ring
    linarith
  rw [haμ] at hs3
  have hs4 : 8 * L * lam ^ 2 * M ^ 2 * r * (4 * (n - 1)) ^ 2 ≤ 256 * L * lam ^ 2 * M ^ 2 * (w * r) := by
    have hk : 0 ≤ 256 * L * lam ^ 2 * M ^ 2 * r := by positivity
    have hm := mul_le_mul_of_nonneg_left hwlow hk
    have e : 8 * L * lam ^ 2 * M ^ 2 * r * (4 * (n - 1)) ^ 2 =
        256 * L * lam ^ 2 * M ^ 2 * r * ((n - 1) ^ 2 / 2) := by ring
    have e2 : 256 * L * lam ^ 2 * M ^ 2 * r * w = 256 * L * lam ^ 2 * M ^ 2 * (w * r) := by ring
    linarith
  have hs5 : 256 * L * lam ^ 2 * M ^ 2 * (w * r) < μ ^ 2 := by
    have h := hfinal.trans_lt hburn
    rw [lt_div_iff₀ (by positivity)] at h
    linarith
  linarith

end OracleTemplate.HeavyTailedPL
