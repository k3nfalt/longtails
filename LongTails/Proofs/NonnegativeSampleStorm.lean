import LongTails.Proofs.NonnegativeSampleMoments
import LongTails.Proofs.NormalizedStormConvergence

open MeasureTheory
open OracleTemplate OracleTemplate.NormalizedStorm
open LongTails.Setups.NonnegativeSmoothSampleLoss

namespace LongTails.Proofs.NonnegativeSampleStorm

lemma enough_calls {L Δ ε : ℝ} (hL : 0 < L) (hΔ : 0 ≤ Δ) (he : 0 < ε) :
    tB0 L L 0 Δ ε + tT L L 0 Δ ε ≤ ⌈8192 * Real.sqrt (1 + L * Δ / ε ^ 2) ^ 3⌉₊ := by
  have h : TuneHyp L L 0 Δ ε := ⟨hL, hL.le, le_rfl, hΔ, he⟩
  apply h.calls.trans
  let S := L * Δ / ε ^ 2
  let t := Real.sqrt (1 + S)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have ht : 1 ≤ t := by simpa [t] using Real.sqrt_le_sqrt (show 1 ≤ 1 + S by linarith)
  have ht2 : t ^ 2 = 1 + S := Real.sq_sqrt (by linarith)
  have hs : Real.sqrt (4 * L * Δ + 2 * L * ε ^ 2 / L + 0) ≤ 2 * ε * t := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hid : 4 * L * Δ + 2 * L * ε ^ 2 / L + 0 = ε ^ 2 * (4 * S + 2) := by
        dsimp [S]
        field_simp
        ring
      rw [hid]
      nlinarith [congrArg (fun z : ℝ => ε ^ 2 * z) ht2, sq_nonneg ε]
  have heq : 1600 * L * Δ * (2 * ε * t) / ε ^ 3 = 3200 * S * t := by
    dsimp [S]
    field_simp
    ring
  have hup : (192 * (4 * L * Δ + 0) + 80 * L * Δ) / ε ^ 2 + 384 * L / L +
      1600 * L * Δ * Real.sqrt (4 * L * Δ + 2 * L * ε ^ 2 / L + 0) / ε ^ 3 ≤
      848 * S + 384 + 3200 * S * t := by
    have hstep := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 1600 * L * Δ)) (by positivity : 0 ≤ ε ^ 3)
    rw [heq] at hstep
    have hinit : (192 * (4 * L * Δ + 0) + 80 * L * Δ) / ε ^ 2 + 384 * L / L = 848 * S + 384 := by
      dsimp [S]
      field_simp
      ring
    linarith
  have hbig : 848 * S + 384 + 3200 * S * t + 4 ≤ 8192 * t ^ 3 := by
    nlinarith [mul_nonneg hS (sub_nonneg.mpr ht), congrArg (fun z : ℝ => t * z) ht2]
  have hceil := Nat.ceil_mono hup
  have hn : (⌈848 * S + 384 + 3200 * S * t⌉₊ : ℝ) < 848 * S + 384 + 3200 * S * t + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hx := Nat.le_ceil (8192 * t ^ 3)
  change _ ≤ ⌈8192 * t ^ 3⌉₊
  apply le_trans (Nat.add_le_add_right hceil 3)
  exact_mod_cast (show (⌈848 * S + 384 + 3200 * S * t⌉₊ : ℝ) + 3 ≤ (⌈8192 * t ^ 3⌉₊ : ℝ) by linarith)

lemma output_accurate (q : Params) (hq : spec.valid q) (f O) (hO : spec.admissible q f O)
    (K : ℕ) (hK : tB0 q.L q.L 0 q.Δ q.ε + tT q.L q.L 0 q.Δ q.ε ≤ K) :
    let η := tEta q.L q.L 0 q.Δ q.ε
    let a := tA q.L q.L 0 q.Δ q.ε
    let b0 := tB0 q.L q.L 0 q.Δ q.ε
    let T := tT q.L q.L 0 q.Δ q.ε
    let A := normalizedStorm η a b0 T q.x0
    spec.successful q f (fun s : A.Seed × ((k : ℕ) → O.Seed k) =>
      execute O A (fun _ => K) s.1 s.2) ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hL, hΔ, hε⟩ := hq
  have h := NonnegativeSampleMoments.admissible hL hO
  obtain ⟨g, p, P, hIID, rfl, hgrad, hlip, hgm, hint, hmean, hvi, hdi, hmss, lower, hlow, hgap,
    habc⟩ := h
  have H : Hyp (p : Measure q.Ω) f g q.L q.L 0 lower :=
    ⟨hgrad, hlip, hgm, hint, hmean, hvi, hdi, hmss, hlow, habc, hL, hL.le, le_rfl⟩
  dsimp only
  let η := tEta q.L q.L 0 q.Δ q.ε
  let a := tA q.L q.L 0 q.Δ q.ε
  let b0 := tB0 q.L q.L 0 q.Δ q.ε
  let T := tT q.L q.L 0 q.Δ q.ε
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω) := by
    exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans hIID.stream_law.map_eq
  let out := fun s : Fin (T + 1) × (ℕ → q.Ω) => (stormPair g η a b0 q.x0 s.2 s.1.val).1
  have hexec : (fun s : Fin (T + 1) × (ℕ → q.Ω) =>
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (q.E × q.E) (q.E × q.E)) (normalizedStorm η a b0 T q.x0) (fun _ => K) s.1 s.2) = out :=
    funext fun s => execute_normalizedStorm g P η a b0 T q.x0 K s.1 s.2 hK
  change Measurable _ ∧ Integrable _ _ ∧ _ ≤ _
  erw [hexec]
  have ho : Measurable out := measurable_out hgm η a b0 T q.x0
  refine ⟨ho, ?_⟩
  have hnorm : (fun s : Fin (T + 1) × (ℕ → q.Ω) => ‖gradient f
      (execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (q.E × q.E) (q.E × q.E)) (normalizedStorm η a b0 T q.x0) (fun _ => K) s.1 s.2)‖) =
      fun s => ‖gradient f (out s)‖ := funext fun s => congrArg (fun x => ‖gradient f x‖) (congrFun hexec s)
  erw [hnorm]
  change Integrable (fun s => ‖gradient f (out s)‖)
      ((PMF.uniformOfFintype (Fin (T + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ∧
    ∫ s, ‖gradient f (out s)‖
      ∂((PMF.uniformOfFintype (Fin (T + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
  rw [hP]
  have hm : Measurable (fun s => ‖gradient f (out s)‖) := (H.grad_continuous.measurable.comp ho).norm
  have hb := H.master_lintegral hΔ hε q.x0 hgap
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  constructor
  · have := integrable_toReal_of_lintegral_ne_top (ENNReal.measurable_ofReal.comp hm).aemeasurable hfin
    simpa [ENNReal.toReal_ofReal (norm_nonneg _)] using this
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hb

end LongTails.Proofs.NonnegativeSampleStorm
