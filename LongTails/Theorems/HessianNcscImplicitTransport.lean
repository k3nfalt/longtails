import LongTails.Proofs.Execution
import LongTails.Setups.StochasticHessianNcsc
import LongTails.Proofs.HessianNcscTuning
import LongTails.Proofs.AdaptiveIID

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.HessianNcsc

open LongTails.Setups.StochasticHessianNcsc

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈10 ^ 6 * (1 + q.L / q.μ) ^ 2 * (1 + q.σ ^ 2 / q.ε ^ 2) * (1 + q.ρ * q.ε * (1 + q.L / q.μ) / q.L ^ 2) * ((1 + q.L / q.μ) * q.Δ / q.ε * Real.sqrt (40 * q.ρ * (1 + q.L / q.μ) / q.ε + q.L ^ 2 / (q.ε ^ 2 + 20 * q.σ ^ 2)) + 1 + q.σ / q.ε + Real.log (1 + q.G ^ 2 / q.μ ^ 2 * (40 * q.ρ * (1 + q.L / q.μ) / q.ε + q.L ^ 2 / (q.ε ^ 2 + 20 * q.σ ^ 2))))⌉₊

noncomputable def tunedConfig (q : Params) : IgtConfig :=
  tCfg q.L q.μ q.ρ q.σ q.ε q.G (budget q 0 - off (tCfg q.L q.μ q.ρ q.σ q.ε q.G 0))

theorem result : Convergence LongTails.Setups.StochasticHessianNcsc.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => igtSgda (tunedConfig q) q.x0 q.y0, ?_, fun _ _ => trivial⟩
  intro q hq f O hadm
  dsimp only
  obtain ⟨hμ, hμL, hρ, hσ, hΔ, hG, hε⟩ := hq
  obtain ⟨gx, gy, Hx, Hy, ox, oy, p, P, hIID, rfl, hgx, hgy, hHx, hHy, hlip, hhess, hsc, hgap, hG0,
    hmx, hmy, hix, hiy, hex, hey, hiv, hv⟩ := hadm
  have H : Hyp f gx gy Hx Hy q.L q.μ q.ρ := ⟨hgx, hgy, hHx, hHy, hlip, hhess, hsc, hμ, hμL, hρ.le⟩
  have O' : OracleHyp gx gy ox oy (p : Measure q.Ω) q.σ := ⟨hmx, hmy, hix, hiy, hex, hey, hiv, hv⟩
  have h : TuneHyp q.L q.μ q.ρ q.σ q.ε := ⟨hμ, hμL, hρ, hσ, hε⟩
  set T := budget q 0 - off (tCfg q.L q.μ q.ρ q.σ q.ε q.G 0) with hTdef
  set cfg := tunedConfig q with hcfg
  have hcfgT : cfg = tCfg q.L q.μ q.ρ q.σ q.ε q.G T := rfl
  have hoff : off cfg = off (tCfg q.L q.μ q.ρ q.σ q.ε q.G 0) := rfl
  have hbo := h.budget_ok q.G q.Δ hΔ T
  have hceil := Nat.le_ceil (10 ^ 6 * (1 + q.L / q.μ) ^ 2 * (1 + q.σ ^ 2 / q.ε ^ 2) *
    (1 + q.ρ * q.ε * (1 + q.L / q.μ) / q.L ^ 2) * ((1 + q.L / q.μ) * q.Δ / q.ε *
      Real.sqrt (40 * q.ρ * (1 + q.L / q.μ) / q.ε + q.L ^ 2 / (q.ε ^ 2 + 20 * q.σ ^ 2)) + 1 + q.σ / q.ε +
      Real.log (1 + q.G ^ 2 / q.μ ^ 2 * (40 * q.ρ * (1 + q.L / q.μ) / q.ε + q.L ^ 2 / (q.ε ^ 2 + 20 * q.σ ^ 2)))))
  have hbud : (budget q 0 : ℝ) ≥ ((tCfg q.L q.μ q.ρ q.σ q.ε q.G T).NA : ℝ) + (tCfg q.L q.μ q.ρ q.σ q.ε q.G T).NB +
      (tCfg q.L q.μ q.ρ q.σ q.ε q.G T).NC +
      (8 * q.Δ / (q.ε * tη q.L q.μ q.ρ q.σ q.ε) + 16 * (3 * q.ε + 10 * q.σ) / (q.ε * tα q.L q.μ q.ρ q.σ q.ε)) + 1 :=
    hbo.trans hceil
  have hη := h.η0
  have hα := h.α0
  have hpos : 0 ≤ 8 * q.Δ / (q.ε * tη q.L q.μ q.ρ q.σ q.ε) + 16 * (3 * q.ε + 10 * q.σ) / (q.ε * tα q.L q.μ q.ρ q.σ q.ε) := by
    positivity
  have hoffT : off (tCfg q.L q.μ q.ρ q.σ q.ε q.G T) = off (tCfg q.L q.μ q.ρ q.σ q.ε q.G 0) := rfl
  have hle : off (tCfg q.L q.μ q.ρ q.σ q.ε q.G 0) ≤ budget q 0 := by
    have : ((off (tCfg q.L q.μ q.ρ q.σ q.ε q.G T) : ℕ) : ℝ) ≤ budget q 0 := by
      simp only [off]; push_cast; linarith
    rw [← hoffT]; exact_mod_cast this
  have hK : off cfg + cfg.T = budget q 0 := by
    rw [hoff]
    show off (tCfg q.L q.μ q.ρ q.σ q.ε q.G 0) + (budget q 0 - off (tCfg q.L q.μ q.ρ q.σ q.ε q.G 0)) = budget q 0
    exact Nat.add_sub_cancel' hle
  have hT : 8 * q.Δ / (q.ε * tη q.L q.μ q.ρ q.σ q.ε) + 16 * (3 * q.ε + 10 * q.σ) / (q.ε * tα q.L q.μ q.ρ q.σ q.ε) ≤
      (T : ℝ) + 1 := by
    have e : (T : ℝ) = budget q 0 - off (tCfg q.L q.μ q.ρ q.σ q.ε q.G 0) := by
      rw [hTdef, Nat.cast_sub hle]
    rw [e, ← hoffT]; simp only [off]; push_cast; linarith
  have hNB := h.NB1 q.G T
  have hc := h.cfgOK q.G T
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω) := by
    have := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans this
  have hexec : ∀ (τ : Fin (cfg.T + 1)) (ξ : ℕ → q.Ω),
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (ox z ω, oy z ω) } :
        Oracle (q.E × q.F) (q.E × q.F)) (igtSgda cfg q.x0 q.y0) (fun _ => (budget q 0))
        (show (igtSgda cfg q.x0 q.y0).Seed from τ) ξ =
      outRec cfg q.x0 q.y0 ox oy ξ τ.val cfg.T := by
    intro τ ξ
    rw [← hK]
    exact igt_execute cfg q.x0 q.y0 ox oy P (hcfgT ▸ hNB) τ ξ
  have hout : (fun seed : (igtSgda cfg q.x0 q.y0).Seed × ((k : ℕ) → q.Ω) =>
      (execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (ox z ω, oy z ω) } :
        Oracle (q.E × q.F) (q.E × q.F)) (igtSgda cfg q.x0 q.y0) (fun _ => (budget q 0)) seed.1 seed.2)) =
      fun ω => outRec cfg q.x0 q.y0 ox oy ω.2 ω.1.val cfg.T := by
    funext seed; rw [hexec seed.1 seed.2]
  refine ⟨?_, ⟨ystar H, H.ystar_max⟩, fun ys hys => ?_⟩
  · erw [hout]; exact measurable_out cfg q.x0 q.y0 hmx hmy
  have hys : ys = ystar H := funext fun x => H.ystar_unique x (ys x) (hys x)
  subst hys
  have hgrad : ∀ x, gradient (fun x => f x (ystar H x)) x = Gs H x := fun x => (H.Phi_hasGradient x).gradient
  simp only [hgrad]
  have hfun : (fun ω : (igtSgda (tunedConfig q) q.x0 q.y0).Seed × (ℕ → q.Ω) =>
      ‖Gs H (execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (ox z ω, oy z ω) } :
        Oracle (q.E × q.F) (q.E × q.F)) (igtSgda (tunedConfig q) q.x0 q.y0) (fun _ => (budget q 0)) ω.1 ω.2)‖) =
      fun ω => ‖Gs H (outRec cfg q.x0 q.y0 ox oy ω.2 ω.1.val cfg.T)‖ := by
    funext ω; rw [hexec ω.1 ω.2]
  erw [hfun]
  change Integrable (fun ω : Fin (cfg.T + 1) × (ℕ → q.Ω) => ‖Gs H (outRec cfg q.x0 q.y0 ox oy ω.2 ω.1.val cfg.T)‖)
      ((PMF.uniformOfFintype (Fin (cfg.T + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ∧
    ∫ ω : Fin (cfg.T + 1) × (ℕ → q.Ω), ‖Gs H (outRec cfg q.x0 q.y0 ox oy ω.2 ω.1.val cfg.T)‖
      ∂((PMF.uniformOfFintype (Fin (cfg.T + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
  rw [hP]
  have hm : Measurable (fun ω : Fin (cfg.T + 1) × (ℕ → q.Ω) => ‖Gs H (outRec cfg q.x0 q.y0 ox oy ω.2 ω.1.val cfg.T)‖) :=
    (H.Gs_continuous.measurable.comp (measurable_out cfg q.x0 q.y0 hmx hmy)).norm
  have hL := master_lintegral H O' cfg q.x0 q.y0 hc hNB hG0 hgap h.Es0 (by
      have := h.Es0; simp only [tPs]; have := h.α0; positivity : 0 < tPs q.L q.μ q.ρ q.σ q.ε)
    hσ hη (h.hA q.G T) (h.hC q.G T) (h.hB q.G T) (h.c1 q.G T) (h.c2 q.G T)
    (h.hfin q.G q.Δ hΔ T hT)
  have hfin : ∫⁻ ω, ENNReal.ofReal ‖Gs H (outRec cfg q.x0 q.y0 ox oy ω.2 ω.1.val cfg.T)‖
      ∂((PMF.uniformOfFintype (Fin (cfg.T + 1))).toMeasure.prod (Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω))) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL
  refine ⟨?_, ?_⟩
  · have := integrable_toReal_of_lintegral_ne_top (ENNReal.measurable_ofReal.comp hm).aemeasurable hfin
    simpa [ENNReal.toReal_ofReal (norm_nonneg _)] using this
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hL

end OracleTemplate.HessianNcsc
