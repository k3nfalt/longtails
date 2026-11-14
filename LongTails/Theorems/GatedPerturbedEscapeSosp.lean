import LongTails.Setups.VarianceOnlySecondOrder
import LongTails.Proofs.GatedEscapeBudget
import LongTails.Proofs.GatedEscapeFinal

namespace OracleTemplate.GatedPerturbedEscapeSosp

open MeasureTheory LongTails.Setups.VarianceOnlySecondOrder LongTails.Algorithms.GatedPerturbedEscape
  LongTails.Proofs.GatedEscapeBudget LongTails.Proofs.GatedEscapeFinal LongTails.Proofs.GatedEscapeSaddle
  LongTails.Proofs.GatedEscapeMoments LongTails.Proofs.ComparisonTrustTaylor

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  ⌈2 ^ 40 * Real.log (4096 * Real.log (20480 * Module.finrank ℝ q.E) * (q.L / Real.sqrt (q.ρ * q.ε)) * (1 + Real.sqrt q.ρ * q.Δ / (q.ε * Real.sqrt q.ε)) / q.δ) ^ 2 * Real.log (20480 * Module.finrank ℝ q.E) ^ 4 * (q.L / Real.sqrt (q.ρ * q.ε)) * (1 + Real.sqrt q.ρ * q.Δ / (q.ε * Real.sqrt q.ε))⌉₊ * (⌈2 ^ 54 * Real.log (20480 * Module.finrank ℝ q.E) ^ 4 * (1 + Module.finrank ℝ q.E * q.σ ^ 2 * Real.sqrt q.ρ / (q.L * q.ε * Real.sqrt q.ε) + q.σ ^ 2 / q.ε ^ 2)⌉₊ + 1)

theorem result : Convergence LongTails.Setups.VarianceOnlySecondOrder.spec budget := by
  refine ⟨fun q => method (cfgOf q.L q.ρ q.σ q.Δ q.ε q.δ (Module.finrank ℝ q.E)) q.x0, ?_,
    fun _ _ => trivial⟩
  intro q hq f O hadm
  dsimp only
  obtain ⟨hL, hρ, hσ, hΔ, hε, hδ, hδ1, hρε, hd⟩ := hq
  obtain ⟨g, P0, P, hIID, rfl, hf, hlip, hhess, hΔf, hmeas, hint, hmean, hint2, hvar⟩ := hadm
  set d := Module.finrank ℝ q.E with hdE
  have V : Valid q.L q.ρ q.σ q.Δ q.ε q.δ d := ⟨hL, hρ, hσ, hΔ, hε, hδ, hδ1, hρε, hd⟩
  have hsm : Smooth f q.L q.ρ := Smooth.of_contDiff hf hlip hhess
  have hN : Noise g (gradient f) (P0 : Measure q.Ω) q.σ := ⟨hmeas, hint, hmean, hint2, hvar⟩
  set cfg := cfgOf q.L q.ρ q.σ q.Δ q.ε q.δ d with hcfg
  have hbpos : 0 < cfg.b := by simp only [hcfg, cfgOf, bc]; omega
  have hTpos : 0 < cfg.T := by simp only [hcfg, cfgOf, Tc]; omega
  have H : SHyp cfg q.L q.ρ (Real.sqrt (q.ρ * q.ε)) q.σ d :=
    { hL := hL, hρ := hρ, hγ := γ_pos V, hγL := γ_le V, hη := rfl, hθ := θ_pos V, hr := rfl,
      hs0 := rfl, hθγ := hθγ V, hT := hTpos, hμ := hμ V, haT := haT, hTL := hTL V,
      hτ0 := τ0_pos V, h3τ0 := by show 3 * (rc q.ρ q.ε d * θc q.ρ q.ε d / 24) ≤ rc q.ρ q.ε d * θc q.ρ q.ε d / 8; linarith,
      hgrow := hgrow V, hd := hd, hb := hbpos, hbdev := hbdev V, hbL1 := hbL1 V, hben := hben V }
  obtain ⟨hϱ, hgd, hesc, hNbig⟩ := hN_facts V
  have h0 := hvar0 V
  have hres := final_success cfg d g f q.x0 hdE.symm H hsm P0 P hIID hN hσ hΔf
    (by have := M_ge6 V; simp only [hcfg, cfgOf]; omega) (by have := M_ge6 V; simp only [hcfg, cfgOf]; omega)
    (hM6 V) (by have := θ_pos V; simp only [hcfg, cfgOf]; positivity) (by simp only [hcfg, cfgOf]; linarith)
    h0 (var_mono (τ0_pos V) (τ0_le_q V) h0) (by simp only [hcfg, cfgOf]; positivity)
    (var_mono (τ0_pos V) (τ0_le_g V) h0) rfl (by simp only [hcfg, cfgOf]; linarith) hϱ hgd hesc
    (Nc q.L q.ρ q.Δ q.ε q.δ d) hNbig (hδ_bound V)
  have hbud : budget q = fun _ => Nc q.L q.ρ q.Δ q.ε q.δ d * cfg.b := by
    funext i
    simp only [budget, hcfg, cfgOf, Nc, lgc, κc, Dc, Kc, γc, bc, hdE]
  rw [hbud]
  exact hres

end OracleTemplate.GatedPerturbedEscapeSosp
