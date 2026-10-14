import LongTails.Proofs.RegularizedProxEgAssembly

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.StochasticCohypomonotone

open LongTails.Setups.StochasticCohypomonotoneInclusion

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
variable {F : E → E} {G : E → Set E} {J : ℝ → E → E} {L ρ R σ ε M : ℝ} {g : E → Ω → E}
  {p : Measure Ω} [IsProbabilityMeasure p] {cfg : RegCfg} {δ : ℕ → ℝ}

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma final_pathwise (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ) (x0 xs : E)
    (hxs : -F xs ∈ G xs) (hR : ‖x0 - xs‖ ≤ R) (ξ : ℕ → Ω) :
    (evalP (reply g J) (regularizedPlan cfg x0) ξ).2 ∈ G (evalP (reply g J) (regularizedPlan cfg x0) ξ).1 ∧
      ‖F (evalP (reply g J) (regularizedPlan cfg x0) ξ).1 +
          (evalP (reply g J) (regularizedPlan cfg x0) ξ).2‖ ≤
        8 / cfg.γ * ‖(stT g J cfg x0 (cfg.S + 1) ξ).1 - zT H hc g x0 cfg.S ξ‖ +
          4 * ‖(1 / (cfg.bf : ℝ)) • ∑ i : Fin cfg.bf,
            g (stT g J cfg x0 (cfg.S + 1) ξ).1 (ξ (stagesLen cfg (cfg.S + 1) + i)) -
              F (stT g J cfg x0 (cfg.S + 1) ξ).1‖ +
          (Real.sqrt 2 * cfg.lam 0 * R + 3 * ∑ t ∈ Finset.range cfg.S,
            cfg.lam (t + 1) * ‖(stT g J cfg x0 (t + 1) ξ).1 - zT H hc g x0 t ξ‖) := by
  rw [out_eval]
  set x := (stT g J cfg x0 (cfg.S + 1) ξ).1
  set c := ctr cfg cfg.S (stT g J cfg x0 cfg.S ξ)
  set e := (1 / (cfg.bf : ℝ)) • ∑ i : Fin cfg.bf, g x (ξ (stagesLen cfg (cfg.S + 1) + i)) - F x
  have hcm : (cfg.Lam cfg.S)⁻¹ • (stT g J cfg x0 (cfg.S + 1) ξ).2 = c := by
    simp only [c]; rw [stT_succ]; rfl
  have hin : (1 / (cfg.bf : ℝ)) • ∑ i : Fin cfg.bf, g x (ξ (stagesLen cfg (cfg.S + 1) + i)) +
      cfg.Lam cfg.S • (x - c) = F x + cfg.Lam cfg.S • (x - c) + e := by
    simp only [e]; abel
  rw [hcm, hin]
  have hst := hc.step cfg.S le_rfl
  have hfc := H.final_cert (Λ := cfg.Lam cfg.S) c (zT H hc g x0 cfg.S ξ) x e
    (J cfg.γ (x - cfg.γ • (F x + cfg.Lam cfg.S • (x - c) + e))) hst.γ_pos hst.Λ_nonneg hst.γL.le
    (zT_mem H hc x0 le_rfl ξ) rfl
  refine ⟨hfc.1, hfc.2.trans ?_⟩
  have hQ := Q_bound H hc x0 xs hxs hR ξ cfg.S le_rfl (g := g)
  simp only [c] at hQ ⊢
  linarith

theorem regularized_main (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator p F g σ) (hσ : 0 ≤ σ) (x0 xs : E)
    (hxs : -F xs ∈ G xs) (hR : ‖x0 - xs‖ ≤ R) :
    Measurable (fun ξ => evalP (reply g J) (regularizedPlan cfg x0) ξ) ∧
      (∀ ξ, (evalP (reply g J) (regularizedPlan cfg x0) ξ).2 ∈
        G (evalP (reply g J) (regularizedPlan cfg x0) ξ).1) ∧
      ∫⁻ ξ, ENNReal.ofReal ‖F (evalP (reply g J) (regularizedPlan cfg x0) ξ).1 +
          (evalP (reply g J) (regularizedPlan cfg x0) ξ).2‖ ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        ENNReal.ofReal ε := by
  have hgm := hg.measurable
  have hJ := H.res_continuous hc.γ_pos
  have hF : Continuous F := (LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ H.L_pos.le]; exact H.lip a b).continuous
  have hW : ∀ s, Measurable (stT g J cfg x0 s) := stT_measurable hgm cfg hJ x0
  have hS : Measurable (fun ξ : ℕ → Ω => ∑ i : Fin cfg.bf,
      g (stT g J cfg x0 (cfg.S + 1) ξ).1 (ξ (stagesLen cfg (cfg.S + 1) + i))) :=
    Finset.measurable_sum _ fun i _ => hgm.comp ((measurable_fst.comp (hW _)).prodMk
      (measurable_pi_apply _))
  have hout : Measurable (fun ξ => evalP (reply g J) (regularizedPlan cfg x0) ξ) := by
    simp_rw [out_eval]
    have hy : Measurable (fun ξ : ℕ → Ω => (stT g J cfg x0 (cfg.S + 1) ξ).1 - cfg.γ •
        ((1 / (cfg.bf : ℝ)) • ∑ i : Fin cfg.bf,
            g (stT g J cfg x0 (cfg.S + 1) ξ).1 (ξ (stagesLen cfg (cfg.S + 1) + i)) +
          cfg.Lam cfg.S • ((stT g J cfg x0 (cfg.S + 1) ξ).1 -
            (cfg.Lam cfg.S)⁻¹ • (stT g J cfg x0 (cfg.S + 1) ξ).2))) :=
      (measurable_fst.comp (hW _)).sub (((hS.const_smul _).add (((measurable_fst.comp (hW _)).sub
        ((measurable_snd.comp (hW _)).const_smul _)).const_smul _)).const_smul _)
    exact (hJ.measurable.comp hy).prodMk ((hy.sub (hJ.measurable.comp hy)).const_smul _)
  refine ⟨hout, fun ξ => (final_pathwise H hc x0 xs hxs hR ξ (g := g)).1, ?_⟩
  set D : ℕ → (ℕ → Ω) → ℝ := fun t ξ => ‖(stT g J cfg x0 (t + 1) ξ).1 - zT H hc g x0 t ξ‖ with hDdef
  set Ef : (ℕ → Ω) → ℝ := fun ξ => eErr F g cfg.bf (stT g J cfg x0 (cfg.S + 1) ξ).1
    (fun i => ξ (stagesLen cfg (cfg.S + 1) + i)) with hEfdef
  have hDm : ∀ t, t ≤ cfg.S → Measurable (fun ξ => ENNReal.ofReal (D t ξ)) := fun t ht =>
    ENNReal.measurable_ofReal.comp (((measurable_fst.comp (hW _)).sub (zT_measurable H hc hgm x0 ht)).norm)
  have hEm : Measurable (fun ξ => ENNReal.ofReal (Ef ξ)) := by
    simp only [hEfdef, eErr]
    exact ENNReal.measurable_ofReal.comp ((hS.const_smul _).sub
      (hF.measurable.comp (measurable_fst.comp (hW _)))).norm
  have hDexp : ∀ t, t ≤ cfg.S →
      ∫⁻ ξ, ENNReal.ofReal (D t ξ) ∂(Measure.infinitePi fun _ : ℕ => p) ≤ ENNReal.ofReal (δ t) := by
    intro t ht
    have h := enn_l1_of_l2 (Measure.infinitePi fun _ : ℕ => p) (D t)
      (((measurable_fst.comp (hW _)).sub (zT_measurable H hc hgm x0 ht)).norm)
      (sq_nonneg (δ t)) (err_bound H hc hg x0 xs hxs hR t ht) (by simp)
    rwa [Real.sqrt_sq (hc.δ_pos t).le] at h
  have hE : ∫⁻ ξ, ENNReal.ofReal (Ef ξ) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (σ / Real.sqrt cfg.bf) := final_err_expect H hc hg hσ x0
  have hpt : ∀ ξ, ENNReal.ofReal ‖F (evalP (reply g J) (regularizedPlan cfg x0) ξ).1 +
        (evalP (reply g J) (regularizedPlan cfg x0) ξ).2‖ ≤
      ENNReal.ofReal (8 / cfg.γ) * ENNReal.ofReal (D cfg.S ξ) +
        ENNReal.ofReal 4 * ENNReal.ofReal (Ef ξ) +
        ENNReal.ofReal (Real.sqrt 2 * cfg.lam 0 * R) +
        ∑ t ∈ Finset.range cfg.S, ENNReal.ofReal (3 * cfg.lam (t + 1)) * ENNReal.ofReal (D t ξ) := by
    intro ξ
    have hb := (final_pathwise H hc x0 xs hxs hR ξ (g := g)).2
    have hsum : 3 * ∑ t ∈ Finset.range cfg.S,
        cfg.lam (t + 1) * ‖(stT g J cfg x0 (t + 1) ξ).1 - zT H hc g x0 t ξ‖ =
        ∑ t ∈ Finset.range cfg.S, (3 * cfg.lam (t + 1)) * D t ξ := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => by simp only [hDdef]; ring
    rw [hsum] at hb
    have hb2 : ‖F (evalP (reply g J) (regularizedPlan cfg x0) ξ).1 +
          (evalP (reply g J) (regularizedPlan cfg x0) ξ).2‖ ≤
        8 / cfg.γ * D cfg.S ξ + 4 * Ef ξ + Real.sqrt 2 * cfg.lam 0 * R +
          ∑ t ∈ Finset.range cfg.S, 3 * cfg.lam (t + 1) * D t ξ := by
      simp only [hDdef, hEfdef, eErr]; linarith [hb]
    refine (ENNReal.ofReal_le_ofReal hb2).trans ?_
    refine (ENNReal.ofReal_add_le).trans ?_
    refine add_le_add ?_ ?_
    · refine (ENNReal.ofReal_add_le).trans (add_le_add ?_ le_rfl)
      refine (ENNReal.ofReal_add_le).trans (add_le_add ?_ ?_)
      · rw [ENNReal.ofReal_mul (by have := hc.γ_pos; positivity)]
      · rw [ENNReal.ofReal_mul (by norm_num)]
    · rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => mul_nonneg
        (by have := hc.lam_pos (t + 1); positivity) (norm_nonneg _))]
      refine le_of_eq (Finset.sum_congr rfl fun t _ => ?_)
      exact ENNReal.ofReal_mul (by have := hc.lam_pos (t + 1); positivity)
  refine (lintegral_mono hpt).trans ?_
  have hm3 : Measurable (fun ξ => ENNReal.ofReal (8 / cfg.γ) * ENNReal.ofReal (D cfg.S ξ) +
      ENNReal.ofReal 4 * ENNReal.ofReal (Ef ξ) + ENNReal.ofReal (Real.sqrt 2 * cfg.lam 0 * R)) :=
    (((hDm cfg.S le_rfl).const_mul _).add (hEm.const_mul _)).add measurable_const
  have hm2 : Measurable (fun ξ => ENNReal.ofReal (8 / cfg.γ) * ENNReal.ofReal (D cfg.S ξ) +
      ENNReal.ofReal 4 * ENNReal.ofReal (Ef ξ)) :=
    ((hDm cfg.S le_rfl).const_mul _).add (hEm.const_mul _)
  have hm1 : Measurable (fun ξ => ENNReal.ofReal (8 / cfg.γ) * ENNReal.ofReal (D cfg.S ξ)) :=
    (hDm cfg.S le_rfl).const_mul _
  rw [lintegral_add_left hm3, lintegral_add_left hm2, lintegral_add_left hm1,
    lintegral_const_mul _ (hDm cfg.S le_rfl), lintegral_const_mul _ hEm,
    lintegral_const, measure_univ, mul_one,
    lintegral_finsetSum _ (fun t ht => ((hDm t (by simp at ht; omega)).const_mul _))]
  have hsumb : ∑ t ∈ Finset.range cfg.S, ∫⁻ ξ, ENNReal.ofReal (3 * cfg.lam (t + 1)) *
        ENNReal.ofReal (D t ξ) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ∑ t ∈ Finset.range cfg.S, ENNReal.ofReal (3 * cfg.lam (t + 1)) * ENNReal.ofReal (δ t) := by
    refine Finset.sum_le_sum fun t ht => ?_
    rw [lintegral_const_mul _ (hDm t (by simp at ht; omega))]
    gcongr
    exact hDexp t (by simp at ht; omega)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have hδ : ∀ t, 0 ≤ δ t := fun t => (hc.δ_pos t).le
  have hl : ∀ t, 0 ≤ 3 * cfg.lam (t + 1) := fun t => by have := hc.lam_pos (t + 1); positivity
  have hγ := hc.γ_pos
  have hlam0 := hc.lam_pos 0
  calc ENNReal.ofReal (8 / cfg.γ) * ∫⁻ ξ, ENNReal.ofReal (D cfg.S ξ) ∂(Measure.infinitePi fun _ : ℕ => p) +
        ENNReal.ofReal 4 * ∫⁻ ξ, ENNReal.ofReal (Ef ξ) ∂(Measure.infinitePi fun _ : ℕ => p) +
        ENNReal.ofReal (Real.sqrt 2 * cfg.lam 0 * R) +
        ∑ t ∈ Finset.range cfg.S, ∫⁻ ξ, ENNReal.ofReal (3 * cfg.lam (t + 1)) *
          ENNReal.ofReal (D t ξ) ∂(Measure.infinitePi fun _ : ℕ => p)
      ≤ ENNReal.ofReal (8 / cfg.γ) * ENNReal.ofReal (δ cfg.S) +
          ENNReal.ofReal 4 * ENNReal.ofReal (σ / Real.sqrt cfg.bf) +
          ENNReal.ofReal (Real.sqrt 2 * cfg.lam 0 * R) +
          ∑ t ∈ Finset.range cfg.S, ENNReal.ofReal (3 * cfg.lam (t + 1)) * ENNReal.ofReal (δ t) := by
        gcongr
        exact hDexp cfg.S le_rfl
    _ = ENNReal.ofReal (8 / cfg.γ * δ cfg.S + 4 * (σ / Real.sqrt cfg.bf) +
          Real.sqrt 2 * cfg.lam 0 * R +
          ∑ s ∈ Finset.range cfg.S, 3 * cfg.lam (s + 1) * δ s) := by
        rw [ENNReal.ofReal_add (by have := hδ cfg.S; positivity)
            (Finset.sum_nonneg fun t _ => mul_nonneg (hl t) (hδ t)),
          ENNReal.ofReal_add (by have := hδ cfg.S; positivity) (by have := hc.lam_pos 0; positivity),
          ENNReal.ofReal_add (by have := hδ cfg.S; positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_sum_of_nonneg (fun t _ => mul_nonneg (hl t) (hδ t))]
        congr 1
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← ENNReal.ofReal_mul (hl t)]
    _ ≤ ENNReal.ofReal ε := by
        apply ENNReal.ofReal_le_ofReal
        have h := hc.acc
        have e : 3 * ∑ s ∈ Finset.range cfg.S, cfg.lam (s + 1) * δ s =
            ∑ s ∈ Finset.range cfg.S, 3 * cfg.lam (s + 1) * δ s := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => by ring
        linarith

end OracleTemplate.StochasticCohypomonotone
