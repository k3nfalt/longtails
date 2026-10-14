import LongTails.Proofs.RegularizedProxEgRepeat
import LongTails.Proofs.RegularizedProxEgConfig
import LongTails.Proofs.CohypoStageGeometry

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.StochasticCohypomonotone

open LongTails.Setups.StochasticCohypomonotoneInclusion

open QueryPlan

noncomputable def ctr {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (cfg : RegCfg)
    (s : ℕ) (st : E × E) : E :=
  (cfg.Lam s)⁻¹ • (st.2 + cfg.lam s • st.1)

section Zeros

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {F : E → E} {G : E → Set E} {J : ℝ → E → E} {L ρ : ℝ}

noncomputable def zeroAt (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L < 1)
    (h2ρ : 2 * ρ ≤ γ) (Λ : ℝ) (c : E) : E :=
  if h : 0 < Λ ∧ γ * Λ < 1 then regZero H hγ hγL h2ρ h.1 h.2 c else c

lemma zeroAt_mem (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L < 1)
    (h2ρ : 2 * ρ ≤ γ) {Λ : ℝ} (hΛ : 0 < Λ) (hγΛ : γ * Λ < 1) (c : E) :
    -(F (zeroAt H hγ hγL h2ρ Λ c) + Λ • (zeroAt H hγ hγL h2ρ Λ c - c)) ∈
      G (zeroAt H hγ hγL h2ρ Λ c) := by
  unfold zeroAt; rw [dite_eq_left ⟨hΛ, hγΛ⟩]; exact H.regZero_mem hγ hγL h2ρ hΛ hγΛ c

lemma zeroAt_continuous (H : OpHyp F G J L ρ) {γ : ℝ} (hγ : 0 < γ) (hγL : γ * L < 1)
    (h2ρ : 2 * ρ ≤ γ) {Λ : ℝ} (hΛ : 0 < Λ) (hγΛ : γ * Λ < 1) :
    Continuous (zeroAt H hγ hγL h2ρ Λ) := by
  have : zeroAt H hγ hγL h2ρ Λ = regZero H hγ hγL h2ρ hΛ hγΛ := by
    funext c; unfold zeroAt; rw [dite_eq_left ⟨hΛ, hγΛ⟩]
  rw [this]; exact H.regZero_continuous hγ hγL h2ρ hΛ hγΛ

end Zeros

lemma StepOK.γΛ {L ρ γ α Λ M : ℝ} (h : StepOK L ρ γ α Λ M) (hL : 0 < L) : γ * Λ < 1 := by
  have := h.γL; have := h.γ_pos; nlinarith

lemma enn_l1_of_l2 {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ) (f : Ξ → ℝ) (hf : Measurable f)
    {V : ℝ} (hV : 0 ≤ V)
    (h : ∫⁻ ξ, ENNReal.ofReal (f ξ ^ 2) ∂P ≤ ENNReal.ofReal V) (hP : P Set.univ ≤ 1) :
    ∫⁻ ξ, ENNReal.ofReal (f ξ) ∂P ≤ ENNReal.ofReal (Real.sqrt V) := by
  rcases hV.eq_or_lt with hV0 | hVp
  · subst hV0
    have h0 : ∫⁻ ξ, ENNReal.ofReal (f ξ ^ 2) ∂P = 0 := le_antisymm (by simpa using h) (by positivity)
    have hm : Measurable (fun ξ => ENNReal.ofReal (f ξ ^ 2)) :=
      ENNReal.measurable_ofReal.comp (hf.pow_const 2)
    have hae := (lintegral_eq_zero_iff hm).mp h0
    have : (fun ξ => ENNReal.ofReal (f ξ)) =ᵐ[P] 0 := by
      filter_upwards [hae] with ξ hξ
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hξ ⊢
      nlinarith
    rw [lintegral_congr_ae this]; simp
  · have hs : 0 < Real.sqrt V := Real.sqrt_pos.mpr hVp
    have hpt : ∀ ξ, ENNReal.ofReal (f ξ) ≤
        ENNReal.ofReal (1 / (2 * Real.sqrt V)) * ENNReal.ofReal (f ξ ^ 2) +
          ENNReal.ofReal (Real.sqrt V / 2) := by
      intro ξ
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have : 0 ≤ (f ξ - Real.sqrt V) ^ 2 / (2 * Real.sqrt V) := by positivity
      have e : 1 / (2 * Real.sqrt V) * f ξ ^ 2 + Real.sqrt V / 2 - f ξ =
          (f ξ - Real.sqrt V) ^ 2 / (2 * Real.sqrt V) := by
        field_simp; ring
      linarith
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_add_right _ measurable_const, lintegral_const,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (1 / (2 * Real.sqrt V)) * ∫⁻ ξ, ENNReal.ofReal (f ξ ^ 2) ∂P +
          ENNReal.ofReal (Real.sqrt V / 2) * P Set.univ
        ≤ ENNReal.ofReal (1 / (2 * Real.sqrt V)) * ENNReal.ofReal V +
          ENNReal.ofReal (Real.sqrt V / 2) * 1 := by gcongr
      _ = ENNReal.ofReal (Real.sqrt V) := by
          rw [mul_one, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          congr 1
          have hv : V = Real.sqrt V * Real.sqrt V := (Real.mul_self_sqrt hVp.le).symm
          set s := Real.sqrt V
          rw [hv]; field_simp; ring

section Trajectory

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

noncomputable def stT (g : E → Ω → E) (J : ℝ → E → E) (cfg : RegCfg) (x0 : E) (s : ℕ)
    (ξ : ℕ → Ω) : E × E :=
  evalP (reply g J) (stagesPlan cfg s (x0, 0)) ξ

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma stT_zero (g : E → Ω → E) (J : ℝ → E → E) (cfg : RegCfg) (x0 : E) (ξ : ℕ → Ω) :
    stT g J cfg x0 0 ξ = (x0, 0) := rfl

noncomputable def outW (g : E → Ω → E) (J : ℝ → E → E) (cfg : RegCfg) (s : ℕ) (w : E × E)
    (t : ℕ → Ω) : E :=
  evalP (reply g J) (repeatPlan (egStep cfg.γ cfg.α (cfg.Lam s) (cfg.b s) (ctr cfg s w)) (cfg.T s) w.1) t

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma evalP_stages_succ (g : E → Ω → E) (J : ℝ → E → E) (cfg : RegCfg) (st : E × E) (s : ℕ)
    (ξ : ℕ → Ω) :
    evalP (reply g J) (stagesPlan cfg (s + 1) st) ξ =
      evalP (reply g J) (stagePlan cfg s (evalP (reply g J) (stagesPlan cfg s st) ξ))
        (fun i => ξ (stagesLen cfg s + i)) :=
  evalP_bind (reply g J) (stagesPlan cfg s st) (stagePlan cfg s) ξ

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma evalP_stagePlan (g : E → Ω → E) (J : ℝ → E → E) (cfg : RegCfg) (s : ℕ) (st : E × E)
    (t : ℕ → Ω) :
    evalP (reply g J) (stagePlan cfg s st) t = (outW g J cfg s st t, st.2 + cfg.lam s • st.1) :=
  evalP_map (reply g J) (fun y => (y, st.2 + cfg.lam s • st.1))
    (repeatPlan (egStep cfg.γ cfg.α (cfg.Lam s) (cfg.b s) (ctr cfg s st)) (cfg.T s) st.1) t

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma stT_succ (g : E → Ω → E) (J : ℝ → E → E) (cfg : RegCfg) (x0 : E) (s : ℕ) (ξ : ℕ → Ω) :
    stT g J cfg x0 (s + 1) ξ =
      (outW g J cfg s (stT g J cfg x0 s ξ) (fun i => ξ (stagesLen cfg s + i)),
        (stT g J cfg x0 s ξ).2 + cfg.lam s • (stT g J cfg x0 s ξ).1) := by
  unfold stT
  rw [evalP_stages_succ, evalP_stagePlan]

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma stT_succ_fst (g : E → Ω → E) (J : ℝ → E → E) (cfg : RegCfg) (x0 : E) (s : ℕ) (ξ : ℕ → Ω) :
    (stT g J cfg x0 (s + 1) ξ).1 = outW g J cfg s (stT g J cfg x0 s ξ) (fun i => ξ (stagesLen cfg s + i)) := by
  rw [stT_succ]

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma stT_succ_snd (g : E → Ω → E) (J : ℝ → E → E) (cfg : RegCfg) (x0 : E) (s : ℕ) (ξ : ℕ → Ω) :
    (stT g J cfg x0 (s + 1) ξ).2 = (stT g J cfg x0 s ξ).2 + cfg.lam s • (stT g J cfg x0 s ξ).1 := by
  rw [stT_succ]

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma ctr_continuous (cfg : RegCfg) (s : ℕ) : Continuous (ctr (E := E) cfg s) := by
  unfold ctr; fun_prop

omit [CompleteSpace E] in
lemma stT_measurable {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) {J : ℝ → E → E}
    (cfg : RegCfg) (hJ : Continuous (J cfg.γ)) (x0 : E) :
    ∀ s, Measurable (stT g J cfg x0 s)
  | 0 => measurable_const
  | s + 1 => by
      have ih := stT_measurable hg cfg hJ x0 s
      have hr := repeat_measurable hg hJ cfg.α (cfg.Lam s) (cfg.b s) (cfg.T s) (Ω := Ω)
      have hsh : Measurable (fun ξ : ℕ → Ω => fun i => ξ (stagesLen cfg s + i)) := by fun_prop
      have e : stT g J cfg x0 (s + 1) = fun ξ =>
          (outW g J cfg s (stT g J cfg x0 s ξ) (fun i => ξ (stagesLen cfg s + i)),
            (stT g J cfg x0 s ξ).2 + cfg.lam s • (stT g J cfg x0 s ξ).1) :=
        funext (stT_succ g J cfg x0 s)
      rw [e]
      exact (hr.comp (((ctr_continuous cfg s).measurable.comp ih).prodMk
        ((measurable_fst.comp ih).prodMk hsh))).prodMk
        ((measurable_snd.comp ih).add ((measurable_fst.comp ih).const_smul _))

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma stT_extend (g : E → Ω → E) (J : ℝ → E → E) (cfg : RegCfg) (x0 : E) (s : ℕ) (ω0 : Ω)
    (ξ : ℕ → Ω) :
    stT g J cfg x0 s ξ = stT g J cfg x0 s
      (extendP ω0 (stagesLen cfg s) (fun i => ξ i)) :=
  evalP_extend (reply g J) (stagesPlan cfg s (x0, 0)) ω0 ξ

end Trajectory


section Main

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
variable {F : E → E} {G : E → Set E} {J : ℝ → E → E} {L ρ R σ ε M : ℝ} {g : E → Ω → E}
  {p : Measure Ω} [IsProbabilityMeasure p] {cfg : RegCfg} {δ : ℕ → ℝ}

lemma CfgOK.γ_pos (hc : CfgOK cfg L ρ R σ ε M δ) : 0 < cfg.γ := (hc.step 0 (Nat.zero_le _)).γ_pos

noncomputable def zW (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ) (s : ℕ) (w : E × E) : E :=
  zeroAt H hc.γ_pos hc.γL hc.two_ρ (cfg.Lam s) (ctr cfg s w)

noncomputable def zT (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ) (g : E → Ω → E)
    (x0 : E) (s : ℕ) (ξ : ℕ → Ω) : E :=
  zW H hc s (stT g J cfg x0 s ξ)

omit [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma zT_def (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ) (g : E → Ω → E) (x0 : E)
    (s : ℕ) (ξ : ℕ → Ω) : zT H hc g x0 s ξ = zW H hc s (stT g J cfg x0 s ξ) := rfl

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma stT_eq (g : E → Ω → E) (J : ℝ → E → E) (x0 : E) (s : ℕ) (ξ : ℕ → Ω) :
    stT g J cfg x0 s ξ = evalP (reply g J) (stagesPlan cfg s (x0, 0)) ξ := rfl

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma outW_eq (g : E → Ω → E) (J : ℝ → E → E) (s : ℕ) (w : E × E) (t : ℕ → Ω) :
    outW g J cfg s w t =
      evalP (reply g J) (repeatPlan (egStep cfg.γ cfg.α (cfg.Lam s) (cfg.b s) (ctr cfg s w)) (cfg.T s) w.1) t :=
  rfl

attribute [local irreducible] stT outW

omit [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma zW_mem (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ) {s : ℕ} (hs : s ≤ cfg.S)
    (w : E × E) :
    -(F (zW H hc s w) + cfg.Lam s • (zW H hc s w - ctr cfg s w)) ∈ G (zW H hc s w) :=
  zeroAt_mem H hc.γ_pos hc.γL hc.two_ρ (hc.Lam_pos s) ((hc.step s hs).γΛ H.L_pos) _

omit [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma zW_continuous (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ) {s : ℕ} (hs : s ≤ cfg.S) :
    Continuous (zW H hc s) :=
  (zeroAt_continuous H hc.γ_pos hc.γL hc.two_ρ (hc.Lam_pos s) ((hc.step s hs).γΛ H.L_pos)).comp
    (ctr_continuous cfg s)

omit [MeasurableSpace Ω] in
omit [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma zT_mem (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ) (x0 : E) {s : ℕ}
    (hs : s ≤ cfg.S) (ξ : ℕ → Ω) :
    -(F (zT H hc g x0 s ξ) + cfg.Lam s • (zT H hc g x0 s ξ - ctr cfg s (stT g J cfg x0 s ξ))) ∈
      G (zT H hc g x0 s ξ) :=
  zW_mem H hc hs _

omit [MeasurableSpace Ω] in
omit [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma path_zero (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ) (x0 xs : E)
    (hxs : -F xs ∈ G xs) (hR : ‖x0 - xs‖ ≤ R) (ξ : ℕ → Ω) :
    ‖(stT g J cfg x0 0 ξ).1 - zT H hc g x0 0 ξ‖ ^ 2 ≤ 2 * R ^ 2 ∧
      ‖cfg.Lam 0 • (zT H hc g x0 0 ξ - ctr cfg 0 (stT g J cfg x0 0 ξ))‖ ≤
        Real.sqrt 2 * cfg.lam 0 * R := by
  have hl := hc.lam_pos 0
  have hctr : ctr cfg 0 (stT g J cfg x0 0 ξ) = x0 := by
    rw [stT_zero]; unfold ctr; simp only [zero_add]
    rw [smul_smul, hc.Lam_zero, inv_mul_cancel₀ hl.ne', one_smul]
  have hz := zT_mem H hc x0 (Nat.zero_le _) ξ (g := g)
  rw [hctr, hc.Lam_zero] at hz
  have hz' : -(F (zT H hc g x0 0 ξ) + (0 + cfg.lam 0) • (zT H hc g x0 0 ξ - x0)) ∈
      G (zT H hc g x0 0 ξ) := by rwa [zero_add]
  have hd := H.stage_dist (Λ' := 0) (l := cfg.lam 0) x0 x0 x0 xs (zT H hc g x0 0 ξ) le_rfl hl
    (by have := hc.four_ρ 0 (Nat.zero_le _); rw [hc.Lam_zero] at this; linarith)
    (by simp) (by simpa using hxs) hz'
  have h1 : ‖zT H hc g x0 0 ξ - x0‖ ^ 2 ≤ 2 * R ^ 2 := by
    refine hd.1.trans ?_
    have : ‖xs - x0‖ ≤ R := by rw [norm_sub_rev]; exact hR
    have := pow_le_pow_left₀ (norm_nonneg _) this 2
    linarith
  refine ⟨?_, ?_⟩
  · rw [stT_zero, norm_sub_rev]; exact h1
  rw [hctr, hc.Lam_zero, norm_smul, Real.norm_of_nonneg hl.le]
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hR
  have h2 : ‖zT H hc g x0 0 ξ - x0‖ ≤ Real.sqrt 2 * R := by
    have h3 : ‖zT H hc g x0 0 ξ - x0‖ ^ 2 ≤ (Real.sqrt 2 * R) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; exact h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3
  have := mul_le_mul_of_nonneg_left h2 hl.le
  linarith

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma ctr_succ (hc : CfgOK cfg L ρ R σ ε M δ) (x0 : E) (s : ℕ) (ξ : ℕ → Ω) :
    (cfg.Lam s + cfg.lam (s + 1)) • ctr cfg (s + 1) (stT g J cfg x0 (s + 1) ξ) =
      cfg.Lam s • ctr cfg s (stT g J cfg x0 s ξ) + cfg.lam (s + 1) • (stT g J cfg x0 (s + 1) ξ).1 := by
  have h1 := hc.Lam_pos (s + 1)
  have h0 := hc.Lam_pos s
  unfold ctr
  rw [← hc.Lam_succ, smul_smul, mul_inv_cancel₀ h1.ne', one_smul, smul_smul,
    mul_inv_cancel₀ h0.ne', one_smul, stT_succ_snd]

omit [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma path_succ (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ) (x0 : E) {s : ℕ}
    (hs : s + 1 ≤ cfg.S) (ξ : ℕ → Ω) :
    ‖(stT g J cfg x0 (s + 1) ξ).1 - zT H hc g x0 (s + 1) ξ‖ ^ 2 ≤
        2 * ‖(stT g J cfg x0 (s + 1) ξ).1 - zT H hc g x0 s ξ‖ ^ 2 ∧
      ‖cfg.Lam (s + 1) • (zT H hc g x0 (s + 1) ξ - ctr cfg (s + 1) (stT g J cfg x0 (s + 1) ξ))‖ ≤
        ‖cfg.Lam s • (zT H hc g x0 s ξ - ctr cfg s (stT g J cfg x0 s ξ))‖ +
          3 * cfg.lam (s + 1) * ‖(stT g J cfg x0 (s + 1) ξ).1 - zT H hc g x0 s ξ‖ := by
  have hzp := zT_mem H hc x0 (Nat.le_of_succ_le hs) ξ (g := g)
  have hz := zT_mem H hc x0 hs ξ (g := g)
  rw [hc.Lam_succ] at hz
  have hd := H.stage_dist (Λ' := cfg.Lam s) (l := cfg.lam (s + 1)) _ _ _ _ _
    (hc.Lam_pos s).le (hc.lam_pos (s + 1))
    (by have := hc.four_ρ (s + 1) hs; rwa [hc.Lam_succ] at this)
    (ctr_succ hc x0 s ξ) hzp hz
  set a := (stT g J cfg x0 (s + 1) ξ).1
  set D := ‖a - zT H hc g x0 s ξ‖
  have hD1 : ‖zT H hc g x0 (s + 1) ξ - a‖ ≤ Real.sqrt 2 * D := by
    have h1 := hd.1
    rw [norm_sub_rev (zT H hc g x0 s ξ) a] at h1
    have h2 : ‖zT H hc g x0 (s + 1) ξ - a‖ ^ 2 ≤ (Real.sqrt 2 * D) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; exact h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
  have hD2 : ‖zT H hc g x0 (s + 1) ξ - zT H hc g x0 s ξ‖ ≤ D := by
    have h := hd.2
    rw [norm_sub_rev (zT H hc g x0 s ξ) a] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  refine ⟨by rw [norm_sub_rev]; have := hd.1; rw [norm_sub_rev (zT H hc g x0 s ξ) a] at this; exact this, ?_⟩
  have hstep := anchor_norm_step (ctr cfg s (stT g J cfg x0 s ξ))
    (ctr cfg (s + 1) (stT g J cfg x0 (s + 1) ξ)) a (zT H hc g x0 s ξ) (zT H hc g x0 (s + 1) ξ)
    (hc.Lam_pos s).le (hc.lam_pos (s + 1)).le (ctr_succ hc x0 s ξ)
  rw [← hc.Lam_succ] at hstep
  have hle := hc.Lam_le s
  have hl := hc.lam_pos (s + 1)
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hD0 : 0 ≤ D := norm_nonneg _
  have e1 : cfg.Lam s * ‖zT H hc g x0 (s + 1) ξ - zT H hc g x0 s ξ‖ ≤ cfg.lam (s + 1) * D :=
    mul_le_mul hle hD2 (norm_nonneg _) hl.le
  have e2 : cfg.lam (s + 1) * ‖zT H hc g x0 (s + 1) ξ - a‖ ≤ cfg.lam (s + 1) * (2 * D) :=
    mul_le_mul_of_nonneg_left (hD1.trans (by nlinarith)) hl.le
  linarith


lemma zT_measurable (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ)
    (hg : Measurable (Function.uncurry g)) (x0 : E) {s : ℕ} (hs : s ≤ cfg.S) :
    Measurable (zT H hc g x0 s) :=
  (zW_continuous H hc hs).measurable.comp (stT_measurable hg cfg (H.res_continuous hc.γ_pos) x0 s)

lemma stage_expect (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator p F g σ) (x0 : E) {s : ℕ}
    (hs : s ≤ cfg.S) :
    ∫⁻ ξ, ENNReal.ofReal (‖(stT g J cfg x0 (s + 1) ξ).1 - zT H hc g x0 s ξ‖ ^ 2)
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal ((1 - stageQ cfg s) ^ cfg.T s) *
          ∫⁻ ξ, ENNReal.ofReal (‖(stT g J cfg x0 s ξ).1 - zT H hc g x0 s ξ‖ ^ 2)
            ∂(Measure.infinitePi fun _ : ℕ => p) +
        ENNReal.ofReal (stageC L ρ σ cfg s / stageQ cfg s) := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  have hst := hc.step s hs
  have hΛ := hc.Lam_pos s
  have hJ := H.res_continuous hc.γ_pos
  have hgm := hg.measurable
  have hZc := zW_continuous H hc hs
  have hW := stT_measurable hgm cfg hJ x0 s (g := g)
  have hext := measurable_extendP ω0 (stagesLen cfg s) (Ω := Ω)
  have hout : Measurable (fun q : (E × E) × (ℕ → Ω) => outW g J cfg s q.1 q.2) := by
    have hr := repeat_measurable hgm hJ cfg.α (cfg.Lam s) (cfg.b s) (cfg.T s) (Ω := Ω)
    simp_rw [outW_eq]
    exact hr.comp (((ctr_continuous cfg s).measurable.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hΨ : Measurable (fun q : (E × E) × (ℕ → Ω) =>
      ENNReal.ofReal (‖outW g J cfg s q.1 q.2 - zW H hc s q.1‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((hout.sub (hZc.measurable.comp measurable_fst)).norm).pow_const 2)
  have heq : ∀ ξ, ENNReal.ofReal (‖(stT g J cfg x0 (s + 1) ξ).1 - zT H hc g x0 s ξ‖ ^ 2) =
      ENNReal.ofReal (‖outW g J cfg s (stT g J cfg x0 s (extendP ω0 (stagesLen cfg s) (fun i => ξ i)))
          (fun i => ξ (stagesLen cfg s + i)) -
        zW H hc s (stT g J cfg x0 s (extendP ω0 (stagesLen cfg s) (fun i => ξ i)))‖ ^ 2) := by
    intro ξ
    rw [stT_succ_fst, zT_def, ← stT_extend g J cfg x0 s ω0 ξ]
  simp_rw [heq]
  rw [lintegral_split p (stagesLen cfg s) (fun u t => ENNReal.ofReal
      (‖outW g J cfg s (stT g J cfg x0 s (extendP ω0 (stagesLen cfg s) u)) t -
        zW H hc s (stT g J cfg x0 s (extendP ω0 (stagesLen cfg s) u))‖ ^ 2))
    (hΨ.comp ((hW.comp (hext.comp measurable_fst)).prodMk measurable_snd))]
  have hq0 : 0 < stageQ cfg s := by
    have := hst.α_pos; have := hst.γ_pos; simp only [stageQ]; positivity
  have hq1 : 0 ≤ 1 - stageQ cfg s := by simp only [stageQ]; linarith [hst.q_le]
  have hC0 : 0 ≤ stageC L ρ σ cfg s := by
    have := stepK_nonneg H.ρ_nonneg H.L_pos.le hst
    simp only [stageC]; positivity
  have hinner : ∀ w : E × E, ∫⁻ t, ENNReal.ofReal (‖outW g J cfg s w t - zW H hc s w‖ ^ 2)
      ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal ((1 - stageQ cfg s) ^ cfg.T s) * ENNReal.ofReal (‖w.1 - zW H hc s w‖ ^ 2) +
        ENNReal.ofReal (stageC L ρ σ cfg s / stageQ cfg s) := by
    intro w
    have h := H.repeat_expect hg hst hΛ (hc.b_pos s) (ctr cfg s w) (zW H hc s w)
      (zW_mem H hc hs w) (cfg.T s) w.1
    simp_rw [outW_eq]
    refine h.trans ?_
    rw [← ENNReal.ofReal_mul (pow_nonneg hq1 _), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hpow : 0 ≤ (1 - stageQ cfg s) ^ cfg.T s := pow_nonneg hq1 _
    have hpow1 : (1 - stageQ cfg s) ^ cfg.T s ≤ 1 := pow_le_one₀ hq1 (by linarith)
    have : stageC L ρ σ cfg s * (1 - (1 - stageQ cfg s) ^ cfg.T s) / stageQ cfg s ≤
        stageC L ρ σ cfg s / stageQ cfg s := by
      apply div_le_div_of_nonneg_right _ hq0.le
      nlinarith
    simp only [stageQ, stageC] at this hpow ⊢
    linarith
  refine (lintegral_mono fun u => hinner _).trans ?_
  have hm2 : Measurable (fun u : Fin (stagesLen cfg s) → Ω => ENNReal.ofReal
      (‖(stT g J cfg x0 s (extendP ω0 (stagesLen cfg s) u)).1 -
        zW H hc s (stT g J cfg x0 s (extendP ω0 (stagesLen cfg s) u))‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((((measurable_fst.comp (hW.comp hext)).sub
      (hZc.measurable.comp (hW.comp hext))).norm).pow_const 2)
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hm2, lintegral_const,
    measure_univ, mul_one]
  have hback := lintegral_prefix_only p ω0 (stagesLen cfg s)
    (fun ξ => ENNReal.ofReal (‖(stT g J cfg x0 s ξ).1 - zW H hc s (stT g J cfg x0 s ξ)‖ ^ 2))
    (ENNReal.measurable_ofReal.comp ((((measurable_fst.comp hW).sub
      (hZc.measurable.comp hW)).norm).pow_const 2))
    (fun ξ => by rw [← stT_extend g J cfg x0 s ω0 ξ])
  rw [← hback]
  simp only [zT_def, le_refl]

lemma err_bound (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator p F g σ) (x0 xs : E)
    (hxs : -F xs ∈ G xs) (hR : ‖x0 - xs‖ ≤ R) :
    ∀ s, s ≤ cfg.S →
      ∫⁻ ξ, ENNReal.ofReal (‖(stT g J cfg x0 (s + 1) ξ).1 - zT H hc g x0 s ξ‖ ^ 2)
          ∂(Measure.infinitePi fun _ : ℕ => p) ≤ ENNReal.ofReal (δ s ^ 2) := by
  have hq : ∀ s, s ≤ cfg.S → 0 ≤ 1 - stageQ cfg s := fun s hs => by
    simp only [stageQ]; linarith [(hc.step s hs).q_le]
  have hqp : ∀ s, s ≤ cfg.S → 0 < stageQ cfg s := fun s hs => by
    have := (hc.step s hs).α_pos; have := (hc.step s hs).γ_pos; have := hc.Lam_pos s
    simp only [stageQ]; positivity
  have hC : ∀ s, s ≤ cfg.S → 0 ≤ stageC L ρ σ cfg s := fun s hs => by
    have := stepK_nonneg H.ρ_nonneg H.L_pos.le (hc.step s hs)
    simp only [stageC]; positivity
  intro s
  induction s with
  | zero =>
      intro hs
      refine (stage_expect H hc hg x0 hs).trans ?_
      have h0 : ∫⁻ ξ, ENNReal.ofReal (‖(stT g J cfg x0 0 ξ).1 - zT H hc g x0 0 ξ‖ ^ 2)
          ∂(Measure.infinitePi fun _ : ℕ => p) ≤ ENNReal.ofReal (2 * R ^ 2) := by
        refine (lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal
          (path_zero H hc x0 xs hxs hR ξ).1).trans ?_
        rw [lintegral_const, measure_univ, mul_one]
      calc ENNReal.ofReal ((1 - stageQ cfg 0) ^ cfg.T 0) *
            ∫⁻ ξ, ENNReal.ofReal (‖(stT g J cfg x0 0 ξ).1 - zT H hc g x0 0 ξ‖ ^ 2)
              ∂(Measure.infinitePi fun _ : ℕ => p) +
            ENNReal.ofReal (stageC L ρ σ cfg 0 / stageQ cfg 0)
          ≤ ENNReal.ofReal ((1 - stageQ cfg 0) ^ cfg.T 0) * ENNReal.ofReal (2 * R ^ 2) +
            ENNReal.ofReal (stageC L ρ σ cfg 0 / stageQ cfg 0) := by gcongr
        _ ≤ ENNReal.ofReal (δ 0 ^ 2) := by
            rw [← ENNReal.ofReal_mul (pow_nonneg (hq 0 hs) _),
              ← ENNReal.ofReal_add (mul_nonneg (pow_nonneg (hq 0 hs) _) (by positivity))
                (div_nonneg (hC 0 hs) (hqp 0 hs).le)]
            exact ENNReal.ofReal_le_ofReal hc.rec0
  | succ s ih =>
      intro hs
      have ih' := ih (Nat.le_of_succ_le hs)
      refine (stage_expect H hc hg x0 hs).trans ?_
      have h0 : ∫⁻ ξ, ENNReal.ofReal (‖(stT g J cfg x0 (s + 1) ξ).1 - zT H hc g x0 (s + 1) ξ‖ ^ 2)
          ∂(Measure.infinitePi fun _ : ℕ => p) ≤ ENNReal.ofReal (2 * δ s ^ 2) := by
        calc _ ≤ ∫⁻ ξ, ENNReal.ofReal 2 *
              ENNReal.ofReal (‖(stT g J cfg x0 (s + 1) ξ).1 - zT H hc g x0 s ξ‖ ^ 2)
                ∂(Measure.infinitePi fun _ : ℕ => p) := by
              refine lintegral_mono fun ξ => ?_
              rw [← ENNReal.ofReal_mul (by norm_num)]
              exact ENNReal.ofReal_le_ofReal (path_succ H hc x0 hs ξ).1
          _ = ENNReal.ofReal 2 * ∫⁻ ξ, ENNReal.ofReal
                (‖(stT g J cfg x0 (s + 1) ξ).1 - zT H hc g x0 s ξ‖ ^ 2)
                ∂(Measure.infinitePi fun _ : ℕ => p) :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (δ s ^ 2) := by gcongr
          _ = ENNReal.ofReal (2 * δ s ^ 2) := by rw [← ENNReal.ofReal_mul (by norm_num)]
      calc ENNReal.ofReal ((1 - stageQ cfg (s + 1)) ^ cfg.T (s + 1)) *
            ∫⁻ ξ, ENNReal.ofReal (‖(stT g J cfg x0 (s + 1) ξ).1 - zT H hc g x0 (s + 1) ξ‖ ^ 2)
              ∂(Measure.infinitePi fun _ : ℕ => p) +
            ENNReal.ofReal (stageC L ρ σ cfg (s + 1) / stageQ cfg (s + 1))
          ≤ ENNReal.ofReal ((1 - stageQ cfg (s + 1)) ^ cfg.T (s + 1)) *
              ENNReal.ofReal (2 * δ s ^ 2) +
            ENNReal.ofReal (stageC L ρ σ cfg (s + 1) / stageQ cfg (s + 1)) := by gcongr
        _ ≤ ENNReal.ofReal (δ (s + 1) ^ 2) := by
            rw [← ENNReal.ofReal_mul (pow_nonneg (hq _ hs) _),
              ← ENNReal.ofReal_add (mul_nonneg (pow_nonneg (hq _ hs) _) (by positivity))
                (div_nonneg (hC _ hs) (hqp _ hs).le)]
            exact ENNReal.ofReal_le_ofReal (hc.recS s hs)


omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma Q_bound (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ) (x0 xs : E)
    (hxs : -F xs ∈ G xs) (hR : ‖x0 - xs‖ ≤ R) (ξ : ℕ → Ω) :
    ∀ s, s ≤ cfg.S →
      ‖cfg.Lam s • (zT H hc g x0 s ξ - ctr cfg s (stT g J cfg x0 s ξ))‖ ≤
        Real.sqrt 2 * cfg.lam 0 * R + 3 * ∑ t ∈ Finset.range s,
          cfg.lam (t + 1) * ‖(stT g J cfg x0 (t + 1) ξ).1 - zT H hc g x0 t ξ‖ := by
  intro s
  induction s with
  | zero => intro _; simpa using (path_zero H hc x0 xs hxs hR ξ).2
  | succ s ih =>
      intro hs
      refine (path_succ H hc x0 hs ξ).2.trans ?_
      rw [Finset.sum_range_succ, mul_add]
      have := ih (Nat.le_of_succ_le hs)
      linarith

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
omit [MeasurableSpace E] in
lemma out_eval (cfg : RegCfg) (x0 : E) (ξ : ℕ → Ω) :
    evalP (reply g J) (regularizedPlan cfg x0) ξ =
      (J cfg.γ ((stT g J cfg x0 (cfg.S + 1) ξ).1 - cfg.γ • ((1 / (cfg.bf : ℝ)) •
          ∑ i : Fin cfg.bf, g (stT g J cfg x0 (cfg.S + 1) ξ).1 (ξ (stagesLen cfg (cfg.S + 1) + i)) +
          cfg.Lam cfg.S • ((stT g J cfg x0 (cfg.S + 1) ξ).1 -
            (cfg.Lam cfg.S)⁻¹ • (stT g J cfg x0 (cfg.S + 1) ξ).2))),
        cfg.γ⁻¹ • (((stT g J cfg x0 (cfg.S + 1) ξ).1 - cfg.γ • ((1 / (cfg.bf : ℝ)) •
          ∑ i : Fin cfg.bf, g (stT g J cfg x0 (cfg.S + 1) ξ).1 (ξ (stagesLen cfg (cfg.S + 1) + i)) +
          cfg.Lam cfg.S • ((stT g J cfg x0 (cfg.S + 1) ξ).1 -
            (cfg.Lam cfg.S)⁻¹ • (stT g J cfg x0 (cfg.S + 1) ξ).2))) -
          J cfg.γ ((stT g J cfg x0 (cfg.S + 1) ξ).1 - cfg.γ • ((1 / (cfg.bf : ℝ)) •
          ∑ i : Fin cfg.bf, g (stT g J cfg x0 (cfg.S + 1) ξ).1 (ξ (stagesLen cfg (cfg.S + 1) + i)) +
          cfg.Lam cfg.S • ((stT g J cfg x0 (cfg.S + 1) ξ).1 -
            (cfg.Lam cfg.S)⁻¹ • (stT g J cfg x0 (cfg.S + 1) ξ).2))))) := by
  have e : evalP (reply g J) (regularizedPlan cfg x0) ξ =
      evalP (reply g J) (finalPlan cfg (stT g J cfg x0 (cfg.S + 1) ξ))
        (fun i => ξ (stagesLen cfg (cfg.S + 1) + i)) :=
    by rw [stT_eq]; exact evalP_bind (reply g J) (stagesPlan cfg (cfg.S + 1) (x0, 0)) (finalPlan cfg) ξ
  rw [e]
  unfold finalPlan
  rw [evalP_bind, evalP_batchSum, evalP_map, evalP_resolvent]

noncomputable def eErr (F : E → E) (g : E → Ω → E) (b : ℕ) (x : E) (v : Fin b → Ω) : ℝ :=
  ‖(1 / (b : ℝ)) • ∑ i : Fin b, g x (v i) - F x‖

lemma final_err_expect (H : OpHyp F G J L ρ) (hc : CfgOK cfg L ρ R σ ε M δ)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator p F g σ) (hσ : 0 ≤ σ) (x0 : E) :
    ∫⁻ ξ, ENNReal.ofReal (eErr F g cfg.bf (stT g J cfg x0 (cfg.S + 1) ξ).1
        (fun i => ξ (stagesLen cfg (cfg.S + 1) + i))) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (σ / Real.sqrt cfg.bf) := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  have hgm := hg.measurable
  have hJ := H.res_continuous hc.γ_pos
  have hF : Continuous F := (LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ H.L_pos.le]; exact H.lip a b).continuous
  have hW := stT_measurable hgm cfg hJ x0 (cfg.S + 1) (g := g)
  have hext := measurable_extendP ω0 (stagesLen cfg (cfg.S + 1)) (Ω := Ω)
  have hE : Measurable (fun q : E × (Fin cfg.bf → Ω) => eErr F g cfg.bf q.1 q.2) := by
    have hS : Measurable (fun q : E × (Fin cfg.bf → Ω) => ∑ i : Fin cfg.bf, g q.1 (q.2 i)) :=
      Finset.measurable_sum _ fun i _ => hgm.comp (measurable_fst.prodMk
        ((measurable_pi_apply i).comp measurable_snd))
    unfold eErr
    exact ((hS.const_smul _).sub (hF.measurable.comp measurable_fst)).norm
  have heq : ∀ ξ : ℕ → Ω, ENNReal.ofReal (eErr F g cfg.bf (stT g J cfg x0 (cfg.S + 1) ξ).1
        (fun i => ξ (stagesLen cfg (cfg.S + 1) + i))) =
      ENNReal.ofReal (eErr F g cfg.bf
        (stT g J cfg x0 (cfg.S + 1) (extendP ω0 (stagesLen cfg (cfg.S + 1)) (fun i => ξ i))).1
        (fun i : Fin cfg.bf => (fun j => ξ (stagesLen cfg (cfg.S + 1) + j)) (i : ℕ))) := by
    intro ξ
    rw [← stT_extend g J cfg x0 (cfg.S + 1) ω0 ξ]
  simp_rw [heq]
  rw [lintegral_split p (stagesLen cfg (cfg.S + 1)) (fun u t => ENNReal.ofReal (eErr F g cfg.bf
      (stT g J cfg x0 (cfg.S + 1) (extendP ω0 (stagesLen cfg (cfg.S + 1)) u)).1
      (fun i : Fin cfg.bf => t (i : ℕ))))
    (ENNReal.measurable_ofReal.comp (hE.comp ((measurable_fst.comp (hW.comp (hext.comp measurable_fst))).prodMk
      ((by fun_prop : Measurable (fun t : ℕ → Ω => fun i : Fin cfg.bf => t (i : ℕ))).comp measurable_snd))))]
  have hinner : ∀ x : E, ∫⁻ t, ENNReal.ofReal (eErr F g cfg.bf x (fun i : Fin cfg.bf => t (i : ℕ)))
      ∂(Measure.infinitePi fun _ : ℕ => p) ≤ ENNReal.ofReal (σ / Real.sqrt cfg.bf) := by
    intro x
    rw [lintegral_tuple p (fun i : Fin cfg.bf => (i : ℕ)) Fin.val_injective
      (fun v => ENNReal.ofReal (eErr F g cfg.bf x v))
      (ENNReal.measurable_ofReal.comp (hE.comp (measurable_const.prodMk measurable_id)))]
    have hb := hc.bf_pos
    have h2 := batch_lintegral_sq hg x hb
    have := enn_l1_of_l2 (Measure.pi fun _ : Fin cfg.bf => p) (fun v => eErr F g cfg.bf x v)
      (hE.comp (measurable_const.prodMk measurable_id))
      (V := σ ^ 2 / cfg.bf) (by positivity) (by simpa only [eErr] using h2) (by simp)
    refine this.trans (le_of_eq ?_)
    congr 1
    rw [Real.sqrt_div' _ (Nat.cast_nonneg _), Real.sqrt_sq hσ]
  refine (lintegral_mono fun u => hinner _).trans ?_
  rw [lintegral_const, measure_univ, mul_one]

end Main

end OracleTemplate.StochasticCohypomonotone
