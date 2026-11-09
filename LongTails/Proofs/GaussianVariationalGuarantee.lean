import LongTails.Proofs.GaussianVariationalConvergence

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GaussianVariational

open LongTails.Setups.GaussianVariationalInference

variable {d : ℕ} {L μ : ℝ} {V : Point d → ℝ}

noncomputable def sgdOutput (V : Point d → ℝ) (μ a : ℝ) (m0 : Location d) (C0 : Scale d) (K : ℕ)
    (ω : ℕ → Fin d → ℝ) : Location d × Scale d :=
  (reparameterizedProxSgd μ a m0 C0).output
    ((fun s => (reparameterizedProxSgd μ a m0 C0).update s
      (gradient V ((reparameterizedProxSgd μ a m0 C0).query s).2))^[K]
      ((reparameterizedProxSgd μ a m0 C0).initial ω))

lemma sgdOutput_eq (V : Point d → ℝ) (μ : ℝ) {a : ℝ} (ha : 2 ≤ a) (m0 : Location d) (C0 : Scale d)
    {K : ℕ} (hK : 0 < K) (ω : ℕ → Fin d → ℝ) :
    sgdOutput V μ a m0 C0 K ω = (wmass a 0 K)⁻¹ • wsum V μ a 0 K (m0, C0) (fun i => ω i) := by
  unfold sgdOutput
  have hi : (reparameterizedProxSgd μ a m0 C0).initial ω = (⟨ω, 0, (m0, C0), 0, 0⟩ : SgdState d) :=
    rfl
  rw [hi, sgd_trace]
  have hm := wmass_pos ha 0 hK
  simp only [zero_add]
  change (if wmass a 0 K = 0 then _ else (wmass a 0 K)⁻¹ • wsum V μ a 0 K (m0, C0) _) = _
  simp only [hm.ne', ↓reduceIte]

lemma budget_algebra {L μ τ R ε dd K W r D A : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) (hτ : 0 ≤ τ)
    (hdd : 0 ≤ dd) (hR : 0 ≤ R) (hε : 0 < ε) (hK1 : 1 ≤ K) (hW : K ^ 2 / 2 ≤ W) (hr0 : 0 ≤ r)
    (hr : r ≤ R ^ 2) (hD0 : 0 ≤ D) (hD : D ≤ L / 2 * R ^ 2)
    (hA : A = 16 * (L * (2 + τ)) / μ + 2)
    (hK : (2 + τ) * (26 * L * R / Real.sqrt (μ * ε) + 32 * dd * L / (μ * ε)) ≤ K) :
    2 / W * (μ / 4 * ((0 + A - 1) * (0 + A - 2)) * r +
      8 * (L * (2 + τ)) / μ * D + 4 * K * ((2 + τ) * L * dd) / μ) ≤ ε := by
  have hL : 0 < L := lt_of_lt_of_le hμ hμL
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = L * (2 + τ) := ⟨_, rfl⟩
  obtain ⟨σ2, hσ2⟩ : ∃ σ2, σ2 = (2 + τ) * L * dd := ⟨_, rfl⟩
  rw [← hℓ, ← hσ2]
  rw [← hℓ] at hA
  have hℓL : 2 * L ≤ ℓ := by
    have e : L * (2 + τ) = 2 * L + L * τ := by ring
    rw [hℓ, e]
    linarith [mul_nonneg hL.le hτ]
  have hℓ0 : 0 < ℓ := by linarith
  have hσ0 : 0 ≤ σ2 := by
    rw [hσ2]
    positivity
  have hx : 0 ≤ 16 * ℓ / μ := by positivity
  have hA2 : 2 ≤ A := by rw [hA]; linarith
  have h2x : 2 ≤ 2 * ℓ / μ := by
    rw [le_div_iff₀ hμ]
    linarith
  have hA18 : A ≤ 18 * ℓ / μ := by
    have e1 : 16 * ℓ / μ = 8 * (2 * ℓ / μ) := by ring
    have e2 : 18 * ℓ / μ = 9 * (2 * ℓ / μ) := by ring
    rw [hA, e1, e2]
    linarith
  have hK0 : 0 < K := by linarith
  have hW0 : 0 < W := lt_of_lt_of_le (by positivity) hW
  have hz1 : (0 + A - 1) * (0 + A - 2) = A ^ 2 - 3 * A + 2 := by ring
  have hP0 : 0 ≤ (0 + A - 1) * (0 + A - 2) := mul_nonneg (by linarith) (by linarith)
  have hP1 : (0 + A - 1) * (0 + A - 2) ≤ A ^ 2 := by rw [hz1]; linarith
  have hfirst : μ / 4 * ((0 + A - 1) * (0 + A - 2)) * r ≤ μ / 4 * A ^ 2 * R ^ 2 := by
    have h3 := mul_le_mul hP1 hr hr0 (sq_nonneg A)
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ μ / 4)
    calc μ / 4 * ((0 + A - 1) * (0 + A - 2)) * r = μ / 4 * ((0 + A - 1) * (0 + A - 2) * r) := by
          ring
      _ ≤ μ / 4 * (A ^ 2 * R ^ 2) := h4
      _ = μ / 4 * A ^ 2 * R ^ 2 := by ring
  have hAsq : μ / 4 * A ^ 2 ≤ 81 * ℓ ^ 2 / μ := by
    have h1 : A ^ 2 ≤ (18 * ℓ / μ) ^ 2 := pow_le_pow_left₀ (by linarith) hA18 2
    have h2 : μ / 4 * (18 * ℓ / μ) ^ 2 = 81 * ℓ ^ 2 / μ := by
      field_simp; ring1
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ μ / 4)
    linarith
  have hsecond : 8 * ℓ / μ * D ≤ 2 * ℓ ^ 2 / μ * R ^ 2 := by
    have h1 : 8 * ℓ / μ * D ≤ 8 * ℓ / μ * (L / 2 * R ^ 2) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    have h3 : 4 * ℓ * L ≤ 2 * ℓ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hℓL (by positivity : (0 : ℝ) ≤ 2 * ℓ)
      calc 4 * ℓ * L = 2 * ℓ * (2 * L) := by ring
        _ ≤ 2 * ℓ * ℓ := this
        _ = 2 * ℓ ^ 2 := by ring
    have h4 : 4 * ℓ * L / μ ≤ 2 * ℓ ^ 2 / μ := div_le_div_of_nonneg_right h3 hμ.le
    have h5 := mul_le_mul_of_nonneg_right h4 (sq_nonneg R)
    have e : 8 * ℓ / μ * (L / 2 * R ^ 2) = 4 * ℓ * L / μ * R ^ 2 := by ring
    linarith
  have hnum : μ / 4 * ((0 + A - 1) * (0 + A - 2)) * r + 8 * ℓ / μ * D + 4 * K * σ2 / μ ≤
      83 * ℓ ^ 2 / μ * R ^ 2 + 4 * K * σ2 / μ := by
    have h1 := mul_le_mul_of_nonneg_right hAsq (sq_nonneg R)
    have e : 81 * ℓ ^ 2 / μ * R ^ 2 + 2 * ℓ ^ 2 / μ * R ^ 2 = 83 * ℓ ^ 2 / μ * R ^ 2 := by ring
    linarith
  have hnum0 : 0 ≤ μ / 4 * ((0 + A - 1) * (0 + A - 2)) * r + 8 * ℓ / μ * D + 4 * K * σ2 / μ := by
    have h1 := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ μ / 4) hP0) hr0
    have h2 := mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * ℓ / μ) hD0
    have h3 : 0 ≤ 4 * K * σ2 / μ := by positivity
    linarith
  have hstep : 2 / W * (μ / 4 * ((0 + A - 1) * (0 + A - 2)) * r + 8 * ℓ / μ * D +
      4 * K * σ2 / μ) ≤ 2 / (K ^ 2 / 2) * (83 * ℓ ^ 2 / μ * R ^ 2 + 4 * K * σ2 / μ) := by
    apply mul_le_mul _ hnum hnum0 (by positivity)
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hW
  have hsplit : 2 / (K ^ 2 / 2) * (83 * ℓ ^ 2 / μ * R ^ 2 + 4 * K * σ2 / μ) =
      332 * (ℓ ^ 2 * R ^ 2) / (μ * K ^ 2) + 16 * σ2 / (μ * K) := by
    field_simp; ring1
  have hsq : 0 < Real.sqrt (μ * ε) := Real.sqrt_pos.mpr (by positivity)
  have hsq2 : Real.sqrt (μ * ε) ^ 2 = μ * ε := Real.sq_sqrt (by positivity)
  have hb1 : 0 ≤ (2 + τ) * (26 * L * R / Real.sqrt (μ * ε)) := by positivity
  have hb2 : 0 ≤ (2 + τ) * (32 * dd * L / (μ * ε)) := by positivity
  have hsum : (2 + τ) * (26 * L * R / Real.sqrt (μ * ε) + 32 * dd * L / (μ * ε)) =
      (2 + τ) * (26 * L * R / Real.sqrt (μ * ε)) + (2 + τ) * (32 * dd * L / (μ * ε)) := by ring
  have hKa : 26 * ℓ * R / Real.sqrt (μ * ε) ≤ K := by
    have e : 26 * ℓ * R / Real.sqrt (μ * ε) = (2 + τ) * (26 * L * R / Real.sqrt (μ * ε)) := by
      rw [hℓ]
      ring
    rw [e]
    linarith
  have hKb : 32 * σ2 / (μ * ε) ≤ K := by
    have e : 32 * σ2 / (μ * ε) = (2 + τ) * (32 * dd * L / (μ * ε)) := by
      rw [hσ2]
      ring
    rw [e]
    linarith
  have ht1 : 332 * (ℓ ^ 2 * R ^ 2) / (μ * K ^ 2) ≤ ε / 2 := by
    have h1 : 26 * ℓ * R ≤ K * Real.sqrt (μ * ε) := (div_le_iff₀ hsq).mp hKa
    have h0 : 0 ≤ 26 * ℓ * R := by positivity
    have h2 : (26 * ℓ * R) ^ 2 ≤ (K * Real.sqrt (μ * ε)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have h3 : (26 * ℓ * R) ^ 2 = 676 * (ℓ ^ 2 * R ^ 2) := by ring
    have h4 : (K * Real.sqrt (μ * ε)) ^ 2 = K ^ 2 * (μ * ε) := by rw [mul_pow, hsq2]
    rw [h3, h4] at h2
    have h6 : ℓ ^ 2 * R ^ 2 ≤ K ^ 2 * (μ * ε) / 676 := by linarith
    have hden : 0 < μ * K ^ 2 := by positivity
    calc 332 * (ℓ ^ 2 * R ^ 2) / (μ * K ^ 2) ≤ 332 * (K ^ 2 * (μ * ε) / 676) / (μ * K ^ 2) :=
          div_le_div_of_nonneg_right (by linarith) hden.le
      _ = 332 * ε / 676 := by field_simp
      _ ≤ ε / 2 := by linarith
  have ht2 : 16 * σ2 / (μ * K) ≤ ε / 2 := by
    have h1 : 32 * σ2 ≤ K * (μ * ε) := (div_le_iff₀ (by positivity)).mp hKb
    have hden : 0 < μ * K := by positivity
    calc 16 * σ2 / (μ * K) ≤ (K * (μ * ε) / 2) / (μ * K) :=
          div_le_div_of_nonneg_right (by linarith) hden.le
      _ = ε / 2 := by field_simp
  linarith

lemma main_guarantee (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (hopt : IsOptimal V ms Cs) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) {m0 : Location d}
    {C0 : Scale d} (hC0 : IsCholesky C0) (hdist : sqDist m0 ms C0 Cs ≤ R ^ 2) {K : ℕ}
    (hK1 : 1 ≤ K)
    (hK : (2 + tau d (L / μ)) * (26 * L * R / Real.sqrt (μ * ε) + 32 * d * L / (μ * ε)) ≤ K) :
    Measurable (sgdOutput V μ (offset L μ d) m0 C0 K) ∧
    (∀ ω, IsCholesky (sgdOutput V μ (offset L μ d) m0 C0 K ω).2) ∧
    Integrable (fun ω => objective V (sgdOutput V μ (offset L μ d) m0 C0 K ω).1
      (sgdOutput V μ (offset L μ d) m0 C0 K ω).2 - objective V ms Cs)
      (Measure.infinitePi fun _ : ℕ => noiseLaw d) ∧
    (∫ ω, objective V (sgdOutput V μ (offset L μ d) m0 C0 K ω).1
      (sgdOutput V μ (offset L μ d) m0 C0 K ω).2 - objective V ms Cs
      ∂Measure.infinitePi fun _ : ℕ => noiseLaw d) ≤ ε := by
  have hμ := h.pos
  have hκ : 1 ≤ L / μ := (one_le_div hμ).mpr h.le
  have hτ : 0 ≤ tau d (L / μ) := tau_nonneg d hκ
  have ha : 2 ≤ offset L μ d := by
    have : 0 ≤ 16 * smoothConst L μ d / μ := by
      unfold smoothConst
      have := h.L_pos
      positivity
    unfold offset
    linarith
  have hK0 : 0 < K := hK1
  have hpre := StochasticGradient.prefix_measurePreserving (noiseLaw d) K
  have hout : ∀ ω, sgdOutput V μ (offset L μ d) m0 C0 K ω =
      (wmass (offset L μ d) 0 K)⁻¹ • wsum V μ (offset L μ d) 0 K (m0, C0) (fun i => ω i) :=
    fun ω => sgdOutput_eq V μ ha m0 C0 hK0 ω
  have hz0 : IsCholesky (m0, C0).2 := hC0
  have havg := fun ω : ℕ → Fin d → ℝ =>
    avg_bound h ms Cs ha K hK0 0 (m0, C0) (fun i : Fin K => ω i) hz0
  have hW := wmass_pos ha 0 hK0
  have hwsm : Measurable (fun ω : ℕ → Fin d → ℝ =>
      wsum V μ (offset L μ d) 0 K (m0, C0) (fun i : Fin K => ω i)) :=
    (measurable_wsum h (offset L μ d) K 0).comp (measurable_const.prodMk hpre.measurable)
  have hmeas : Measurable (sgdOutput V μ (offset L μ d) m0 C0 K) := by
    have he : sgdOutput V μ (offset L μ d) m0 C0 K = fun ω =>
        (wmass (offset L μ d) 0 K)⁻¹ • wsum V μ (offset L μ d) 0 K (m0, C0) (fun i => ω i) :=
      funext hout
    rw [he]
    exact (hwsm.fst.const_smul (wmass (offset L μ d) 0 K)⁻¹).prodMk
      (hwsm.snd.const_smul (wmass (offset L μ d) 0 K)⁻¹)
  refine ⟨hmeas, fun ω => by rw [hout]; exact (havg ω).1, ?_⟩
  have hpot := pot_bound h hopt K 0 (m0, C0) hz0
  have hgap_le : ∀ ω, objective V (sgdOutput V μ (offset L μ d) m0 C0 K ω).1
      (sgdOutput V μ (offset L μ d) m0 C0 K ω).2 - objective V ms Cs ≤
      2 / wmass (offset L μ d) 0 K *
        pot V ms Cs μ (offset L μ d) 0 K (m0, C0) (fun i => ω i) := by
    intro ω
    have h2 := (havg ω).2
    rw [hout ω]
    unfold gap objectivePair at h2
    exact h2.trans (le_of_eq (by ring))
  have hgap_nn : ∀ ω, 0 ≤ objective V (sgdOutput V μ (offset L μ d) m0 C0 K ω).1
      (sgdOutput V μ (offset L μ d) m0 C0 K ω).2 - objective V ms Cs := by
    intro ω
    have hc : IsCholesky (sgdOutput V μ (offset L μ d) m0 C0 K ω).2 := by
      rw [hout]
      exact (havg ω).1
    exact sub_nonneg.mpr (hopt.2 _ _ hc)
  have hpm : Measurable (fun ξ : Fin K → Fin d → ℝ =>
      pot V ms Cs μ (offset L μ d) 0 K (m0, C0) ξ) :=
    (measurable_pot h ms Cs (offset L μ d) K 0).of_uncurry_left
  have hpotP : Integrable (fun ω : ℕ → Fin d → ℝ =>
      pot V ms Cs μ (offset L μ d) 0 K (m0, C0) (fun i => ω i))
      (Measure.infinitePi fun _ : ℕ => noiseLaw d) :=
    hpre.integrable_comp_of_integrable hpot.1
  have hpotval : ∫ ω, pot V ms Cs μ (offset L μ d) 0 K (m0, C0) (fun i => ω i)
      ∂Measure.infinitePi (fun _ : ℕ => noiseLaw d) =
      ∫ ξ, pot V ms Cs μ (offset L μ d) 0 K (m0, C0) ξ ∂Measure.pi (fun _ : Fin K => noiseLaw d) := by
    have hm := integral_map (μ := Measure.infinitePi fun _ : ℕ => noiseLaw d)
      hpre.measurable.aemeasurable
      (f := fun ξ : Fin K → Fin d → ℝ => pot V ms Cs μ (offset L μ d) 0 K (m0, C0) ξ)
      (by rw [hpre.map_eq]; exact hpm.aestronglyMeasurable)
    rw [hpre.map_eq] at hm
    exact hm.symm
  have hgmeas : Measurable (fun ω => objective V (sgdOutput V μ (offset L μ d) m0 C0 K ω).1
      (sgdOutput V μ (offset L μ d) m0 C0 K ω).2 - objective V ms Cs) :=
    ((measurable_objectivePair h).comp hmeas).sub_const _
  have hint : Integrable (fun ω => objective V (sgdOutput V μ (offset L μ d) m0 C0 K ω).1
      (sgdOutput V μ (offset L μ d) m0 C0 K ω).2 - objective V ms Cs)
      (Measure.infinitePi fun _ : ℕ => noiseLaw d) := by
    refine Integrable.mono' (hpotP.const_mul (2 / wmass (offset L μ d) 0 K))
      hgmeas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hgap_nn ω)]
    exact hgap_le ω
  refine ⟨hint, ?_⟩
  have hm := integral_mono hint (hpotP.const_mul (2 / wmass (offset L μ d) 0 K)) hgap_le
  rw [integral_const_mul, hpotval] at hm
  have hD := bregmanMean_upper h (ms := ms) (Cs := Cs) m0 (isLower_sub hC0.1 hopt.1.1)
  have hD0 : 0 ≤ bregmanMean V ms Cs m0 C0 := by
    have := bregmanMean_lower h (ms := ms) (Cs := Cs) m0 (isLower_sub hC0.1 hopt.1.1)
    have := sqDist_nonneg m0 ms C0 Cs
    nlinarith
  have hDR : bregmanMean V ms Cs m0 C0 ≤ L / 2 * R ^ 2 := by
    have := mul_le_mul_of_nonneg_left hdist (by have := h.L_pos; positivity : (0 : ℝ) ≤ L / 2)
    exact hD.trans this
  have hbound := hpot.2
  simp only [Nat.cast_zero] at hbound
  have hscaled := mul_le_mul_of_nonneg_left hbound
    (by positivity : (0 : ℝ) ≤ 2 / wmass (offset L μ d) 0 K)
  have halg := budget_algebra (L := L) (μ := μ) (τ := tau d (L / μ)) (R := R) (ε := ε)
    (dd := d) (K := K) (W := wmass (offset L μ d) 0 K) (r := sqd (m0, C0) (ms, Cs))
    (D := bregmanMean V ms Cs m0 C0) (A := offset L μ d) hμ h.le hτ (Nat.cast_nonneg d) hR hε
    (by exact_mod_cast hK1) (wmass_ge ha K) (sqd_nonneg _ _) hdist hD0 hDR rfl hK
  have hsm : smoothConst L μ d = L * (2 + tau d (L / μ)) := rfl
  have hns : noiseConst L μ d = (2 + tau d (L / μ)) * L * d := rfl
  rw [hsm, hns] at hscaled
  linarith

end OracleTemplate.GaussianVariational
