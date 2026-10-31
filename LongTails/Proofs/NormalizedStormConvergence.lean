import LongTails.Proofs.NormalizedStormDescent
import LongTails.Proofs.AdaptiveIID
import LongTails.Setups.ExpectedSmoothnessNonconvex

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.NormalizedStorm

noncomputable def tS (L A C Δ ε : ℝ) : ℝ := 4 * A * Δ + 2 * A * ε ^ 2 / L + C

noncomputable def tA (L A C Δ ε : ℝ) : ℝ := ε ^ 2 / (ε ^ 2 + 400 * tS L A C Δ ε)

noncomputable def tEta (L A C Δ ε : ℝ) : ℝ := ε * Real.sqrt (tA L A C Δ ε) / (40 * L)

noncomputable def tB0 (L A C Δ ε : ℝ) : ℕ := ⌈192 * tS L A C Δ ε / ε ^ 2⌉₊ + 1

noncomputable def tT (L A C Δ ε : ℝ) : ℕ := ⌈80 * L * Δ / (ε ^ 2 * Real.sqrt (tA L A C Δ ε))⌉₊

lemma ceil_add_ceil_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : ⌈x⌉₊ + ⌈y⌉₊ ≤ ⌈x + y⌉₊ + 1 := by
  have h1 := Nat.ceil_lt_add_one hx
  have h2 := Nat.ceil_lt_add_one hy
  have h3 := Nat.le_ceil (x + y)
  have h : ((⌈x⌉₊ + ⌈y⌉₊ : ℕ) : ℝ) < ((⌈x + y⌉₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
  have h' : ⌈x⌉₊ + ⌈y⌉₊ < ⌈x + y⌉₊ + 2 := by exact_mod_cast h
  omega

section Tuning

variable {L A C Δ ε : ℝ}

structure TuneHyp (L A C Δ ε : ℝ) : Prop where
  L_pos : 0 < L
  A_nn : 0 ≤ A
  C_nn : 0 ≤ C
  Δ_nn : 0 ≤ Δ
  ε_pos : 0 < ε

lemma TuneHyp.s_nn (h : TuneHyp L A C Δ ε) : 0 ≤ tS L A C Δ ε := by
  have := h.L_pos; have := h.A_nn; have := h.C_nn; have := h.Δ_nn
  unfold tS; positivity

lemma TuneHyp.a_pos (h : TuneHyp L A C Δ ε) : 0 < tA L A C Δ ε := by
  have := h.s_nn; have := h.ε_pos
  unfold tA; positivity

lemma TuneHyp.a_le (h : TuneHyp L A C Δ ε) : tA L A C Δ ε ≤ 1 := by
  have := h.s_nn; have := h.ε_pos
  unfold tA
  rw [div_le_one (by positivity)]
  linarith

lemma TuneHyp.as_le (h : TuneHyp L A C Δ ε) :
    tA L A C Δ ε * tS L A C Δ ε ≤ ε ^ 2 / 400 := by
  have := h.s_nn; have := h.ε_pos
  unfold tA
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg ε]

lemma TuneHyp.r_pos (h : TuneHyp L A C Δ ε) : 0 < Real.sqrt (tA L A C Δ ε) :=
  Real.sqrt_pos.mpr h.a_pos

lemma TuneHyp.r_le (h : TuneHyp L A C Δ ε) : Real.sqrt (tA L A C Δ ε) ≤ 1 := by
  rw [Real.sqrt_le_one]; exact h.a_le

lemma TuneHyp.eta_pos (h : TuneHyp L A C Δ ε) : 0 < tEta L A C Δ ε := by
  have := h.r_pos; have := h.ε_pos; have := h.L_pos
  unfold tEta; positivity

lemma tB0_pos (L A C Δ ε : ℝ) : 1 ≤ tB0 L A C Δ ε := by
  unfold tB0; omega

lemma sqrt_V {ε : ℝ} (hε : 0 < ε) : Real.sqrt (ε ^ 2 / 64) = ε / 8 := by
  rw [show ε ^ 2 / 64 = (ε / 8) ^ 2 by ring, Real.sqrt_sq (by positivity)]

lemma TuneHyp.init (h : TuneHyp L A C Δ ε) {F0 : ℝ} (hF0 : 0 ≤ F0) (hF0Δ : F0 ≤ Δ) :
    (2 * A * F0 + C) / (tB0 L A C Δ ε : ℝ) ≤ ε ^ 2 / 64 := by
  have hs := h.s_nn
  have hε := h.ε_pos
  have hL := h.L_pos
  have hA := h.A_nn
  have hb : (192 * tS L A C Δ ε / ε ^ 2) + 1 ≤ (tB0 L A C Δ ε : ℝ) := by
    unfold tB0; push_cast
    linarith [Nat.le_ceil (192 * tS L A C Δ ε / ε ^ 2)]
  have hb0 : (0 : ℝ) < tB0 L A C Δ ε := by
    have : 0 ≤ 192 * tS L A C Δ ε / ε ^ 2 := by positivity
    linarith
  have hnum : 2 * A * F0 + C ≤ tS L A C Δ ε := by
    unfold tS
    have : 0 ≤ 2 * A * ε ^ 2 / L := by positivity
    nlinarith
  rw [div_le_iff₀ hb0]
  have h192 : 192 * tS L A C Δ ε / ε ^ 2 * ε ^ 2 = 192 * tS L A C Δ ε := by
    field_simp
  nlinarith

lemma TuneHyp.contract (h : TuneHyp L A C Δ ε) :
    (1 - tA L A C Δ ε) ^ 2 * (ε ^ 2 / 64) +
      (2 * tA L A C Δ ε ^ 2 * (2 * A * (2 * Δ + ε ^ 2 / L) + C) + 8 * L ^ 2 * tEta L A C Δ ε ^ 2) ≤
        ε ^ 2 / 64 := by
  have ha0 := h.a_pos
  have ha1 := h.a_le
  have has := h.as_le
  have hL := h.L_pos
  have hε := h.ε_pos
  have hD : 2 * A * (2 * Δ + ε ^ 2 / L) + C = tS L A C Δ ε := by
    unfold tS; ring
  have hη : 8 * L ^ 2 * tEta L A C Δ ε ^ 2 = tA L A C Δ ε * ε ^ 2 / 200 := by
    unfold tEta
    rw [div_pow, mul_pow, Real.sq_sqrt h.a_pos.le]
    field_simp
    ring
  rw [hD, hη]
  have e : 2 * tA L A C Δ ε ^ 2 * tS L A C Δ ε =
      2 * tA L A C Δ ε * (tA L A C Δ ε * tS L A C Δ ε) := by ring
  rw [e]
  have h1 : (1 - tA L A C Δ ε) ^ 2 ≤ 1 - tA L A C Δ ε := by nlinarith
  have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ ε ^ 2 / 64)
  have h3 := mul_le_mul_of_nonneg_left has (by linarith : (0 : ℝ) ≤ 2 * tA L A C Δ ε)
  have h4 : 0 ≤ tA L A C Δ ε * ε ^ 2 := by positivity
  nlinarith

lemma TuneHyp.horizon (h : TuneHyp L A C Δ ε) :
    2 * Δ ≤ ((tT L A C Δ ε : ℝ) + 1) * tEta L A C Δ ε * ε ∧
      ((tT L A C Δ ε : ℝ) + 1) * tEta L A C Δ ε * ε ≤ 2 * Δ + ε ^ 2 / (20 * L) := by
  have hr := h.r_pos
  have hr1 := h.r_le
  have hL := h.L_pos
  have hε := h.ε_pos
  have hΔ := h.Δ_nn
  set r := Real.sqrt (tA L A C Δ ε)
  set T := tT L A C Δ ε
  have hx : 0 ≤ 80 * L * Δ / (ε ^ 2 * r) := by positivity
  have hT1 : 80 * L * Δ / (ε ^ 2 * r) ≤ (T : ℝ) := Nat.le_ceil _
  have hT2 : (T : ℝ) < 80 * L * Δ / (ε ^ 2 * r) + 1 := Nat.ceil_lt_add_one hx
  have hd : 0 < ε ^ 2 * r := by positivity
  rw [div_le_iff₀ hd] at hT1
  have hT2' : (T : ℝ) * (ε ^ 2 * r) < 80 * L * Δ + ε ^ 2 * r := by
    have := (lt_div_iff₀ hd).mp (by linarith : (T : ℝ) - 1 < 80 * L * Δ / (ε ^ 2 * r))
    nlinarith
  have hY : ((T : ℝ) + 1) * tEta L A C Δ ε * ε = ((T : ℝ) + 1) * (ε ^ 2 * r) / (40 * L) := by
    change ((T : ℝ) + 1) * (ε * r / (40 * L)) * ε = _
    field_simp
  rw [hY]
  constructor
  · rw [le_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have : ε ^ 2 / (20 * L) * (40 * L) = 2 * ε ^ 2 := by field_simp; ring
    nlinarith

lemma TuneHyp.step_cost (h : TuneHyp L A C Δ ε) :
    2 * tEta L A C Δ ε * Real.sqrt (ε ^ 2 / 64) + L / 2 * tEta L A C Δ ε ^ 2 ≤
      (21 / 80) * (tEta L A C Δ ε * ε) := by
  rw [sqrt_V h.ε_pos]
  have hη := h.eta_pos
  have hLη : L * tEta L A C Δ ε ≤ ε / 40 := by
    have hr1 := h.r_le; have hL := h.L_pos; have hε := h.ε_pos
    change L * (ε * Real.sqrt (tA L A C Δ ε) / (40 * L)) ≤ ε / 40
    rw [show L * (ε * Real.sqrt (tA L A C Δ ε) / (40 * L)) = ε * Real.sqrt (tA L A C Δ ε) / 40 by
      field_simp]
    have := mul_le_mul_of_nonneg_left hr1 hε.le
    linarith
  nlinarith

lemma TuneHyp.bounds (h : TuneHyp L A C Δ ε) {F0 : ℝ} (hF0 : 0 ≤ F0) (hF0Δ : F0 ≤ Δ) :
    F0 + ((tT L A C Δ ε : ℝ) + 1) * (2 * tEta L A C Δ ε * Real.sqrt (ε ^ 2 / 64) +
        L / 2 * tEta L A C Δ ε ^ 2) ≤ 2 * Δ + ε ^ 2 / L ∧
      F0 + ((tT L A C Δ ε : ℝ) + 1) * (2 * tEta L A C Δ ε * Real.sqrt (ε ^ 2 / 64) +
        L / 2 * tEta L A C Δ ε ^ 2) ≤ ((tT L A C Δ ε : ℝ) + 1) * tEta L A C Δ ε * ε := by
  obtain ⟨h1, h2⟩ := h.horizon
  have hc := h.step_cost
  have hT : (0 : ℝ) ≤ (tT L A C Δ ε : ℝ) + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hc hT
  have hL := h.L_pos
  have hε := h.ε_pos
  have e1 : ε ^ 2 / (20 * L) ≤ ε ^ 2 / L := by
    apply div_le_div_of_nonneg_left (by positivity) hL (by linarith)
  constructor <;> nlinarith

lemma TuneHyp.calls (h : TuneHyp L A C Δ ε) :
    tB0 L A C Δ ε + tT L A C Δ ε ≤
      ⌈(192 * (4 * A * Δ + C) + 80 * L * Δ) / ε ^ 2 + 384 * A / L +
        1600 * L * Δ * Real.sqrt (4 * A * Δ + 2 * A * ε ^ 2 / L + C) / ε ^ 3⌉₊ + 3 := by
  have hs := h.s_nn
  have hε := h.ε_pos
  have hL := h.L_pos
  have hΔ := h.Δ_nn
  have hr := h.r_pos
  set s := tS L A C Δ ε with hsdef
  set u := Real.sqrt s
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = s := Real.sq_sqrt hs
  set r := Real.sqrt (tA L A C Δ ε)
  have hr2 : r ^ 2 = tA L A C Δ ε := Real.sq_sqrt h.a_pos.le
  have hkey : ε ≤ r * (ε + 20 * u) := by
    have hsq : ε ^ 2 ≤ (r * (ε + 20 * u)) ^ 2 := by
      rw [mul_pow, hr2]
      unfold tA
      rw [← hsdef, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg ε, mul_nonneg hε.le hu]
    have hp : 0 ≤ r * (ε + 20 * u) := by positivity
    nlinarith [sq_nonneg (r * (ε + 20 * u) - ε), sq_nonneg (r * (ε + 20 * u) + ε)]
  have hT : 80 * L * Δ / (ε ^ 2 * r) ≤ 80 * L * Δ / ε ^ 2 + 1600 * L * Δ * u / ε ^ 3 := by
    rw [div_le_iff₀ (by positivity)]
    have e : (80 * L * Δ / ε ^ 2 + 1600 * L * Δ * u / ε ^ 3) * (ε ^ 2 * r) =
        80 * L * Δ * (r * (ε + 20 * u)) / ε := by
      field_simp; ring
    rw [e, le_div_iff₀ hε]
    have : 0 ≤ 80 * L * Δ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hkey this]
  have hTc : tT L A C Δ ε ≤ ⌈80 * L * Δ / ε ^ 2 + 1600 * L * Δ * u / ε ^ 3⌉₊ :=
    Nat.ceil_mono hT
  have hx : 0 ≤ 192 * s / ε ^ 2 := by positivity
  have hy : 0 ≤ 80 * L * Δ / ε ^ 2 + 1600 * L * Δ * u / ε ^ 3 := by positivity
  have hsum := ceil_add_ceil_le hx hy
  have he : 192 * s / ε ^ 2 + (80 * L * Δ / ε ^ 2 + 1600 * L * Δ * u / ε ^ 3) =
      (192 * (4 * A * Δ + C) + 80 * L * Δ) / ε ^ 2 + 384 * A / L +
        1600 * L * Δ * Real.sqrt (4 * A * Δ + 2 * A * ε ^ 2 / L + C) / ε ^ 3 := by
    simp only [u, hsdef, tS]
    field_simp
    ring
  rw [he] at hsum
  unfold tB0
  rw [← hsdef]
  omega

end Tuning

section Master

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {F : E → ℝ} {g : E → Ω → E} {L A C lower : ℝ}

omit [CompleteSpace E] in
lemma measurable_out (hg : Measurable (Function.uncurry g)) (η a : ℝ) (b0 T : ℕ) (x0 : E) :
    Measurable (fun ω : Fin (T + 1) × (ℕ → Ω) => (stormPair g η a b0 x0 ω.2 ω.1.val).1) :=
  measurable_from_prod_countable_right fun τ => (measurable_stormPair hg η a b0 x0 τ.val).fst

theorem Hyp.master_lintegral (H : Hyp p F g L A C lower) {Δ ε : ℝ} (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (x0 : E) (hgap : F x0 - lower ≤ Δ) :
    ∫⁻ ω, ENNReal.ofReal ‖gradient F (stormPair g (tEta L A C Δ ε) (tA L A C Δ ε) (tB0 L A C Δ ε)
        x0 ω.2 ω.1.val).1‖
      ∂((PMF.uniformOfFintype (Fin (tT L A C Δ ε + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => p)) ≤ ENNReal.ofReal ε := by
  have h : TuneHyp L A C Δ ε := ⟨H.L_pos, H.A_nn, H.C_nn, hΔ, hε⟩
  set η := tEta L A C Δ ε
  set a := tA L A C Δ ε
  set b0 := tB0 L A C Δ ε
  set T := tT L A C Δ ε
  have hF0 : 0 ≤ F x0 - lower := sub_nonneg.mpr (H.low x0)
  obtain ⟨hD1, hD2⟩ := h.bounds hF0 hgap
  have hV := h.contract
  have h0 := h.init hF0 hgap
  have hs := H.grad_sum h.eta_pos h.a_pos.le h.a_le (tB0_pos L A C Δ ε) x0 (V := ε ^ 2 / 64)
    (Dmax := 2 * Δ + ε ^ 2 / L) (T := T) (by simpa [mul_sub] using h0) hV hD1
  obtain ⟨hgi, hsum⟩ := hs
  set P := Measure.infinitePi fun _ : ℕ => p
  have hm : Measurable (fun ω : Fin (T + 1) × (ℕ → Ω) =>
      ENNReal.ofReal ‖gradient F (stormPair g η a b0 x0 ω.2 ω.1.val).1‖) :=
    ENNReal.measurable_ofReal.comp
      (H.grad_continuous.measurable.comp (measurable_out H.meas η a b0 T x0)).norm
  rw [lintegral_prod _ hm.aemeasurable, lintegral_fintype]
  simp only [PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _), Fintype.card_fin]
  have hc : ∀ τ : Fin (T + 1), (Fintype.card ({τ} : Set (Fin (T + 1))) : ℝ≥0∞) = 1 := by
    intro τ; simp
  simp only [hc, one_div]
  have hj : ∀ τ : Fin (T + 1), ∫⁻ ξ, ENNReal.ofReal ‖gradient F (stormPair g η a b0 x0 ξ τ.val).1‖ ∂P =
      ENNReal.ofReal (∫ ξ, ‖gradient F (stormPair g η a b0 x0 ξ τ.val).1‖ ∂P) := by
    intro τ
    rw [ofReal_integral_eq_lintegral_ofReal (hgi τ.val (Nat.lt_succ_iff.mp τ.isLt))
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
  simp_rw [hj]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => integral_nonneg fun _ => norm_nonneg _)]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∫ ξ, ‖gradient F (stormPair g η a b0 x0 ξ k).1‖ ∂P)]
  have hT : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hη := h.eta_pos
  have hbound : ∑ k ∈ Finset.range (T + 1), ∫ ξ, ‖gradient F (stormPair g η a b0 x0 ξ k).1‖ ∂P ≤
      ((T : ℝ) + 1) * ε := by
    have h1 := hsum.trans hD2
    have h2 : η * ∑ k ∈ Finset.range (T + 1), ∫ ξ, ‖gradient F (stormPair g η a b0 x0 ξ k).1‖ ∂P ≤
        η * (((T : ℝ) + 1) * ε) := by linarith
    exact le_of_mul_le_mul_left h2 hη
  have hinv : (((T + 1 : ℕ) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / ((T : ℝ) + 1)) := by
    rw [ENNReal.ofReal_div_of_pos hT, ENNReal.ofReal_one, one_div]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]
    simp
  rw [hinv, ← ENNReal.ofReal_mul (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_one_div, div_le_iff₀ hT]
  linarith

end Master

open LongTails.Setups.ExpectedSmoothnessNonconvex

theorem convergence : Convergence LongTails.Setups.ExpectedSmoothnessNonconvex.spec
    (fun q _ => ⌈(192 * (4 * q.A * q.Δ + q.C) + 80 * q.L * q.Δ) / q.ε ^ 2 + 384 * q.A / q.L +
      1600 * q.L * q.Δ * Real.sqrt (4 * q.A * q.Δ + 2 * q.A * q.ε ^ 2 / q.L + q.C) / q.ε ^ 3⌉₊ + 3) := by
  apply convergence_of_public_budget (S := spec) (fun q => ⌈(192 * (4 * q.A * q.Δ + q.C) +
    80 * q.L * q.Δ) / q.ε ^ 2 + 384 * q.A / q.L +
      1600 * q.L * q.Δ * Real.sqrt (4 * q.A * q.Δ + 2 * q.A * q.ε ^ 2 / q.L + q.C) / q.ε ^ 3⌉₊ + 3)
  refine ⟨fun q => normalizedStorm (tEta q.L q.A q.C q.Δ q.ε) (tA q.L q.A q.C q.Δ q.ε)
    (tB0 q.L q.A q.C q.Δ q.ε) (tT q.L q.A q.C q.Δ q.ε) q.x0, ?_, fun _ _ => trivial⟩
  intro q hq f O hadm
  dsimp only
  obtain ⟨hL, hA, hC, hΔ, hε⟩ := hq
  obtain ⟨g, p, P, hIID, rfl, hgrad, hlip, hgm, hint, hmean, hvi, hdi, hmss, lower, hlow, hgap,
    habc⟩ := hadm
  have H : Hyp (p : Measure q.Ω) f g q.L q.A q.C lower :=
    ⟨hgrad, hlip, hgm, hint, hmean, hvi, hdi, hmss, hlow, habc, hL, hA, hC⟩
  have h : TuneHyp q.L q.A q.C q.Δ q.ε := ⟨hL, hA, hC, hΔ, hε⟩
  set η := tEta q.L q.A q.C q.Δ q.ε
  set a := tA q.L q.A q.C q.Δ q.ε
  set b0 := tB0 q.L q.A q.C q.Δ q.ε
  set T := tT q.L q.A q.C q.Δ q.ε
  set K := ⌈(192 * (4 * q.A * q.Δ + q.C) + 80 * q.L * q.Δ) / q.ε ^ 2 + 384 * q.A / q.L +
      1600 * q.L * q.Δ * Real.sqrt (4 * q.A * q.Δ + 2 * q.A * q.ε ^ 2 / q.L + q.C) / q.ε ^ 3⌉₊ + 3
  have hK : b0 + T ≤ K := h.calls
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω) := by
    have := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans this
  have hexec : ∀ (τ : Fin (T + 1)) (ξ : ℕ → q.Ω),
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (q.E × q.E) (q.E × q.E)) (normalizedStorm η a b0 T q.x0) (fun _ => K)
        (show (normalizedStorm η a b0 T q.x0).Seed from τ) ξ =
      (stormPair g η a b0 q.x0 ξ τ.val).1 :=
    fun τ ξ => execute_normalizedStorm g P η a b0 T q.x0 K τ ξ hK
  have hout : (fun seed : (normalizedStorm η a b0 T q.x0).Seed × ((k : ℕ) → q.Ω) =>
      (execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (q.E × q.E) (q.E × q.E)) (normalizedStorm η a b0 T q.x0) (fun _ => K) seed.1 seed.2)) =
      fun ω => (stormPair g η a b0 q.x0 ω.2 ω.1.val).1 := by
    funext seed; exact hexec seed.1 seed.2
  refine ⟨?_, ?_⟩
  · erw [hout]; exact measurable_out hgm η a b0 T q.x0
  have hfun : (fun ω : (normalizedStorm η a b0 T q.x0).Seed × (ℕ → q.Ω) =>
      ‖gradient f (execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (q.E × q.E) (q.E × q.E)) (normalizedStorm η a b0 T q.x0) (fun _ => K) ω.1 ω.2)‖) =
      fun ω => ‖gradient f (stormPair g η a b0 q.x0 ω.2 ω.1.val).1‖ := by
    funext ω; rw [hexec ω.1 ω.2]
  erw [hfun]
  change Integrable (fun ω : Fin (T + 1) × (ℕ → q.Ω) => ‖gradient f (stormPair g η a b0 q.x0 ω.2 ω.1.val).1‖)
      ((PMF.uniformOfFintype (Fin (T + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ∧
    ∫ ω : Fin (T + 1) × (ℕ → q.Ω), ‖gradient f (stormPair g η a b0 q.x0 ω.2 ω.1.val).1‖
      ∂((PMF.uniformOfFintype (Fin (T + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
  rw [hP]
  have hm : Measurable (fun ω : Fin (T + 1) × (ℕ → q.Ω) =>
      ‖gradient f (stormPair g η a b0 q.x0 ω.2 ω.1.val).1‖) :=
    (H.grad_continuous.measurable.comp (measurable_out hgm η a b0 T q.x0)).norm
  have hL' := H.master_lintegral hΔ hε q.x0 hgap
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL'
  refine ⟨?_, ?_⟩
  · have := integrable_toReal_of_lintegral_ne_top (ENNReal.measurable_ofReal.comp hm).aemeasurable hfin
    simpa [ENNReal.toReal_ofReal (norm_nonneg _)] using this
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hL'

end OracleTemplate.NormalizedStorm
