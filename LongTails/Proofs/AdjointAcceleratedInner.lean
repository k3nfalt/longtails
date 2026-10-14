import LongTails.Proofs.AdjointInner
import LongTails.Algorithms.AdjointAcceleratedProximal

open scoped RealInnerProductSpace

namespace OracleTemplate.CohypomonotoneAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : E → E} {J : E → E →L[ℝ] E} {L L₂ ρ : ℝ}

noncomputable def mgrad (L ρ : ℝ) (F : E → E) (adj : E → E → E) (t v : E) : E :=
  res L ρ F t v + (2 * ρ + 1 / L) • adj v (res L ρ F t v)

noncomputable def agdStep (L ρ : ℝ) (F : E → E) (adj : E → E → E) (t : E) (s : AgdState E) :
    AgdState E :=
  agdUpdate L ρ s (mgrad L ρ F adj t s.y)

noncomputable def agdRun (L ρ : ℝ) (F : E → E) (adj : E → E → E) (t v0 : E) (N : ℕ) : E :=
  ((agdStep L ρ F adj t)^[N] ⟨v0, v0, v0⟩).x

noncomputable def innerSolve (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (t v0 : E) : E :=
  if useAgd L L₂ ρ ‖res L ρ F t v0‖ then agdRun L ρ F adj t v0 (agdLen L ρ)
  else innerRun L L₂ ρ F adj t v0 (innerLen L L₂ ρ ‖res L ρ F t v0‖)

section Geometry

lemma res_sub (t x y : E) :
    res L ρ F t y - res L ρ F t x = (y - x) + (2 * ρ + 1 / L) • (F y - F x) := by
  rw [res, res, smul_sub]; abel

lemma res_expand (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hρ : 0 ≤ ρ) (t x y : E) :
    ‖y - x‖ ≤ ‖res L ρ F t y - res L ρ F t x‖ := by
  set γ := 2 * ρ + 1 / L with hγ
  have hγ0 : 0 ≤ γ := by positivity
  have hγ2 : 2 * ρ ≤ γ := by
    have : 0 < 1 / L := by positivity
    linarith
  rw [res_sub, ← hγ]
  have hc := h.cohypo y x
  have hsq : ‖y - x‖ ^ 2 ≤ ‖(y - x) + γ • (F y - F x)‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0, real_inner_smul_right,
      real_inner_comm]
    have hF := sq_nonneg ‖F y - F x‖
    nlinarith [mul_le_mul_of_nonneg_left hc hγ0, mul_nonneg hγ0 (mul_nonneg (sub_nonneg.mpr hγ2) hF)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

lemma res_lip (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hρ : 0 ≤ ρ) (t x y : E) :
    ‖res L ρ F t y - res L ρ F t x‖ ≤ (2 + 2 * ρ * L) * ‖y - x‖ := by
  have hγ0 : 0 ≤ 2 * ρ + 1 / L := by positivity
  rw [res_sub, ← gam_L hL]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0]
  have := h.lip y x
  nlinarith [mul_le_mul_of_nonneg_left this hγ0, norm_nonneg (y - x)]

lemma merit_bounds (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ)
    {adj : E → E → E} (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (t x y : E)
    (hx : 4 * (2 * ρ + 1 / L) * L₂ * ‖res L ρ F t x‖ ≤ 1) :
    ‖res L ρ F t x‖ ^ 2 / 2 + ⟪mgrad L ρ F adj t x, y - x⟫ + ‖y - x‖ ^ 2 / 4 ≤
        ‖res L ρ F t y‖ ^ 2 / 2 ∧
      ‖res L ρ F t y‖ ^ 2 / 2 ≤ ‖res L ρ F t x‖ ^ 2 / 2 + ⟪mgrad L ρ F adj t x, y - x⟫ +
        (2 + 2 * ρ * L) ^ 2 * ‖y - x‖ ^ 2 := by
  set γ := 2 * ρ + 1 / L with hγ
  set Λ := 2 + 2 * ρ * L with hΛ
  set r := res L ρ F t x with hr
  set d := y - x with hd
  set Δ := res L ρ F t y - r with hΔ
  set E1 := F (x + d) - F x - J x d with hE1
  have hγ0 : 0 ≤ γ := by positivity
  have hxd : x + d = y := by rw [hd]; abel
  have hΔeq : Δ = (d + γ • J x d) + γ • E1 := by
    rw [hΔ, hr, res_sub, ← hγ, hE1, hxd, ← hd]; module
  have hg : ⟪mgrad L ρ F adj t x, d⟫ = ⟪r, d + γ • J x d⟫ := by
    rw [mgrad, ← hr, ← hγ]
    exact adj_inner (fun h' => hadj x r h') d
  have hres : res L ρ F t y = r + Δ := by rw [hΔ]; abel
  have hkey : ‖res L ρ F t y‖ ^ 2 / 2 = ‖r‖ ^ 2 / 2 + ⟪mgrad L ρ F adj t x, d⟫ +
      (‖Δ‖ ^ 2 / 2 + γ * ⟪r, E1⟫) := by
    rw [hres, hg, norm_add_sq_real, hΔeq, inner_add_right, real_inner_smul_right]
    ring
  have hTay : ‖E1‖ ≤ L₂ * ‖d‖ ^ 2 := h.taylor hL₂ x d
  have hrE : |γ * ⟪r, E1⟫| ≤ ‖d‖ ^ 2 / 4 := by
    rw [abs_mul, abs_of_nonneg hγ0]
    have h1 : |⟪r, E1⟫| ≤ ‖r‖ * ‖E1‖ := abs_real_inner_le_norm r E1
    have h2 : γ * (‖r‖ * ‖E1‖) ≤ γ * (‖r‖ * (L₂ * ‖d‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTay (norm_nonneg r)) hγ0
    have h3 : γ * (‖r‖ * (L₂ * ‖d‖ ^ 2)) = (4 * γ * L₂ * ‖r‖) * ‖d‖ ^ 2 / 4 := by ring
    have h4 : (4 * γ * L₂ * ‖r‖) * ‖d‖ ^ 2 / 4 ≤ 1 * ‖d‖ ^ 2 / 4 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hx (sq_nonneg _)) (by norm_num)
    calc γ * |⟪r, E1⟫| ≤ γ * (‖r‖ * ‖E1‖) := mul_le_mul_of_nonneg_left h1 hγ0
      _ ≤ _ := h2
      _ = _ := h3
      _ ≤ 1 * ‖d‖ ^ 2 / 4 := h4
      _ = ‖d‖ ^ 2 / 4 := by ring
  have hlow : ‖d‖ ≤ ‖Δ‖ := by rw [hΔ, hr, hd]; exact res_expand h hL hρ t x y
  have hup : ‖Δ‖ ≤ Λ * ‖d‖ := by rw [hΔ, hr, hd]; exact res_lip h hL hρ t x y
  have hΛ2 : 2 ≤ Λ := by rw [hΛ]; nlinarith [mul_nonneg hρ hL.le]
  have hlow2 : ‖d‖ ^ 2 ≤ ‖Δ‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hlow 2
  have hup2 : ‖Δ‖ ^ 2 ≤ Λ ^ 2 * ‖d‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hup 2
    rwa [mul_pow] at this
  have hab := abs_le.mp hrE
  constructor
  · rw [hkey]; nlinarith
  · rw [hkey]; nlinarith [sq_nonneg ‖d‖]

end Geometry

section Root

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma res_continuous (h : Hyp F J L L₂ ρ) (t : E) : Continuous (res L ρ F t) := by
  have hF : Continuous F := by
    exact continuous_iff_continuousAt.mpr fun x => (h.deriv x).continuousAt
  unfold res
  fun_prop

lemma exists_root (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ)
    {adj : E → E → E} (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (t v0 : E) :
    ∃ w, res L ρ F t w = 0 ∧ ‖v0 - w‖ ≤ ‖res L ρ F t v0‖ := by
  set S := {v : E | ‖res L ρ F t v‖ ≤ ‖res L ρ F t v0‖} with hS
  have hcont := res_continuous h t
  have hclosed : IsClosed S := isClosed_le (hcont.norm) continuous_const
  have hsub : S ⊆ Metric.closedBall v0 (2 * ‖res L ρ F t v0‖) := by
    intro v hv
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 := res_expand h hL hρ t v0 v
    have h2 : ‖res L ρ F t v - res L ρ F t v0‖ ≤ ‖res L ρ F t v‖ + ‖res L ρ F t v0‖ :=
      norm_sub_le _ _
    have hv' : ‖res L ρ F t v‖ ≤ ‖res L ρ F t v0‖ := hv
    linarith
  have hcpt : IsCompact S := (isCompact_closedBall _ _).of_isClosed_subset hclosed hsub
  have hne : S.Nonempty := ⟨v0, show ‖res L ρ F t v0‖ ≤ ‖res L ρ F t v0‖ from le_rfl⟩
  obtain ⟨w, hwS, hmin⟩ := hcpt.exists_isMinOn hne hcont.norm.continuousOn
  have hw0 : res L ρ F t w = 0 := by
    by_contra hne0
    have hpos : 0 < ‖res L ρ F t w‖ := norm_pos_iff.mpr hne0
    have hstep := res_step h hL hL₂ hρ hadj t w
    have hΛpos : 0 < 2 + 2 * ρ * L := by positivity
    have hM : 0 < max 1 (4 * (2 * ρ + 1 / L) * L₂ * ‖res L ρ F t w‖) :=
      lt_max_of_lt_left one_pos
    have hdec : 0 < (1 / (4 * (2 + 2 * ρ * L) ^ 2)) * ‖res L ρ F t w‖ /
        max 1 (4 * (2 * ρ + 1 / L) * L₂ * ‖res L ρ F t w‖) := by positivity
    have hlt : ‖res L ρ F t (innerStep L L₂ ρ F adj t w)‖ < ‖res L ρ F t w‖ := by linarith
    have hin : innerStep L L₂ ρ F adj t w ∈ S := by
      show ‖res L ρ F t (innerStep L L₂ ρ F adj t w)‖ ≤ ‖res L ρ F t v0‖
      exact hlt.le.trans hwS
    have := hmin hin
    simp only [Set.mem_ofPred_eq] at this
    linarith
  refine ⟨w, hw0, ?_⟩
  have := res_expand h hL hρ t w v0
  rwa [hw0, sub_zero] at this

end Root

section AGD

noncomputable def apot (L ρ : ℝ) (F : E → E) (t w : E) (s : AgdState E) : ℝ :=
  ‖res L ρ F t s.x‖ ^ 2 / 2 + ‖s.z - w‖ ^ 2 / 4

lemma agdq_pos (hL : 0 < L) (hρ : 0 ≤ ρ) : 0 < agdq L ρ := by
  unfold agdq; positivity

lemma agdq_le (hL : 0 < L) (hρ : 0 ≤ ρ) : agdq L ρ ≤ 1 / 4 := by
  unfold agdq
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_nonneg hρ hL.le]

lemma jensen_sq (a b : E) (q : ℝ) :
    (1 - q) * ‖a‖ ^ 2 + q * ‖b‖ ^ 2 - ‖(1 - q) • a + q • b‖ ^ 2 = q * (1 - q) * ‖a - b‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right,
    norm_sub_sq_real]
  ring

lemma agd_step (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ)
    {adj : E → E → E} (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (t w : E)
    (hw : res L ρ F t w = 0) (s : AgdState E)
    (hy : s.y = (1 / (1 + agdq L ρ)) • (s.x + agdq L ρ • s.z))
    (hc : 4 * (2 * ρ + 1 / L) * L₂ * ‖res L ρ F t s.y‖ ≤ 1) :
    apot L ρ F t w (agdStep L ρ F adj t s) ≤ (1 - agdq L ρ) * apot L ρ F t w s := by
  set q := agdq L ρ with hq
  set Λ := 2 + 2 * ρ * L with hΛ
  set g := mgrad L ρ F adj t s.y with hg
  have hq0 : 0 < q := agdq_pos hL hρ
  have hq1 : q ≤ 1 / 4 := agdq_le hL hρ
  have hΛpos : 0 < Λ := by rw [hΛ]; positivity
  have hqΛ : q = 1 / (2 * Λ) := rfl
  have hLm : agdL L ρ = 2 * Λ ^ 2 := rfl
  set x' := s.y - (1 / agdL L ρ) • g with hx'
  set z' := (1 - q) • s.z + q • s.y - (2 * q) • g with hz'
  have hsx : (agdStep L ρ F adj t s).x = x' := rfl
  have hsz : (agdStep L ρ F adj t s).z = z' := rfl
  simp only [apot, hsx, hsz]
  have ha := (merit_bounds h hL hL₂ hρ hadj t s.y x' hc).2
  have hb := (merit_bounds h hL hL₂ hρ hadj t s.y w hc).1
  have hc' := (merit_bounds h hL hL₂ hρ hadj t s.y s.x hc).1
  rw [← hg] at ha hb hc'
  rw [hw, norm_zero] at hb
  have hx'y : x' - s.y = -((1 / (2 * Λ ^ 2)) • g) := by rw [hx', hLm]; abel
  have hq2 : q ^ 2 = 1 / (4 * Λ ^ 2) := by rw [hqΛ]; field_simp; ring
  have hxyi : ⟪g, x' - s.y⟫ = -(2 * q ^ 2) * ‖g‖ ^ 2 := by
    rw [hx'y, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hq2]
    field_simp; ring
  have hxyn : Λ ^ 2 * ‖x' - s.y‖ ^ 2 = q ^ 2 * ‖g‖ ^ 2 := by
    rw [hx'y, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Λ ^ 2)), mul_pow, hq2]
    field_simp; ring
  rw [hxyi] at ha
  set a := s.z - w with ha_def
  set b := s.y - w with hb_def
  have hrel : q • ((1 - q) • a + q • b) = (1 - q) • (s.y - s.x) + q • (s.y - w) := by
    have h1 : (1 + q) • s.y = s.x + q • s.z := by
      rw [hy, smul_smul]
      have : (1 + q) * (1 / (1 + q)) = 1 := by field_simp
      rw [this, one_smul]
    have h2 : q • s.z = (1 + q) • s.y - s.x := by rw [h1]; abel
    calc q • ((1 - q) • a + q • b)
        = (1 - q) • (q • s.z) - (q * (1 - q)) • w + (q * q) • (s.y - w) := by
          rw [ha_def, hb_def]; module
      _ = (1 - q) • ((1 + q) • s.y - s.x) - (q * (1 - q)) • w + (q * q) • (s.y - w) := by rw [h2]
      _ = (1 - q) • (s.y - s.x) + q • (s.y - w) := by module
  have hzw : z' - w = ((1 - q) • a + q • b) - (2 * q) • g := by
    rw [hz', ha_def, hb_def]; module
  set P := (1 - q) • a + q • b with hP
  have hPg : q * ⟪P, g⟫ = (1 - q) * ⟪s.y - s.x, g⟫ + q * ⟪s.y - w, g⟫ := by
    rw [← real_inner_smul_left, hrel, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h1q : 0 ≤ 1 - q := by linarith
  have hjensen : ‖P‖ ^ 2 ≤ (1 - q) * ‖a‖ ^ 2 + q * ‖b‖ ^ 2 := by
    have e := jensen_sq a b q
    rw [← hP] at e
    have : 0 ≤ q * (1 - q) * ‖a - b‖ ^ 2 := by positivity
    linarith
  have hznorm : ‖z' - w‖ ^ 2 = ‖P‖ ^ 2 - 4 * (q * ⟪P, g⟫) + 4 * q ^ 2 * ‖g‖ ^ 2 := by
    rw [hzw, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * q), real_inner_smul_right]
    ring
  have hip1 : ⟪s.y - s.x, g⟫ = -⟪g, s.x - s.y⟫ := by
    rw [real_inner_comm, ← inner_neg_right, neg_sub]
  have hip2 : ⟪s.y - w, g⟫ = -⟪g, w - s.y⟫ := by
    rw [real_inner_comm, ← inner_neg_right, neg_sub]
  have hbn : ‖w - s.y‖ = ‖b‖ := by rw [hb_def, norm_sub_rev]
  rw [hbn] at hb
  rw [hznorm, hPg, hip1, hip2]
  have k1 := mul_le_mul_of_nonneg_left hc' h1q
  have k2 := mul_le_mul_of_nonneg_left hb hq0.le
  have hxs : 0 ≤ ‖s.x - s.y‖ ^ 2 / 4 := by positivity
  nlinarith [k1, k2, hjensen, ha, hxyn, hxs, mul_nonneg h1q hxs]

lemma agd_y (L ρ : ℝ) (F : E → E) (adj : E → E → E) (t : E) (s : AgdState E) :
    (agdStep L ρ F adj t s).y =
      (1 / (1 + agdq L ρ)) • ((agdStep L ρ F adj t s).x + agdq L ρ • (agdStep L ρ F adj t s).z) :=
  rfl

lemma agd_region (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ)
    {adj : E → E → E} (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (t w v0 : E)
    (hw : res L ρ F t w = 0) (hv0w : ‖v0 - w‖ ≤ ‖res L ρ F t v0‖)
    (hin : 7 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) * ‖res L ρ F t v0‖ ≤ 1) (k : ℕ) :
    apot L ρ F t w ((agdStep L ρ F adj t)^[k] ⟨v0, v0, v0⟩) ≤
      (1 - agdq L ρ) ^ k * (3 / 4 * ‖res L ρ F t v0‖ ^ 2) := by
  set q := agdq L ρ with hq
  set Λ := 2 + 2 * ρ * L with hΛ
  set γ := 2 * ρ + 1 / L with hγ
  set r0 := ‖res L ρ F t v0‖ with hr0
  have hq0 : 0 < q := agdq_pos hL hρ
  have hq1 : q ≤ 1 / 4 := agdq_le hL hρ
  have hγ0 : 0 ≤ γ := by positivity
  have hΛpos : 0 < Λ := by rw [hΛ]; positivity
  have hpot0 : apot L ρ F t w ⟨v0, v0, v0⟩ ≤ 3 / 4 * r0 ^ 2 := by
    simp only [apot]
    have := pow_le_pow_left₀ (norm_nonneg _) hv0w 2
    nlinarith [sq_nonneg ‖v0 - w‖]
  induction k with
  | zero => simpa using hpot0
  | succ k ih =>
    set s := (agdStep L ρ F adj t)^[k] ⟨v0, v0, v0⟩ with hs
    have hyk : s.y = (1 / (1 + q)) • (s.x + q • s.z) := by
      rcases k with _ | k
      · simp only [hs, Function.iterate_zero, id]
        have hq1' : 1 / (1 + q) * (1 + q) = 1 := by field_simp
        rw [show v0 + q • v0 = (1 + q) • v0 by module, smul_smul, hq1', one_smul]
      · rw [hs, Function.iterate_succ_apply']
        exact agd_y L ρ F adj t _
    have hpk : apot L ρ F t w s ≤ 3 / 4 * r0 ^ 2 := by
      refine ih.trans ?_
      have : (1 - q) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have : 0 ≤ 3 / 4 * r0 ^ 2 := by positivity
      nlinarith
    have hxw : ‖s.x - w‖ ^ 2 ≤ 2 * apot L ρ F t w s := by
      have := res_expand h hL hρ t w s.x
      rw [hw, sub_zero] at this
      have := pow_le_pow_left₀ (norm_nonneg _) this 2
      simp only [apot]
      nlinarith [sq_nonneg ‖s.z - w‖]
    have hzw : ‖s.z - w‖ ^ 2 ≤ 4 * apot L ρ F t w s := by
      simp only [apot]; nlinarith [sq_nonneg ‖res L ρ F t s.x‖]
    have hyw : ‖s.y - w‖ ^ 2 ≤ 4 * apot L ρ F t w s := by
      have e : s.y - w = (1 / (1 + q)) • ((s.x - w) + q • (s.z - w)) := by
        rw [hyk]
        have : (1 / (1 + q)) • ((s.x - w) + q • (s.z - w)) =
            (1 / (1 + q)) • (s.x + q • s.z) - ((1 / (1 + q)) * (1 + q)) • w := by module
        rw [this]
        have hh : (1 / (1 + q)) * (1 + q) = 1 := by field_simp
        rw [hh, one_smul]
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (1 + q))]
      have htri : ‖(s.x - w) + q • (s.z - w)‖ ≤ ‖s.x - w‖ + q * ‖s.z - w‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq0]
      have hpnn : 0 ≤ apot L ρ F t w s := by simp only [apot]; positivity
      set M := 2 * Real.sqrt (apot L ρ F t w s) with hM
      have hM0 : 0 ≤ M := by positivity
      have hMsq : M ^ 2 = 4 * apot L ρ F t w s := by
        rw [hM, mul_pow, Real.sq_sqrt hpnn]; ring
      have hx1 : ‖s.x - w‖ ≤ M := by
        apply (pow_le_pow_iff_left₀ (norm_nonneg _) hM0 two_ne_zero).mp
        rw [hMsq]; nlinarith
      have hz1 : ‖s.z - w‖ ≤ M := by
        apply (pow_le_pow_iff_left₀ (norm_nonneg _) hM0 two_ne_zero).mp
        rw [hMsq]; exact hzw
      have hcomb : 1 / (1 + q) * (‖s.x - w‖ + q * ‖s.z - w‖) ≤ M := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hz1 hq0.le]
      have := mul_le_mul_of_nonneg_left htri (by positivity : (0 : ℝ) ≤ 1 / (1 + q))
      have hfin := this.trans hcomb
      have := pow_le_pow_left₀ (by positivity) hfin 2
      rw [hMsq] at this
      exact this
    have hcond : 4 * γ * L₂ * ‖res L ρ F t s.y‖ ≤ 1 := by
      have hr := res_lip h hL hρ t w s.y
      rw [hw, sub_zero, ← hΛ] at hr
      have hr2 : ‖res L ρ F t s.y‖ ^ 2 ≤ Λ ^ 2 * (4 * (3 / 4 * r0 ^ 2)) := by
        have := pow_le_pow_left₀ (norm_nonneg _) hr 2
        rw [mul_pow] at this
        nlinarith [mul_le_mul_of_nonneg_left (hyw.trans (show 4 * apot L ρ F t w s ≤ 4 * (3 / 4 * r0 ^ 2) by linarith)) (sq_nonneg Λ)]
      have hin2 : (7 * γ * L₂ * Λ * r0) ^ 2 ≤ 1 := by
        have h0 : 0 ≤ 7 * γ * L₂ * Λ * r0 := by positivity
        nlinarith
      have hsq : (4 * γ * L₂ * ‖res L ρ F t s.y‖) ^ 2 ≤ 1 := by
        have : (4 * γ * L₂ * ‖res L ρ F t s.y‖) ^ 2 =
            16 * (γ * L₂) ^ 2 * ‖res L ρ F t s.y‖ ^ 2 := by ring
        rw [this]
        have hγL : 0 ≤ (γ * L₂) ^ 2 := sq_nonneg _
        have h1 : 16 * (γ * L₂) ^ 2 * ‖res L ρ F t s.y‖ ^ 2 ≤
            16 * (γ * L₂) ^ 2 * (Λ ^ 2 * (4 * (3 / 4 * r0 ^ 2))) :=
          mul_le_mul_of_nonneg_left hr2 (by positivity)
        have e2 : 16 * (γ * L₂) ^ 2 * (Λ ^ 2 * (4 * (3 / 4 * r0 ^ 2))) =
            48 * (γ * L₂ * Λ * r0) ^ 2 := by ring
        have e3 : (7 * γ * L₂ * Λ * r0) ^ 2 = 49 * (γ * L₂ * Λ * r0) ^ 2 := by ring
        have := sq_nonneg (γ * L₂ * Λ * r0)
        linarith
      have h0 : 0 ≤ 4 * γ * L₂ * ‖res L ρ F t s.y‖ := by positivity
      by_contra hcon
      push Not at hcon
      have : 1 < (4 * γ * L₂ * ‖res L ρ F t s.y‖) ^ 2 := by nlinarith
      linarith
    rw [Function.iterate_succ_apply']
    calc apot L ρ F t w (agdStep L ρ F adj t s) ≤ (1 - q) * apot L ρ F t w s :=
          agd_step h hL hL₂ hρ hadj t w hw s hyk hcond
      _ ≤ (1 - q) * ((1 - q) ^ k * (3 / 4 * r0 ^ 2)) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 - q) ^ (k + 1) * (3 / 4 * r0 ^ 2) := by ring

variable [FiniteDimensional ℝ E]

lemma agd_guarantee (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ)
    {adj : E → E → E} (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (t v0 : E)
    (hin : 7 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) * ‖res L ρ F t v0‖ ≤ 1) :
    ‖res L ρ F t (agdRun L ρ F adj t v0 (agdLen L ρ))‖ ≤ ‖res L ρ F t v0‖ / (11 + 10 * ρ * L) := by
  obtain ⟨w, hw, hv0w⟩ := exists_root h hL hL₂ hρ hadj t v0
  have hreg := agd_region h hL hL₂ hρ hadj t w v0 hw hv0w hin (agdLen L ρ)
  set q := agdq L ρ with hq
  set N := agdLen L ρ with hN
  set r0 := ‖res L ρ F t v0‖ with hr0
  have hq0 : 0 < q := agdq_pos hL hρ
  have hq1 : q ≤ 1 / 4 := agdq_le hL hρ
  have hpos : 0 < 11 + 10 * ρ * L := by positivity
  have hpos2 : 0 < 22 + 20 * ρ * L := by positivity
  have hxN : ‖res L ρ F t (agdRun L ρ F adj t v0 N)‖ ^ 2 / 2 ≤
      (1 - q) ^ N * (3 / 4 * r0 ^ 2) := by
    refine le_trans ?_ hreg
    simp only [apot, agdRun]
    linarith [sq_nonneg ‖((agdStep L ρ F adj t)^[N] ⟨v0, v0, v0⟩).z - w‖]
  have hqN : 2 * Real.log (22 + 20 * ρ * L) ≤ q * N := by
    have h1 := Nat.le_ceil (4 * (2 + 2 * ρ * L) * Real.log (22 + 20 * ρ * L))
    have hqe : q * (4 * (2 + 2 * ρ * L) * Real.log (22 + 20 * ρ * L)) =
        2 * Real.log (22 + 20 * ρ * L) := by
      rw [hq, agdq]; field_simp; ring
    calc 2 * Real.log (22 + 20 * ρ * L)
        = q * (4 * (2 + 2 * ρ * L) * Real.log (22 + 20 * ρ * L)) := hqe.symm
      _ ≤ q * N := mul_le_mul_of_nonneg_left h1 hq0.le
  have hexp : (1 - q) ^ N ≤ 1 / (22 + 20 * ρ * L) ^ 2 := by
    have h1 : (1 - q) ^ N ≤ Real.exp (-q) ^ N :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-q)]) N
    rw [← Real.exp_nat_mul] at h1
    refine h1.trans ?_
    have e : 1 / (22 + 20 * ρ * L) ^ 2 = Real.exp (-(2 * Real.log (22 + 20 * ρ * L))) := by
      rw [Real.exp_neg, show 2 * Real.log (22 + 20 * ρ * L) = Real.log ((22 + 20 * ρ * L) ^ 2) by
        rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
      ring
    rw [e]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsq : ‖res L ρ F t (agdRun L ρ F adj t v0 N)‖ ^ 2 ≤ (r0 / (11 + 10 * ρ * L)) ^ 2 := by
    have h1 : ‖res L ρ F t (agdRun L ρ F adj t v0 N)‖ ^ 2 ≤
        2 * ((1 - q) ^ N * (3 / 4 * r0 ^ 2)) := by linarith
    have h2 : (1 - q) ^ N * (3 / 4 * r0 ^ 2) ≤ 1 / (22 + 20 * ρ * L) ^ 2 * (3 / 4 * r0 ^ 2) :=
      mul_le_mul_of_nonneg_right hexp (by positivity)
    have e : (22 + 20 * ρ * L) ^ 2 = 4 * (11 + 10 * ρ * L) ^ 2 := by ring
    rw [e] at h2
    have h3 : 2 * (1 / (4 * (11 + 10 * ρ * L) ^ 2) * (3 / 4 * r0 ^ 2)) ≤
        (r0 / (11 + 10 * ρ * L)) ^ 2 := by
      rw [div_pow]
      have : 0 < (11 + 10 * ρ * L) ^ 2 := by positivity
      field_simp
      nlinarith [sq_nonneg r0]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

lemma solve_guarantee (h : Hyp F J L L₂ ρ) (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ)
    {adj : E → E → E} (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) (t v0 : E) :
    ‖res L ρ F t (innerSolve L L₂ ρ F adj t v0)‖ ≤ ‖res L ρ F t v0‖ / (11 + 10 * ρ * L) := by
  unfold innerSolve
  split_ifs with hu
  · exact agd_guarantee h hL hL₂ hρ hadj t v0 (by simpa [useAgd] using hu)
  · exact inner_guarantee h hL hL₂ hρ hadj t v0

end AGD

end OracleTemplate.CohypomonotoneAdjoint
