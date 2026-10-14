import LongTails.Proofs.ConstrainedAnchoredRun

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ConstrainedMonotone

open GeneralizedMonotone (Hyp)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section rate

variable {F P : E → E} {X : Set E} {L0 L1 : ℝ} {a xs : E} {R G : ℝ}

lemma grad_bound (c : Ctx F P X L0 L1 a xs R G) {s : E × E × ℝ} (hI : Inv F X a xs R s)
    (hS : 0 < s.2.2) :
    ‖F s.1‖ ≤ G + 8 * (L0 + L1 * G) * R + 6 * R * (1 + 2 * L1 * R) / s.2.2 := by
  have hL0 := c.hyp.L0_pos
  have hL1 := c.hyp.L1_nonneg
  have hR := c.R_pos
  have hG : 0 ≤ G := (norm_nonneg _).trans c.grad
  set ε := R / (1 + 2 * L1 * R) with hεdef
  have hden : 0 < 1 + 2 * L1 * R := by positivity
  have hε : 0 < ε := by positivity
  have hεR : ε ≤ R := by
    rw [hεdef, div_le_iff₀ hden]
    nlinarith [mul_nonneg hL1 hR.le]
  have hcap : L1 * ε ≤ 1 / 2 := by
    rw [hεdef, ← mul_div_assoc, div_le_iff₀ hden]
    nlinarith [mul_nonneg hL1 hR.le]
  have hop := one_point c.hyp s.1 xs hε hcap
  have hres := residual_bound c hI
  have hdist := hI.dist
  have hpair : ⟪F s.1 - F xs, s.1 - xs⟫ ≤ ⟪F s.1 + s.2.1, s.1 - xs⟫ := by
    have h2 := c.vi s.1 hI.mem
    have h3 := hI.normal xs c.sol
    have e1 : ⟪F s.1 + s.2.1, s.1 - xs⟫ = ⟪F s.1, s.1 - xs⟫ + ⟪s.2.1, s.1 - xs⟫ :=
      inner_add_left _ _ _
    have e2 : ⟪F s.1 - F xs, s.1 - xs⟫ = ⟪F s.1, s.1 - xs⟫ - ⟪F xs, s.1 - xs⟫ :=
      inner_sub_left _ _ _
    have e3 : ⟪s.2.1, xs - s.1⟫ = -⟪s.2.1, s.1 - xs⟫ := by rw [← inner_neg_right, neg_sub]
    linarith
  have hcs := real_inner_le_norm (F s.1 + s.2.1) (s.1 - xs)
  have hp0 := norm_nonneg (F s.1 + s.2.1)
  have hx0 := norm_nonneg (s.1 - xs)
  have hm : ⟪F s.1 - F xs, s.1 - xs⟫ ≤ 6 * R ^ 2 / s.2.2 := by
    rw [le_div_iff₀ hS]
    have : s.2.2 * (‖F s.1 + s.2.1‖ * ‖s.1 - xs‖) ≤ 2 * R * (3 * R) := by
      have := mul_le_mul hres hdist hx0 (by linarith)
      nlinarith
    nlinarith
  have hLy : L0 + L1 * ‖F xs‖ ≤ L0 + L1 * G := by nlinarith [c.grad]
  have hLy0 : 0 ≤ L0 + L1 * ‖F xs‖ := by positivity
  have hsum : ‖s.1 - xs‖ + ε ≤ 4 * R := by linarith
  have hk : 2 * (L0 + L1 * ‖F xs‖) * ε * (‖s.1 - xs‖ + ε) ≤ 2 * (L0 + L1 * G) * ε * (4 * R) := by
    have := mul_le_mul hLy hsum (by positivity) (by positivity)
    nlinarith
  have hd : ‖F s.1 - F xs‖ * ε ≤ 6 * R ^ 2 / s.2.2 + 8 * (L0 + L1 * G) * R * ε := by linarith
  have hd2 : ‖F s.1 - F xs‖ ≤ 6 * R * (1 + 2 * L1 * R) / s.2.2 + 8 * (L0 + L1 * G) * R := by
    have e : 6 * R ^ 2 / s.2.2 = 6 * R * (1 + 2 * L1 * R) / s.2.2 * ε := by
      rw [hεdef]
      field_simp
    rw [e] at hd
    have := (le_div_iff₀ hε).mpr hd
    rw [show (6 * R * (1 + 2 * L1 * R) / s.2.2 * ε + 8 * (L0 + L1 * G) * R * ε) / ε =
      6 * R * (1 + 2 * L1 * R) / s.2.2 + 8 * (L0 + L1 * G) * R by field_simp] at this
    exact this
  have := norm_le_insert' (F s.1) (F xs)
  linarith [c.grad]

lemma step_bound (c : Ctx F P X L0 L1 a xs R G) {s : E × E × ℝ} (hI : Inv F X a xs R s)
    (hS : 0 < s.2.2) :
    L0 + L1 * mval a s.1 (F s.1) s.2.1 s.2.2 ≤
      (L0 + L1 * G) * (1 + 8 * L1 * R) + 12 * L1 * R * (1 + L1 * R) / s.2.2 := by
  have hL1 := c.hyp.L1_nonneg
  have hR := c.R_pos
  have hgb := grad_bound c hI hS
  have hres := residual_bound c hI
  have hp : ‖F s.1 + s.2.1‖ ≤ 2 * R / s.2.2 := by
    rw [le_div_iff₀ hS]
    linarith
  have hxa : ‖s.1 - a‖ ≤ 4 * R := by
    have e : s.1 - a = (s.1 - xs) - (a - xs) := by abel
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith [hI.dist, c.dist0])
  have hxaS : ‖s.1 - a‖ / s.2.2 ≤ 4 * R / s.2.2 := div_le_div_of_nonneg_right hxa hS.le
  have hm : mval a s.1 (F s.1) s.2.1 s.2.2 ≤
      G + 8 * (L0 + L1 * G) * R + (12 * R + 12 * L1 * R ^ 2) / s.2.2 := by
    unfold mval
    have e : (12 * R + 12 * L1 * R ^ 2) / s.2.2 =
        6 * R * (1 + 2 * L1 * R) / s.2.2 + 2 * R / s.2.2 + 4 * R / s.2.2 := by
      field_simp
      ring
    rw [e]
    linarith
  have := mul_le_mul_of_nonneg_left hm hL1
  have e2 : L1 * (G + 8 * (L0 + L1 * G) * R + (12 * R + 12 * L1 * R ^ 2) / s.2.2) =
      L1 * G + 8 * L1 * (L0 + L1 * G) * R + 12 * L1 * R * (1 + L1 * R) / s.2.2 := by
    field_simp
  nlinarith

noncomputable def growth (A C S : ℝ) : ℝ := 8 * A * S + (11 * C + 4) * Real.log S

lemma growth_step (c : Ctx F P X L0 L1 a xs R G) {s : E × E × ℝ} (hI : Inv F X a xs R s)
    (hS : 0 < s.2.2) :
    growth ((L0 + L1 * G) * (1 + 8 * L1 * R)) (12 * L1 * R * (1 + L1 * R)) s.2.2 + 1 ≤
      growth ((L0 + L1 * G) * (1 + 8 * L1 * R)) (12 * L1 * R * (1 + L1 * R))
        (s.2.2 + stepSize L0 L1 a s.1 (F s.1) s.2.1 s.2.2) := by
  have hL0 := c.hyp.L0_pos
  have hL1 := c.hyp.L1_nonneg
  have hR := c.R_pos
  have hG : 0 ≤ G := (norm_nonneg _).trans c.grad
  set S := s.2.2 with hSdef
  set A := (L0 + L1 * G) * (1 + 8 * L1 * R) with hA
  set C := 12 * L1 * R * (1 + L1 * R) with hC
  have hA0 : 0 ≤ A := by positivity
  have hC0 : 0 ≤ C := by positivity
  have hsb := step_bound c hI hS
  rw [← hA, ← hC] at hsb
  set m := mval a s.1 (F s.1) s.2.1 S with hm
  have hm0 : 0 ≤ m := by rw [hm]; unfold mval; positivity
  have hγ : stepSize L0 L1 a s.1 (F s.1) s.2.1 S = min (S / 3) (1 / (4 * (L0 + L1 * m))) := by
    rw [stepSize, ite_eq_right hS.ne']
  set γ := stepSize L0 L1 a s.1 (F s.1) s.2.1 S with hγdef
  have hγpos : 0 < γ := by
    rw [hγ]
    exact lt_min (by positivity) (by positivity)
  have hγle : γ ≤ S / 3 := by rw [hγ]; exact min_le_left _ _
  have hlog : γ / (S + γ) ≤ Real.log (S + γ) - Real.log S := by
    rw [← Real.log_div (by linarith : S + γ ≠ 0) hS.ne']
    have h1 := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < (S + γ) / S)
    have h2 : 1 - ((S + γ) / S)⁻¹ = γ / (S + γ) := by
      rw [inv_div]
      field_simp
      ring
    linarith
  have hfrac : 3 / 4 * (γ / S) ≤ γ / (S + γ) := by
    rw [show 3 / 4 * (γ / S) = 3 / 4 * γ / S by ring, div_le_div_iff₀ hS (by linarith)]
    nlinarith [mul_nonneg hγpos.le (by linarith : (0 : ℝ) ≤ S / 4 - 3 / 4 * γ)]
  have hcoef : 0 ≤ 11 * C + 4 := by positivity
  have hkey : 1 ≤ 8 * A * γ + (11 * C + 4) * (3 / 4 * (γ / S)) := by
    rcases min_choice (S / 3) (1 / (4 * (L0 + L1 * m))) with hmin | hmin
    · have hγS : γ / S = 1 / 3 := by
        rw [hγ, hmin]
        field_simp
      rw [hγS]
      have : 0 ≤ 8 * A * γ := by positivity
      nlinarith
    · have hγv : γ * (4 * (L0 + L1 * m)) = 1 := by
        rw [hγ, hmin]
        field_simp
      have hCS : C / S * γ = C * (γ / S) := by ring
      have h1 : 1 ≤ 4 * γ * (A + C / S) := by
        have := mul_le_mul_of_nonneg_left hsb (by positivity : (0 : ℝ) ≤ 4 * γ)
        nlinarith
      have h2 : 0 ≤ C * (γ / S) := by positivity
      have h3 : 4 * γ * (A + C / S) = 4 * A * γ + 4 * (C * (γ / S)) := by rw [← hCS]; ring
      have h4 : 0 ≤ A * γ := by positivity
      have h5 : 0 ≤ γ / S := by positivity
      nlinarith
  have hmul := mul_le_mul_of_nonneg_left (hfrac.trans hlog) hcoef
  unfold growth
  nlinarith

lemma run_pos (c : Ctx F P X L0 L1 a xs R G) (k : ℕ) : 0 < (run F P L0 L1 a (k + 1)).2.2 := by
  have hI := run_inv c k
  have hγ := (stepSize_spec c.hyp.L0_pos c.hyp.L1_nonneg a (run F P L0 L1 a k).1
    (F (run F P L0 L1 a k).1) (run F P L0 L1 a k).2.1 hI.S_nonneg hI.start).1
  have := hI.S_nonneg
  show 0 < (run F P L0 L1 a k).2.2 + _
  linarith

lemma growth_run (c : Ctx F P X L0 L1 a xs R G) (n : ℕ) :
    growth ((L0 + L1 * G) * (1 + 8 * L1 * R)) (12 * L1 * R * (1 + L1 * R))
        (run F P L0 L1 a 1).2.2 + n ≤
      growth ((L0 + L1 * G) * (1 + 8 * L1 * R)) (12 * L1 * R * (1 + L1 * R))
        (run F P L0 L1 a (n + 1)).2.2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := growth_step c (run_inv c (n + 1)) (run_pos c n)
    have e : (run F P L0 L1 a (n + 1 + 1)).2.2 = (run F P L0 L1 a (n + 1)).2.2 +
        stepSize L0 L1 a (run F P L0 L1 a (n + 1)).1 (F (run F P L0 L1 a (n + 1)).1)
          (run F P L0 L1 a (n + 1)).2.1 (run F P L0 L1 a (n + 1)).2.2 := rfl
    rw [← e] at hstep
    push_cast
    linarith

lemma run_first (F P : E → E) (L0 L1 : ℝ) (a : E) :
    (run F P L0 L1 a 1).2.2 = 1 / (4 * (L0 + L1 * (2 * ‖F a‖))) := by
  show 0 + stepSize L0 L1 a a (F a) 0 0 = _
  rw [zero_add, stepSize, ite_eq_left rfl]
  have : mval a a (F a) (0 : E) 0 = 2 * ‖F a‖ := by
    unfold mval
    simp only [add_zero, sub_self, norm_zero, div_zero]
    ring
  rw [this]

theorem run_accuracy (c : Ctx F P X L0 L1 a xs R G) {G0 ε : ℝ} (hG0 : ‖F a‖ ≤ G0) (hε : 0 < ε)
    (n : ℕ)
    (hn : 16 * ((L0 + L1 * G) * (1 + 8 * L1 * R)) * R / ε +
      (132 * L1 * R * (1 + L1 * R) + 4) * Real.log (2 + 8 * R * (L0 + 2 * L1 * G0) / ε) ≤ n) :
    (run F P L0 L1 a (n + 1)).1 ∈ X ∧ Normal X (run F P L0 L1 a (n + 1)).1
      (run F P L0 L1 a (n + 1)).2.1 ∧
    ‖F (run F P L0 L1 a (n + 1)).1 + (run F P L0 L1 a (n + 1)).2.1‖ ≤ ε := by
  have hL0 := c.hyp.L0_pos
  have hL1 := c.hyp.L1_nonneg
  have hR := c.R_pos
  have hG : 0 ≤ G := (norm_nonneg _).trans c.grad
  have hρ := norm_nonneg (F a)
  have hSpos := run_pos c n
  have hI := run_inv c (n + 1)
  refine ⟨hI.mem, hI.normal, ?_⟩
  have hres := residual_bound c hI
  set S := (run F P L0 L1 a (n + 1)).2.2 with hSdef
  set A := (L0 + L1 * G) * (1 + 8 * L1 * R) with hA
  set C := 12 * L1 * R * (1 + L1 * R) with hC
  have hA0 : 0 ≤ A := by positivity
  by_cases hbig : 2 * R / ε ≤ S
  · rw [div_le_iff₀ hε] at hbig
    by_contra hcon
    push Not at hcon
    nlinarith [mul_lt_mul_of_pos_left hcon hSpos]
  · push Not at hbig
    exfalso
    have hgr := growth_run c n
    rw [run_first] at hgr
    set S1 := 1 / (4 * (L0 + L1 * (2 * ‖F a‖))) with hS1
    have hS1pos : 0 < S1 := by rw [hS1]; positivity
    have hlogS : Real.log S < Real.log (2 * R / ε) := Real.log_lt_log hSpos hbig
    have hcoef : 0 < 11 * C + 4 := by positivity
    have harg : 2 * R / ε / S1 ≤ 2 + 8 * R * (L0 + 2 * L1 * G0) / ε := by
      have : 2 * R / ε / S1 = 8 * R * (L0 + 2 * L1 * ‖F a‖) / ε := by
        rw [hS1]
        field_simp
        ring
      rw [this]
      have h1 : 8 * R * (L0 + 2 * L1 * ‖F a‖) / ε ≤ 8 * R * (L0 + 2 * L1 * G0) / ε := by
        apply div_le_div_of_nonneg_right _ hε.le
        have := mul_le_mul_of_nonneg_left hG0 hL1
        nlinarith
      linarith
    have hlog2 : Real.log (2 * R / ε) - Real.log S1 ≤
        Real.log (2 + 8 * R * (L0 + 2 * L1 * G0) / ε) := by
      rw [← Real.log_div (by positivity) hS1pos.ne']
      exact Real.log_le_log (by positivity) harg
    have hSlt : 8 * A * S ≤ 8 * A * (2 * R / ε) :=
      mul_le_mul_of_nonneg_left hbig.le (by positivity)
    have h8 : 8 * A * (2 * R / ε) = 16 * A * R / ε := by ring
    have hS1n : 0 ≤ 8 * A * S1 := by positivity
    have e11 : 11 * C + 4 = 132 * L1 * R * (1 + L1 * R) + 4 := by rw [hC]; ring
    unfold growth at hgr
    have hm1 := mul_lt_mul_of_pos_left hlogS hcoef
    have hm2 := mul_le_mul_of_nonneg_left hlog2 hcoef.le
    rw [e11] at hm1 hm2
    rw [e11] at hgr
    nlinarith

end rate

end OracleTemplate.ConstrainedMonotone
