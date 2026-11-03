import LongTails.Proofs.TwoSidedPerceptronTrajectory

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSidedPerceptronContraction

open TwoSidedPerceptronDynamics TwoSidedPerceptronPotential TwoSidedPerceptronTrajectory

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def _root_.LongTails.Proofs.TwoSidedPerceptronTrajectory.Control.threshold
    (c : Control) (K₁ : ℕ) : ℝ :=
  Real.sqrt (128 * c.δ * c.F * c.Z K₁) / c.clo

lemma _root_.LongTails.Proofs.TwoSidedPerceptronTrajectory.Control.threshold_nonneg
    (c : Control) (K₁ : ℕ) : 0 ≤ c.threshold K₁ := by
  unfold Control.threshold; exact div_nonneg (Real.sqrt_nonneg _) c.clo_pos.le

lemma _root_.LongTails.Proofs.TwoSidedPerceptronTrajectory.Control.threshold_sq
    (c : Control) (K₁ : ℕ) : (c.threshold K₁) ^ 2 = 128 * c.δ * c.F * c.Z K₁ / c.clo ^ 2 := by
  unfold Control.threshold
  rw [div_pow, Real.sq_sqrt]
  have := c.Z_nonneg K₁
  have := c.δ_pos
  have := c.F_pos
  positivity

lemma _root_.LongTails.Proofs.TwoSidedPerceptronTrajectory.Control.clo_le_one (c : Control) :
    c.clo ≤ 1 := by linarith [c.clo_le, c.C_le]

variable {c : Control} {b : ι → ℝ} {p r : ι → E} {w : E}

section SingleStep

variable {β : ℝ} {P R : E} {y : State E} {Z F : ℝ}

lemma forcing_step_le (hP : ‖P‖ ≤ 1) (hz : ‖y.z‖ ≤ Z) : |c.δ * ⟪P, y.z⟫| ≤ c.δ * Z :=
  (forcing_le c.δ_pos.le hP).trans (mul_le_mul_of_nonneg_left hz c.δ_pos.le)

lemma mass_next_le (hβhi : |β| ≤ c.C) (hP : ‖P‖ ≤ 1) (hz : ‖y.z‖ ≤ Z) :
    mass (step β c.δ P R y) ≤ mass y + β * gap y + 2 * (c.δ * Z) := by
  have h := mass_step_le (c := β) (δ := c.δ) (p := P) (r := R) (x := y)
    (hβhi.trans (by linarith [c.C_le]))
  have hf := forcing_step_le (c := c) hP hz
  linarith

lemma mass_next_ge (hβhi : |β| ≤ c.C) (hP : ‖P‖ ≤ 1) (hz : ‖y.z‖ ≤ Z) :
    mass y + β * gap y - 2 * (c.δ * Z) ≤ mass (step β c.δ P R y) := by
  have h := mass_step_ge (c := β) (δ := c.δ) (p := P) (r := R) (x := y)
    (hβhi.trans (by linarith [c.C_le]))
  have hf := forcing_step_le (c := c) hP hz
  linarith

lemma mass_next_le_crude (hβhi : |β| ≤ c.C) (hP : ‖P‖ ≤ 1) (hz : ‖y.z‖ ≤ Z) :
    mass (step β c.δ P R y) ≤ 9 / 8 * mass y + 2 * (c.δ * Z) := by
  have h := mass_next_le (R := R) hβhi hP hz
  have hg := abs_gap_le_mass y
  have hm := mass_nonneg y
  have : β * gap y ≤ 1 / 8 * mass y := by
    calc
      β * gap y ≤ |β * gap y| := le_abs_self _
      _ = |β| * |gap y| := abs_mul _ _
      _ ≤ c.C * mass y := mul_le_mul hβhi hg (abs_nonneg _) c.C_nonneg
      _ ≤ 1 / 8 * mass y := mul_le_mul_of_nonneg_right c.C_le hm
  linarith

lemma mass_next_ge_crude (hβhi : |β| ≤ c.C) (hP : ‖P‖ ≤ 1) (hz : ‖y.z‖ ≤ Z) :
    7 / 8 * mass y - 2 * (c.δ * Z) ≤ mass (step β c.δ P R y) := by
  have h := mass_next_ge (R := R) hβhi hP hz
  have hg := abs_gap_le_mass y
  have hm := mass_nonneg y
  have : -(1 / 8 * mass y) ≤ β * gap y := by
    have h1 : |β * gap y| ≤ 1 / 8 * mass y := by
      calc
        |β * gap y| = |β| * |gap y| := abs_mul _ _
        _ ≤ c.C * mass y := mul_le_mul hβhi hg (abs_nonneg _) c.C_nonneg
        _ ≤ 1 / 8 * mass y := mul_le_mul_of_nonneg_right c.C_le hm
    linarith [neg_abs_le (β * gap y)]
  linarith

lemma gate_gap (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hz : ‖y.z‖ ≤ Z) (hF : |y.a| + |y.t| ≤ F)
    (hF0 : 0 ≤ F) (hm : margin β c.δ P R y ≤ 0) (hpos : 0 < β * gap y) :
    |β| * |gap y| * mass y ≤ 4 * (c.δ * F * Z) := by
  have hprod := gap_mul_mass y
  have hcaq : 0 < β * y.a * y.q := by
    have hm0 := mass_nonneg y
    have hmpos : 0 < mass y := by
      rcases hm0.lt_or_eq with h | h
      · exact h
      · exfalso
        have : gap y = 0 := by
          have := abs_gap_le_mass y; rw [← h] at this
          exact abs_nonpos_iff.mp this
        rw [this] at hpos; simp at hpos
    have : β * y.a * y.q = β * gap y * mass y / 4 := by
      rw [mul_assoc β (gap y), hprod]; ring
    rw [this]; positivity
  have hgate := expanding_gate (c := β) (δ := c.δ) (p := P) (r := R) (x := y) c.δ_pos.le hP hR hm hcaq
  have h1 : β * y.a * y.q = β * gap y * mass y / 4 := by
    rw [mul_assoc β (gap y), hprod]; ring
  have h2 : |β| * |gap y| = β * gap y := by
    rw [← abs_mul, abs_of_pos hpos]
  have h3 : (|y.a| + |y.t|) * ‖y.z‖ ≤ F * Z := mul_le_mul hF hz (norm_nonneg _) hF0
  rw [h2]
  have := mul_le_mul_of_nonneg_left h3 c.δ_pos.le
  rw [h1] at hgate
  nlinarith

end SingleStep

section TwoStep

variable {x : ℕ → State E} {i : ℕ → ι} {K K₁ : ℕ}

lemma threshold_facts (hR : Regime c K) (hK1 : K₁ ≤ K) (hK1pos : 0 < K₁) :
    0 < c.threshold K₁ ∧ 16 * (c.δ * c.Z K₁) ≤ c.clo * c.threshold K₁ := by
  have hZ1 : 0 < c.Z K₁ := by
    unfold Control.Z
    have : (0:ℝ) < K₁ := by exact_mod_cast hK1pos
    have := c.δ_pos
    have := c.F_pos
    positivity
  have hsq := c.threshold_sq K₁
  have hclo := c.clo_pos
  have hF := c.F_pos
  have hδ := c.δ_pos
  have hzs : 2 * c.δ * c.Z K₁ ≤ c.F := by
    have h1 := hR.z_small
    have h2 := c.Z_mono hK1
    have h3 : 2 * c.δ * c.Z K₁ ≤ 2 * c.δ * c.Z K := mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  have hpos : 0 < c.threshold K₁ := by
    unfold Control.threshold
    apply div_pos _ hclo
    apply Real.sqrt_pos.mpr
    exact mul_pos (mul_pos (mul_pos (by norm_num) hδ) hF) hZ1
  refine ⟨hpos, ?_⟩
  have h1 : (16 * (c.δ * c.Z K₁)) ^ 2 ≤ (c.clo * c.threshold K₁) ^ 2 := by
    have e : (c.clo * c.threshold K₁) ^ 2 = c.clo ^ 2 * c.threshold K₁ ^ 2 := mul_pow _ _ _
    have hc2 : c.clo ^ 2 ≠ 0 := (pow_pos hclo 2).ne'
    have e2 : c.clo ^ 2 * (128 * c.δ * c.F * c.Z K₁ / c.clo ^ 2) = 128 * c.δ * c.F * c.Z K₁ := by
      field_simp
    rw [e, hsq, e2]
    have hδZ : 0 ≤ 128 * (c.δ * c.Z K₁) := by positivity
    have h3 := mul_le_mul_of_nonneg_left hzs hδZ
    nlinarith [h3]
  have h0 : 0 ≤ 16 * (c.δ * c.Z K₁) := by positivity
  exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).mp h1

set_option maxHeartbeats 2000000 in
lemma two_step (hR : Regime c K) (G : Geometry c b p r w) (tr : Trajectory c b p r x i K)
    {k : ℕ} (hk : k + 2 ≤ K) (hk1 : k + 1 ≤ K₁) (hK1 : K₁ ≤ K)
    (hW : c.threshold K₁ ≤ mass (x k)) :
    mass (x (k + 2)) ≤ (1 - c.clo ^ 2 / 8) * mass (x k) + 5 * (c.δ * c.Z K₁) := by
  set Z₁ := c.Z K₁ with hZ₁
  set W₁ := c.threshold K₁ with hW₁
  set F := c.F with hFdef
  set clo := c.clo with hclodef
  have hclo := c.clo_pos
  have hclo1 := c.clo_le_one
  have hδ := c.δ_pos
  have hFpos := c.F_pos
  have hZ1 := c.Z_nonneg K₁
  obtain ⟨hW1pos, hreg⟩ := threshold_facts hR hK1 (by omega)
  have hW1sq := c.threshold_sq K₁
  have hC := c.C_le
  have hIk := trajectory_invariant hR G tr k (by omega)
  have hIk1 := trajectory_invariant hR G tr (k + 1) (by omega)
  have hzk : ‖(x k).z‖ ≤ Z₁ := hIk.z_le.trans (c.Z_mono (by omega))
  have hzk1 : ‖(x (k + 1)).z‖ ≤ Z₁ := hIk1.z_le.trans (c.Z_mono hk1)
  have hFk := hIk.F_le hR (by omega)
  have hFk1 := hIk1.F_le hR (by omega)
  have hu0 := tr.update k (by omega)
  have hu1 := tr.update (k + 1) (by omega)
  have hm0 := tr.mistake k (by omega)
  have hm1 := tr.mistake (k + 1) (by omega)
  set β₀ := b (i k) with hβ₀
  set β₁ := b (i (k + 1)) with hβ₁
  set M := mass (x k) with hM
  set D := gap (x k) with hD
  set M' := mass (x (k + 1)) with hM'
  set D' := gap (x (k + 1)) with hD'
  have hβ₀lo := G.lower (i k)
  have hβ₀hi := G.upper (i k)
  have hβ₁lo := G.lower (i (k + 1))
  have hβ₁hi := G.upper (i (k + 1))
  have hP0 := G.p_norm (i k)
  have hR0 := G.r_norm (i k)
  have hP1 := G.p_norm (i (k + 1))
  have hR1 := G.r_norm (i (k + 1))
  have hMnn := mass_nonneg (x k)
  have hMpos : 0 < M := lt_of_lt_of_le hW1pos hW
  have hgD := abs_gap_le_mass (x k)
  have hup0 : M' ≤ M + β₀ * D + 2 * (c.δ * Z₁) := by
    rw [hM', hu0]; exact mass_next_le hβ₀hi hP0 hzk
  have hlo0 : M + β₀ * D - 2 * (c.δ * Z₁) ≤ M' := by
    rw [hM', hu0]; exact mass_next_ge hβ₀hi hP0 hzk
  have hgate0 : 0 < β₀ * D → |β₀| * |D| * M ≤ 4 * (c.δ * F * Z₁) := fun h =>
    gate_gap hP0 hR0 hzk hFk hFpos.le hm0 h
  have hup1 : mass (x (k + 2)) ≤ M' + β₁ * D' + 2 * (c.δ * Z₁) := by
    rw [hu1]; exact mass_next_le hβ₁hi hP1 hzk1
  have hgate1 : 0 < β₁ * D' → |β₁| * |D'| * M' ≤ 4 * (c.δ * F * Z₁) := fun h =>
    gate_gap hP1 hR1 hzk1 hFk1 hFpos.le hm1 h
  have hgap_pos : 0 ≤ β₀ → D + β₀ * M - 2 * (c.δ * Z₁) ≤ D' := by
    intro h
    rw [hD', hu0]
    have := gap_step_ge_of_nonneg (c := β₀) (δ := c.δ) (p := p (i k)) (r := r (i k)) (x := x k)
      h (by linarith [abs_le.mp hβ₀hi])
    have hf := forcing_step_le (c := c) hP0 hzk
    linarith
  have hgap_neg : β₀ ≤ 0 → D' ≤ D + β₀ * M + 2 * (c.δ * Z₁) := by
    intro h
    rw [hD', hu0]
    have := gap_step_le_of_nonpos (c := β₀) (δ := c.δ) (p := p (i k)) (r := r (i k)) (x := x k)
      h (by linarith [abs_le.mp hβ₀hi])
    have hf := forcing_step_le (c := c) hP0 hzk
    linarith
  have hδZ : 16 * (c.δ * Z₁) ≤ clo * M := by
    have : clo * W₁ ≤ clo * M := mul_le_mul_of_nonneg_left hW hclo.le
    linarith
  have hcloM1 : clo * M ≤ M := by
    have := mul_le_mul_of_nonneg_right hclo1 hMnn; linarith
  have hδZM : 16 * (c.δ * Z₁) ≤ M := by linarith
  have hδZnn : 0 ≤ c.δ * Z₁ := mul_nonneg hδ.le hZ1
  have hW1M : W₁ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hW1pos.le hW 2
  have hkey : 128 * c.δ * F * Z₁ ≤ clo ^ 2 * M ^ 2 := by
    rw [hW1sq] at hW1M
    have hc2 : 0 < clo ^ 2 := pow_pos hclo 2
    rw [div_le_iff₀ hc2] at hW1M
    linarith
  have hβ₀abs := abs_le.mp hβ₀hi
  have hβ₁abs := abs_le.mp hβ₁hi
  have hcloC : clo ≤ c.C := c.clo_le
  have hcloM : 0 ≤ clo ^ 2 * M := mul_nonneg (sq_nonneg clo) hMnn
  have hcloM2 : 0 < clo ^ 2 * M ^ 2 := mul_pos (pow_pos hclo 2) (pow_pos hMpos 2)
  have hcloM4 : 0 ≤ clo * M / 4 := by
    have := mul_nonneg hclo.le hMnn; linarith
  have hM0' : M ≠ 0 := hMpos.ne'
  rcases le_or_gt (clo * M / 4) |D| with hbig | hsmall
  · -- case (i): large gap, step k must be contracting
    have hcon : β₀ * D ≤ 0 := by
      by_contra hpos
      have hpos' := not_le.mp hpos
      have h1 := hgate0 hpos'
      have h2 : clo * (clo * M / 4) * M ≤ |β₀| * |D| * M :=
        mul_le_mul_of_nonneg_right (mul_le_mul hβ₀lo hbig hcloM4 (abs_nonneg _)) hMnn
      have e : clo * (clo * M / 4) * M = clo ^ 2 * M ^ 2 / 4 := by ring
      linarith [h1, h2, hkey, hcloM2, e]
    have hβD : β₀ * D = -(|β₀| * |D|) := by
      rw [← abs_mul, abs_of_nonpos hcon, neg_neg]
    have hβDlo : clo * (clo * M / 4) ≤ |β₀| * |D| :=
      mul_le_mul hβ₀lo hbig hcloM4 (abs_nonneg _)
    have hM'le : M' ≤ (1 - clo ^ 2 / 4) * M + 2 * (c.δ * Z₁) := by
      have e : clo * (clo * M / 4) = clo ^ 2 * M / 4 := by ring
      linarith [hup0, hβD, hβDlo, e]
    have hβDhi : |β₀| * |D| ≤ M / 8 := by
      have h1 : |β₀| * |D| ≤ c.C * M := mul_le_mul hβ₀hi hgD (abs_nonneg _) c.C_nonneg
      have h2 : c.C * M ≤ 1 / 8 * M := mul_le_mul_of_nonneg_right c.C_le hMnn
      linarith
    have hM'ge : 3 / 4 * M ≤ M' := by linarith [hlo0, hβD, hβDhi, hδZM]
    rcases le_or_gt (β₁ * D') 0 with hcon1 | hexp1
    · linarith [hup1, hcon1, hM'le, hcloM, hδZnn]
    · have h1 := hgate1 hexp1
      have hM'pos : 0 < M' := by linarith
      have h4 : β₁ * D' ≤ |β₁| * |D'| := by rw [← abs_mul]; exact le_abs_self _
      have h5 : |β₁| * |D'| * (3 / 4 * M) ≤ |β₁| * |D'| * M' :=
        mul_le_mul_of_nonneg_left hM'ge (by positivity)
      have h6 : |β₁| * |D'| ≤ clo ^ 2 * M / 24 := by
        have h7 : |β₁| * |D'| * (3 / 4 * M) ≤ clo ^ 2 * M ^ 2 / 32 := by linarith [h5, h1, hkey]
        have hM34 : 0 < 3 / 4 * M := by linarith
        have h8 := (le_div_iff₀ hM34).mpr h7
        have e : clo ^ 2 * M ^ 2 / 32 / (3 / 4 * M) = clo ^ 2 * M / 24 := by
          field_simp
          ring
        linarith [h8, e]
      linarith [hup1, h4, h6, hM'le, hcloM, hδZnn]
  · -- case (ii): small gap, step k may expand slightly, step k+1 contracts strongly
    have hβD : |β₀ * D| ≤ clo * M / 32 := by
      rw [abs_mul]
      have h1 : |β₀| * |D| ≤ c.C * (clo * M / 4) :=
        mul_le_mul hβ₀hi hsmall.le (abs_nonneg _) c.C_nonneg
      have h2 : c.C * (clo * M / 4) ≤ 1 / 8 * (clo * M / 4) :=
        mul_le_mul_of_nonneg_right c.C_le hcloM4
      linarith
    have hβDle := le_abs_self (β₀ * D)
    have hβDge := neg_abs_le (β₀ * D)
    have hM'le : M' ≤ M + clo * M / 32 + 2 * (c.δ * Z₁) := by linarith
    have hM'ge : 3 / 4 * M ≤ M' := by linarith [hlo0, hβDge, hβD, hδZM, hcloM1]
    have hM'pos : 0 < M' := by linarith
    have hDabs := abs_lt.mp hsmall
    rcases le_or_gt 0 β₀ with hβ₀nn | hβ₀neg
    · have hβ₀clo : clo ≤ β₀ := by rwa [abs_of_nonneg hβ₀nn] at hβ₀lo
      have hβ₀M : clo * M ≤ β₀ * M := mul_le_mul_of_nonneg_right hβ₀clo hMnn
      have hD' : 5 / 8 * (β₀ * M) ≤ D' := by
        have h := hgap_pos hβ₀nn
        linarith [h, hDabs.1, hβ₀M, hδZ]
      have hD'pos : 0 < D' := by
        have : 0 < β₀ * M := mul_pos (lt_of_lt_of_le hclo hβ₀clo) hMpos
        linarith
      have hcon1 : β₁ * D' ≤ 0 := by
        by_contra hpos
        have hpos' := not_le.mp hpos
        have h1 := hgate1 hpos'
        have h2 : clo * (5 / 8 * (clo * M)) * (3 / 4 * M) ≤ |β₁| * |D'| * M' := by
          apply mul_le_mul _ hM'ge (by linarith) (by positivity)
          apply mul_le_mul hβ₁lo _ (by linarith) (abs_nonneg _)
          rw [abs_of_pos hD'pos]
          linarith
        have e : clo * (5 / 8 * (clo * M)) * (3 / 4 * M) = 15 / 32 * (clo ^ 2 * M ^ 2) := by ring
        linarith [h1, h2, hkey, hcloM2, e]
      have hβ₁D' : β₁ * D' ≤ -(clo * D') := by
        have hβ₁np : β₁ ≤ 0 := by
          by_contra h
          have h' := not_le.mp h
          have := mul_pos h' hD'pos
          linarith
        have h1 : clo ≤ -β₁ := by rwa [abs_of_nonpos hβ₁np] at hβ₁lo
        have h2 := mul_le_mul_of_nonneg_right h1 hD'pos.le
        linarith
      have hβD2 : β₀ * D ≤ β₀ * (clo * M / 4) :=
        mul_le_mul_of_nonneg_left hDabs.2.le hβ₀nn
      have h8 : clo * (5 / 8 * (β₀ * M)) ≤ clo * D' := mul_le_mul_of_nonneg_left hD' hclo.le
      have h9 : clo * (clo * M) ≤ clo * (β₀ * M) := mul_le_mul_of_nonneg_left hβ₀M hclo.le
      linarith [hup1, hβ₁D', hup0, hβD2, h8, h9, hδZnn, hcloM]
    · have hβ₀clo : clo ≤ -β₀ := by rwa [abs_of_neg hβ₀neg] at hβ₀lo
      have hβ₀M : clo * M ≤ -β₀ * M := mul_le_mul_of_nonneg_right hβ₀clo hMnn
      have hD' : D' ≤ -(5 / 8 * (-β₀ * M)) := by
        have h := hgap_neg hβ₀neg.le
        linarith [h, hDabs.2, hβ₀M, hδZ]
      have hD'neg : D' < 0 := by
        have : 0 < -β₀ * M := mul_pos (lt_of_lt_of_le hclo hβ₀clo) hMpos
        linarith
      have hcon1 : β₁ * D' ≤ 0 := by
        by_contra hpos
        have hpos' := not_le.mp hpos
        have h1 := hgate1 hpos'
        have h2 : clo * (5 / 8 * (clo * M)) * (3 / 4 * M) ≤ |β₁| * |D'| * M' := by
          apply mul_le_mul _ hM'ge (by linarith) (by positivity)
          apply mul_le_mul hβ₁lo _ (by linarith) (abs_nonneg _)
          rw [abs_of_neg hD'neg]
          linarith
        have e : clo * (5 / 8 * (clo * M)) * (3 / 4 * M) = 15 / 32 * (clo ^ 2 * M ^ 2) := by ring
        linarith [h1, h2, hkey, hcloM2, e]
      have hβ₁D' : β₁ * D' ≤ -(clo * (-D')) := by
        have hβ₁nn : 0 ≤ β₁ := by
          by_contra h
          have h' := not_le.mp h
          have := mul_pos_of_neg_of_neg h' hD'neg
          linarith
        have h1 : clo ≤ β₁ := by rwa [abs_of_nonneg hβ₁nn] at hβ₁lo
        have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ -D')
        linarith
      have hβD2 : β₀ * D ≤ -β₀ * (clo * M / 4) := by
        have := mul_le_mul_of_nonpos_left hDabs.1.le hβ₀neg.le
        linarith
      have h8 : clo * (5 / 8 * (-β₀ * M)) ≤ clo * (-D') :=
        mul_le_mul_of_nonneg_left (by linarith) hclo.le
      have h9 : clo * (clo * M) ≤ clo * (-β₀ * M) := mul_le_mul_of_nonneg_left hβ₀M hclo.le
      linarith [hup1, hβ₁D', hup0, hβD2, h8, h9, hδZnn, hcloM]

end TwoStep

end LongTails.Proofs.TwoSidedPerceptronContraction
