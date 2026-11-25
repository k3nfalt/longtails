import LongTails.Proofs.CenteredLogisticSlowDynamics

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.CenteredLogisticSlowTrajectory

open LongTails.Setups.CenteredLogisticClassification
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift margin)
open CenteredLogisticSlowDrift CenteredLogisticSlowDynamics CenteredLogisticSteps
open TwoSampleQuadraticPerceptronEmbedding

variable {p : Params} {D : Data p} {μ η : ℝ} (F : Cloud p D μ)

noncomputable def distance {d : ℕ} (s : Split d) := |s.a - 1| + |s.b| + ‖s.z‖

lemma coefficients (s : Split p.d) (hd : distance s ≤ 1 / 64) :
    |s.a| + |s.b| ≤ 17 / 16 ∧ 15 / 16 ≤ s.a + s.b ∧
      s.a + s.b ≤ 17 / 16 ∧ ‖s.z‖ ≤ 1 / 64 := by
  unfold distance at hd
  have ha := abs_add_le (s.a - 1) 1
  rw [sub_add_cancel, abs_one] at ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [norm_nonneg s.z]
  · linarith [neg_abs_le (s.a - 1), neg_abs_le s.b, norm_nonneg s.z]
  · linarith [le_abs_self s.a, le_abs_self s.b, norm_nonneg s.z]
  · linarith [abs_nonneg (s.a - 1), abs_nonneg s.b]

lemma detail_bound (s : Split p.d) (hμ : 0 < μ) (hd : distance s ≤ 1 / 64) (i : Fin p.n) :
    |detail F s i| ≤ μ / 32 := by
  have h := coefficients s hd
  have hz (u : Features p.d) (hu : ‖u‖ ≤ 1) : |⟪u,s.z⟫| ≤ ‖s.z‖ :=
    (abs_real_inner_le_norm u s.z).trans ((mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans_eq
      (one_mul _))
  have hsu : ‖shift (F.u i)‖ ≤ 1 := by rw [norm_shift]; exact F.residual i
  have hab := add_le_add (mul_le_mul_of_nonneg_left (hz _ (F.residual i)) (abs_nonneg s.a))
    (mul_le_mul_of_nonneg_left (hz _ hsu) (abs_nonneg s.b))
  have htri := abs_add_le (s.a * ⟪F.u i,s.z⟫) (s.b * ⟪shift (F.u i),s.z⟫)
  simp only [abs_mul] at htri
  have hprod := mul_le_mul h.1 h.2.2.2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 17 / 16)
  rw [detail, abs_mul, abs_of_pos hμ]
  have hsum : |s.a * ⟪F.u i,s.z⟫ + s.b * ⟪shift (F.u i),s.z⟫| ≤ 1 / 32 := by nlinarith
  linarith [mul_le_mul_of_nonneg_left hsum hμ.le]

lemma drift_step (s : Split p.d) (hμ : 0 < μ) (hμ' : μ ≤ 1 / 64)
    (hη : 1 ≤ η) (hη' : η ≤ 2) (hd : distance s ≤ 1 / 64)
    (hz : ⟪F.e,s.z⟫ = 0) (hq : -4 * μ ≤ s.q) (hq' : s.q ≤ 0) :
    let s' := advance F s η;
    -4 * μ ≤ s'.q ∧ s'.q ≤ -μ / 8 ∧ distance s' ≤ distance s + 32 * μ := by
  have hc := coefficients s hd
  have hqabs : |s.q| ≤ 4 * μ := abs_le.mpr ⟨by linarith, by linarith⟩
  have hCabs : |s.a + s.b| ≤ 17 / 16 := abs_le.mpr ⟨by linarith [hc.2.1], hc.2.2.1⟩
  have herr := background_force hμ hμ' hCabs hqabs F.levels (detail_bound F s hμ hd) F.mean
  dsimp only at herr
  have hbg : background F s = 𝔼 i, F.A i *
      Real.sigmoid (-(F.A i * (s.a + s.b) * s.q + detail F s i)) := by
    simp only [background, weight, margin_eq F s hz]
  rw [← hbg] at herr
  obtain ⟨hlo,hhi,hk⟩ := trapping hμ hc.2.1 hc.2.2.1 hη hη' F.energy_lo F.energy_hi hq hq' herr
  refine ⟨hlo,hhi,?_⟩
  have hη0 : 0 ≤ η := by linarith
  let k := background F s
  let U := residualForce F s
  have hU : ‖U‖ ≤ 1 := force_norm F s
  have hS : ‖shift U‖ ≤ 1 := by rwa [norm_shift]
  have hcoord (v : Features p.d) (hv : ‖v‖ ≤ 1) :
      |η * (k * s.q + μ * ⟪v,s.z⟫)| ≤ 4 * μ := by
    have h1 := mul_le_mul hk hqabs (abs_nonneg _) (by linarith : 0 ≤ 4 * μ)
    have h2 := (abs_real_inner_le_norm v s.z).trans (mul_le_mul hv hc.2.2.2 (norm_nonneg _)
      zero_le_one)
    have h3 := abs_add_le (k * s.q) (μ * ⟪v,s.z⟫)
    simp only [abs_mul, abs_of_pos hμ] at h3
    have hμ2 := mul_le_mul_of_nonneg_right hμ' hμ.le
    have hsum : |k * s.q + μ * ⟪v,s.z⟫| ≤ 2 * μ := by
      change |k| * |s.q| ≤ _ at h1
      nlinarith [mul_le_mul_of_nonneg_left h2 hμ.le]
    rw [abs_mul, abs_of_nonneg hη0]
    linarith [mul_le_mul hη' hsum (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  have hnorm : ‖s.a • U + s.b • shift U‖ ≤ 17 / 16 := by
    have h := norm_add_le (s.a • U) (s.b • shift U)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at h
    linarith [mul_le_mul_of_nonneg_left hU (abs_nonneg s.a),
      mul_le_mul_of_nonneg_left hS (abs_nonneg s.b), hc.1]
  have hzup := norm_add_le s.z ((η * μ) • (s.a • U + s.b • shift U))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hη0 hμ.le)] at hzup
  have hm := mul_le_mul (mul_le_mul_of_nonneg_right hη' hμ.le) hnorm (norm_nonneg _)
    (by linarith : 0 ≤ 2 * μ)
  dsimp only [distance, advance]
  change |s.a + η * (k * s.q + μ * ⟪U,s.z⟫) - 1| + |s.b + η * (k * s.q + μ * ⟪shift U,s.z⟫)| +
    ‖s.z + (η * μ) • (s.a • U + s.b • shift U)‖ ≤ _
  rw [add_sub_right_comm]
  linarith [abs_add_le (s.a - 1) (η * (k * s.q + μ * ⟪U,s.z⟫)),
    abs_add_le s.b (η * (k * s.q + μ * ⟪shift U,s.z⟫)), hcoord U hU, hcoord (shift U) hS]

lemma slow_iterate (hμ : 0 < μ) (hμ' : μ ≤ 1 / 64) (hη : 1 ≤ η) (hη' : η ≤ 2)
    (t : ℕ) (ht : (t : ℝ) * μ ≤ 1 / 2048) :
    ∃ s : Split p.d, (step D η)^[t] (initialPoint p.d) = point F s ∧ ⟪F.e,s.z⟫ = 0 ∧
      -4 * μ ≤ s.q ∧ s.q ≤ 0 ∧ (t ≠ 0 → s.q ≤ -μ / 8) ∧ distance s ≤ 32 * t * μ := by
  induction t with
  | zero =>
    refine ⟨⟨1,0,0,0⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initialPoint, point, distance, hμ.le]
  | succ t ih =>
    have ht' : (t : ℝ) * μ ≤ 1 / 2048 := by push_cast at ht; nlinarith
    obtain ⟨s,hs,hz,hl,hh,_,hd⟩ := ih ht'
    have hsmall : distance s ≤ 1 / 64 := by nlinarith
    obtain ⟨hlo,hhi,hdis⟩ := drift_step F s hμ hμ' hη hη' hsmall hz hl hh
    refine ⟨advance F s η, ?_, advance_centered F s η hz, hlo, by linarith,
      fun _ => hhi, ?_⟩
    · rw [Function.iterate_succ_apply', hs, step_eq F s η hz]
    · push_cast
      linarith

include F in
lemma slow_failure (hμ : 0 < μ) (hμ' : μ ≤ 1 / 64) (hη : 1 ≤ η) (hη' : η ≤ 2)
    (t : ℕ) (ht : (t : ℝ) * μ ≤ 1 / 2048) :
    ∃ i, margin .conv p.d (D i) ((step D η)^[t] (initialPoint p.d)) ≤ 0 := by
  obtain ⟨i,hi⟩ := F.pos_row
  refine ⟨i,?_⟩
  by_cases ht0 : t = 0
  · subst t
    simp [initialPoint, margin]
  obtain ⟨s,hs,hz,_,_,hq,hdis⟩ := slow_iterate F hμ hμ' hη hη' t ht
  have hsmall : distance s ≤ 1 / 64 := by nlinarith
  have hc := (coefficients s hsmall).2.1
  have hprod := mul_le_mul hi hc (by norm_num : (0 : ℝ) ≤ 15 / 16) (by linarith)
  have hq' := hq ht0
  have hmg := mul_le_mul_of_nonneg_left hq' (by nlinarith : 0 ≤ F.A i * (s.a + s.b))
  have hr := (abs_le.mp (detail_bound F s hμ hsmall i)).2
  rw [hs, margin_eq F s hz]
  nlinarith [mul_le_mul_of_nonneg_right hprod hμ.le]

end LongTails.Proofs.CenteredLogisticSlowTrajectory
