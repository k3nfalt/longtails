import LongTails.Proofs.FrankWolfeDynamics

open Set Filter
open scoped Topology

namespace OracleTemplate.FrankWolfe.HardDynamics

noncomputable def b0 (q : ℝ) : ℝ := (q / (q + 1)) ^ (1 / q)
noncomputable def beta (q : ℝ) : ℝ := b0 q ^ (q - 1)
noncomputable def b (q v : ℝ) : ℝ := b0 q * v ^ (1 / (q - 1))
noncomputable def k (q m v : ℝ) : ℝ := m * beta q * v
noncomputable def area (q u v : ℝ) : ℝ := (1 + b q v ^ q * u) ^ (-1 / q)
noncomputable def z (q u v : ℝ) : ℝ := b q v ^ q * curvatureSlope q (b q v ^ q * u)
noncomputable def tangent (q r m u v : ℝ) : ℝ :=
  b q v * area q u v + k q m v * u ^ (r - 2 / q)
noncomputable def gapFactor (q r m u v : ℝ) : ℝ :=
  1 - z q u v + b q v ^ q * area q u v + (k q m v ^ 2 / m) * u ^ (r - 2 / q)
noncomputable def normFactor (q r m u v : ℝ) : ℝ :=
  tangent q r m u v ^ 2 + u ^ (2 - 2 / q) * (1 - z q u v) ^ 2
noncomputable def radial (q r m u v : ℝ) : ℝ :=
  m * gapFactor q r m u v * (1 - z q u v) / normFactor q r m u v
noncomputable def stepSize (q r m u v : ℝ) : ℝ :=
  m * u ^ (r - 2 / q) * gapFactor q r m u v / normFactor q r m u v
noncomputable def transverse (q r m u v : ℝ) : ℝ :=
  (gapFactor q r m u v * tangent q r m u v / (beta q * normFactor q r m u v) - v) *
    (1 - radial q r m u v * u ^ (r - 2 / q)) ^ (-(r - 1 / q))

lemma b0_pos {q : ℝ} (hq : 3 < q) : 0 < b0 q := by
  apply Real.rpow_pos_of_pos
  exact div_pos (by linarith) (by linarith)

lemma beta_pos {q : ℝ} (hq : 3 < q) : 0 < beta q := Real.rpow_pos_of_pos (b0_pos hq) _

lemma b_pos {q v : ℝ} (hq : 3 < q) (hv : 0 < v) : 0 < b q v :=
  mul_pos (b0_pos hq) (Real.rpow_pos_of_pos hv _)

lemma b0_power {q : ℝ} (hq : 3 < q) : b0 q ^ q = q / (q + 1) := by
  rw [b0, ← Real.rpow_mul (show 0 ≤ q / (q + 1) by positivity),
    one_div_mul_cancel (by linarith : q ≠ 0), Real.rpow_one]

lemma b_power {q v : ℝ} (hq : 3 < q) (hv : 0 < v) :
    b q v ^ (q - 1) = beta q * v := by
  rw [b, Real.mul_rpow (b0_pos hq).le (Real.rpow_nonneg hv.le _),
    ← Real.rpow_mul hv.le, one_div_mul_cancel (by linarith : q - 1 ≠ 0), Real.rpow_one]
  rfl

lemma exponents_pos {q r : ℝ} (hq : 3 < q) (hr : 2 < r) :
    0 < r - 2 / q ∧ 0 < 2 - 2 / q := by
  have hqpos : 0 < q := by linarith
  have hdiv : 2 / q < 1 := (div_lt_one hqpos).mpr (by linarith)
  constructor <;> linarith

lemma area_zero (q v : ℝ) : area q 0 v = 1 := by simp [area]

lemma z_zero (q v : ℝ) : z q 0 v = b q v ^ q / q := by
  simp [z, curvatureSlope_zero, div_eq_mul_inv]

lemma z_identity (q u v : ℝ) : u * z q u v = 1 - area q u v := by
  have h := curvatureSlope_identity q (b q v ^ q * u)
  dsimp [z, area]
  nlinarith

lemma tangent_zero {q r : ℝ} (hq : 3 < q) (hr : 2 < r) (m v : ℝ) :
    tangent q r m 0 v = b q v := by
  simp [tangent, area_zero, Real.zero_rpow (exponents_pos hq hr).1.ne']

lemma normFactor_zero {q r : ℝ} (hq : 3 < q) (hr : 2 < r) (m v : ℝ) :
    normFactor q r m 0 v = b q v ^ 2 := by
  simp [normFactor, tangent_zero hq hr, Real.zero_rpow (exponents_pos hq hr).2.ne']

lemma gapFactor_zero {q r : ℝ} (hq : 3 < q) (hr : 2 < r) (m v : ℝ) :
    gapFactor q r m 0 v = 1 + (1 - 1 / q) * b q v ^ q := by
  simp only [gapFactor, z_zero, area_zero, mul_one,
    Real.zero_rpow (exponents_pos hq hr).1.ne', mul_zero, add_zero]
  ring

lemma b_continuous {q : ℝ} (hq : 3 < q) : Continuous (b q) := by
  exact continuous_const.mul (Real.continuous_rpow_const (div_nonneg zero_le_one (by linarith)))

lemma area_continuous_zero {q v : ℝ} (hq : 3 < q) :
    ContinuousAt (fun p : ℝ × ℝ => area q p.1 p.2) (0, v) := by
  have hb : ContinuousAt (fun p : ℝ × ℝ => b q p.2) (0, v) :=
    (b_continuous hq).continuousAt.comp continuousAt_snd
  have hB := hb.rpow_const (Or.inr (by linarith : 0 ≤ q))
  exact (continuousAt_const.add (hB.mul continuousAt_fst)).rpow_const
    (Or.inl (by simp))

lemma z_continuous_zero {q v : ℝ} (hq : 3 < q) :
    ContinuousAt (fun p : ℝ × ℝ => z q p.1 p.2) (0, v) := by
  have hb : ContinuousAt (fun p : ℝ × ℝ => b q p.2) (0, v) :=
    (b_continuous hq).continuousAt.comp continuousAt_snd
  have hB := hb.rpow_const (Or.inr (by linarith : 0 ≤ q))
  have harg := hB.mul continuousAt_fst
  have hsl : ContinuousAt (curvatureSlope q) (b q v ^ q * (0 : ℝ)) := by
    simpa using curvatureSlope_continuous q
  exact hB.mul (ContinuousAt.comp (g := curvatureSlope q)
    (f := fun p : ℝ × ℝ => b q p.2 ^ q * p.1) hsl harg)

lemma tangent_continuous_zero {q r v : ℝ} (hq : 3 < q) (hr : 2 < r) (m : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => tangent q r m p.1 p.2) (0, v) := by
  have hb : ContinuousAt (fun p : ℝ × ℝ => b q p.2) (0, v) :=
    (b_continuous hq).continuousAt.comp continuousAt_snd
  have hk : ContinuousAt (fun p : ℝ × ℝ => k q m p.2) (0, v) := by
    unfold k
    fun_prop
  exact (hb.mul (area_continuous_zero hq)).add
    (hk.mul (continuousAt_fst.rpow_const (Or.inr (exponents_pos hq hr).1.le)))

lemma gapFactor_continuous_zero {q r v : ℝ} (hq : 3 < q) (hr : 2 < r) (m : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => gapFactor q r m p.1 p.2) (0, v) := by
  have hb : ContinuousAt (fun p : ℝ × ℝ => b q p.2) (0, v) :=
    (b_continuous hq).continuousAt.comp continuousAt_snd
  have hB := hb.rpow_const (Or.inr (by linarith : 0 ≤ q))
  have hk : ContinuousAt (fun p : ℝ × ℝ => k q m p.2 ^ 2 / m) (0, v) := by
    unfold k
    fun_prop
  exact ((continuousAt_const.sub (z_continuous_zero hq)).add
    (hB.mul (area_continuous_zero hq))).add
    (hk.mul (continuousAt_fst.rpow_const (Or.inr (exponents_pos hq hr).1.le)))

lemma normFactor_continuous_zero {q r v : ℝ} (hq : 3 < q) (hr : 2 < r) (m : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => normFactor q r m p.1 p.2) (0, v) := by
  exact ((tangent_continuous_zero hq hr m).pow 2).add
    ((continuousAt_fst.rpow_const (Or.inr (exponents_pos hq hr).2.le)).mul
      ((continuousAt_const.sub (z_continuous_zero hq)).pow 2))

lemma radial_continuous_zero {q r v : ℝ} (hq : 3 < q) (hr : 2 < r)
    (hv : 0 < v) (m : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => radial q r m p.1 p.2) (0, v) := by
  apply ((continuousAt_const.mul (gapFactor_continuous_zero hq hr m)).mul
    (continuousAt_const.sub (z_continuous_zero hq))).div (normFactor_continuous_zero hq hr m)
  rw [normFactor_zero hq hr]
  exact pow_ne_zero _ (b_pos hq hv).ne'

lemma transverse_continuous_zero {q r v : ℝ} (hq : 3 < q) (hr : 2 < r)
    (hv : 0 < v) (m : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => transverse q r m p.1 p.2) (0, v) := by
  have hden : beta q * normFactor q r m 0 v ≠ 0 := by
    rw [normFactor_zero hq hr]
    exact mul_ne_zero (beta_pos hq).ne' (pow_ne_zero _ (b_pos hq hv).ne')
  have hleft := (((gapFactor_continuous_zero hq hr m).mul
    (tangent_continuous_zero hq hr m)).div
      (continuousAt_const.mul (normFactor_continuous_zero hq hr m)) hden).sub continuousAt_snd
  apply hleft.mul
  apply (continuousAt_const.sub ((radial_continuous_zero hq hr hv m).mul
    (continuousAt_fst.rpow_const (Or.inr (exponents_pos hq hr).1.le)))).rpow_const
  left
  simp [Real.zero_rpow (exponents_pos hq hr).1.ne']

lemma beta_mul_b {q v : ℝ} (hq : 3 < q) :
    beta q * b q v = q / (q + 1) * v ^ (1 / (q - 1)) := by
  have hp : b0 q ^ (q - 1) * b0 q = b0 q ^ q := by
    calc
      _ = b0 q ^ (q - 1) * b0 q ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = b0 q ^ (q - 1 + 1) := (Real.rpow_add (b0_pos hq) _ _).symm
      _ = b0 q ^ q := by congr 1; ring
  rw [beta, b, ← mul_assoc, hp, b0_power hq]

lemma inverse_beta_b {q v : ℝ} (hq : 3 < q) (hv : 0 < v) :
    1 / (beta q * b q v) = (q + 1) / q * v ^ (-1 / (q - 1)) := by
  rw [beta_mul_b hq, neg_div, Real.rpow_neg hv.le]
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

lemma b_full_power {q v : ℝ} (hq : 3 < q) (hv : 0 < v) :
    b q v ^ q = beta q * v * b q v := by
  calc
    _ = b q v ^ ((q - 1) + 1) := by congr 1; ring
    _ = b q v ^ (q - 1) * b q v := by rw [Real.rpow_add (b_pos hq hv), Real.rpow_one]
    _ = beta q * v * b q v := by rw [b_power hq hv]

lemma transverse_zero {q r v : ℝ} (hq : 3 < q) (hr : 2 < r)
    (hv : 0 < v) (m : ℝ) : transverse q r m 0 v = limitingMap q v := by
  simp only [transverse, tangent_zero hq hr, gapFactor_zero hq hr,
    normFactor_zero hq hr, Real.zero_rpow (exponents_pos hq hr).1.ne',
    mul_zero, sub_zero, Real.one_rpow, mul_one]
  rw [b_full_power hq hv]
  have hβ := (beta_pos hq).ne'
  have hb := (b_pos hq hv).ne'
  calc
    (1 + (1 - 1 / q) * (beta q * v * b q v)) * b q v /
        (beta q * b q v ^ 2) - v = 1 / (beta q * b q v) + (1 - 1 / q) * v - v := by
      field_simp
    _ = limitingMap q v := by rw [inverse_beta_b hq hv]; unfold limitingMap; ring

lemma radial_center {q r : ℝ} (hq : 3 < q) (hr : 2 < r) (m : ℝ) :
    radial q r m 0 1 = 2 * m * (q / (q + 1)) ^ 2 / b0 q ^ 2 := by
  simp only [radial, gapFactor_zero hq hr, normFactor_zero hq hr, z_zero,
    b, Real.one_rpow, mul_one, b0_power hq]
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q + 1 ≠ 0 := by linarith
  field_simp
  ring

lemma radial_center_pos {q r m : ℝ} (hq : 3 < q) (hr : 2 < r) (hm : 0 < m) :
    0 < radial q r m 0 1 := by
  rw [radial_center hq hr]
  exact div_pos (mul_pos (mul_pos (by norm_num) hm)
    (sq_pos_of_pos (div_pos (by linarith) (by linarith)))) (sq_pos_of_pos (b0_pos hq))

lemma exists_invariant_rectangle {q r bound : ℝ} (hq : 3 < q) (hr : 2 < r)
    (hbound : 0 < bound) (m : ℝ) :
    ∃ δ, 0 < δ ∧ δ ≤ bound ∧ δ ≤ 1 / 4 ∧
      ∃ u0 > 0, ∀ u ∈ Icc (0 : ℝ) u0, ∀ v ∈ Icc (1 - δ) (1 + δ),
        |transverse q r m u v - 1| ≤ δ := by
  let rate := (1 + 2 / (q - 1)) / 2
  have hq1 : 0 < q - 1 := by linarith
  have hsmall : 2 / (q - 1) < 1 := (div_lt_one hq1).mpr (by linarith)
  have hnonneg : 0 ≤ 2 / (q - 1) := div_nonneg (by norm_num) hq1.le
  have hrate : 0 ≤ rate ∧ rate < 1 := by dsimp [rate]; constructor <;> linarith
  have hderiv : |-2 / (q - 1)| < rate := by
    rw [abs_div, abs_of_pos hq1]
    norm_num
    dsimp [rate]
    linarith
  obtain ⟨radius, hrad, hcontract⟩ := local_fixed_point_contraction
    (limitingMap_derivative_one hq) hderiv
  let δ := min radius (min bound (1 / 4))
  have hδ : 0 < δ := lt_min hrad (lt_min hbound (by norm_num))
  have hδrad : δ ≤ radius := min_le_left _ _
  have hδbound : δ ≤ bound := (min_le_right _ _).trans (min_le_left _ _)
  have hδquarter : δ ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, hδbound, hδquarter, ?_⟩
  apply invariant_strip (W := fun p : ℝ × ℝ => transverse q r m p.1 p.2) hδ hrate.2
  · intro v hv
    exact transverse_continuous_zero hq hr (by linarith [hv.1]) m
  · intro v hv
    have hvδ : |v - 1| ≤ δ := abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hc := hcontract v (hvδ.trans hδrad)
    rw [limitingMap_one (by linarith : q ≠ 0)] at hc
    rw [transverse_zero hq hr (by linarith [hv.1])]
    exact hc.trans (mul_le_mul_of_nonneg_left hvδ hrate.1)

lemma stepSize_zero {q r : ℝ} (hq : 3 < q) (hr : 2 < r) (m v : ℝ) :
    stepSize q r m 0 v = 0 := by
  simp [stepSize, Real.zero_rpow (exponents_pos hq hr).1.ne']

lemma stepSize_continuous_zero {q r v : ℝ} (hq : 3 < q) (hr : 2 < r)
    (hv : 0 < v) (m : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => stepSize q r m p.1 p.2) (0, v) := by
  apply ((continuousAt_const.mul
    (continuousAt_fst.rpow_const (Or.inr (exponents_pos hq hr).1.le))).mul
      (gapFactor_continuous_zero hq hr m)).div (normFactor_continuous_zero hq hr m)
  rw [normFactor_zero hq hr]
  exact pow_ne_zero _ (b_pos hq hv).ne'

lemma gapFactor_zero_pos {q r : ℝ} (hq : 3 < q) (hr : 2 < r) (m v : ℝ) (hv : 0 < v) :
    0 < gapFactor q r m 0 v := by
  rw [gapFactor_zero hq hr]
  have hqpos : 0 < q := by linarith
  have hdiv : 1 / q < 1 := (div_lt_one hqpos).mpr (by linarith)
  have hB : 0 ≤ b q v ^ q := Real.rpow_nonneg (b_pos hq hv).le _
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - 1 / q) hB]

lemma exists_stable_strip {q r m : ℝ} (hq : 3 < q) (hr : 2 < r) (hm : 0 < m) :
    ∃ δ, 0 < δ ∧ δ ≤ 1 / 4 ∧ ∃ u0, 0 < u0 ∧ u0 ≤ 1 / 2 ∧
      ∀ u ∈ Icc (0 : ℝ) u0, ∀ v ∈ Icc (1 - δ) (1 + δ),
        0 < radial q r m u v ∧ radial q r m u v ≤ 2 * radial q r m 0 1 ∧
        0 < normFactor q r m u v ∧ 0 < gapFactor q r m u v ∧
        0 ≤ stepSize q r m u v ∧ stepSize q r m u v < 1 ∧
        (r - 2 / q + 1) * radial q r m u v * u ^ (r - 2 / q) ≤ 1 / 2 ∧
        |transverse q r m u v - 1| ≤ δ := by
  have hcpos := radial_center_pos hq hr hm
  have hcont : ContinuousAt (fun v : ℝ => radial q r m 0 v) 1 :=
    (radial_continuous_zero hq hr (by norm_num : (0 : ℝ) < 1) m).comp
      (continuousAt_const.prodMk continuousAt_id)
  have hevent : ∀ᶠ v in 𝓝 (1 : ℝ),
      0 < radial q r m 0 v ∧ radial q r m 0 v < 2 * radial q r m 0 1 :=
    (hcont.eventually (lt_mem_nhds hcpos)).and
      (hcont.eventually (gt_mem_nhds (by linarith)))
  obtain ⟨ε, hε, hεbound⟩ := Metric.eventually_nhds_iff.mp hevent
  obtain ⟨δ, hδ, hδε, hδquarter, u1, hu1, hinv⟩ :=
    exists_invariant_rectangle hq hr (half_pos hε) m
  have hface : ∀ v ∈ Icc (1 - δ) (1 + δ),
      0 < radial q r m 0 v ∧ radial q r m 0 v < 2 * radial q r m 0 1 := by
    intro v hv
    apply hεbound
    rw [Real.dist_eq]
    have hvδ : |v - 1| ≤ δ := abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
    linarith
  have he := (exponents_pos hq hr).1
  have hlocal : ∀ v ∈ Icc (1 - δ) (1 + δ), ∀ᶠ p : ℝ × ℝ in 𝓝 (0, v),
      0 < radial q r m p.1 p.2 ∧ radial q r m p.1 p.2 < 2 * radial q r m 0 1 ∧
      0 < normFactor q r m p.1 p.2 ∧ 0 < gapFactor q r m p.1 p.2 ∧
      stepSize q r m p.1 p.2 < 1 ∧
      (r - 2 / q + 1) * radial q r m p.1 p.2 * p.1 ^ (r - 2 / q) < 1 / 2 := by
    intro v hv
    have hvpos : 0 < v := by linarith [hv.1]
    have hc := radial_continuous_zero hq hr hvpos m
    have hn := normFactor_continuous_zero hq hr (v := v) m
    have hg := gapFactor_continuous_zero hq hr (v := v) m
    have hγ := stepSize_continuous_zero hq hr hvpos m
    have hp : ContinuousAt (fun p : ℝ × ℝ =>
        (r - 2 / q + 1) * radial q r m p.1 p.2 * p.1 ^ (r - 2 / q)) (0, v) :=
      (continuousAt_const.mul hc).mul (continuousAt_fst.rpow_const (Or.inr he.le))
    have hnpos : 0 < normFactor q r m 0 v := by
      rw [normFactor_zero hq hr]
      exact sq_pos_of_pos (b_pos hq hvpos)
    have hpzero : (r - 2 / q + 1) * radial q r m 0 v * (0 : ℝ) ^ (r - 2 / q) < 1 / 2 := by
      simp [Real.zero_rpow he.ne']
    exact (hc.eventually (lt_mem_nhds (hface v hv).1)).and
      ((hc.eventually (gt_mem_nhds (hface v hv).2)).and
        ((hn.eventually (lt_mem_nhds hnpos)).and
          ((hg.eventually (lt_mem_nhds (gapFactor_zero_pos hq hr m v hvpos))).and
            ((hγ.eventually (gt_mem_nhds (by dsimp only; rw [stepSize_zero hq hr]; norm_num))).and
              (hp.eventually (gt_mem_nhds hpzero))))))
  obtain ⟨u2, hu2, hvalid⟩ := compact_strip
    (P := fun u v => 0 < radial q r m u v ∧ radial q r m u v < 2 * radial q r m 0 1 ∧
      0 < normFactor q r m u v ∧ 0 < gapFactor q r m u v ∧ stepSize q r m u v < 1 ∧
      (r - 2 / q + 1) * radial q r m u v * u ^ (r - 2 / q) < 1 / 2) hlocal
  let u0 := min u1 (min u2 (1 / 2))
  have hu0 : 0 < u0 := lt_min hu1 (lt_min hu2 (by norm_num))
  refine ⟨δ, hδ, hδquarter, u0, hu0, (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro u hu v hv
  have huone : u ∈ Icc (0 : ℝ) u1 := ⟨hu.1, hu.2.trans (min_le_left _ _)⟩
  have hutwo : u ∈ Icc (0 : ℝ) u2 :=
    ⟨hu.1, hu.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  obtain ⟨hc, hcupper, hn, hg, hγ, hp⟩ := hvalid u hutwo v hv
  have hγnonneg : 0 ≤ stepSize q r m u v := by
    unfold stepSize
    exact div_nonneg (mul_nonneg (mul_nonneg hm.le (Real.rpow_nonneg hu.1 _)) hg.le) hn.le
  exact ⟨hc, hcupper.le, hn, hg, hγnonneg, hγ, hp.le, hinv u huone v hv⟩

lemma b0_le_one {q : ℝ} (hq : 3 < q) : b0 q ≤ 1 := by
  have hqpos : 0 < q := by linarith
  have hq1 : 0 < q + 1 := by linarith
  have hbase : q / (q + 1) ≤ 1 := (div_le_one hq1).mpr (by linarith)
  simpa only [b0, Real.one_rpow] using
    Real.rpow_le_rpow (div_nonneg hqpos.le hq1.le) hbase (div_nonneg zero_le_one hqpos.le)

lemma beta_le_one {q : ℝ} (hq : 3 < q) : beta q ≤ 1 := by
  simpa only [beta, Real.one_rpow] using
    Real.rpow_le_rpow (b0_pos hq).le (b0_le_one hq) (by linarith : 0 ≤ q - 1)

lemma radial_center_le {q r m : ℝ} (hq : 3 < q) (hr : 2 < r) (hm : 0 ≤ m) :
    radial q r m 0 1 ≤ 2 * m := by
  have hp := beta_mul_b (v := 1) hq
  simp only [b, Real.one_rpow, mul_one] at hp
  have heq : radial q r m 0 1 = 2 * m * beta q ^ 2 := by
    rw [radial_center hq hr, ← hp]
    field_simp [(b0_pos hq).ne']
  rw [heq]
  have hb := beta_le_one hq
  have hbpos := (beta_pos hq).le
  have hsq : beta q ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * m)]

end OracleTemplate.FrankWolfe.HardDynamics
