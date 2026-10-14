import LongTails.Proofs.FrankWolfeNormalized
import LongTails.Proofs.FrankWolfeLinearOracle

open Set Filter
open scoped Topology
open scoped RealInnerProductSpace

namespace OracleTemplate.FrankWolfe.HardDynamics

open LongTails.Setups.UniformlyConvexHolder

open HardInstance

noncomputable def point (q r m u v sign : ℝ) : Plane :=
  WithLp.toLp 2 ![1 - u, sign * k q m v * u ^ (r - 1 / q)]

noncomputable def atom (q u v sign : ℝ) : Plane :=
  WithLp.toLp 2 ![area q u v, -sign * b q v * u ^ (1 / q) * area q u v]

noncomputable def coordinateGradient (q r m u v sign : ℝ) : Plane :=
  WithLp.toLp 2 ![-2 * m * u ^ (r - 1), 2 * sign * k q m v * u ^ (r - 1 / q)]

lemma area_pos {q u v : ℝ} (hq : 3 < q) (hu : 0 ≤ u) (hv : 0 < v) :
    0 < area q u v := by
  apply Real.rpow_pos_of_pos
  have h := mul_nonneg (Real.rpow_nonneg (b_pos hq hv).le q) hu
  linarith

lemma area_power {q u v : ℝ} (hq : 3 < q) (hu : 0 ≤ u) (hv : 0 < v) :
    area q u v ^ q = (1 + b q v ^ q * u)⁻¹ := by
  have hbase : 0 < 1 + b q v ^ q * u := by
    have := mul_nonneg (Real.rpow_nonneg (b_pos hq hv).le q) hu
    linarith
  rw [area, ← Real.rpow_mul hbase.le]
  have hq0 : q ≠ 0 := by linarith
  rw [show (-1 / q) * q = -1 by field_simp, Real.rpow_neg_one]

lemma sign_abs {sign : ℝ} (h : sign ^ 2 = 1) : |sign| = 1 := by
  nlinarith [sq_abs sign, abs_nonneg sign]

lemma atom_boundary {q u v sign : ℝ} (hq : 3 < q) (hu : 0 < u) (hv : 0 < v)
    (hsign : sign ^ 2 = 1) : |atom q u v sign 0| ^ q + |atom q u v sign 1| ^ q = 1 := by
  have hA := area_pos hq hu.le hv
  have hb := b_pos hq hv
  have huq := Real.rpow_pos_of_pos hu (1 / q)
  have hq0 : q ≠ 0 := by linarith
  have htail : |-sign * b q v * u ^ (1 / q) * area q u v| =
      b q v * u ^ (1 / q) * area q u v := by
    simp only [abs_mul, abs_neg, sign_abs hsign, abs_of_pos hb, abs_of_pos huq, abs_of_pos hA, one_mul]
  simp only [atom, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [abs_of_pos hA, htail,
    Real.mul_rpow (mul_nonneg hb.le huq.le) hA.le, Real.mul_rpow hb.le huq.le,
    ← Real.rpow_mul hu.le, one_div_mul_cancel hq0, Real.rpow_one, area_power hq hu.le hv]
  have hbase : 1 + b q v ^ q * u ≠ 0 := by positivity
  field_simp

lemma point_gradient {q r u v sign : ℝ} :
    grad r (point q r (coefficient r * r / 2) u v sign) =
      WithLp.toLp 2 ![-2 * (coefficient r * r / 2) * u ^ (r - 1),
        2 * sign * k q (coefficient r * r / 2) v * u ^ (r - 1 / q)] := by
  ext i
  fin_cases i <;> simp only [grad, point, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, sub_sub_cancel] <;> ring

lemma tail_power_identity {q r u v : ℝ} (hq : 3 < q) (hu : 0 < u) (hv : 0 < v) :
    u ^ (r - 1) * (b q v * u ^ (1 / q)) ^ (q - 1) =
      beta q * v * u ^ (r - 1 / q) := by
  rw [Real.mul_rpow (b_pos hq hv).le (Real.rpow_nonneg hu.le _), b_power hq hv,
    ← Real.rpow_mul hu.le]
  have he : r - 1 + 1 / q * (q - 1) = r - 1 / q := by
    have hq0 : q ≠ 0 := by linarith
    field_simp
    ring
  calc
    u ^ (r - 1) * (beta q * v * u ^ (1 / q * (q - 1))) =
        beta q * v * (u ^ (r - 1) * u ^ (1 / q * (q - 1))) := by ring
    _ = _ := by rw [← Real.rpow_add hu, he]

lemma atom_lmo {q r m u v sign : ℝ} (hq : 3 < q) (hm : 0 < m)
    (hu : 0 < u) (hv : 0 < v) (hsign : sign ^ 2 = 1) :
    atom q u v sign ∈ twoBall q ∧ ∀ x ∈ twoBall q,
      ⟪coordinateGradient q r m u v sign, atom q u v sign⟫ ≤
        ⟪coordinateGradient q r m u v sign, x⟫ := by
  let A := area q u v
  let T := b q v * u ^ (1 / q) * A
  let c := 2 * m * u ^ (r - 1) / A ^ (q - 1)
  have hA : 0 < A := area_pos hq hu.le hv
  have hT : 0 < T := mul_pos (mul_pos (b_pos hq hv) (Real.rpow_pos_of_pos hu _)) hA
  have hAp : A ^ (q - 1) ≠ 0 := (Real.rpow_pos_of_pos hA _).ne'
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hnormal : c * A ^ (q - 1) = 2 * m * u ^ (r - 1) := div_mul_cancel₀ _ hAp
  have htail : c * T ^ (q - 1) = 2 * k q m v * u ^ (r - 1 / q) := by
    have ht := tail_power_identity (r := r) hq hu hv
    calc
      c * T ^ (q - 1) = 2 * m *
          (u ^ (r - 1) * (b q v * u ^ (1 / q)) ^ (q - 1)) := by
        dsimp [c, T]
        rw [Real.mul_rpow (mul_nonneg (b_pos hq hv).le (Real.rpow_nonneg hu.le _)) hA.le]
        field_simp
      _ = _ := by rw [ht]; dsimp [k]; ring
  have hboundary : A ^ q + T ^ q = 1 := by
    have hb := atom_boundary hq hu hv hsign
    have hatom : atom q u v sign = WithLp.toLp 2 ![A, -sign * T] := by
      ext i
      fin_cases i <;> dsimp [atom, A, T]; ring
    rw [hatom] at hb
    simpa [abs_of_pos hA, abs_mul, abs_neg, sign_abs hsign, abs_of_pos hT] using hb
  have hcert := signed_atom_lmo (by linarith : 2 ≤ q) hA hT (sign_abs hsign) hc hboundary
  have heqa : (WithLp.toLp 2 ![A, -sign * T] : Plane) = atom q u v sign := by
    ext i
    fin_cases i <;> dsimp [atom, A, T]; ring
  have heqg : (WithLp.toLp 2 ![-c * A ^ (q - 1), sign * c * T ^ (q - 1)] : Plane) =
      coordinateGradient q r m u v sign := by
    ext i
    fin_cases i
    · dsimp [coordinateGradient]
      nlinarith [hnormal]
    · dsimp [coordinateGradient]
      have hh := congrArg (fun z => sign * z) htail
      nlinarith
  dsimp only at hcert
  rw [heqa, heqg] at hcert
  exact hcert

lemma tail_power_split {q r u : ℝ} (hu : 0 < u) :
    u ^ (r - 1 / q) = u ^ (1 / q) * u ^ (r - 2 / q) := by
  rw [← Real.rpow_add hu]
  congr 1
  ring

lemma direction_normal (q r m u v sign : ℝ) :
    (atom q u v sign - point q r m u v sign) 0 = u * (1 - z q u v) := by
  have h := z_identity q u v
  dsimp [atom, point]
  nlinarith

lemma direction_tail {q r m u v sign : ℝ} (hu : 0 < u) :
    (atom q u v sign - point q r m u v sign) 1 =
      -sign * u ^ (1 / q) * tangent q r m u v := by
  dsimp [atom, point, tangent]
  rw [tail_power_split hu]
  ring

lemma direction_norm_sq {q r m u v sign : ℝ} (hu : 0 < u) (hsign : sign ^ 2 = 1) :
    ‖atom q u v sign - point q r m u v sign‖ ^ 2 = u ^ (2 / q) * normFactor q r m u v := by
  have hpow : (u ^ (1 / q)) ^ 2 = u ^ (2 / q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
    congr 1
    ring
  have hsplit : u ^ 2 = u ^ (2 / q) * u ^ (2 - 2 / q) := by
    rw [← Real.rpow_add hu, show 2 / q + (2 - 2 / q) = 2 by ring, Real.rpow_two]
  have hn : ‖atom q u v sign - point q r m u v sign‖ ^ 2 =
      ((atom q u v sign - point q r m u v sign) 0) ^ 2 +
      ((atom q u v sign - point q r m u v sign) 1) ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  rw [hn, direction_normal, direction_tail hu]
  simp only [mul_pow, neg_sq, hsign, one_mul, hpow]
  rw [hsplit]
  dsimp [normFactor]
  ring

lemma gap_identity {q r m u v sign : ℝ} (hq : 3 < q) (hm : m ≠ 0)
    (hu : 0 < u) (hv : 0 < v) (hsign : sign ^ 2 = 1) :
    ⟪coordinateGradient q r m u v sign, point q r m u v sign - atom q u v sign⟫ =
      2 * m * u ^ r * gapFactor q r m u v := by
  have hnormal : (point q r m u v sign - atom q u v sign) 0 = -u * (1 - z q u v) := by
    have h := direction_normal q r m u v sign
    simp only [PiLp.sub_apply] at h ⊢
    linarith
  have htail : (point q r m u v sign - atom q u v sign) 1 =
      sign * u ^ (1 / q) * tangent q r m u v := by
    have h := direction_tail (q := q) (r := r) (m := m) (v := v) (sign := sign) hu
    simp only [PiLp.sub_apply] at h ⊢
    linarith
  have hpow0 : u ^ (r - 1) * u = u ^ r := by
    rw [← Real.rpow_add_one hu.ne', show r - 1 + 1 = r by ring]
  have hpow1 : u ^ (r - 1 / q) * u ^ (1 / q) = u ^ r := by
    rw [← Real.rpow_add hu, show r - 1 / q + 1 / q = r by ring]
  have hb : k q m v * b q v = m * b q v ^ q := by rw [b_full_power hq hv]; dsimp [k]; ring
  have hg : m * gapFactor q r m u v = m * (1 - z q u v) + k q m v * tangent q r m u v := by
    dsimp [gapFactor, tangent]
    field_simp
    nlinarith [congrArg (fun z => z * area q u v) hb]
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
    coordinateGradient, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    hnormal, htail]
  calc
    (-u * (1 - z q u v)) * (-2 * m * u ^ (r - 1)) +
        (sign * u ^ (1 / q) * tangent q r m u v) *
          (2 * sign * k q m v * u ^ (r - 1 / q)) =
      2 * m * (u ^ (r - 1) * u) * (1 - z q u v) +
        2 * sign ^ 2 * k q m v * (u ^ (r - 1 / q) * u ^ (1 / q)) * tangent q r m u v := by ring
    _ = 2 * u ^ r * (m * (1 - z q u v) + k q m v * tangent q r m u v) := by
      rw [hpow0, hpow1, hsign]
      ring
    _ = _ := by rw [← hg]; ring

lemma coordinateGradient_ne_zero {q r m u v sign : ℝ} (hm : 0 < m) (hu : 0 < u) :
    coordinateGradient q r m u v sign ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : Plane => x 0) h
  dsimp [coordinateGradient] at h0
  have hneg : -2 * m * u ^ (r - 1) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hm) (Real.rpow_pos_of_pos hu _)
  linarith

lemma lmo_eq_atom {q r m u v sign : ℝ} (hq : 3 < q) (hm : 0 < m)
    (hu : 0 < u) (hv : 0 < v) (hsign : sign ^ 2 = 1) :
    lmo q (by linarith) (coordinateGradient q r m u v sign) = atom q u v sign := by
  have ha := atom_lmo (r := r) hq hm hu hv hsign
  have hb := lmo_spec q (by linarith : 2 ≤ q) (coordinateGradient q r m u v sign)
  exact linear_minimizer_unique (by linarith) (coordinateGradient_ne_zero hm hu) hb.1 ha.1 hb.2 ha.2

lemma stepSize_eq_ratio {q r m u v sign : ℝ} (hq : 3 < q) (hm : m ≠ 0)
    (hu : 0 < u) (hv : 0 < v) (hsign : sign ^ 2 = 1) :
    ⟪coordinateGradient q r m u v sign, point q r m u v sign - atom q u v sign⟫ /
      (2 * ‖atom q u v sign - point q r m u v sign‖ ^ 2) = stepSize q r m u v := by
  rw [gap_identity hq hm hu hv hsign, direction_norm_sq hu hsign]
  calc
    (2 * m * u ^ r * gapFactor q r m u v) / (2 * (u ^ (2 / q) * normFactor q r m u v)) =
        m * (u ^ r / u ^ (2 / q)) * gapFactor q r m u v / normFactor q r m u v := by ring
    _ = _ := by rw [← Real.rpow_sub hu]; rfl

lemma transverse_rescaling {q r m u v : ℝ} (hu : 0 < u)
    (hf : 0 < 1 - radial q r m u v * u ^ (r - 2 / q)) :
    transverse q r m u v * (u * (1 - radial q r m u v * u ^ (r - 2 / q))) ^ (r - 1 / q) =
      (gapFactor q r m u v * tangent q r m u v / (beta q * normFactor q r m u v) - v) *
        u ^ (r - 1 / q) := by
  have hc : (1 - radial q r m u v * u ^ (r - 2 / q)) ^ (-(r - 1 / q)) *
      (1 - radial q r m u v * u ^ (r - 2 / q)) ^ (r - 1 / q) = 1 := by
    rw [← Real.rpow_add hf]
    simp
  dsimp [transverse]
  rw [Real.mul_rpow hu.le hf.le]
  calc
    _ = ((gapFactor q r m u v * tangent q r m u v /
          (beta q * normFactor q r m u v) - v) * u ^ (r - 1 / q)) *
        ((1 - radial q r m u v * u ^ (r - 2 / q)) ^ (-(r - 1 / q)) *
          (1 - radial q r m u v * u ^ (r - 2 / q)) ^ (r - 1 / q)) := by ring
    _ = _ := by rw [hc, mul_one]

lemma coordinate_update {q r m u v sign : ℝ} (hq : 3 < q) (hm : 0 < m)
    (hu : 0 < u) (hv : 0 < v) (hsign : sign ^ 2 = 1)
    (hγ : stepSize q r m u v ≤ 1)
    (hf : 0 < 1 - radial q r m u v * u ^ (r - 2 / q)) :
    shortStep 2 (point q r m u v sign) (coordinateGradient q r m u v sign) (atom q u v sign) =
      point q r m (u * (1 - radial q r m u v * u ^ (r - 2 / q)))
        (transverse q r m u v) (-sign) := by
  have hη : min 1 (⟪coordinateGradient q r m u v sign, point q r m u v sign - atom q u v sign⟫ /
      (2 * ‖atom q u v sign - point q r m u v sign‖ ^ 2)) = stepSize q r m u v := by
    rw [stepSize_eq_ratio hq hm.ne' hu hv hsign, min_eq_right hγ]
  have hrad : stepSize q r m u v * (1 - z q u v) =
      radial q r m u v * u ^ (r - 2 / q) := by dsimp [stepSize, radial]; ring
  have hgp : stepSize q r m u v * u ^ (1 / q) =
      m * gapFactor q r m u v / normFactor q r m u v * u ^ (r - 1 / q) := by
    rw [tail_power_split hu]
    dsimp [stepSize]
    ring
  have hscale := transverse_rescaling (q := q) (r := r) (m := m) (v := v) hu hf
  ext i
  fin_cases i
  · simp only [shortStep, hη, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    change (1 - u) + stepSize q r m u v * (atom q u v sign - point q r m u v sign) 0 =
      1 - u * (1 - radial q r m u v * u ^ (r - 2 / q))
    rw [direction_normal]
    nlinarith [congrArg (fun z => u * z) hrad]
  · simp only [shortStep, hη, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    change sign * k q m v * u ^ (r - 1 / q) + stepSize q r m u v *
      (atom q u v sign - point q r m u v sign) 1 =
      -sign * k q m (transverse q r m u v) *
        (u * (1 - radial q r m u v * u ^ (r - 2 / q))) ^ (r - 1 / q)
    rw [direction_tail hu]
    have hβ := (beta_pos hq).ne'
    calc
      sign * k q m v * u ^ (r - 1 / q) + stepSize q r m u v *
          (-sign * u ^ (1 / q) * tangent q r m u v) =
        sign * m * beta q * v * u ^ (r - 1 / q) - sign *
          (stepSize q r m u v * u ^ (1 / q)) * tangent q r m u v := by dsimp [k]; ring
      _ = -sign * m * beta q *
          ((gapFactor q r m u v * tangent q r m u v /
            (beta q * normFactor q r m u v) - v) * u ^ (r - 1 / q)) := by
        rw [hgp]
        field_simp
        ring
      _ = _ := by rw [← hscale]; dsimp [k]; ring

lemma small_start_feasible {q r m : ℝ} (hq : 3 < q) (hr : 2 < r) (hm : 0 < m) :
    ∃ radius > 0, ∀ u ∈ Ioc (0 : ℝ) radius, point q r m u 1 1 ∈ twoBall q := by
  have hqpos : 0 < q := by linarith
  have hp : 0 < q * r - 2 := by nlinarith
  have hk : 0 < k q m 1 := by dsimp [k]; exact mul_pos (mul_pos hm (beta_pos hq)) zero_lt_one
  have hc : ContinuousAt (fun u : ℝ => k q m 1 ^ q * u ^ (q * r - 2)) 0 :=
    continuousAt_const.mul ((Real.continuous_rpow_const hp.le).continuousAt)
  have hev : ∀ᶠ u in 𝓝 (0 : ℝ), k q m 1 ^ q * u ^ (q * r - 2) < 1 :=
    hc.eventually (gt_mem_nhds (by simp [Real.zero_rpow hp.ne']))
  obtain ⟨ε, hε, hεbound⟩ := Metric.eventually_nhds_iff.mp hev
  let radius := min (ε / 2) (1 / 2)
  have hrad : 0 < radius := lt_min (half_pos hε) (by norm_num)
  refine ⟨radius, hrad, ?_⟩
  intro u hu
  have hu0 := hu.1
  have hu1 : u ≤ 1 / 2 := hu.2.trans (min_le_right _ _)
  have husmall : k q m 1 ^ q * u ^ (q * r - 2) ≤ 1 := by
    apply le_of_lt (hεbound _)
    rw [Real.dist_eq, sub_zero, abs_of_pos hu0]
    have huε := hu.2.trans (min_le_left (ε / 2) (1 / 2))
    linarith
  have hnormal : (1 - u) ^ q ≤ 1 - u := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' (by linarith : 0 ≤ 1 - u)
      (by linarith : 1 - u ≤ 1) zero_le_one (by linarith : 1 ≤ q)
  have ht : (k q m 1 * u ^ (r - 1 / q)) ^ q = u * (k q m 1 ^ q * u ^ (q * r - 2)) := by
    rw [Real.mul_rpow hk.le (Real.rpow_nonneg hu0.le _), ← Real.rpow_mul hu0.le]
    have he : (r - 1 / q) * q = (q * r - 2) + 1 := by field_simp; ring
    rw [he, Real.rpow_add_one hu0.ne']
    ring
  rw [mem_twoBall_iff hqpos]
  change |1 - u| ^ q + |1 * k q m 1 * u ^ (r - 1 / q)| ^ q ≤ 1
  rw [abs_of_nonneg (by linarith : 0 ≤ 1 - u), one_mul,
    abs_of_pos (mul_pos hk (Real.rpow_pos_of_pos hu0 _)), ht]
  nlinarith [mul_le_mul_of_nonneg_left husmall hu0.le]

end OracleTemplate.FrankWolfe.HardDynamics
