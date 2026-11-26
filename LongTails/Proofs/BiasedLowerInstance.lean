import LongTails.Proofs.AbcLowerBound
import LongTails.Proofs.BiasedDecoy
import LongTails.Setups.HighDimensionalBiasedNoiseNonconvex

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.BiasedLowerInstance

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardOracle
open LongTails.Proofs.AbcLowerParameters LongTails.Proofs.AbcLowerAssembly
open LongTails.Proofs.AbcLowerMeasure LongTails.Proofs.AbcHardContinuity
open LongTails.Proofs.BiasedDecoy

section Maps

variable {d : ℕ}

noncomputable def drop : Space (d + 1) →L[ℝ] Space d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => x (Fin.castSucc i))
      map_add' := by intro x y; ext i; simp
      map_smul' := by intro a x; ext i; simp }

lemma drop_apply (x : Space (d + 1)) (i : Fin d) : drop x i = x (Fin.castSucc i) := rfl

noncomputable def pad : Space d →L[ℝ] Space (d + 1) := ContinuousLinearMap.adjoint drop

noncomputable def eLast : Space (d + 1) := EuclideanSpace.single (Fin.last d) 1

lemma inner_pad (v : Space d) (y : Space (d + 1)) : ⟪pad v, y⟫ = ⟪v, drop y⟫ :=
  ContinuousLinearMap.adjoint_inner_left drop y v

lemma drop_single_castSucc (i : Fin d) :
    drop (EuclideanSpace.single (Fin.castSucc i) (1 : ℝ)) = EuclideanSpace.single i 1 := by
  ext j
  simp only [drop_apply, PiLp.single_apply, Fin.castSucc_inj]

lemma drop_eLast : drop (eLast (d := d)) = 0 := by
  ext j
  simp [drop_apply, eLast, Fin.castSucc_ne_last]

lemma pad_apply_castSucc (v : Space d) (i : Fin d) : pad v (Fin.castSucc i) = v i := by
  have h := inner_pad v (EuclideanSpace.single (Fin.castSucc i) 1)
  rw [drop_single_castSucc] at h
  simpa [EuclideanSpace.inner_single_right] using h

lemma drop_pad (v : Space d) : drop (pad v) = v := by
  ext i
  rw [drop_apply, pad_apply_castSucc]

lemma inner_pad_eLast (v : Space d) : ⟪pad v, eLast (d := d)⟫ = 0 := by
  rw [inner_pad, drop_eLast, inner_zero_right]

lemma norm_pad (v : Space d) : ‖pad v‖ = ‖v‖ := by
  have h : ‖pad v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_pad, drop_pad, real_inner_self_eq_norm_sq]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

lemma norm_eLast : ‖eLast (d := d)‖ = 1 := by simp [eLast]

lemma norm_sq_pad_add (v : Space d) (t : ℝ) :
    ‖pad v + t • eLast (d := d)‖ ^ 2 = ‖v‖ ^ 2 + t ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, inner_pad_eLast, norm_smul, norm_eLast, norm_pad,
    Real.norm_eq_abs, mul_one, sq_abs]
  ring

lemma norm_drop_le (y : Space (d + 1)) : ‖drop y‖ ≤ ‖y‖ := by
  have h : ‖drop y‖ ^ 2 ≤ ‖drop y‖ * ‖y‖ := by
    calc ‖drop y‖ ^ 2 = ⟪pad (drop y), y⟫ := by rw [inner_pad, real_inner_self_eq_norm_sq]
      _ ≤ ‖pad (drop y)‖ * ‖y‖ := real_inner_le_norm _ _
      _ = _ := by rw [norm_pad]
  nlinarith [norm_nonneg (drop y), norm_nonneg y]

lemma abs_inner_eLast_le (y : Space (d + 1)) : |⟪eLast (d := d), y⟫| ≤ ‖y‖ := by
  have h := abs_real_inner_le_norm (eLast (d := d)) y
  rwa [norm_eLast, one_mul] at h

lemma inner_eLast_pad_add (v : Space d) (t : ℝ) :
    ⟪eLast (d := d), pad v + t • eLast⟫ = t := by
  rw [inner_add_right, real_inner_comm, inner_pad_eLast, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_eLast]
  ring

lemma comp_drop_hasGradientAt {h : Space d → ℝ} {v : Space d} {x : Space (d + 1)}
    (hh : HasGradientAt h v (drop x)) : HasGradientAt (fun y => h (drop y)) (pad v) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hh ⊢
  have hc := hh.comp x drop.hasFDerivAt
  have heq : InnerProductSpace.toDual ℝ (Space (d + 1)) (pad v) =
      (InnerProductSpace.toDual ℝ (Space d) v).comp drop := by
    ext y
    rw [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply,
      InnerProductSpace.toDual_apply_apply]
    exact inner_pad v y
  rw [heq]
  exact hc

lemma decoy_hasGradientAt (x0 : Space (d + 1)) (D w c sg : ℝ) (hw : 0 < w) (x : Space (d + 1)) :
    HasGradientAt (fun y => D * pr w (sg * ⟪eLast (d := d), y - x0⟫ - c))
      ((D * dpr w (sg * ⟪eLast (d := d), x - x0⟫ - c) * sg) • eLast) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun y : Space (d + 1) => ⟪eLast (d := d), y - x0⟫)
      (innerSL ℝ (eLast (d := d))) x := by
    have := (innerSL ℝ (eLast (d := d))).hasFDerivAt (x := x - x0)
    exact (this.comp x ((hasFDerivAt_id x).sub_const x0)).congr_fderiv (by ext; simp)
  have hlin : HasFDerivAt (fun y : Space (d + 1) => sg * ⟪eLast (d := d), y - x0⟫ - c)
      (sg • innerSL ℝ (eLast (d := d))) x := (h1.const_mul sg).sub_const c
  have h2 := ((hasDerivAt_pr hw _).comp_hasFDerivAt x hlin).const_mul D
  refine HasFDerivAt.congr_fderiv h2 ?_
  ext v
  simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
    smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

end Maps

section Parameters

open LongTails.Setups.HighDimensionalBiasedNoiseNonconvex

noncomputable def kap (q : Params) : ℝ := Real.sqrt (q.m / (1 - q.m))

noncomputable def epsA (q : Params) : ℝ := 4 * q.ε / (3 * max (kap q) (4 / 3))

noncomputable def theta (q : Params) : ℝ := 3 * epsA q

noncomputable def amp (q : Params) : ℝ := kap q * theta q

noncomputable def wid (q : Params) : ℝ := 2 * (amp q + q.ε) / q.L

noncomputable def abcParams (q : Params) : LongTails.Setups.HighDimensionalAbcNoiseNonconvex.Params :=
  ⟨q.d, q.L / 2, 0, q.M, q.σ ^ 2, q.Δ / 2, epsA q, drop q.x0⟩

variable (q : Params) (hv : spec.valid q)
include hv

lemma one_sub_m_pos : 0 < 1 - q.m := by have := hv.2.2.1; linarith

omit hv in
lemma kap_nonneg : 0 ≤ kap q := Real.sqrt_nonneg _

lemma kap_sq : kap q ^ 2 = q.m / (1 - q.m) :=
  Real.sq_sqrt (div_nonneg hv.2.1 (one_sub_m_pos q hv).le)

omit hv in
lemma max_pos : 0 < max (kap q) (4 / 3) := lt_max_of_lt_right (by norm_num)

lemma epsA_pos : 0 < epsA q := by
  have := max_pos q
  have := hv.2.2.2.2.2.2.1
  unfold epsA; positivity

lemma epsA_le : epsA q ≤ q.ε := by
  have hε := hv.2.2.2.2.2.2.1
  have hmx := le_max_right (kap q) (4 / 3)
  unfold epsA
  rw [div_le_iff₀ (by have := max_pos q; positivity)]
  nlinarith

lemma theta_pos : 0 < theta q := by have := epsA_pos q hv; unfold theta; positivity

lemma amp_nonneg : 0 ≤ amp q := by
  have := kap_nonneg q; have := theta_pos q hv; unfold amp; positivity

lemma amp_le : amp q ≤ 4 * q.ε := by
  have hε := hv.2.2.2.2.2.2.1
  have hmx := le_max_left (kap q) (4 / 3)
  have hpos := max_pos q
  have h4 : 0 ≤ 4 * q.ε / (3 * max (kap q) (4 / 3)) := by positivity
  have h5 : kap q * (4 * q.ε / (3 * max (kap q) (4 / 3))) ≤
      max (kap q) (4 / 3) * (4 * q.ε / (3 * max (kap q) (4 / 3))) :=
    mul_le_mul_of_nonneg_right hmx h4
  have h6 : max (kap q) (4 / 3) * (4 * q.ε / (3 * max (kap q) (4 / 3))) = 4 * q.ε / 3 := by
    rw [show max (kap q) (4 / 3) * (4 * q.ε / (3 * max (kap q) (4 / 3))) =
      4 * q.ε / 3 * (max (kap q) (4 / 3) / max (kap q) (4 / 3)) by ring,
      div_self hpos.ne', mul_one]
  have h7 : amp q = 3 * (kap q * (4 * q.ε / (3 * max (kap q) (4 / 3)))) := by
    unfold amp theta epsA; ring
  rw [h7]
  linarith

lemma wid_pos : 0 < wid q := by
  have := amp_nonneg q hv; have := hv.1; have := hv.2.2.2.2.2.2.1
  unfold wid; positivity

lemma amp_div_wid : amp q / wid q ≤ q.L / 2 := by
  have hL := hv.1
  have hε := hv.2.2.2.2.2.2.1
  have ha := amp_nonneg q hv
  have hw := wid_pos q hv
  rw [div_le_iff₀ hw]
  unfold wid
  have he : q.L / 2 * (2 * (amp q + q.ε) / q.L) = (amp q + q.ε) * (q.L / q.L) := by ring
  rw [he, div_self hL.ne', mul_one]
  linarith

lemma gap_decoy : amp q * (100 * wid q) ≤ q.Δ / 2 := by
  have hL := hv.1
  have hε := hv.2.2.2.2.2.2.1
  have hreg := hv.2.2.2.2.2.2.2.2.1
  have ha := amp_nonneg q hv
  have ha4 := amp_le q hv
  unfold wid
  rw [show amp q * (100 * (2 * (amp q + q.ε) / q.L)) = 200 * (amp q * (amp q + q.ε)) / q.L by
    ring, div_le_iff₀ hL]
  have h1 : amp q * (amp q + q.ε) ≤ 4 * q.ε * (5 * q.ε) := by nlinarith
  nlinarith

omit hv in
lemma epsA_small (h : kap q ≤ 4 / 3) : epsA q = q.ε := by
  unfold epsA; rw [max_eq_right h]; ring

lemma kap_mul : (1 - q.m) * kap q ^ 2 = q.m := by
  have hm1 := one_sub_m_pos q hv
  rw [kap_sq q hv, mul_div_assoc', mul_comm, mul_div_assoc, div_self hm1.ne', mul_one]

omit hv in
lemma epsA_large_mul (h : 4 / 3 ≤ kap q) : epsA q ^ 2 * (9 * kap q ^ 2) = 16 * q.ε ^ 2 := by
  have hkpos : 0 < kap q := by linarith
  have he : epsA q = 4 * q.ε / (3 * kap q) := by unfold epsA; rw [max_eq_left h]
  rw [he, div_pow, div_mul_eq_mul_div, div_eq_iff (by positivity)]
  ring

lemma m_bound_small (h : kap q ≤ 4 / 3) : q.m ≤ 16 / 25 := by
  have hks := kap_sq q hv
  have hk := kap_nonneg q
  have hm1 := one_sub_m_pos q hv
  have hk2 : kap q ^ 2 ≤ 16 / 9 := by nlinarith
  rw [hks, div_le_iff₀ hm1] at hk2
  linarith

lemma m_bound_large (h : 4 / 3 ≤ kap q) : 16 / 25 ≤ q.m := by
  have hks := kap_sq q hv
  have hm1 := one_sub_m_pos q hv
  have hk2 : 16 / 9 ≤ kap q ^ 2 := by nlinarith
  rw [hks, le_div_iff₀ hm1] at hk2
  linarith

lemma epsA_sq_ge : (1 - q.m) * q.ε ^ 2 ≤ epsA q ^ 2 := by
  have hm1 := one_sub_m_pos q hv
  have hε2 := sq_nonneg q.ε
  rcases le_total (kap q) (4 / 3) with h | h
  · rw [epsA_small q h]; nlinarith [hv.2.1]
  · have h1 := epsA_large_mul q h
    have h2 := kap_mul q hv
    have hm := m_bound_large q hv h
    have hk2 : 0 < kap q ^ 2 := pow_pos (by linarith) 2
    have h3 : (1 - q.m) * q.ε ^ 2 * (9 * kap q ^ 2) ≤ epsA q ^ 2 * (9 * kap q ^ 2) := by
      rw [h1]
      have : (1 - q.m) * q.ε ^ 2 * (9 * kap q ^ 2) = 9 * q.m * q.ε ^ 2 := by
        linear_combination 9 * q.ε ^ 2 * h2
      rw [this]
      nlinarith [hv.2.2.1]
    exact le_of_mul_le_mul_right h3 (by positivity)

lemma epsA_sq_le : epsA q ^ 2 ≤ 25 / 9 * ((1 - q.m) * q.ε ^ 2) := by
  have h1m := one_sub_m_pos q hv
  have hε2 := sq_nonneg q.ε
  rcases le_total (kap q) (4 / 3) with h | h
  · rw [epsA_small q h]
    have := m_bound_small q hv h
    nlinarith
  · have h1 := epsA_large_mul q h
    have h2 := kap_mul q hv
    have hm := m_bound_large q hv h
    have hk2 : 0 < kap q ^ 2 := pow_pos (by linarith) 2
    have h3 : epsA q ^ 2 * (9 * kap q ^ 2) ≤ 25 / 9 * ((1 - q.m) * q.ε ^ 2) * (9 * kap q ^ 2) := by
      rw [h1]
      have : 25 / 9 * ((1 - q.m) * q.ε ^ 2) * (9 * kap q ^ 2) = 25 * q.m * q.ε ^ 2 := by
        linear_combination 25 * q.ε ^ 2 * h2
      rw [this]
      nlinarith
    exact le_of_mul_le_mul_right h3 (by positivity)

lemma failure_constant : 2 * q.ε < 49 / 64 * max (6 * epsA q) (99 / 100 * amp q) := by
  have hε := hv.2.2.2.2.2.2.1
  rcases le_total (kap q) (4 / 3) with h | h
  · have := le_max_left (6 * epsA q) (99 / 100 * amp q)
    rw [epsA_small q h] at this ⊢
    nlinarith
  · have he : amp q = 4 * q.ε := by
      have hkpos : 0 < kap q := by linarith
      unfold amp theta epsA
      rw [max_eq_left h, show kap q * (3 * (4 * q.ε / (3 * kap q))) =
        4 * q.ε * (kap q / kap q) by ring, div_self hkpos.ne', mul_one]
    have := le_max_right (6 * epsA q) (99 / 100 * amp q)
    rw [he] at this ⊢
    nlinarith

lemma bias_budget (g t : ℝ) (ht : theta q * |t| ≤ g) :
    (amp q * t) ^ 2 ≤ q.m * (g ^ 2 + (amp q * t) ^ 2) := by
  have hm0 := hv.2.1
  have h1m := one_sub_m_pos q hv
  have hθ := theta_pos q hv
  have h1 : (theta q * t) ^ 2 ≤ g ^ 2 := by
    rw [← sq_abs (theta q * t), abs_mul, abs_of_pos hθ]
    exact pow_le_pow_left₀ (by positivity) ht 2
  have h2 : (amp q * t) ^ 2 * (1 - q.m) = q.m * (theta q * t) ^ 2 := by
    have hkm := kap_mul q hv
    unfold amp
    linear_combination (theta q * t) ^ 2 * hkm
  nlinarith [mul_le_mul_of_nonneg_left h1 hm0]

lemma abc_valid : LongTails.Setups.HighDimensionalAbcNoiseNonconvex.spec.valid (abcParams q) := by
  obtain ⟨hL, hm0, hm1, hM, hσ, hζ, hε, hfloor, hreg, hdim⟩ := hv
  have hv' : spec.valid q := ⟨hL, hm0, hm1, hM, hσ, hζ, hε, hfloor, hreg, hdim⟩
  have hea := epsA_pos q hv'
  have hle := epsA_le q hv'
  have hge := epsA_sq_ge q hv'
  have h1m := one_sub_m_pos q hv'
  have hΔ : 0 ≤ q.Δ := by
    by_contra hneg
    push Not at hneg
    nlinarith [sq_nonneg q.ε, mul_neg_of_pos_of_neg hL hneg]
  refine ⟨by simp only [abcParams]; positivity, le_rfl, hM, sq_nonneg _, hea, ?_, ?_⟩
  · simp only [abcParams]
    have : epsA q ^ 2 ≤ q.ε ^ 2 := pow_le_pow_left₀ hea.le hle 2
    nlinarith
  · simp only [abcParams]
    set r := (1 - q.m) * q.ε ^ 2 with hr
    have hrpos : 0 < r := by positivity
    have hz : (0 : ℝ) * (q.Δ / 2) / epsA q ^ 2 = 0 := by simp
    have hX : q.L / 2 * (q.Δ / 2) * (1 + q.M + 0 * (q.Δ / 2) / epsA q ^ 2 + q.σ ^ 2 / epsA q ^ 2) /
        epsA q ^ 2 ≤ q.L * q.Δ * (1 + q.M + q.σ ^ 2 / r) / r := by
      rw [hz, add_zero]
      have h1 : q.σ ^ 2 / epsA q ^ 2 ≤ q.σ ^ 2 / r :=
        div_le_div_of_nonneg_left (sq_nonneg _) hrpos hge
      have h2 : 0 ≤ q.L * q.Δ := by positivity
      have hY : 0 ≤ 1 + q.M + q.σ ^ 2 / r := by positivity
      have h3 : q.L / 2 * (q.Δ / 2) * (1 + q.M + q.σ ^ 2 / epsA q ^ 2) ≤
          q.L * q.Δ * (1 + q.M + q.σ ^ 2 / r) := by
        calc q.L / 2 * (q.Δ / 2) * (1 + q.M + q.σ ^ 2 / epsA q ^ 2) ≤
            q.L / 2 * (q.Δ / 2) * (1 + q.M + q.σ ^ 2 / r) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ ≤ q.L * q.Δ * (1 + q.M + q.σ ^ 2 / r) := by nlinarith [mul_nonneg h2 hY]
      calc _ ≤ q.L * q.Δ * (1 + q.M + q.σ ^ 2 / r) / epsA q ^ 2 :=
            div_le_div_of_nonneg_right h3 (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hrpos hge
    have h4 : (1 + q.L / 2 * (q.Δ / 2) * (1 + q.M + 0 * (q.Δ / 2) / epsA q ^ 2 +
        q.σ ^ 2 / epsA q ^ 2) / epsA q ^ 2) ^ 4 ≤
        (1 + q.L * q.Δ * (1 + q.M + q.σ ^ 2 / r) / r) ^ 4 := by
      apply pow_le_pow_left₀ _ (by linarith)
      have : 0 ≤ q.L / 2 * (q.Δ / 2) * (1 + q.M + 0 * (q.Δ / 2) / epsA q ^ 2 +
          q.σ ^ 2 / epsA q ^ 2) / epsA q ^ 2 := by positivity
      linarith
    linarith

end Parameters

end LongTails.Proofs.BiasedLowerInstance
