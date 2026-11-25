import LongTails.Setups.HighDimensionalHeavyTailedHighProbabilityStationarity
import LongTails.Proofs.HeavyTailedHighProbabilityMoments
import LongTails.Proofs.HighProbabilityChainFailure
import LongTails.Proofs.HighProbabilityTwoPointFailure
import LongTails.TemplateLowerBound

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.HeavyTailedHighProbabilityLower

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open LongTails.Setups.HighDimensionalHeavyTailedHighProbabilityStationarity
open LongTails.Proofs.HeavyTailedHighProbabilityMoments
open LongTails.Proofs.AbcChain LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardGeometry
open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcLowerParameters
open LongTails.Proofs.AbcHardContinuity LongTails.Proofs.AbcLowerMeasure

noncomputable def chainRatio (q : Params) : ℝ := tailRatio q.p q.σ (1740 * q.ε)

noncomputable def twoPointRatio (q : Params) : ℝ := tailRatio q.p q.σ (2 * q.ε)

noncomputable def noiseExcess (q : Params) : ℝ := (q.σ / q.ε) ^ (q.p / (q.p - 1))

noncomputable def lowerExcess (q : Params) : ℝ := (q.σ / (2 ^ 12 * q.ε)) ^ (q.p / (q.p - 1))

noncomputable def chainParams (q : Params) :
    LongTails.Setups.HighDimensionalAbcNoiseNonconvex.Params where
  d := q.d
  L := q.L
  A := 0
  B := 0
  C := 1740 ^ 2 * q.ε ^ 2 * (1 + chainRatio q)
  Δ := q.Δ
  ε := q.ε
  x0 := q.x0

noncomputable def pointParams (q : Params) :
    LongTails.Setups.HighDimensionalHighProbabilityStationarity.Params where
  d := q.d
  L := q.L
  σ := 2 * q.ε * Real.sqrt (twoPointRatio q)
  Δ := q.Δ
  ε := q.ε
  δ := q.δ
  x0 := q.x0

section Ratios

variable (q : Params) (hv : spec.valid q)
include hv

lemma ratio_le_excess {a : ℝ} (ha : q.ε ≤ a) : tailRatio q.p q.σ a ≤ noiseExcess q := by
  obtain ⟨hL, hp, hp2, hσ, hε, -⟩ := hv
  have hp1 : 0 < q.p - 1 := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le hε ha
  unfold tailRatio noiseExcess
  have hb : 0 ≤ q.σ / q.ε := div_nonneg hσ hε.le
  have hrw : (q.σ / q.ε) ^ (q.p / (q.p - 1)) = ((q.σ / q.ε) ^ q.p) ^ (1 / (q.p - 1)) := by
    rw [← Real.rpow_mul hb]
    congr 1
    field_simp
  rw [hrw, Real.div_rpow hσ hε.le]
  refine Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg hσ _)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg ha0.le _))) ?_ (by positivity)
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hσ _) (Real.rpow_pos_of_pos hε _)
  have h1 : q.ε ^ q.p ≤ a ^ q.p := Real.rpow_le_rpow hε.le ha (by linarith)
  have h2 := Real.rpow_pos_of_pos hε q.p
  linarith

lemma lower_le_ratio {a : ℝ} (ha0 : 0 < a) (ha : 2 * a ≤ 2 ^ 12 * q.ε) :
    lowerExcess q ≤ tailRatio q.p q.σ a := by
  obtain ⟨hL, hp, hp2, hσ, hε, -⟩ := hv
  refine le_trans ?_ (tailRatio_ge q.p q.σ a hp hσ ha0)
  unfold lowerExcess
  refine Real.rpow_le_rpow (by positivity) ?_ (div_nonneg (by linarith) (by linarith))
  exact div_le_div_of_nonneg_left hσ (by positivity) ha

lemma chainRatio_nonneg : 0 ≤ chainRatio q :=
  tailRatio_nonneg _ _ _ hv.2.2.2.1 (by have := hv.2.2.2.2.1; positivity)

lemma twoPointRatio_nonneg : 0 ≤ twoPointRatio q :=
  tailRatio_nonneg _ _ _ hv.2.2.2.1 (by have := hv.2.2.2.2.1; positivity)

lemma noiseExcess_nonneg : 0 ≤ noiseExcess q := by
  unfold noiseExcess
  exact Real.rpow_nonneg (div_nonneg hv.2.2.2.1 hv.2.2.2.2.1.le) _

lemma lowerExcess_nonneg : 0 ≤ lowerExcess q := by
  unfold lowerExcess
  exact Real.rpow_nonneg (div_nonneg hv.2.2.2.1 (by have := hv.2.2.2.2.1; positivity)) _

lemma chainRatio_le : chainRatio q ≤ noiseExcess q :=
  ratio_le_excess q hv (by have := hv.2.2.2.2.1; linarith)

lemma twoPointRatio_le : twoPointRatio q ≤ noiseExcess q :=
  ratio_le_excess q hv (by have := hv.2.2.2.2.1; linarith)

lemma lower_le_chain : lowerExcess q ≤ chainRatio q :=
  lower_le_ratio q hv (by have := hv.2.2.2.2.1; positivity) (by have := hv.2.2.2.2.1; linarith)

lemma lower_le_twoPoint : lowerExcess q ≤ twoPointRatio q :=
  lower_le_ratio q hv (by have := hv.2.2.2.2.1; positivity) (by have := hv.2.2.2.2.1; linarith)

end Ratios

lemma chainParams_valid (q : Params) (hv : spec.valid q) :
    LongTails.Setups.HighDimensionalAbcNoiseNonconvex.spec.valid (chainParams q) := by
  have ht := chainRatio_nonneg q hv
  have hS := chainRatio_le q hv
  have hS0 := noiseExcess_nonneg q hv
  obtain ⟨hL, hp, hp2, hσ, hε, hδ, hδ1, hreg, hd⟩ := hv
  refine ⟨hL, le_rfl, le_rfl, mul_nonneg (by positivity) (by linarith), hε, ?_, ?_⟩
  · change 2 ^ 26 * q.ε ^ 2 ≤ q.L * q.Δ
    nlinarith [sq_nonneg q.ε]
  · change 2 ^ 40 * (1 + q.L * q.Δ * (1 + 0 + 0 * q.Δ / q.ε ^ 2 +
      1740 ^ 2 * q.ε ^ 2 * (1 + chainRatio q) / q.ε ^ 2) / q.ε ^ 2) ^ 4 ≤ (q.d : ℝ)
    have hε2 : 0 < q.ε ^ 2 := by positivity
    have hLΔ : 0 ≤ q.L * q.Δ := by nlinarith
    have he : 1740 ^ 2 * q.ε ^ 2 * (1 + chainRatio q) / q.ε ^ 2 = 1740 ^ 2 * (1 + chainRatio q) := by
      field_simp
    rw [he]
    simp only [add_zero, zero_mul, zero_div]
    set X := q.L * q.Δ * (1 + noiseExcess q) / q.ε ^ 2
    have hX : 0 ≤ X := by positivity
    have hY : q.L * q.Δ * (1 + 1740 ^ 2 * (1 + chainRatio q)) / q.ε ^ 2 ≤ 2 ^ 22 * X := by
      have h1 : 1 + 1740 ^ 2 * (1 + chainRatio q) ≤ 2 ^ 22 * (1 + noiseExcess q) := by nlinarith
      have h2 : q.L * q.Δ * (1 + 1740 ^ 2 * (1 + chainRatio q)) ≤
          q.L * q.Δ * (2 ^ 22 * (1 + noiseExcess q)) := mul_le_mul_of_nonneg_left h1 hLΔ
      calc q.L * q.Δ * (1 + 1740 ^ 2 * (1 + chainRatio q)) / q.ε ^ 2 ≤
            q.L * q.Δ * (2 ^ 22 * (1 + noiseExcess q)) / q.ε ^ 2 :=
          div_le_div_of_nonneg_right h2 hε2.le
        _ = 2 ^ 22 * X := by simp only [X]; ring
    have hZ : 1 + q.L * q.Δ * (1 + 1740 ^ 2 * (1 + chainRatio q)) / q.ε ^ 2 ≤ 2 ^ 22 * (1 + X) := by
      nlinarith
    have hpow : (1 + q.L * q.Δ * (1 + 1740 ^ 2 * (1 + chainRatio q)) / q.ε ^ 2) ^ 4 ≤
        (2 ^ 22 * (1 + X)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hZ 4
    have hd' : 2 ^ 130 * (1 + X) ^ 4 ≤ (q.d : ℝ) := by
      have : q.L * q.Δ * (1 + (q.σ / q.ε) ^ (q.p / (q.p - 1))) / q.ε ^ 2 = X := rfl
      rw [this] at hd
      exact hd
    calc 2 ^ 40 * (1 + q.L * q.Δ * (1 + 1740 ^ 2 * (1 + chainRatio q)) / q.ε ^ 2) ^ 4 ≤
          2 ^ 40 * (2 ^ 22 * (1 + X)) ^ 4 := mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = 2 ^ 128 * (1 + X) ^ 4 := by ring
      _ ≤ 2 ^ 130 * (1 + X) ^ 4 := by
          have : 0 ≤ (1 + X) ^ 4 := by positivity
          nlinarith
      _ ≤ (q.d : ℝ) := hd'

lemma revealProb_chain (q : Params) (hv : spec.valid q) (n m : ℕ) :
    revealProb (chainParams q) n m = 1 / (1 + chainRatio q) := by
  have ht := chainRatio_nonneg q hv
  have hε := hv.2.2.2.2.1
  unfold revealProb secretScale levelBudget
  change 1740 ^ 2 * q.ε ^ 2 / max (1740 ^ 2 * q.ε ^ 2)
    (6 * 0 * amplitude (chainParams q) * ((n : ℝ) - m) + 9 * 0 * q.ε ^ 2 +
      1740 ^ 2 * q.ε ^ 2 * (1 + chainRatio q)) = 1 / (1 + chainRatio q)
  have hle : 1740 ^ 2 * q.ε ^ 2 ≤ 6 * 0 * amplitude (chainParams q) * ((n : ℝ) - m) +
      9 * 0 * q.ε ^ 2 + 1740 ^ 2 * q.ε ^ 2 * (1 + chainRatio q) := by
    have : 0 ≤ 1740 ^ 2 * q.ε ^ 2 * chainRatio q := by positivity
    nlinarith
  rw [max_eq_right hle]
  have : 0 < q.ε ^ 2 := by positivity
  field_simp
  ring

open LongTails.Proofs.AbcLowerAssembly in
lemma chain_moment (q : Params) (hv : spec.valid q) (π : Fin (chainDim (chainParams q) + 1) ↪ Fin q.d)
    (x : EuclideanSpace ℝ (Fin q.d)) :
    Integrable (fun ω => ‖reply (scaleOf (chainParams q) hv.1 hv.2.2.2.2.1)
      (revealProb (chainParams q) (chainDim (chainParams q))) π q.x0 x ω -
        gradient (objective (scaleOf (chainParams q) hv.1 hv.2.2.2.2.1) π q.x0) x‖ ^ q.p) unif ∧
    ∫ ω, ‖reply (scaleOf (chainParams q) hv.1 hv.2.2.2.2.1)
      (revealProb (chainParams q) (chainDim (chainParams q))) π q.x0 x ω -
        gradient (objective (scaleOf (chainParams q) hv.1 hv.2.2.2.2.1) π q.x0) x‖ ^ q.p ∂unif ≤
      q.σ ^ q.p := by
  have ht := chainRatio_nonneg q hv
  have hp := hv.2.1
  have hp2 := hv.2.2.1
  have hσ := hv.2.2.2.1
  have hε := hv.2.2.2.2.1
  set S := scaleOf (chainParams q) hv.1 hv.2.2.2.2.1 with hSdef
  have hratio : S.a / S.lam = 60 * q.ε := amplitude_ratio (chainParams q) hv.1 hε
  rw [objective_gradient]
  set m := stage (sel π (toUnit S q.x0 x)) with hm
  set v := objGrad S π q.x0 x - knownPart S π m q.x0 x with hvdef
  have he : (fun ω => ‖reply S (revealProb (chainParams q) (chainDim (chainParams q))) π q.x0 x ω -
      objGrad S π q.x0 x‖ ^ q.p) = fun ω => ‖(coin (1 / (1 + chainRatio q)) ω - 1) • v‖ ^ q.p := by
    funext ω
    rw [← revealProb_chain q hv (chainDim (chainParams q)) m]
    have : reply S (revealProb (chainParams q) (chainDim (chainParams q))) π q.x0 x ω -
        objGrad S π q.x0 x = (coin (revealProb (chainParams q) (chainDim (chainParams q)) m) ω - 1) • v := by
      simp only [reply, v, m, sub_smul, one_smul]
      abel
    rw [this]
  rw [he]
  have hsec := secret_norm S π q.x0 x
  rw [hratio] at hsec
  have hvn : ‖v‖ ≤ 1740 * q.ε := le_of_le_of_eq hsec (by ring)
  obtain ⟨h1, h2⟩ := coin_moment (chainRatio q) q.p (1740 * q.ε) ht hp hp2 v hvn
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  have h := tailRatio_rpow q.p q.σ (1740 * q.ε) hp hσ (by positivity)
  unfold chainRatio
  linarith

open LongTails.Proofs.AbcLowerAssembly in
lemma chain_admissible (q : Params) (hv : spec.valid q)
    (π : Fin (chainDim (chainParams q) + 1) ↪ Fin q.d) :
    spec.admissible q
      (objective (scaleOf (chainParams q) hv.1 hv.2.2.2.2.1) π q.x0)
      (hardOracle (chainParams q) (scaleOf (chainParams q) hv.1 hv.2.2.2.2.1) π) := by
  have hv' := chainParams_valid q hv
  have hL := hv.1
  have hε := hv.2.2.2.2.1
  set S := scaleOf (chainParams q) hv.1 hv.2.2.2.2.1
  have hn1 := chainDim_succ (chainParams q) hv'
  have hsmooth : 1024 * S.a / S.lam ^ 2 = q.L := smoothness_eq (chainParams q) hL hε
  let fstar : ℝ := S.a * (-3 * (((chainDim (chainParams q)) : ℝ) + 1))
  refine ⟨fun x ω => reply S (revealProb (chainParams q) (chainDim (chainParams q))) π q.x0 x ω,
    ⟨unif, inferInstanceAs (IsProbabilityMeasure unif)⟩,
    ⟨stream, inferInstanceAs (IsProbabilityMeasure stream)⟩, fstar, stream_iid, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try dsimp only [toGeneral]
  · intro x
    first | simp only [objective_gradient] | erw [objective_gradient]
    exact objective_hasGradientAt S π q.x0 x
  · intro x y
    first | simp only [objective_gradient] | erw [objective_gradient, objective_gradient]
    rw [← hsmooth]
    exact objGrad_lipschitz S π q.x0 x y
  · intro x
    exact mul_le_mul_of_nonneg_left (hardValue_lower π _) S.ha.le
  · intro η hη
    refine ⟨q.x0 + S.lam • hardMinimizer π, ?_⟩
    have ht' : toUnit S q.x0 (q.x0 + S.lam • hardMinimizer π) = hardMinimizer π := by
      simp only [toUnit, add_sub_cancel_left, smul_smul, one_div, inv_mul_cancel₀ S.hlam.ne',
        one_smul]
    simp only [objective, ht', hardValue_minimizer, fstar]
    linarith
  · have ht' : toUnit S q.x0 q.x0 = 0 := by simp [toUnit]
    simp only [objective, ht', hardValue_zero, fstar]
    have h := amplitude_chain_le (chainParams q) hv'
    have hc : (((chainDim (chainParams q)) : ℝ) + 1) = chainLength (chainParams q) := by
      rw [← hn1]; push_cast; ring
    rw [hc]
    have : S.a = amplitude (chainParams q) := rfl
    rw [this]
    have h' : 3 * amplitude (chainParams q) * chainLength (chainParams q) ≤ q.Δ := h
    nlinarith [S.ha]
  · exact reply_measurable S _ π q.x0
  · intro x
    exact reply_integrable S _ π q.x0 x
  · intro x
    first | simp only [objective_gradient] | erw [objective_gradient]
    exact reply_integral S _ (revealProb_pos (chainParams q) hε _)
      (revealProb_le (chainParams q) hε _) π q.x0 x
  · intro x
    exact (chain_moment q hv π x).1
  · intro x
    exact (chain_moment q hv π x).2

section TwoPoint

open LongTails.Proofs.HighProbabilityTwoPointFailure

lemma pointParams_valid (q : Params) (hv : spec.valid q) :
    LongTails.Setups.HighDimensionalHighProbabilityStationarity.spec.valid (pointParams q) := by
  have ht := twoPointRatio_nonneg q hv
  have hS := twoPointRatio_le q hv
  have hS0 := noiseExcess_nonneg q hv
  obtain ⟨hL, hp, hp2, hσ, hε, hδ, hδ1, hreg, hd⟩ := hv
  refine ⟨hL, by change 0 ≤ 2 * q.ε * Real.sqrt (twoPointRatio q); positivity, hε, hδ, hδ1, hreg, ?_⟩
  change 2 ^ 40 * (1 + q.L * q.Δ * (1 + (2 * q.ε * Real.sqrt (twoPointRatio q)) ^ 2 / q.ε ^ 2) /
    q.ε ^ 2) ^ 4 ≤ (q.d : ℝ)
  have hε2 : 0 < q.ε ^ 2 := by positivity
  have hLΔ : 0 ≤ q.L * q.Δ := by nlinarith
  have he : (2 * q.ε * Real.sqrt (twoPointRatio q)) ^ 2 / q.ε ^ 2 = 4 * twoPointRatio q := by
    rw [mul_pow, Real.sq_sqrt ht]
    field_simp
    ring
  rw [he]
  set X := q.L * q.Δ * (1 + noiseExcess q) / q.ε ^ 2
  have hX : 0 ≤ X := by positivity
  have hY : q.L * q.Δ * (1 + 4 * twoPointRatio q) / q.ε ^ 2 ≤ 4 * X := by
    have h1 : 1 + 4 * twoPointRatio q ≤ 4 * (1 + noiseExcess q) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hLΔ
    calc q.L * q.Δ * (1 + 4 * twoPointRatio q) / q.ε ^ 2 ≤
          q.L * q.Δ * (4 * (1 + noiseExcess q)) / q.ε ^ 2 := div_le_div_of_nonneg_right h2 hε2.le
      _ = 4 * X := by simp only [X]; ring
  have hZ : 1 + q.L * q.Δ * (1 + 4 * twoPointRatio q) / q.ε ^ 2 ≤ 4 * (1 + X) := by nlinarith
  have hpow := pow_le_pow_left₀ (by positivity) hZ 4
  have hd' : 2 ^ 130 * (1 + X) ^ 4 ≤ (q.d : ℝ) := hd
  have h0 : 0 ≤ (1 + X) ^ 4 := by positivity
  calc 2 ^ 40 * (1 + q.L * q.Δ * (1 + 4 * twoPointRatio q) / q.ε ^ 2) ^ 4 ≤
        2 ^ 40 * (4 * (1 + X)) ^ 4 := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ 2 ^ 130 * (1 + X) ^ 4 := by nlinarith
    _ ≤ (q.d : ℝ) := hd'

lemma revealLevel_point (q : Params) (hv : spec.valid q) :
    revealLevel (pointParams q).σ (pointParams q).ε = 1 / (1 + twoPointRatio q) := by
  have ht := twoPointRatio_nonneg q hv
  have hε := hv.2.2.2.2.1
  change revealLevel (2 * q.ε * Real.sqrt (twoPointRatio q)) q.ε = 1 / (1 + twoPointRatio q)
  unfold revealLevel
  rw [mul_pow, mul_pow, Real.sq_sqrt ht]
  have : 0 < q.ε ^ 2 := by positivity
  field_simp
  ring

lemma point_moment (q : Params) (hv : spec.valid q) (hd : 0 < (pointParams q).d) (s : ℝ)
    (hs : s * s = 1) (x : EuclideanSpace ℝ (Fin (pointParams q).d)) :
    Integrable (fun ω => ‖hardReply (pointParams q) hd s x ω -
      gradient (hardObjective (pointParams q) hd s) x‖ ^ q.p) unif ∧
    ∫ ω, ‖hardReply (pointParams q) hd s x ω -
      gradient (hardObjective (pointParams q) hd s) x‖ ^ q.p ∂unif ≤ q.σ ^ q.p := by
  have ht := twoPointRatio_nonneg q hv
  have hp := hv.2.1
  have hp2 := hv.2.2.1
  have hσ := hv.2.2.2.1
  have hε : 0 < (pointParams q).ε := hv.2.2.2.2.1
  have hnoise (ω : ℝ) :
      hardReply (pointParams q) hd s x ω - gradient (hardObjective (pointParams q) hd s) x =
        (coin (1 / (1 + twoPointRatio q)) ω - 1) •
          ((2 * s * (pointParams q).ε) • unitVector (pointParams q).d hd) := by
    rw [hardReply_noise, smul_smul, revealLevel_point q hv]
    congr 1
    change 2 * s * (pointParams q).ε * (coin (1 / (1 + twoPointRatio q)) ω - 1) = _
    ring
  have hvnorm : ‖(2 * s * (pointParams q).ε) • unitVector (pointParams q).d hd‖ ≤ 2 * q.ε := by
    rw [norm_smul, unitVector_norm, mul_one, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hε]
    have : |s| = 1 := by
      have h0 : |s| * |s| = 1 := by rw [← abs_mul, hs, abs_one]
      have h1 : 0 ≤ |s| := abs_nonneg s
      nlinarith
    rw [this]
    norm_num
    rfl
  have he : (fun ω => ‖hardReply (pointParams q) hd s x ω -
      gradient (hardObjective (pointParams q) hd s) x‖ ^ q.p) = fun ω =>
        ‖(coin (1 / (1 + twoPointRatio q)) ω - 1) •
          ((2 * s * (pointParams q).ε) • unitVector (pointParams q).d hd)‖ ^ q.p := by
    funext ω
    rw [hnoise ω]
  rw [he]
  obtain ⟨h1, h2⟩ := coin_moment (twoPointRatio q) q.p (2 * q.ε) ht hp hp2 _ hvnorm
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  have h := tailRatio_rpow q.p q.σ (2 * q.ε) hp hσ (by positivity)
  unfold twoPointRatio
  linarith

lemma point_admissible (q : Params) (hv : spec.valid q) (hd : 0 < (pointParams q).d) (s : ℝ)
    (hs : s * s = 1) :
    spec.admissible q (hardObjective (pointParams q) hd s) (hardOracle (pointParams q) hd s) := by
  have hε : 0 < (pointParams q).ε := hv.2.2.2.2.1
  have hL : 0 < (pointParams q).L := hv.1
  have hreg : 2 ^ 54 * (pointParams q).ε ^ 2 ≤ (pointParams q).L * (pointParams q).Δ :=
    hv.2.2.2.2.2.2.2.1
  refine ⟨hardReply (pointParams q) hd s, ⟨unif, inferInstanceAs (IsProbabilityMeasure unif)⟩,
    ⟨stream, inferInstanceAs (IsProbabilityMeasure stream)⟩, -(2 * q.ε ^ 2 / q.L), stream_iid,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try dsimp only [toGeneral]
  · exact fun x => hardObjective_hasGradient (pointParams q) hd s x
  · exact fun x y => hard_lipschitz (pointParams q) hd s hL x y
  · exact fun x => hard_lower (pointParams q) hd s hs hL x
  · exact fun η hη => hard_inf (pointParams q) hd s hs hL η hη
  · exact hard_gap (pointParams q) hd s hL hreg
  · exact measurable_hardReply (pointParams q) hd s
  · exact fun x => hardReply_integrable (pointParams q) hd s hε x
  · exact fun x => hard_mean (pointParams q) hd s hε x
  · exact fun x => (point_moment q hv hd s hs x).1
  · exact fun x => (point_moment q hv hd s hs x).2

end TwoPoint

lemma lowerBudget_ge (q : Params) (hv : spec.valid q) :
    (1 + lowerExcess q) * q.L * q.Δ / q.ε ^ 2 ≤
      q.L * q.Δ * (1 + 0 + 0 * q.Δ / q.ε ^ 2 + (chainParams q).C / q.ε ^ 2) / q.ε ^ 2 := by
  have hle := lower_le_chain q hv
  have ht := chainRatio_nonneg q hv
  have hε := hv.2.2.2.2.1
  have hε2 : 0 < q.ε ^ 2 := by positivity
  have hLΔ : 0 ≤ q.L * q.Δ := by nlinarith [hv.2.2.2.2.2.2.2.1]
  have hC : (chainParams q).C / q.ε ^ 2 = 1740 ^ 2 * (1 + chainRatio q) := by
    change 1740 ^ 2 * q.ε ^ 2 * (1 + chainRatio q) / q.ε ^ 2 = _
    field_simp
  rw [hC]
  refine div_le_div_of_nonneg_right ?_ hε2.le
  have h1 : 1 + lowerExcess q ≤ 1 + 0 + 0 * q.Δ / q.ε ^ 2 + 1740 ^ 2 * (1 + chainRatio q) := by
    simp only [zero_mul, zero_div, add_zero]
    nlinarith
  calc (1 + lowerExcess q) * q.L * q.Δ = q.L * q.Δ * (1 + lowerExcess q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 hLΔ

lemma budget_split (q : Params) (hv : spec.valid q) (N : ℕ)
    (hN : N ≤ ⌊((1 + lowerExcess q) * q.L * q.Δ / q.ε ^ 2 +
      lowerExcess q * Real.log (1 / (4 * q.δ))) / 2 ^ 55⌋₊)
    (hbig : LongTails.Proofs.AbcLowerParameters.lowerBudget (chainParams q) < N) :
    (N : ℝ) * (8 * q.ε ^ 2) ≤ (pointParams q).σ ^ 2 * Real.log (1 / (4 * q.δ)) := by
  have hX0 := lowerBudget_ge q hv
  have hlt := lower_le_twoPoint q hv
  have hS0 := lowerExcess_nonneg q hv
  have ht := twoPointRatio_nonneg q hv
  have hε := hv.2.2.2.2.1
  have hδ := hv.2.2.2.2.2.1
  have hδ1 := hv.2.2.2.2.2.2.1
  have hε2 : 0 < q.ε ^ 2 := by positivity
  have hLΔ : 0 ≤ q.L * q.Δ := by nlinarith [hv.2.2.2.2.2.2.2.1]
  have hlog : 0 ≤ Real.log (1 / (4 * q.δ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
  set X := (1 + lowerExcess q) * q.L * q.Δ / q.ε ^ 2
  set Y := lowerExcess q * Real.log (1 / (4 * q.δ))
  have hX : 0 ≤ X := div_nonneg (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 + lowerExcess q) hLΔ]) hε2.le
  have hY0 : 0 ≤ Y := mul_nonneg hS0 hlog
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlow : (X / 2 ^ 53 : ℝ) < N := by
    have h1 := Nat.lt_floor_add_one
      (q.L * q.Δ * (1 + 0 + 0 * q.Δ / q.ε ^ 2 + (chainParams q).C / q.ε ^ 2) / (2 ^ 53 * q.ε ^ 2))
    have h2 : (LongTails.Proofs.AbcLowerParameters.lowerBudget (chainParams q) : ℝ) + 1 ≤ N := by
      exact_mod_cast hbig
    have h3 : X / 2 ^ 53 ≤
        q.L * q.Δ * (1 + 0 + 0 * q.Δ / q.ε ^ 2 + (chainParams q).C / q.ε ^ 2) / (2 ^ 53 * q.ε ^ 2) := by
      have he : q.L * q.Δ * (1 + 0 + 0 * q.Δ / q.ε ^ 2 + (chainParams q).C / q.ε ^ 2) /
          (2 ^ 53 * q.ε ^ 2) = q.L * q.Δ * (1 + 0 + 0 * q.Δ / q.ε ^ 2 + (chainParams q).C / q.ε ^ 2) /
            q.ε ^ 2 / 2 ^ 53 := by ring
      rw [he]
      exact div_le_div_of_nonneg_right hX0 (by norm_num)
    have h4 : (LongTails.Proofs.AbcLowerParameters.lowerBudget (chainParams q) : ℝ) =
        (⌊q.L * q.Δ * (1 + 0 + 0 * q.Δ / q.ε ^ 2 + (chainParams q).C / q.ε ^ 2) /
          (2 ^ 53 * q.ε ^ 2)⌋₊ : ℝ) := rfl
    linarith
  have hY : (N : ℝ) ≤ (X + Y) / 2 ^ 55 :=
    (Nat.cast_le.mpr hN).trans (Nat.floor_le (by positivity))
  have hNY : (N : ℝ) ≤ Y / 2 ^ 54 := by
    rw [le_div_iff₀ (by norm_num)] at hY
    rw [div_lt_iff₀ (by norm_num)] at hlow
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hσ2 : (pointParams q).σ ^ 2 = 4 * q.ε ^ 2 * twoPointRatio q := by
    change (2 * q.ε * Real.sqrt (twoPointRatio q)) ^ 2 = _
    rw [mul_pow, mul_pow, Real.sq_sqrt ht]
    ring
  rw [hσ2]
  have hYt : Y ≤ twoPointRatio q * Real.log (1 / (4 * q.δ)) :=
    mul_le_mul_of_nonneg_right hlt hlog
  have h5 : (N : ℝ) ≤ twoPointRatio q * Real.log (1 / (4 * q.δ)) / 2 ^ 54 :=
    hNY.trans (div_le_div_of_nonneg_right hYt (by norm_num))
  have h6 : 0 ≤ twoPointRatio q * Real.log (1 / (4 * q.δ)) := mul_nonneg ht hlog
  calc (N : ℝ) * (8 * q.ε ^ 2) ≤ twoPointRatio q * Real.log (1 / (4 * q.δ)) / 2 ^ 54 *
        (8 * q.ε ^ 2) := mul_le_mul_of_nonneg_right h5 (by positivity)
    _ ≤ 4 * q.ε ^ 2 * twoPointRatio q * Real.log (1 / (4 * q.δ)) := by
        nlinarith [mul_nonneg h6 hε2.le]

lemma nonConvergence :
    NonConvergence spec (fun q _ => ⌊((1 + lowerExcess q) * q.L * q.Δ / q.ε ^ 2 +
      lowerExcess q * Real.log (1 / (4 * q.δ))) / 2 ^ 55⌋₊) := by
  intro q hv A _ b hb
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  have hδ1 : q.δ ≤ 1 / 4 := hv.2.2.2.2.2.2.1
  by_cases hsmall : b 0 ≤ LongTails.Proofs.AbcLowerParameters.lowerBudget (chainParams q)
  · have hv' := chainParams_valid q hv
    obtain ⟨π, hπ⟩ := LongTails.Proofs.HighProbabilityChainFailure.exists_hp_failure
      (chainParams q) hv' A (b 0) hsmall
    refine ⟨_, _, chain_admissible q hv π, ?_⟩
    intro _ hs
    apply hπ
    refine ⟨hs.1, ?_⟩
    have h2 := hs.2
    change 1 - q.δ ≤ _ at h2
    exact le_trans (by linarith) h2
  · push Not at hsmall
    have hN := budget_split q hv (b 0) (hb 0) hsmall
    have hd : 0 < (pointParams q).d := by
      have h : 2 ^ 130 * (1 + q.L * q.Δ * (1 + noiseExcess q) / q.ε ^ 2) ^ 4 ≤ (q.d : ℝ) :=
        hv.2.2.2.2.2.2.2.2
      have hLΔ : 0 ≤ q.L * q.Δ := by nlinarith [hv.2.2.2.2.2.2.2.1, sq_nonneg q.ε]
      have hA : 0 ≤ q.L * q.Δ * (1 + noiseExcess q) / q.ε ^ 2 :=
        div_nonneg (mul_nonneg hLΔ (by linarith [noiseExcess_nonneg q hv])) (sq_nonneg _)
      have hpos : (0 : ℝ) < q.d :=
        lt_of_lt_of_le (mul_pos (by norm_num) (pow_pos (by linarith) 4)) h
      exact_mod_cast hpos
    obtain ⟨s, hs, hfail⟩ := LongTails.Proofs.HighProbabilityTwoPointFailure.exists_failure
      (pointParams q) (pointParams_valid q hv) A (b 0) hN hd
    exact ⟨_, _, point_admissible q hv hd s hs, hfail⟩

end LongTails.Proofs.HeavyTailedHighProbabilityLower
