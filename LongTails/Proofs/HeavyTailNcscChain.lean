import LongTails.Setups.HighDimensionalHeavyTailedNcsc
import LongTails.Proofs.HeavyTailNcscLift
import LongTails.Proofs.HighProbabilityChainFailure
import LongTails.Proofs.HeavyTailSaddleGeometry

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailNcscChain

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open LongTails.Setups.HighDimensionalHeavyTailedNcsc
open LongTails.Proofs.HeavyTailNcscLift
open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcChainMask
open LongTails.Proofs.AbcLowerMeasure LongTails.Proofs.AbcLowerParameters
open LongTails.Proofs.AbcLowerAssembly LongTails.Proofs.AbcHardContinuity

noncomputable def gam (q : Params) : ℝ := Real.sqrt (q.L / q.μ) / 2

noncomputable def hh (q : Params) : ℝ := q.μ / (4 * q.L)

noncomputable def nu (q : Params) : ℝ := 5 * q.μ / 4

noncomputable def qq (q : Params) : ℝ := 6 / (5 * gam q)

noncomputable def al (q : Params) : ℝ := qq q ^ 2 / hh q

noncomputable def be (q : Params) : ℝ := hh q / qq q

noncomputable def rr (q : Params) : ℝ := q.p / (q.p - 1)

noncomputable def KK (q : Params) : ℝ := Real.sqrt (q.L / q.μ) * (q.σ / q.ε) / 8352

noncomputable def chainParams (q : Params) : LongTails.Setups.HighDimensionalAbcNoiseNonconvex.Params where
  d := q.d
  L := q.L
  A := 0
  B := 0
  C := 2 * 1740 ^ 2 * q.ε ^ 2 * KK q ^ rr q
  Δ := 25 * q.Δ / 1152
  ε := q.ε
  x0 := 0

section constants

variable {q : Params} (hv : spec.valid q)
include hv

lemma mu_pos : 0 < q.μ := hv.1.1

lemma L_pos : 0 < q.L := lt_of_lt_of_le hv.1.1 hv.1.2.1

lemma eps_pos : 0 < q.ε := hv.1.2.2.2.2.2.2.2.1

lemma kappa_ge : 8 ≤ q.L / q.μ := by
  rw [le_div_iff₀ (mu_pos hv)]; linarith [hv.2.2.1]

lemma gam_pos : 0 < gam q := by
  unfold gam
  have := kappa_ge hv
  positivity

lemma gam_sq : gam q ^ 2 = q.L / (4 * q.μ) := by
  unfold gam
  rw [div_pow, Real.sq_sqrt (by have := kappa_ge hv; positivity)]
  field_simp
  ring

lemma hh_pos : 0 < hh q := by
  unfold hh; have := mu_pos hv; have := L_pos hv; positivity

lemma nu_pos : 0 < nu q := by unfold nu; have := mu_pos hv; positivity

lemma qq_pos : 0 < qq q := by unfold qq; have := gam_pos hv; positivity

lemma al_pos : 0 < al q := by unfold al; have := qq_pos hv; have := hh_pos hv; positivity

lemma be_pos : 0 < be q := by unfold be; have := qq_pos hv; have := hh_pos hv; positivity

lemma al_be : al q * be q = qq q := by
  unfold al be
  have := qq_pos hv; have := hh_pos hv
  field_simp

lemma al_be_sq : al q * be q ^ 2 = hh q := by
  unfold al be
  have := qq_pos hv; have := hh_pos hv
  field_simp

lemma qq_be : qq q * be q = hh q := by
  unfold be
  have := qq_pos hv
  field_simp

lemma gam_qq : gam q * qq q = 6 / 5 := by
  unfold qq
  have := gam_pos hv
  field_simp

lemma nu_sub : nu q - hh q * q.L = q.μ := by
  unfold nu hh
  have := L_pos hv
  field_simp
  ring

lemma smooth_const :
    (nu q * gam q ^ 2) ^ 2 + 2 * (nu q * gam q) ^ 2 + (qq q * be q * q.L + nu q) ^ 2 ≤ q.L ^ 2 := by
  have hμ := mu_pos hv
  have hL := L_pos hv
  have h8 : 8 * q.μ ≤ q.L := hv.2.2.1
  have hg := gam_sq hv
  have h1 : (nu q * gam q ^ 2) ^ 2 = 25 / 256 * q.L ^ 2 := by
    rw [mul_pow, hg]; unfold nu; field_simp; ring
  have h2 : 2 * (nu q * gam q) ^ 2 = 25 / 32 * q.μ * q.L := by
    rw [mul_pow, hg]; unfold nu; field_simp; ring
  have h3 : qq q * be q * q.L + nu q = 3 / 2 * q.μ := by
    rw [qq_be hv]; unfold hh nu; field_simp; ring
  rw [h1, h2, h3]
  nlinarith

lemma transfer_const : (nu q + qq q * be q * q.L) / (nu q * gam q * qq q) = 1 := by
  have h3 : nu q + qq q * be q * q.L = 3 / 2 * q.μ := by
    rw [qq_be hv]; unfold hh nu; have := L_pos hv; field_simp; ring
  rw [h3, mul_assoc, gam_qq hv]
  unfold nu
  have := mu_pos hv
  field_simp
  ring

lemma qq_eps : qq q * (1740 * q.ε) = 4176 * q.ε / Real.sqrt (q.L / q.μ) := by
  unfold qq gam
  have hs : 0 < Real.sqrt (q.L / q.μ) := by have := kappa_ge hv; positivity
  field_simp
  ring

lemma chain_delta : al q * (25 * q.Δ / 1152) = q.Δ / 2 := by
  unfold al
  rw [div_mul_eq_mul_div, qq, div_pow, hh]
  have hμ := mu_pos hv
  have hL := L_pos hv
  have hg := gam_sq hv
  have hg0 := gam_pos hv
  field_simp
  rw [hg]
  field_simp
  ring

lemma init_term : qq q ^ 2 * (1740 * q.ε) ^ 2 / (2 * q.μ) ≤ q.Δ / 2 := by
  have hμ := mu_pos hv
  have hL := L_pos hv
  have hreg : 2 ^ 32 * q.ε ^ 2 ≤ q.L * q.Δ := hv.2.2.2.1
  have hq2 : qq q ^ 2 = 144 * q.μ / (25 * q.L) := by
    unfold qq
    rw [div_pow, mul_pow, gam_sq hv]
    field_simp
    ring
  rw [hq2, div_le_div_iff₀ (by positivity) (by norm_num)]
  have he : 0 ≤ q.ε ^ 2 := sq_nonneg _
  field_simp
  nlinarith

lemma sigma_nonneg : 0 ≤ q.σ := hv.1.2.2.2.2.1

lemma rr_ge_two : 2 ≤ rr q := by
  have hp1 : 1 < q.p := hv.1.2.2.1
  have hp2 : q.p ≤ 2 := hv.1.2.2.2.1
  unfold rr
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma rr_mul : rr q * (q.p - 1) = q.p := by
  have hp1 : 1 < q.p := hv.1.2.2.1
  unfold rr
  exact div_mul_cancel₀ _ (by linarith)

lemma KK_nonneg : 0 ≤ KK q := by
  unfold KK
  have := sigma_nonneg hv
  have := eps_pos hv
  positivity

lemma KK_rpow_le :
    2 * 1740 ^ 2 * KK q ^ rr q ≤ (Real.sqrt (q.L / q.μ) * (q.σ / q.ε)) ^ rr q := by
  have hs : 0 ≤ Real.sqrt (q.L / q.μ) * (q.σ / q.ε) := by
    have := sigma_nonneg hv; have := eps_pos hv; positivity
  have hK : KK q ^ rr q = (Real.sqrt (q.L / q.μ) * (q.σ / q.ε)) ^ rr q / 8352 ^ rr q := by
    unfold KK
    exact Real.div_rpow hs (by norm_num) _
  have h8 : (8352 : ℝ) ^ (2 : ℝ) ≤ 8352 ^ rr q :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (rr_ge_two hv)
  rw [Real.rpow_two] at h8
  have hX : 0 ≤ (Real.sqrt (q.L / q.μ) * (q.σ / q.ε)) ^ rr q := Real.rpow_nonneg hs _
  rw [hK, mul_div_assoc']
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma chainParams_valid :
    LongTails.Setups.HighDimensionalAbcNoiseNonconvex.spec.valid (chainParams q) := by
  have hL := L_pos hv
  have hε := eps_pos hv
  have hreg : 2 ^ 32 * q.ε ^ 2 ≤ q.L * q.Δ := hv.2.2.2.1
  have hd := hv.2.2.2.2.2
  have hK : 2 * 1740 ^ 2 * KK q ^ rr q ≤
      (Real.sqrt (q.L / q.μ) * (q.σ / q.ε)) ^ (q.p / (q.p - 1)) := KK_rpow_le hv
  have hKn : 0 ≤ KK q ^ rr q := Real.rpow_nonneg (KK_nonneg hv) _
  have hA : 0 ≤ q.L * q.Δ / q.ε ^ 2 := by
    have : 0 ≤ q.L * q.Δ := le_trans (by positivity) hreg
    positivity
  have hΔ : 0 ≤ q.Δ := by
    have : 0 ≤ q.L * q.Δ := le_trans (by positivity) hreg
    nlinarith
  refine ⟨hL, le_rfl, le_rfl, by simp only [chainParams]; positivity, hε, ?_, ?_⟩
  · change 2 ^ 26 * q.ε ^ 2 ≤ q.L * (25 * q.Δ / 1152)
    nlinarith [sq_nonneg q.ε]
  · change 2 ^ 40 * (1 + q.L * (25 * q.Δ / 1152) * (1 + 0 + 0 * (25 * q.Δ / 1152) / q.ε ^ 2 +
      2 * 1740 ^ 2 * q.ε ^ 2 * KK q ^ rr q / q.ε ^ 2) / q.ε ^ 2) ^ 4 ≤ (q.d : ℝ)
    refine le_trans ?_ hd
    have he : q.L * (25 * q.Δ / 1152) * (1 + 0 + 0 * (25 * q.Δ / 1152) / q.ε ^ 2 +
        2 * 1740 ^ 2 * q.ε ^ 2 * KK q ^ rr q / q.ε ^ 2) / q.ε ^ 2 =
        25 / 1152 * (q.L * q.Δ / q.ε ^ 2) * (1 + 2 * 1740 ^ 2 * KK q ^ rr q) := by
      field_simp
      ring
    rw [he]
    have h1 : 25 / 1152 * (q.L * q.Δ / q.ε ^ 2) * (1 + 2 * 1740 ^ 2 * KK q ^ rr q) ≤
        q.L * q.Δ / q.ε ^ 2 * (1 + (Real.sqrt (q.L / q.μ) * (q.σ / q.ε)) ^ (q.p / (q.p - 1))) := by
      have h2 := mul_le_mul_of_nonneg_left (add_le_add_left hK 1) hA
      nlinarith [mul_nonneg hA (add_nonneg zero_le_one hKn)]
    gcongr

end constants


lemma two_value_integral {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a b : ℝ) :
    Integrable (fun ω : ℝ => if ω ≤ t then a else b) unif ∧
      ∫ ω, (if ω ≤ t then a else b) ∂unif = t * a + (1 - t) * b := by
  have he : (fun ω : ℝ => if ω ≤ t then a else b) =
      fun ω => Set.indicator {ω | ω ≤ t} (fun _ => a - b) ω + b := by
    funext ω
    simp only [Set.indicator, Set.mem_ofPred_eq]
    split_ifs <;> ring
  have hi : Integrable (fun ω : ℝ => Set.indicator {ω | ω ≤ t} (fun _ => a - b) ω + b) unif :=
    ((integrable_const (a - b)).indicator (setOf_le_measurable t)).add (integrable_const b)
  refine ⟨he ▸ hi, ?_⟩
  rw [he, integral_add ((integrable_const (a - b)).indicator (setOf_le_measurable t))
    (integrable_const b), integral_indicator (setOf_le_measurable _), setIntegral_const,
    unif_real_le t ht0 ht1, integral_const, probReal_univ, smul_eq_mul, smul_eq_mul]
  ring

lemma moment_scalar {t a p : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (ha : 0 ≤ a) (hp : 1 ≤ p) :
    t * ((1 / t - 1) * a) ^ p + (1 - t) * a ^ p ≤ 2 * t ^ (1 - p) * a ^ p := by
  have hb : 0 ≤ (1 / t - 1) * a := mul_nonneg (by rw [sub_nonneg, le_div_iff₀ ht0]; linarith) ha
  have h1 : ((1 / t - 1) * a) ^ p ≤ (a / t) ^ p := by
    apply Real.rpow_le_rpow hb _ (by linarith)
    rw [show (1 / t - 1) * a = a / t - a by ring]
    linarith
  have h2 : t * (a / t) ^ p = t ^ (1 - p) * a ^ p := by
    rw [Real.div_rpow ha ht0.le, Real.rpow_sub ht0, Real.rpow_one]
    field_simp
  have h3 : 1 ≤ t ^ (1 - p) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith)
  have hap : 0 ≤ a ^ p := Real.rpow_nonneg ha _
  have h4 : (1 - t) * a ^ p ≤ t ^ (1 - p) * a ^ p := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 ht0.le]

section hardInstance

variable (q : Params) (hv : spec.valid q)

abbrev Sp := EuclideanSpace ℝ (Fin q.d)

noncomputable def scl : Scale := scaleOf (chainParams q) (L_pos hv) (eps_pos hv)

noncomputable abbrev nDim : ℕ := chainDim (chainParams q)

noncomputable def qf : ℕ → ℝ := revealProb (chainParams q) (nDim q)

noncomputable def liftedF (π : Fin (nDim q + 1) ↪ Fin q.d) : Sp q → Sp q → ℝ :=
  lift (objective (scl q hv) π 0) (al q) (be q) (nu q) (gam q)

noncomputable def gyF (π : Fin (nDim q + 1) ↪ Fin q.d) : Sp q × Sp q → Sp q :=
  liftGy (objGrad (scl q hv) π 0) (qq q) (be q) (nu q) (gam q)

noncomputable def oyF (π : Fin (nDim q + 1) ↪ Fin q.d) (z : Sp q × Sp q) (ω : ℝ) : Sp q :=
  qq q • reply (scl q hv) (qf q) π 0 (be q • z.2) ω - nu q • (z.2 - gam q • z.1)

noncomputable def liftOracle (π : Fin (nDim q + 1) ↪ Fin q.d) : Oracle (Sp q × Sp q) (Sp q × Sp q) where
  Seed := fun _ => ℝ
  law := ⟨stream, inferInstance⟩
  answer := fun _ (_, z) ω => (liftGx (nu q) (gam q) z, oyF q hv π z ω)

end hardInstance

section facts

variable {q : Params} (hv : spec.valid q)
include hv

lemma objGrad_lip (π : Fin (nDim q + 1) ↪ Fin q.d) (u v : Sp q) :
    ‖objGrad (scl q hv) π 0 u - objGrad (scl q hv) π 0 v‖ ≤ q.L * ‖u - v‖ := by
  have h := objGrad_lipschitz (scl q hv) π 0 u v
  have hs : 1024 * (scl q hv).a / (scl q hv).lam ^ 2 = q.L :=
    smoothness_eq (chainParams q) (L_pos hv) (eps_pos hv)
  rwa [hs] at h

lemma objGrad_zero_norm (π : Fin (nDim q + 1) ↪ Fin q.d) :
    ‖objGrad (scl q hv) π 0 0‖ ≤ 1740 * q.ε := by
  have h := secret_norm (scl q hv) π 0 0
  have hratio : (scl q hv).a / (scl q hv).lam = 60 * q.ε :=
    amplitude_ratio (chainParams q) (L_pos hv) (eps_pos hv)
  have hu : toUnit (scl q hv) (0 : Sp q) 0 = 0 := by simp [toUnit]
  have hst : stage (sel π (toUnit (scl q hv) (0 : Sp q) 0)) = 0 := by
    rw [hu, map_zero]
    unfold stage
    simp
  have hk : knownPart (scl q hv) π (stage (sel π (toUnit (scl q hv) (0 : Sp q) 0))) 0 0 = 0 := by
    rw [hst]
    unfold knownPart knownGrad
    have hkf : knownField 0 (sel π (toUnit (scl q hv) (0 : Sp q) 0)) = 0 := by
      ext k
      simp [knownField]
    rw [hkf, hu, map_zero]
    simp [wallGrad]
  rw [hk, sub_zero, hratio] at h
  linarith

omit hv in
lemma qf_eq (m : ℕ) : qf q m = 1740 ^ 2 * q.ε ^ 2 /
    max (1740 ^ 2 * q.ε ^ 2) (2 * 1740 ^ 2 * q.ε ^ 2 * KK q ^ rr q) := by
  unfold qf revealProb levelBudget secretScale
  simp [chainParams]

lemma qf_pos (m : ℕ) : 0 < qf q m := revealProb_pos (chainParams q) (eps_pos hv) _ _

lemma qf_le (m : ℕ) : qf q m ≤ 1 := revealProb_le (chainParams q) (eps_pos hv) _ _

lemma moment_bound (m : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1740 * q.ε) :
    qf q m * ((1 / qf q m - 1) * (qq q * c)) ^ q.p + (1 - qf q m) * (qq q * c) ^ q.p ≤
      q.σ ^ q.p := by
  have hp1 : 1 < q.p := hv.1.2.2.1
  have hσ := sigma_nonneg hv
  have hε := eps_pos hv
  have hqq := qq_pos hv
  have ht0 := qf_pos hv m
  have ht1 := qf_le hv m
  have ha : 0 ≤ qq q * c := mul_nonneg hqq.le hc0
  have hK := KK_nonneg hv
  rcases le_or_gt (2 * 1740 ^ 2 * q.ε ^ 2 * KK q ^ rr q) (1740 ^ 2 * q.ε ^ 2) with hC | hC
  · have h1 : qf q m = 1 := by
      rw [qf_eq, max_eq_left hC, div_self (by positivity)]
    rw [h1]
    simp only [div_one, sub_self, zero_mul, one_mul, add_zero]
    rw [Real.zero_rpow (by linarith)]
    exact Real.rpow_nonneg hσ _
  · have hKr : 0 < KK q ^ rr q := by
      by_contra hneg
      push Not at hneg
      have : KK q ^ rr q = 0 := le_antisymm hneg (Real.rpow_nonneg hK _)
      rw [this] at hC
      nlinarith [sq_nonneg q.ε]
    have ht : qf q m = (2 * KK q ^ rr q)⁻¹ := by
      rw [qf_eq, max_eq_right hC.le]
      field_simp
    have hs := moment_scalar ht0 ht1 ha hp1.le
    refine hs.trans ?_
    have hpow : qf q m ^ (1 - q.p) = 2 ^ (q.p - 1) * KK q ^ q.p := by
      rw [ht, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_sub,
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg hK _), ← Real.rpow_mul hK, rr_mul hv]
    have hcp : (qq q * c) ^ q.p ≤ (qq q * (1740 * q.ε)) ^ q.p :=
      Real.rpow_le_rpow ha (mul_le_mul_of_nonneg_left hc hqq.le) (by linarith)
    have hval : 2 * KK q * (qq q * (1740 * q.ε)) = q.σ := by
      rw [qq_eps hv]
      unfold KK
      have hs : 0 < Real.sqrt (q.L / q.μ) := by have := kappa_ge hv; positivity
      field_simp
      ring
    have hc' : 0 ≤ qq q * (1740 * q.ε) := by positivity
    have hexp : (2 * KK q * (qq q * (1740 * q.ε))) ^ q.p =
        2 ^ q.p * KK q ^ q.p * (qq q * (1740 * q.ε)) ^ q.p := by
      rw [Real.mul_rpow (mul_nonneg (by norm_num) hK) hc', Real.mul_rpow (by norm_num) hK]
    have h2 : (2 : ℝ) * 2 ^ (q.p - 1) = 2 ^ q.p := by
      rw [← Real.rpow_one_add' (by norm_num) (by linarith)]
      ring_nf
    calc 2 * qf q m ^ (1 - q.p) * (qq q * c) ^ q.p
        ≤ 2 * qf q m ^ (1 - q.p) * (qq q * (1740 * q.ε)) ^ q.p := by
          gcongr
      _ = (2 * KK q * (qq q * (1740 * q.ε))) ^ q.p := by
          rw [hpow, hexp, ← h2]
          ring
      _ = q.σ ^ q.p := by rw [hval]

end facts

section admissible

variable {q : Params} (hv : spec.valid q)
include hv

lemma oy_sub (π : Fin (nDim q + 1) ↪ Fin q.d) (z : Sp q × Sp q) (ω : ℝ) :
    oyF q hv π z ω - gyF q hv π z =
      qq q • ((coin (qf q (stage (sel π (toUnit (scl q hv) 0 (be q • z.2))))) ω - 1) •
        (objGrad (scl q hv) π 0 (be q • z.2) -
          knownPart (scl q hv) π (stage (sel π (toUnit (scl q hv) 0 (be q • z.2)))) 0
            (be q • z.2))) := by
  simp only [oyF, gyF, liftGy, reply]
  module

lemma moment_eq (π : Fin (nDim q + 1) ↪ Fin q.d) (z : Sp q × Sp q) :
    ∃ t c : ℝ, 0 < t ∧ t ≤ 1 ∧ 0 ≤ c ∧ c ≤ 1740 * q.ε ∧ ∃ m : ℕ, t = qf q m ∧
      (fun ω => (Real.sqrt (‖liftGx (nu q) (gam q) z - liftGx (nu q) (gam q) z‖ ^ 2 +
        ‖oyF q hv π z ω - gyF q hv π z‖ ^ 2)) ^ q.p) =
        fun ω => if ω ≤ t then ((1 / t - 1) * (qq q * c)) ^ q.p else (qq q * c) ^ q.p := by
  set m := stage (sel π (toUnit (scl q hv) 0 (be q • z.2)))
  set w := objGrad (scl q hv) π 0 (be q • z.2) - knownPart (scl q hv) π m 0 (be q • z.2)
  have hw : ‖w‖ ≤ 1740 * q.ε := by
    have h := secret_norm (scl q hv) π 0 (be q • z.2)
    have hratio : (scl q hv).a / (scl q hv).lam = 60 * q.ε :=
      amplitude_ratio (chainParams q) (L_pos hv) (eps_pos hv)
    rw [hratio] at h
    change ‖w‖ ≤ 29 * (60 * q.ε) at h
    linarith
  refine ⟨qf q m, ‖w‖, qf_pos hv m, qf_le hv m, norm_nonneg _, hw, m, rfl, ?_⟩
  funext ω
  rw [sub_self, norm_zero, oy_sub hv π z ω]
  have hq := qq_pos hv
  have ht0 := qf_pos hv m
  have ht1 := qf_le hv m
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hq.le, Real.norm_eq_abs]
  have hsq : Real.sqrt ((0 : ℝ) ^ 2 + (qq q * (|coin (qf q m) ω - 1| * ‖w‖)) ^ 2) =
      qq q * (|coin (qf q m) ω - 1| * ‖w‖) := by
    rw [zero_pow two_ne_zero, zero_add, Real.sqrt_sq (by positivity)]
  rw [hsq]
  unfold coin
  split_ifs with h
  · have : |1 / qf q m - 1| = 1 / qf q m - 1 :=
      abs_of_nonneg (by rw [sub_nonneg, le_div_iff₀ ht0]; linarith)
    rw [this]
    ring_nf
  · norm_num

omit hv in
lemma ox_integrable (z : Sp q × Sp q) :
    Integrable (fun _ : ℝ => liftGx (nu q) (gam q) z) unif := integrable_const _

omit hv in
lemma ox_mean (z : Sp q × Sp q) :
    ∫ _ω, liftGx (nu q) (gam q) z ∂unif = liftGx (nu q) (gam q) z := by simp

lemma oy_integrable (π : Fin (nDim q + 1) ↪ Fin q.d) (z : Sp q × Sp q) :
    Integrable (oyF q hv π z) unif :=
  ((reply_integrable (scl q hv) (qf q) π 0 _).smul (qq q)).sub (integrable_const _)

lemma oy_mean (π : Fin (nDim q + 1) ↪ Fin q.d) (z : Sp q × Sp q) :
    ∫ ω, oyF q hv π z ω ∂unif = gyF q hv π z := by
  have h1 : Integrable (fun ω => qq q • reply (scl q hv) (qf q) π 0 (be q • z.2) ω) unif :=
    (reply_integrable (scl q hv) (qf q) π 0 _).smul (qq q)
  unfold oyF
  rw [integral_sub (f := fun ω => qq q • reply (scl q hv) (qf q) π 0 (be q • z.2) ω)
    (g := fun _ => nu q • (z.2 - gam q • z.1)) h1 (integrable_const _),
    integral_smul, reply_integral (scl q hv) (qf q) (qf_pos hv) (qf_le hv), integral_const,
    probReal_univ, one_smul]
  rfl

lemma moment_integrable (π : Fin (nDim q + 1) ↪ Fin q.d) (z : Sp q × Sp q) :
    Integrable (fun ω => (Real.sqrt (‖liftGx (nu q) (gam q) z - liftGx (nu q) (gam q) z‖ ^ 2 +
      ‖oyF q hv π z ω - gyF q hv π z‖ ^ 2)) ^ q.p) unif := by
  obtain ⟨t, c, ht0, ht1, _, _, m, _, he⟩ := moment_eq hv π z
  rw [he]
  exact (two_value_integral ht0.le ht1 (((1 / t - 1) * (qq q * c)) ^ q.p) ((qq q * c) ^ q.p)).1

lemma moment_le (π : Fin (nDim q + 1) ↪ Fin q.d) (z : Sp q × Sp q) :
    ∫ ω, (Real.sqrt (‖liftGx (nu q) (gam q) z - liftGx (nu q) (gam q) z‖ ^ 2 +
      ‖oyF q hv π z ω - gyF q hv π z‖ ^ 2)) ^ q.p ∂unif ≤ q.σ ^ q.p := by
  obtain ⟨t, c, ht0, ht1, hc0, hc, m, rfl, he⟩ := moment_eq hv π z
  rw [he, (two_value_integral ht0.le ht1 _ _).2]
  exact moment_bound hv m hc0 hc

lemma lifted_grad_x (π : Fin (nDim q + 1) ↪ Fin q.d) (x y : Sp q) :
    HasGradientAt (fun x' => liftedF q hv π x' y) (liftGx (nu q) (gam q) (x, y)) x :=
  lift_hasGradient_x _ _ _ _ _ x y

lemma lifted_grad_y (π : Fin (nDim q + 1) ↪ Fin q.d) (x y : Sp q) :
    HasGradientAt (fun y' => liftedF q hv π x y') (gyF q hv π (x, y)) y :=
  lift_hasGradient_y (objective_hasGradientAt (scl q hv) π (0 : Sp q)) (al_be hv) x y

lemma lifted_smooth (π : Fin (nDim q + 1) ↪ Fin q.d) (z z' : Sp q × Sp q) :
    ‖liftGx (nu q) (gam q) z - liftGx (nu q) (gam q) z'‖ ^ 2 + ‖gyF q hv π z - gyF q hv π z'‖ ^ 2 ≤
      q.L ^ 2 * (‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2) := by
  refine (lift_smooth (objGrad_lip hv π) (qq_pos hv).le (be_pos hv).le (nu_pos hv).le
    (gam_pos hv).le z z').trans ?_
  exact mul_le_mul_of_nonneg_right (smooth_const hv) (by positivity)

lemma lifted_concave (π : Fin (nDim q + 1) ↪ Fin q.d) (x y y' : Sp q) :
    liftedF q hv π x y' ≤ liftedF q hv π x y + ⟪gyF q hv π (x, y), y' - y⟫ -
      q.μ / 2 * ‖y' - y‖ ^ 2 := by
  have h := lift_concave (ν := nu q) (γ := gam q) (objective_hasGradientAt (scl q hv) π (0 : Sp q))
    (objGrad_lip hv π) (al_pos hv).le (al_be hv) (al_be_sq hv) x y y'
  rw [nu_sub hv] at h
  exact h

lemma lifted_admissible (π : Fin (nDim q + 1) ↪ Fin q.d) :
    spec.admissible q (liftedF q hv π) (liftOracle q hv π) := by
  have hμ := mu_pos hv
  have hL := L_pos hv
  have hε := eps_pos hv
  obtain ⟨_, _, _, fstar, -, -, -, -, hlow, -, hgap, -⟩ :=
    hard_admissible (chainParams q) (chainParams_valid hv) π
  have hlip := objGrad_lip hv π
  have hH := objective_hasGradientAt (scl q hv) π (0 : Sp q)
  refine ⟨liftGx (nu q) (gam q), gyF q hv π, fun z _ => liftGx (nu q) (gam q) z, oyF q hv π,
    ⟨unif, inferInstanceAs (IsProbabilityMeasure unif)⟩,
    ⟨stream, inferInstanceAs (IsProbabilityMeasure stream)⟩, stream_iid, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lifted_grad_x hv π
  · exact lifted_grad_y hv π
  · exact lifted_smooth hv π
  · exact lifted_concave hv π
  · intro x y
    refine ⟨gam q • x, ?_⟩
    have h := lift_gap (γ := gam q) hH hlip (al_pos hv).le (al_be hv) (al_be_sq hv)
      (by rw [nu_sub hv]; exact hμ) hlow x y
    rw [nu_sub hv] at h
    have hg0 := objGrad_zero_norm hv π
    have h1 : al q * (objective (scl q hv) π 0 0 - fstar) ≤ q.Δ / 2 := by
      rw [← chain_delta hv]
      exact mul_le_mul_of_nonneg_left hgap (al_pos hv).le
    have h2 : qq q ^ 2 * ‖objGrad (scl q hv) π 0 0‖ ^ 2 / (2 * q.μ) ≤ q.Δ / 2 := by
      refine le_trans ?_ (init_term hv)
      gcongr
    exact h.trans (show _ ≤ q.Δ by linarith)
  · change ‖gyF q hv π (0, 0)‖ ≤ q.G
    have hg0 := objGrad_zero_norm hv π
    have he : gyF q hv π (0, 0) = qq q • objGrad (scl q hv) π 0 0 := by
      simp [gyF, liftGy]
    rw [he, norm_smul, Real.norm_of_nonneg (qq_pos hv).le]
    have hs : 0 < Real.sqrt (q.L / q.μ) := by have := kappa_ge hv; positivity
    have hG : 4176 * q.ε ≤ q.G * Real.sqrt (q.L / q.μ) := hv.2.2.2.2.1
    calc qq q * ‖objGrad (scl q hv) π 0 0‖ ≤ qq q * (1740 * q.ε) :=
          mul_le_mul_of_nonneg_left hg0 (qq_pos hv).le
      _ = 4176 * q.ε / Real.sqrt (q.L / q.μ) := qq_eps hv
      _ ≤ q.G := by rw [div_le_iff₀ hs]; exact hG
  · exact (by unfold liftGx; fun_prop : Continuous fun z : Sp q × Sp q =>
      liftGx (nu q) (gam q) z).measurable.comp measurable_fst
  · have hr := reply_measurable (scl q hv) (qf q) π (0 : Sp q)
    have hm : Measurable fun zw : (Sp q × Sp q) × ℝ => (be q • zw.1.2, zw.2) :=
      ((measurable_const_smul _).comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd
    have h1 := (hr.comp hm).const_smul (qq q)
    have h2 : Measurable fun zw : (Sp q × Sp q) × ℝ => nu q • (zw.1.2 - gam q • zw.1.1) :=
      (by fun_prop : Continuous fun z : Sp q × Sp q => nu q • (z.2 - gam q • z.1)).measurable.comp
        measurable_fst
    exact h1.sub h2
  · exact fun z => ox_integrable z
  · exact fun z => oy_integrable hv π z
  · exact fun z => ox_mean z
  · exact fun z => oy_mean hv π z
  · exact fun z => moment_integrable hv π z
  · exact fun z => moment_le hv π z

end admissible

section simulation

variable (q : Params) (hv : spec.valid q)

noncomputable def baseAlgorithm (A : Algorithm (Sp q × Sp q) (Sp q × Sp q) (Sp q)) :
    Algorithm (Sp q) (Sp q) (Sp q) where
  Seed := A.Seed
  law := A.law
  State := A.State
  initial := A.initial
  query s := ((A.query s).1, be q • (A.query s).2.2)
  update s r := A.update s (liftGx (nu q) (gam q) (A.query s).2,
    qq q • r - nu q • ((A.query s).2.2 - gam q • (A.query s).2.1))
  output s := (be q * gam q) • A.output s

lemma execute_base (π : Fin (nDim q + 1) ↪ Fin q.d)
    (A : Algorithm (Sp q × Sp q) (Sp q × Sp q) (Sp q)) (N : ℕ) (seed : A.Seed) (ω : ℕ → ℝ) :
    execute (hardOracle (chainParams q) (scl q hv) π) (baseAlgorithm q A) (fun _ => N) seed ω =
      (be q * gam q) • execute (liftOracle q hv π) A (fun _ => N) seed ω := by
  rw [execute_indexed_of_answer (hardOracle (chainParams q) (scl q hv) π)
      (baseAlgorithm q A) N seed ω
      (fun t query => reply (scl q hv) (qf q) π 0 query.2 (ω t)) (fun _ query => by cases query; rfl),
    execute_indexed_of_answer (liftOracle q hv π) A N seed ω
      (fun t query => (liftGx (nu q) (gam q) query.2, oyF q hv π query.2 (ω t)))
      (fun _ query => by cases query; rfl)]
  rfl

end simulation

section failure

variable {q : Params} (hv : spec.valid q)
include hv

lemma phi_gradient (π : Fin (nDim q + 1) ↪ Fin q.d) (ys : Sp q → Sp q)
    (hys : ∀ x y, liftedF q hv π x y ≤ liftedF q hv π x (ys x)) (x : Sp q) :
    ‖objGrad (scl q hv) π 0 ((be q * gam q) • x)‖ ≤
      ‖gradient (fun x => liftedF q hv π x (ys x)) x‖ := by
  have Hm := LongTails.Proofs.HeavyTailSaddleGeometry.minimax_value_hyp (E := Sp q) (F := Sp q)
    (mu_pos hv) hv.1.2.1 (lifted_grad_x hv π) (lifted_grad_y hv π) (lifted_smooth hv π)
    (lifted_concave hv π)
  have hmax : (fun x => liftedF q hv π x (ys x)) = LongTails.Setups.StochasticTwoSidedPL.maxValue
      (liftedF q hv π) := funext fun x => (Hm.max_value_eq (hys x)).symm
  rw [hmax, (Hm.value_hasGradient (hys x)).gradient]
  have h0 : gyF q hv π (x, ys x) = 0 := Hm.max_gradient_zero (hys x)
  have ht := lift_transfer (objGrad_lip hv π) (qq_pos hv) (be_pos hv).le (nu_pos hv) (gam_pos hv)
    x (ys x) h0
  rw [transfer_const hv, one_mul] at ht
  exact ht

lemma chain_failure (A : Algorithm (Sp q × Sp q) (Sp q × Sp q) (Sp q)) (N : ℕ)
    (hN : N ≤ lowerBudget (chainParams q)) :
    ∃ π : Fin (nDim q + 1) ↪ Fin q.d,
      ¬ spec.successful q (liftedF q hv π)
        (fun w : A.Seed × ((k : ℕ) → (liftOracle q hv π).Seed k) =>
          execute (liftOracle q hv π) A (fun _ => N) w.1 w.2)
        ⟨(A.law : Measure _).prod ((liftOracle q hv π).law : Measure _), inferInstance⟩ := by
  obtain ⟨π, hπ⟩ := LongTails.Proofs.HighProbabilityChainFailure.exists_hp_failure
    (chainParams q) (chainParams_valid hv) (baseAlgorithm q A) N hN
  refine ⟨π, fun hs => hπ ⟨?_, ?_⟩⟩
  · have hm : Measurable (fun w : A.Seed × (ℕ → ℝ) =>
        execute (liftOracle q hv π) A (fun _ => N) w.1 w.2) := hs.1
    have he : (fun w : A.Seed × (ℕ → ℝ) =>
        execute (hardOracle (chainParams q) (scl q hv) π) (baseAlgorithm q A) (fun _ => N) w.1 w.2) =
        fun w => (be q * gam q) • execute (liftOracle q hv π) A (fun _ => N) w.1 w.2 := by
      funext w
      exact execute_base q hv π A N w.1 w.2
    change Measurable (fun w : A.Seed × (ℕ → ℝ) =>
        execute (hardOracle (chainParams q) (scl q hv) π) (baseAlgorithm q A) (fun _ => N) w.1 w.2)
    rw [he]
    exact (continuous_const_smul (be q * gam q)).measurable.comp hm
  · obtain ⟨ys, hys⟩ := hs.2.1
    have hbad := hs.2.2 ys hys
    let P : Measure (A.Seed × (ℕ → ℝ)) := (A.law : Measure A.Seed).prod stream
    let out := fun w : A.Seed × (ℕ → ℝ) => execute (liftOracle q hv π) A (fun _ => N) w.1 w.2
    have hbad' : P.real {w | q.ε < ‖gradient (fun x => liftedF q hv π x (ys x)) (out w)‖} ≤ q.δ := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
      rwa [ENNReal.toReal_ofReal hv.1.2.2.2.2.2.2.2.2.1.le] at h
    have hgood : 1 - q.δ ≤ P.real {w | ‖gradient (fun x => liftedF q hv π x (ys x)) (out w)‖ ≤ q.ε} := by
      have hu := measureReal_union_le (μ := P)
        {w | ‖gradient (fun x => liftedF q hv π x (ys x)) (out w)‖ ≤ q.ε}
        {w | q.ε < ‖gradient (fun x => liftedF q hv π x (ys x)) (out w)‖}
      have huniv : {w | ‖gradient (fun x => liftedF q hv π x (ys x)) (out w)‖ ≤ q.ε} ∪
          {w | q.ε < ‖gradient (fun x => liftedF q hv π x (ys x)) (out w)‖} = Set.univ := by
        ext w; simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]; exact le_or_gt _ _
      rw [huniv, probReal_univ] at hu
      linarith
    have hsub : {w | ‖gradient (fun x => liftedF q hv π x (ys x)) (out w)‖ ≤ q.ε} ⊆
        {w | ‖gradient (objective (scl q hv) π 0)
          (execute (hardOracle (chainParams q) (scl q hv) π) (baseAlgorithm q A) (fun _ => N) w.1 w.2)‖ ≤
            q.ε} := by
      intro w hw
      simp only [Set.mem_ofPred_eq] at hw ⊢
      rw [objective_gradient]
      have hx := congrArg (fun v => ‖objGrad (scl q hv) π 0 v‖) (execute_base q hv π A N w.1 w.2)
      exact (le_of_eq hx).trans ((phi_gradient hv π ys hys (out w)).trans hw)
    have hmono := measureReal_mono (μ := P) hsub
    have hδ : q.δ ≤ 1 / 4 := hv.2.1
    exact le_trans (by linarith) hmono

end failure

end LongTails.Proofs.HeavyTailNcscChain
