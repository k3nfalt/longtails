import LongTails.Proofs.HeavyTailedHighProbabilityStep
import LongTails.Proofs.HilbertSmallMoments
import LongTails.Algorithms.HeavyTailedHighProbabilityStationarity

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailedHighProbabilityBlock

open LongTails.Algorithms.HighProbabilityStationarity OracleTemplate RobustGradient
open LongTails.Algorithms.HeavyTailedHighProbabilityStationarity
open LongTails.Proofs.HighProbabilityEstimator LongTails.Proofs.HighProbabilityStep
open LongTails.Proofs.HeavyTailedHighProbabilityStep LongTails.Proofs.HilbertSmallMoments
open LongTails.Proofs.HighProbabilityPilot

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma clip_nonexpansive {B : ℝ} (hB : 0 ≤ B) (x y : E) : ‖clip B x - clip B y‖ ≤ ‖x - y‖ := by
  have ha := norm_clip_le hB x
  have hb := norm_clip_le hB y
  have h1 := inner_clip_residual_nonpos hB hb x
  have h2 := inner_clip_residual_nonpos hB ha y
  have hsum : ‖clip B x - clip B y‖ ^ 2 ≤ ⟪x - y, clip B x - clip B y⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    have e1 : ⟪x - clip B x, clip B y - clip B x⟫ + ⟪y - clip B y, clip B x - clip B y⟫ =
        ⟪clip B x - clip B y, clip B x - clip B y⟫ - ⟪x - y, clip B x - clip B y⟫ := by
      have : clip B y - clip B x = -(clip B x - clip B y) := by abel
      rw [this, inner_neg_right]
      have e2 : x - clip B x = (x - y) - (clip B x - clip B y) + (y - clip B y) := by abel
      rw [e2, inner_add_left, inner_sub_left]
      ring
    linarith
  have hcs := real_inner_le_norm (x - y) (clip B x - clip B y)
  have hn := norm_nonneg (clip B x - clip B y)
  by_cases h0 : ‖clip B x - clip B y‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖clip B x - clip B y‖ := lt_of_le_of_ne hn (Ne.symm h0)
    nlinarith

lemma residual_difference {B D : ℝ} (hB : 0 ≤ B) {u c : E} (hD : ‖u - c‖ ≤ D) (hDB : D ≤ B / 2)
    (v : E) :
    ‖(c + clip B (v - c)) - (u + clip B (v - u))‖ ≤ if B / 2 < ‖v - u‖ then 2 * D else 0 := by
  by_cases hv : ‖v - u‖ ≤ B / 2
  · have hvu : ‖v - u‖ ≤ B := by linarith
    have hvc : ‖v - c‖ ≤ B := by
      have := norm_sub_le_norm_sub_add_norm_sub v u c
      linarith
    rw [clip_eq_self hvu, clip_eq_self hvc, ite_eq_right (not_lt.mpr hv)]
    simp
  · rw [ite_eq_left (lt_of_not_ge hv)]
    have h1 := clip_nonexpansive hB (v - c) (v - u)
    have h2 : (v - c) - (v - u) = u - c := by abel
    have he2 : (c + clip B (v - c)) - (u + clip B (v - u)) =
        (clip B (v - c) - clip B (v - u)) - (u - c) := by abel
    rw [he2]
    rw [h2] at h1
    calc ‖clip B (v - c) - clip B (v - u) - (u - c)‖ ≤
          ‖clip B (v - c) - clip B (v - u)‖ + ‖u - c‖ := norm_sub_le _ _
      _ ≤ 2 * D := by linarith

lemma clipMean_eq_mean (B : ℝ) (c : E) {mc : ℕ} (hmc : 0 < mc) (w : Fin mc → E) :
    clipMean B c mc w = (mc : ℝ)⁻¹ • ∑ i, centeredClip B c (w i) := by
  have hmcne : (mc : ℝ) ≠ 0 := by exact_mod_cast hmc.ne'
  simp only [clipMean, centeredClip, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_add, one_div]
  rw [← Nat.cast_smul_eq_nsmul ℝ mc c, smul_smul, inv_mul_cancel₀ hmcne, one_smul]

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

omit [CompleteSpace E] in
lemma measurable_blockEstimate (r B : ℝ) (m0 mc : ℕ) :
    Measurable (blockEstimate (E := E) r B m0 mc) := by
  have hp := measurable_gradedPilot (E := E) (m := m0) r 0 0
  have hpil : Measurable (fun v : Fin (m0 + mc) → E =>
      gradedPilot r 0 (fun i : Fin m0 => v (Fin.castAdd mc i)) 0) :=
    hp.comp (Measurable.of_eval fun i => measurable_pi_apply _)
  unfold blockEstimate
  refine hpil.add (Measurable.const_smul ?_ _)
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_clip B).comp ((measurable_pi_apply _).sub hpil)

lemma fiber_bound {V : Ω → E} (hV : Measurable V) (hVi : Integrable V p) {u : E}
    (hmean : ∫ ω, V ω ∂p = u) {α s : ℝ} (hα1 : 1 ≤ α) (hα2 : α ≤ 2)
    (hpi : Integrable (fun ω => ‖V ω - u‖ ^ α) p) (hpm : (∫ ω, ‖V ω - u‖ ^ α ∂p) ≤ s ^ α)
    (hs : 0 ≤ s) {B D v a : ℝ} {mc : ℕ} (hmc : 0 < mc) (hB : 0 < B) {c : E}
    (hc : ‖u - c‖ ≤ D) (hDB : D ≤ B / 2) (hlink : 2 * s ^ α * B ^ (2 - α) ≤ v)
    (hvB : 8 * v ≤ B ^ 2) (hvar : 1536 * v ≤ mc * a ^ 2) (hν : 2 * D * s ^ α / (B / 2) ^ α ≤ a / 2)
    (ha : 0 < a) :
    (Measure.pi fun _ : Fin mc => p).real
      {w | a < ‖clipMean B c mc (fun j => V (w j)) - (u + ∫ ω, clip B (V ω - u) ∂p)‖} ≤ 1 / 32 := by
  classical
  have hα0 : 0 < α := by linarith
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) hc
  have hcB : ‖u - c‖ ≤ B / 2 := hc.trans hDB
  have hv0 : 0 ≤ v := le_trans (by positivity) hlink
  have hmom := centeredClip_moments_heavy hV hVi hmean hB hcB hα1 hα2 hpi hpm hs
    (σ := Real.sqrt v) (by rw [Real.sq_sqrt hv0]; exact hlink)
  rw [Real.sq_sqrt hv0] at hmom
  obtain ⟨hXi, hX2i, hX2, hbias⟩ := hmom
  set X : Ω → E := fun ω => centeredClip B c (V ω) with hXdef
  have hXm : Measurable X := (measurable_centeredClip B c).comp hV
  set m : E := ∫ ω, X ω ∂p with hmdef
  set Tt : E := u + ∫ ω, clip B (V ω - u) ∂p with hTdef
  have hclipi : Integrable (fun ω => clip B (V ω - u)) p := integrable_clip (hV.sub_const u) hB.le
  have hν' : ‖m - Tt‖ ≤ a / 2 := by
    have hdiff : m - Tt = ∫ ω, ((c + clip B (V ω - c)) - (u + clip B (V ω - u))) ∂p := by
      have h1 : (∫ ω, ((c + clip B (V ω - c)) - (u + clip B (V ω - u))) ∂p) =
          (∫ ω, X ω ∂p) - ∫ ω, (u + clip B (V ω - u)) ∂p :=
        integral_sub hXi ((integrable_const u).add hclipi)
      have h2 : (∫ ω, (u + clip B (V ω - u)) ∂p) = u + ∫ ω, clip B (V ω - u) ∂p := by
        rw [integral_add (integrable_const u) hclipi, integral_const, probReal_univ, one_smul]
      rw [h1, h2]
    have hset : MeasurableSet {ω | B / 2 < ‖V ω - u‖} :=
      measurableSet_lt measurable_const ((hV.sub_const u).norm)
    have hind : Integrable (Set.indicator {ω | B / 2 < ‖V ω - u‖} (fun _ => 2 * D)) p :=
      (integrable_const (2 * D)).indicator hset
    have hpt (ω : Ω) : ‖(c + clip B (V ω - c)) - (u + clip B (V ω - u))‖ ≤
        Set.indicator {ω | B / 2 < ‖V ω - u‖} (fun _ => 2 * D) ω := by
      have h := residual_difference hB.le hc hDB (V ω)
      by_cases hω : B / 2 < ‖V ω - u‖
      · rw [ite_eq_left hω] at h
        rw [Set.indicator_of_mem (show ω ∈ {ω | B / 2 < ‖V ω - u‖} from hω)]
        exact h
      · rw [ite_eq_right hω] at h
        rw [Set.indicator_of_notMem (show ω ∉ {ω | B / 2 < ‖V ω - u‖} from hω)]
        exact h
    have hb := norm_integral_le_of_norm_le hind (Filter.Eventually.of_forall hpt)
    rw [← hdiff, integral_indicator_const _ hset, smul_eq_mul, mul_comm] at hb
    have hfar := far_prob_heavy hα0 hpi (by linarith : (0 : ℝ) < B / 2) hpm
    have hBα : 0 < (B / 2) ^ α := Real.rpow_pos_of_pos (by positivity) _
    have h2 : 2 * D * p.real {ω | B / 2 < ‖V ω - u‖} ≤ 2 * D * (s ^ α / (B / 2) ^ α) :=
      mul_le_mul_of_nonneg_left hfar (by positivity)
    have h3 : 2 * D * (s ^ α / (B / 2) ^ α) = 2 * D * s ^ α / (B / 2) ^ α := by ring
    linarith
  have hmu : ‖m - u‖ ≤ 2 * v / B := hbias
  have hptm (ω : Ω) : ‖X ω - m‖ ^ 2 ≤ 2 * ‖X ω - u‖ ^ 2 + 2 * ‖u - m‖ ^ 2 := by
    have ht : ‖X ω - m‖ ≤ ‖X ω - u‖ + ‖u - m‖ := by
      have := norm_add_le (X ω - u) (u - m)
      simpa only [sub_add_sub_cancel] using this
    nlinarith [norm_nonneg (X ω - u), norm_nonneg (u - m), norm_nonneg (X ω - m),
      sq_nonneg (‖X ω - u‖ - ‖u - m‖)]
  have hi2 : Integrable (fun ω => ‖X ω - m‖ ^ 2) p := by
    refine ((hX2i.const_mul 2).add (integrable_const (2 * ‖u - m‖ ^ 2))).mono'
      ((hXm.sub_const m).norm.pow_const 2).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hptm ω
  have hcen : (∫ ω, ‖X ω - m‖ ^ 2 ∂p) ≤ 3 * v := by
    have hle : (∫ ω, ‖X ω - m‖ ^ 2 ∂p) ≤ ∫ ω, (2 * ‖X ω - u‖ ^ 2 + 2 * ‖u - m‖ ^ 2) ∂p :=
      integral_mono hi2 ((hX2i.const_mul 2).add (integrable_const (2 * ‖u - m‖ ^ 2))) hptm
    rw [integral_add (hX2i.const_mul 2) (integrable_const _), integral_const_mul, integral_const,
      probReal_univ, one_smul] at hle
    have hum : ‖u - m‖ ^ 2 ≤ v / 2 := by
      rw [norm_sub_rev]
      have h1 : ‖m - u‖ ^ 2 ≤ (2 * v / B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmu 2
      have h2 : (2 * v / B) ^ 2 = 4 * v ^ 2 / B ^ 2 := by ring
      have h3 : 4 * v ^ 2 / B ^ 2 ≤ v / 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    nlinarith
  have hmc' : (0 : ℝ) < mc := by exact_mod_cast hmc
  have hpow := iid_centered_mean_power_bound (P := p) hXm (p := 2) (by norm_num) le_rfl hXi m
    (by simp only [Real.rpow_two]; exact hi2) rfl mc hmc
  simp only [Real.rpow_two] at hpow
  obtain ⟨hpi2, hpb⟩ := hpow
  have hsub : {w : Fin mc → Ω | a < ‖clipMean B c mc (fun j => V (w j)) - Tt‖} ⊆
      {w | (a / 2) ^ 2 ≤ ‖(mc : ℝ)⁻¹ • ∑ i, X (w i) - m‖ ^ 2} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    rw [clipMean_eq_mean B c hmc] at hw
    have htri : ‖(mc : ℝ)⁻¹ • ∑ i, centeredClip B c (V (w i)) - Tt‖ ≤
        ‖(mc : ℝ)⁻¹ • ∑ i, X (w i) - m‖ + ‖m - Tt‖ := by
      have := norm_add_le ((mc : ℝ)⁻¹ • ∑ i, X (w i) - m) (m - Tt)
      simpa only [sub_add_sub_cancel, hXdef] using this
    have h1 : a / 2 ≤ ‖(mc : ℝ)⁻¹ • ∑ i, X (w i) - m‖ := by linarith
    exact pow_le_pow_left₀ (by positivity) h1 2
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := Measure.pi fun _ : Fin mc => p)
    (Filter.Eventually.of_forall fun w => sq_nonneg ‖(mc : ℝ)⁻¹ • ∑ i, X (w i) - m‖) hpi2
    ((a / 2) ^ 2)
  have hrhs : (∫ w : Fin mc → Ω, ‖(mc : ℝ)⁻¹ • ∑ i, X (w i) - m‖ ^ 2
      ∂Measure.pi fun _ => p) ≤ 4 * (3 * v) / mc := by
    have h1 : (4 : ℝ) * (mc : ℝ) ^ (1 - 2 : ℝ) = 4 / mc := by
      rw [show (1 - 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
      field_simp
    calc _ ≤ 4 * (mc : ℝ) ^ (1 - 2 : ℝ) * ∫ ω, ‖X ω - m‖ ^ 2 ∂p := hpb
      _ = 4 / mc * ∫ ω, ‖X ω - m‖ ^ 2 ∂p := by rw [h1]
      _ ≤ 4 / mc * (3 * v) := mul_le_mul_of_nonneg_left hcen (by positivity)
      _ = 4 * (3 * v) / mc := by ring
  have hfinal : (Measure.pi fun _ : Fin mc => p).real
      {w | (a / 2) ^ 2 ≤ ‖(mc : ℝ)⁻¹ • ∑ i, X (w i) - m‖ ^ 2} ≤ 1 / 32 := by
    have ha2 : 0 < (a / 2) ^ 2 := by positivity
    have hq : (a / 2) ^ 2 * (Measure.pi fun _ : Fin mc => p).real
        {w | (a / 2) ^ 2 ≤ ‖(mc : ℝ)⁻¹ • ∑ i, X (w i) - m‖ ^ 2} ≤ 4 * (3 * v) / mc :=
      hmark.trans hrhs
    rw [le_div_iff₀ hmc'] at hq
    have hq' : (Measure.pi fun _ : Fin mc => p).real
        {w | (a / 2) ^ 2 ≤ ‖(mc : ℝ)⁻¹ • ∑ i, X (w i) - m‖ ^ 2} * (mc * a ^ 2) ≤ 48 * v := by
      nlinarith
    have hP0 := measureReal_nonneg (μ := Measure.pi fun _ : Fin mc => p)
      (s := {w | (a / 2) ^ 2 ≤ ‖(mc : ℝ)⁻¹ • ∑ i, X (w i) - m‖ ^ 2})
    have hpos : 0 < (mc : ℝ) * a ^ 2 := by positivity
    by_contra hcon
    push Not at hcon
    nlinarith
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans hfinal

lemma block_accuracy {V : Ω → E} (hV : Measurable V) (hVi : Integrable V p) {u : E}
    (hmean : ∫ ω, V ω ∂p = u) {α s : ℝ} (hα1 : 1 ≤ α) (hα2 : α ≤ 2)
    (hpi : Integrable (fun ω => ‖V ω - u‖ ^ α) p) (hpm : (∫ ω, ‖V ω - u‖ ^ α ∂p) ≤ s ^ α)
    (hs : 0 ≤ s) {r0 B v a : ℝ} {mc : ℕ} (hmc : 0 < mc) (hr0 : 0 < r0) (hsr : 192 * s ≤ r0)
    (hrB : 2 * r0 ≤ B) (hlink : 2 * s ^ α * B ^ (2 - α) ≤ v)
    (hvB : 8 * v ≤ B ^ 2) (hvar : 1536 * v ≤ mc * a ^ 2)
    (hν : 2 * (5 * r0 / 6) * s ^ α / (B / 2) ^ α ≤ a / 2) (ha : 0 < a) :
    (Measure.pi fun _ : Fin (4 + mc) => p).real
      {ζ | a < ‖blockEstimate r0 B 4 mc (fun l => V (ζ l)) -
        (u + ∫ ω, clip B (V ω - u) ∂p)‖} ≤ 1 / 16 := by
  classical
  have hB : 0 < B := by linarith
  have hα0 : 0 < α := by linarith
  set Tt : E := u + ∫ ω, clip B (V ω - u) ∂p with hTdef
  let S : Set (Fin (4 + mc) → Ω) :=
    {ζ | a < ‖blockEstimate r0 B 4 mc (fun l => V (ζ l)) - Tt‖}
  have hestm : Measurable (fun ζ : Fin (4 + mc) → Ω => blockEstimate r0 B 4 mc (fun l => V (ζ l))) :=
    (measurable_blockEstimate r0 B 4 mc).comp (Measurable.of_eval fun l => hV.comp (measurable_pi_apply l))
  have hS : MeasurableSet S := measurableSet_lt measurable_const ((hestm.sub_const Tt).norm)
  let join : (Fin 4 → Ω) × (ℕ → Ω) → Fin (4 + mc) → Ω := fun w i =>
    if h : (i : ℕ) < 4 then w.1 ⟨i, h⟩ else w.2 ((i : ℕ) - 4)
  have hjoin : Measurable join := by
    refine Measurable.of_eval fun i => ?_
    by_cases h : (i : ℕ) < 4
    · simp only [join, h, ↓reduceDIte]; exact (measurable_pi_apply _).comp measurable_fst
    · simp only [join, h, ↓reduceDIte]; exact (measurable_pi_apply _).comp measurable_snd
  let H : (Fin 4 → Ω) × (ℕ → Ω) → ℝ := fun w => S.indicator 1 (join w)
  have hH : Measurable H := (measurable_one.indicator hS).comp hjoin
  let pil : (Fin 4 → Ω) → E := fun a' => gradedPilot r0 0 (fun i => V (a' i)) 0
  have hpil : Measurable pil :=
    (measurable_gradedPilot (E := E) (m := 4) r0 0 0).comp
      (Measurable.of_eval fun i => hV.comp (measurable_pi_apply i))
  let Bad : Set (Fin 4 → Ω) := {a' | 5 * r0 / 6 < ‖pil a' - u‖}
  have hBad : MeasurableSet Bad := measurableSet_lt measurable_const ((hpil.sub_const u).norm)
  let G : (Fin 4 → Ω) → ℝ := fun a' => 1 / 32 + Bad.indicator 1 a'
  have hjoin_est (a' : Fin 4 → Ω) (τ : ℕ → Ω) :
      blockEstimate r0 B 4 mc (fun l => V (join (a', τ) l)) =
        clipMean B (pil a') mc (fun j : Fin mc => V (τ j)) := by
    have hc1 : ∀ i : Fin 4, join (a', τ) (Fin.castAdd mc i) = a' i := by
      intro i
      simp [join, Fin.castAdd, i.isLt]
    have hc2 : ∀ i : Fin mc, join (a', τ) (Fin.natAdd 4 i) = τ i := by
      intro i
      simp [join, Fin.natAdd]
    simp only [blockEstimate, clipMean, hc1, hc2]
    rfl
  have hfiber : ∀ a' : Fin 4 → Ω,
      Integrable (fun τ => H (a', τ)) (Measure.infinitePi fun _ : ℕ => p) ∧
        (∫ τ, H (a', τ) ∂(Measure.infinitePi fun _ : ℕ => p)) ≤ G a' := by
    intro a'
    have hHm : Measurable (fun τ : ℕ → Ω => H (a', τ)) := hH.comp measurable_prodMk_left
    have hint : Integrable (fun τ => H (a', τ)) (Measure.infinitePi fun _ : ℕ => p) := by
      refine Integrable.of_bound hHm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun τ => ?_)
      simp only [H, Real.norm_eq_abs]
      by_cases hm : join (a', τ) ∈ S
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    refine ⟨hint, ?_⟩
    have hval : (∫ τ, H (a', τ) ∂(Measure.infinitePi fun _ : ℕ => p)) =
        (Measure.pi fun _ : Fin mc => p).real
          {w | a < ‖clipMean B (pil a') mc (fun j => V (w j)) - Tt‖} := by
      have hset : MeasurableSet {w : Fin mc → Ω | a < ‖clipMean B (pil a') mc (fun j => V (w j)) - Tt‖} := by
        refine measurableSet_lt measurable_const (Measurable.norm (Measurable.sub_const ?_ Tt))
        unfold clipMean
        refine measurable_const.add (Measurable.const_smul ?_ _)
        exact Finset.measurable_sum _ fun i _ =>
          (measurable_clip B).comp ((hV.comp (measurable_pi_apply _)).sub_const _)
      have hfun : (fun τ => H (a', τ)) = Set.indicator
          ((fun ξ : ℕ → Ω => fun i : Fin mc => ξ i) ⁻¹'
            {w | a < ‖clipMean B (pil a') mc (fun j => V (w j)) - Tt‖}) 1 := by
        funext τ
        have hiff : join (a', τ) ∈ S ↔ τ ∈ ((fun ξ : ℕ → Ω => fun i : Fin mc => ξ i) ⁻¹'
            {w | a < ‖clipMean B (pil a') mc (fun j => V (w j)) - Tt‖}) := by
          show a < ‖blockEstimate r0 B 4 mc (fun l => V (join (a', τ) l)) - Tt‖ ↔
            a < ‖clipMean B (pil a') mc (fun j : Fin mc => V (τ j)) - Tt‖
          rw [hjoin_est]
        show S.indicator 1 (join (a', τ)) = _
        by_cases hm : join (a', τ) ∈ S
        · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.mp hm)]
          rfl
        · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (hiff.mpr h))]
      rw [hfun, integral_indicator_one (hset.preimage
          (OracleTemplate.StochasticGeneralized.prefix_preserving p mc).measurable),
        measureReal_def, (OracleTemplate.StochasticGeneralized.prefix_preserving p mc).measure_preimage
          hset.nullMeasurableSet, ← measureReal_def]
    rw [hval]
    by_cases hgood : ‖pil a' - u‖ ≤ 5 * r0 / 6
    · have hb := fiber_bound hV hVi hmean hα1 hα2 hpi hpm hs hmc hB (c := pil a')
        (by rw [norm_sub_rev]; exact hgood) (by linarith) hlink hvB hvar hν ha
      rw [← hTdef] at hb
      have : (0 : ℝ) ≤ Bad.indicator (1 : (Fin 4 → Ω) → ℝ) a' :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) a'
      show _ ≤ 1 / 32 + Bad.indicator 1 a'
      exact le_trans hb (le_add_of_nonneg_right this)
    · have hmem : a' ∈ Bad := lt_of_not_ge hgood
      simp only [G, Set.indicator_of_mem hmem, Pi.one_apply]
      have := measureReal_le_one (μ := Measure.pi fun _ : Fin mc => p)
        (s := {w | a < ‖clipMean B (pil a') mc (fun j => V (w j)) - Tt‖})
      linarith
  have hGi : Integrable G (Measure.pi fun _ : Fin 4 => p) :=
    (integrable_const _).add ((integrable_const 1).indicator hBad)
  have hbound := LongTails.Proofs.WeakGradientConvolution.nonnegative_fiber_integral_bound
    (P := Measure.pi fun _ : Fin 4 => p) (Q := Measure.infinitePi fun _ : ℕ => p)
    hH.stronglyMeasurable (fun w => Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    (Filter.Eventually.of_forall fun a' => (hfiber a').1) hGi
    (Filter.Eventually.of_forall fun a' => (hfiber a').2)
  have hpilot : (Measure.pi fun _ : Fin 4 => p).real Bad ≤ 1 / 64 := by
    have htail : p.real {ω | r0 / 6 < ‖V ω - u‖} ≤ 1 / 32 := by
      have h := far_prob_heavy hα0 hpi (by linarith : (0 : ℝ) < r0 / 6) hpm
      have hratio : s ^ α / (r0 / 6) ^ α = (s / (r0 / 6)) ^ α :=
        (Real.div_rpow hs (by linarith) α).symm
      have hb1 : s / (r0 / 6) ≤ 1 / 32 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have hb0 : 0 ≤ s / (r0 / 6) := div_nonneg hs (by linarith)
      have hb2 : (s / (r0 / 6)) ^ α ≤ (1 / 32 : ℝ) ^ α := Real.rpow_le_rpow hb0 hb1 hα0.le
      have hb3 : (1 / 32 : ℝ) ^ α ≤ (1 / 32 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hα1
      rw [Real.rpow_one] at hb3
      linarith
    have hp := pilot_tail_gen (mp := 4) (K := 0) (B := r0) hV (by norm_num : (0 : ℝ) < 1 / 32)
      (by norm_num) htail (by linarith) (by simp; linarith)
    have hset : {a' : Fin 4 → Ω | 5 * (r0 / 6) < ‖gradedPilot r0 0 (fun i => V (a' i)) 0 - u‖} = Bad := by
      ext a'
      simp only [Bad, pil, Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    rw [hset] at hp
    have hsq : (2 * Real.sqrt (1 / 32 : ℝ)) ^ 4 = 1 / 64 := by
      have : Real.sqrt (1 / 32 : ℝ) ^ 2 = 1 / 32 := Real.sq_sqrt (by norm_num)
      calc (2 * Real.sqrt (1 / 32 : ℝ)) ^ 4 = 16 * (Real.sqrt (1 / 32 : ℝ) ^ 2) ^ 2 := by ring
        _ = 1 / 64 := by rw [this]; norm_num
    rw [hsq] at hp
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hp
  have hGint : (∫ a', G a' ∂(Measure.pi fun _ : Fin 4 => p)) ≤ 1 / 32 + 1 / 64 := by
    simp only [G]
    rw [integral_add (integrable_const _) ((integrable_const 1).indicator hBad), integral_const,
      probReal_univ, one_smul, integral_indicator_one hBad]
    linarith
  have hpre := OracleTemplate.StochasticGeneralized.prefix_preserving p (4 + mc)
  have hsplit := OracleTemplate.StochasticGeneralized.splitStream_preserving p 4
  have hFm : Measurable (S.indicator (1 : (Fin (4 + mc) → Ω) → ℝ)) := measurable_one.indicator hS
  have hcomp : (fun ξ : ℕ → Ω => S.indicator 1 (fun i : Fin (4 + mc) => ξ i)) =
      H ∘ (OracleTemplate.StochasticGeneralized.splitStream 4) := by
    funext ξ
    simp only [H, Function.comp_apply]
    congr 1
    funext i
    by_cases h : (i : ℕ) < 4
    · simp only [join, h, ↓reduceDIte]
      rfl
    · simp only [join, h, ↓reduceDIte]
      show ξ i = ξ (4 + ((i : ℕ) - 4))
      congr 1
      omega
  have hreal : (Measure.pi fun _ : Fin (4 + mc) => p).real S =
      ∫ z, H z ∂((Measure.pi fun _ : Fin 4 => p).prod (Measure.infinitePi fun _ : ℕ => p)) := by
    rw [← integral_indicator_one hS, ← hpre.map_eq,
      integral_map hpre.measurable.aemeasurable hFm.aestronglyMeasurable]
    change (∫ ξ, (fun ξ : ℕ → Ω => S.indicator 1 (fun i : Fin (4 + mc) => ξ i)) ξ
      ∂(Measure.infinitePi fun _ : ℕ => p)) = _
    rw [hcomp, Function.comp_def, hsplit.integral_comp' H]
  rw [show {ζ : Fin (4 + mc) → Ω | a < ‖blockEstimate r0 B 4 mc (fun l => V (ζ l)) -
      (u + ∫ ω, clip B (V ω - u) ∂p)‖} = S from rfl, hreal]
  linarith [hbound.2]

end LongTails.Proofs.HeavyTailedHighProbabilityBlock
