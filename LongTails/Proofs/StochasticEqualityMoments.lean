import LongTails.Algorithms.StochasticEquality
import LongTails.Proofs.AdaptivePilotConfidence
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.MixedNoiseMoments
import LongTails.Proofs.TerminalClippingEnergy
import Mathlib.Analysis.InnerProductSpace.ProdL2

namespace LongTails.Proofs.StochasticEqualityMoments

open MeasureTheory OracleTemplate
open LongTails.Setups.StochasticRegularEqualities
open LongTails.Algorithms.StochasticEquality
open LongTails.Algorithms.MatrixPolar

abbrev HilbertReply (p : Public) := WithLp 2 (Point p.d × WithLp 2 (Point p.m × Space p.d p.m))

noncomputable def pack (p : Public) : Reply p ≃L[ℝ] HilbertReply p :=
  ((ContinuousLinearEquiv.refl ℝ (Point p.d)).prodCongr
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Point p.m) (Space p.d p.m)).symm).trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ (Point p.d)
      (WithLp 2 (Point p.m × Space p.d p.m))).symm

lemma pack_apply (p : Public) (v : Reply p) :
    pack p v = WithLp.toLp 2 (v.1, WithLp.toLp 2 (v.2.1, v.2.2)) := rfl

lemma pack_norm_sq (p : Public) (v : Reply p) :
    ‖pack p v‖ ^ 2 = ‖v.1‖ ^ 2 + ‖v.2.1‖ ^ 2 + ‖v.2.2‖ ^ 2 := by
  simp only [pack_apply, WithLp.prod_norm_sq_eq_of_L2, WithLp.fst, WithLp.snd]
  ring

lemma pack_clip_contraction (p : Public) {G M : ℝ} (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hL : 0 ≤ p.Lc) (u v : Reply p) (huG : ‖u.1‖ ≤ G) (huM : ‖u.2.1‖ ≤ M)
    (huJ : ‖u.2.2‖ ≤ p.Lc) :
    ‖pack p (clipReply p G M v) - pack p u‖ ^ 2 ≤ ‖pack p v - pack p u‖ ^ 2 := by
  rw [← map_sub, ← map_sub, pack_norm_sq, pack_norm_sq]
  have hg := pow_le_pow_left₀ (norm_nonneg _) (norm_clip_sub_le hG huG v.1) 2
  have hc := pow_le_pow_left₀ (norm_nonneg _) (norm_clip_sub_le hM huM v.2.1) 2
  have hj := pow_le_pow_left₀ (norm_nonneg _) (norm_clip_sub_le hL huJ v.2.2) 2
  exact add_le_add (add_le_add hg hc) hj

lemma component_errors_le_pack (p : Public) (u v : Reply p) :
    ‖v.1 - u.1‖ ≤ ‖pack p v - pack p u‖ ∧
    ‖v.2.1 - u.2.1‖ ≤ ‖pack p v - pack p u‖ ∧
    ‖v.2.2 - u.2.2‖ ≤ ‖pack p v - pack p u‖ := by
  have he := pack_norm_sq p (v - u)
  rw [map_sub] at he
  change ‖pack p v - pack p u‖ ^ 2 =
    ‖v.1 - u.1‖ ^ 2 + ‖v.2.1 - u.2.1‖ ^ 2 + ‖v.2.2 - u.2.2‖ ^ 2 at he
  constructor
  · nlinarith [norm_nonneg (pack p v - pack p u), sq_nonneg ‖v.2.1 - u.2.1‖,
      sq_nonneg ‖v.2.2 - u.2.2‖]
  constructor
  · nlinarith [norm_nonneg (pack p v - pack p u), sq_nonneg ‖v.1 - u.1‖,
      sq_nonneg ‖v.2.2 - u.2.2‖]
  · nlinarith [norm_nonneg (pack p v - pack p u), sq_nonneg ‖v.1 - u.1‖,
      sq_nonneg ‖v.2.1 - u.2.1‖]

lemma pack_error_bound (p : Public) {G M : ℝ} (u v : Reply p)
    (huG : ‖u.1‖ ≤ G) (huM : ‖u.2.1‖ ≤ M) (huJ : ‖u.2.2‖ ≤ p.Lc)
    (hvG : ‖v.1‖ ≤ G) (hvM : ‖v.2.1‖ ≤ M) (hvJ : ‖v.2.2‖ ≤ p.Lc) :
    ‖pack p v - pack p u‖ ^ 2 ≤ 4 * (G ^ 2 + M ^ 2 + p.Lc ^ 2) := by
  have hg := pow_le_pow_left₀ (norm_nonneg (v.1 - u.1))
    ((norm_sub_le v.1 u.1).trans (add_le_add hvG huG)) 2
  have hc := pow_le_pow_left₀ (norm_nonneg (v.2.1 - u.2.1))
    ((norm_sub_le v.2.1 u.2.1).trans (add_le_add hvM huM)) 2
  have hj := pow_le_pow_left₀ (norm_nonneg (v.2.2 - u.2.2))
    ((norm_sub_le v.2.2 u.2.2).trans (add_le_add hvJ huJ)) 2
  rw [← map_sub, pack_norm_sq]
  change ‖v.1 - u.1‖ ^ 2 + ‖v.2.1 - u.2.1‖ ^ 2 + ‖v.2.2 - u.2.2‖ ^ 2 ≤ _
  nlinarith

lemma pack_batch_mean (p : Public) {n : ℕ} (v : Fin n → Reply p) :
    pack p ((n : ℝ)⁻¹ • ∑ i, v i) = (n : ℝ)⁻¹ • ∑ i, pack p (v i) := by
  rw [map_smul, map_sum]

lemma pack_reset_centered (p : Public) (n : ℕ) (hn : 0 < n)
    (v : Fin n → Reply p) (u : Reply p) :
    pack p ((n : ℝ)⁻¹ • ∑ i, v i) - pack p u =
      (n : ℝ)⁻¹ • ∑ i, (pack p (v i) - pack p u) := by
  rw [pack_batch_mean]
  simpa only [one_div, id_eq] using RobustGradient.finite_mean_centered
    (X := fun i => pack p (v i)) (pack p u) n hn id

lemma pack_increment_centered (p : Public) (n : ℕ) (hn : 0 < n)
    (v w : Fin n → Reply p) (estimate u z : Reply p) :
    pack p (estimate + (n : ℝ)⁻¹ • ∑ i, (v i - w i)) - pack p u =
      (pack p estimate - pack p z) + (n : ℝ)⁻¹ •
        ∑ i, ((pack p (v i) - pack p u) - (pack p (w i) - pack p z)) := by
  have hc := pack_reset_centered p n hn (fun i => v i - w i) (u - z)
  simp only [map_sub] at hc
  have he (i : Fin n) : (pack p (v i) - pack p u) - (pack p (w i) - pack p z) =
      (pack p (v i) - pack p (w i)) - (pack p u - pack p z) := by abel
  simp_rw [he]
  rw [← hc, map_add]
  abel

lemma pack_integrable {Ω : Type*} [MeasurableSpace Ω] (p : Public) {P : Measure Ω}
    {v : Ω → Reply p} (hv : Integrable v P) : Integrable (fun ω => pack p (v ω)) P :=
  (pack p).toContinuousLinearMap.integrable_comp hv

lemma pack_mean {Ω : Type*} [MeasurableSpace Ω] (p : Public) {P : Measure Ω}
    {v : Ω → Reply p} (hv : Integrable v P) (u : Reply p) (hu : ∫ ω, v ω ∂P = u) :
    (∫ ω, pack p (v ω) ∂P) = pack p u := by
  calc
    _ = pack p (∫ ω, v ω ∂P) := (pack p).toContinuousLinearMap.integral_comp_comm hv
    _ = pack p u := congrArg (pack p) hu

lemma measurable_centered_oracle {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (g : Point p.d → Ω → Reply p) (hg : Measurable (Function.uncurry g))
    (u : Point p.d → Reply p) (hu : Measurable u) :
    Measurable (Function.uncurry (fun x ω => pack p (g x ω) - pack p (u x))) :=
  ((pack p).continuous.measurable.comp hg).sub
    ((pack p).continuous.measurable.comp (hu.comp measurable_fst))

lemma integrable_centered_oracle {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (P : Measure Ω) [IsFiniteMeasure P] (g : Ω → Reply p) (hg : Integrable g P) (u : Reply p) :
    Integrable (fun ω => pack p (g ω) - pack p u) P :=
  (pack_integrable p hg).sub (integrable_const _)

lemma mean_centered_oracle {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (P : Measure Ω) [IsProbabilityMeasure P] (g : Ω → Reply p)
    (hg : Integrable g P) (u : Reply p) (hmean : ∫ ω, g ω ∂P = u) :
    (∫ ω, pack p (g ω) - pack p u ∂P) = 0 := by
  rw [integral_sub (pack_integrable p hg) (integrable_const _), pack_mean p hg u hmean]
  simp

lemma batch_variance {Ω : Type*} [MeasurableSpace Ω] (p : Public) {P : Measure Ω}
    [IsProbabilityMeasure P] (v : Ω → Reply p) (hm : Measurable v) (hi : Integrable v P)
    (u : Reply p) (hmean : ∫ ω, v ω ∂P = u)
    (h2 : Integrable (fun ω => ‖pack p (v ω) - pack p u‖ ^ 2) P)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ : Fin n → Ω =>
      ‖pack p ((n : ℝ)⁻¹ • ∑ i, v (ξ i)) - pack p u‖ ^ 2)
      (Measure.pi fun _ : Fin n => P) ∧
    (∫ ξ : Fin n → Ω, ‖pack p ((n : ℝ)⁻¹ • ∑ i, v (ξ i)) - pack p u‖ ^ 2
      ∂Measure.pi (fun _ : Fin n => P)) = (∫ ω, ‖pack p (v ω) - pack p u‖ ^ 2 ∂P) / n := by
  simp_rw [pack_batch_mean]
  simpa only [one_div, Function.comp_def] using RobustGradient.finite_mean_variance
    ((pack p).continuous.measurable.comp hm) (pack_integrable p hi) (pack p u) h2
    (pack_mean p hi u hmean) n hn

lemma centered_difference {Ω : Type*} [MeasurableSpace Ω] (p : Public) {P : Measure Ω}
    [IsProbabilityMeasure P] (v w : Ω → Reply p) (hv : Integrable v P) (hw : Integrable w P)
    (u z : Reply p) (hu : ∫ ω, v ω ∂P = u) (hz : ∫ ω, w ω ∂P = z)
    (h2 : Integrable (fun ω => ‖pack p (v ω) - pack p (w ω)‖ ^ 2) P) :
    Integrable (fun ω => ‖(pack p (v ω) - pack p u) - (pack p (w ω) - pack p z)‖ ^ 2) P ∧
    (∫ ω, ‖(pack p (v ω) - pack p u) - (pack p (w ω) - pack p z)‖ ^ 2 ∂P) ≤
      ∫ ω, ‖pack p (v ω) - pack p (w ω)‖ ^ 2 ∂P := by
  have h := TerminalClipping.centered_second_moment
    ((pack_integrable p hv).sub (pack_integrable p hw)) h2
  simp only [Pi.sub_apply] at h
  rw [integral_sub (pack_integrable p hv) (pack_integrable p hw),
    pack_mean p hv u hu, pack_mean p hw z hz] at h
  have he (ω : Ω) : (pack p (v ω) - pack p u) - (pack p (w ω) - pack p z) =
      (pack p (v ω) - pack p (w ω)) - (pack p u - pack p z) := by abel
  simp_rw [he]
  exact h

lemma masked_batch_variance {Ω Y : Type} [MeasurableSpace Ω] [MeasurableSpace Y]
    (p : Public) (P : Measure Ω) [IsProbabilityMeasure P] (offset : ℕ)
    (S : (ℕ → Ω) → Y) (hS : Measurable S)
    (hdep : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → S ξ = S ζ)
    (active : Y → Prop) [DecidablePred active] (ha : MeasurableSet {y | active y})
    (B : Y → HilbertReply p) (hB : Measurable B)
    (hB2 : Integrable (fun ξ => ‖if active (S ξ) then B (S ξ) else 0‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => P))
    (W : Y → Ω → HilbertReply p) (hW : Measurable (Function.uncurry W))
    (hWi : ∀ y, Integrable (W y) P) (hW0 : ∀ y, ∫ ω, W y ω ∂P = 0)
    (hW2 : ∀ y, Integrable (fun ω => ‖W y ω‖ ^ 2) P)
    (w : Y → ℝ) (hw : ∀ y, (∫ ω, ‖W y ω‖ ^ 2 ∂P) ≤ w y)
    (hwi : Integrable (fun ξ => if active (S ξ) then w (S ξ) else 0)
      (Measure.infinitePi fun _ : ℕ => P)) (b : ℕ) (hb : 0 < b) :
    Integrable (fun ξ : ℕ → Ω => ‖if active (S ξ) then
      B (S ξ) + (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b, W (S ξ) (ξ (offset + i)) else 0‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ : ℕ → Ω, ‖if active (S ξ) then
      B (S ξ) + (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b, W (S ξ) (ξ (offset + i)) else 0‖ ^ 2
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      (∫ ξ, ‖if active (S ξ) then B (S ξ) else 0‖ ^ 2
        ∂Measure.infinitePi (fun _ : ℕ => P)) +
      (∫ ξ, if active (S ξ) then w (S ξ) else 0
        ∂Measure.infinitePi (fun _ : ℕ => P)) / b := by
  let B₀ := fun ξ => if active (S ξ) then B (S ξ) else 0
  let W₀ := fun y ω => if active y then W y ω else 0
  let w₀ := fun y => if active y then w y else 0
  have hB₀ : Measurable B₀ := (hB.comp hS).ite (ha.preimage hS) measurable_const
  have hdB : ∀ ξ ζ, (∀ i, i < offset → ξ i = ζ i) → B₀ ξ = B₀ ζ := by
    intro ξ ζ he
    dsimp [B₀]
    rw [hdep ξ ζ he]
  have hW₀ : Measurable (Function.uncurry W₀) :=
    hW.ite (ha.preimage measurable_fst) measurable_const
  have hi (y : Y) : Integrable (W₀ y) P := by
    by_cases hy : active y
    · simpa only [W₀, hy, ↓reduceIte] using hWi y
    · simp only [W₀, hy, ↓reduceIte]
      exact integrable_const 0
  have hz (y : Y) : (∫ ω, W₀ y ω ∂P) = 0 := by
    by_cases hy : active y
    · simpa only [W₀, hy, ↓reduceIte] using hW0 y
    · simp [W₀, hy]
  have hi2 (y : Y) : Integrable (fun ω => ‖W₀ y ω‖ ^ 2) P := by
    by_cases hy : active y
    · simpa only [W₀, hy, ↓reduceIte] using hW2 y
    · simp [W₀, hy]
  have hbound (y : Y) : (∫ ω, ‖W₀ y ω‖ ^ 2 ∂P) ≤ w₀ y := by
    by_cases hy : active y
    · simpa only [W₀, w₀, hy, ↓reduceIte] using hw y
    · simp [W₀, w₀, hy]
  have h := MixedNoise.batch_average_variable_variance P offset S hS hdep B₀ hB₀ hdB hB2
    W₀ hW₀ hi hz hi2 w₀ hbound hwi b hb
  have he (ξ : ℕ → Ω) : B₀ ξ + (b : ℝ)⁻¹ •
      ∑ i ∈ Finset.range b, W₀ (S ξ) (ξ (offset + i)) =
      if active (S ξ) then B (S ξ) + (b : ℝ)⁻¹ •
        ∑ i ∈ Finset.range b, W (S ξ) (ξ (offset + i)) else 0 := by
    by_cases hy : active (S ξ) <;> simp [B₀, W₀, hy]
  simp_rw [he] at h
  exact h

lemma masked_clip_error_bound {X : Type*} [MeasurableSpace X] (p : Public)
    (P : Measure X) (active : X → Prop) [DecidablePred active]
    (ha : MeasurableSet {z | active z}) (u v : X → Reply p)
    (hu : Measurable u) {G M : ℝ}
    (hG : 0 ≤ G) (hM : 0 ≤ M) (hL : 0 ≤ p.Lc)
    (hcaps : ∀ z, active z → ‖(u z).1‖ ≤ G ∧ ‖(u z).2.1‖ ≤ M ∧ ‖(u z).2.2‖ ≤ p.Lc)
    (hclip : Measurable (fun z => clipReply p G M (v z)))
    (hi : Integrable (fun z => if active z then ‖pack p (v z) - pack p (u z)‖ ^ 2 else 0) P) :
    Integrable (fun z => if active z then
      ‖pack p (clipReply p G M (v z)) - pack p (u z)‖ ^ 2 else 0) P ∧
    (∫ z, if active z then ‖pack p (clipReply p G M (v z)) - pack p (u z)‖ ^ 2 else 0 ∂P) ≤
      ∫ z, if active z then ‖pack p (v z) - pack p (u z)‖ ^ 2 else 0 ∂P := by
  have hm : Measurable (fun z => if active z then
      ‖pack p (clipReply p G M (v z)) - pack p (u z)‖ ^ 2 else 0) :=
    ((((pack p).continuous.measurable.comp hclip).sub
    ((pack p).continuous.measurable.comp hu)).norm.pow_const 2).ite ha measurable_const
  have hle (z : X) : (if active z then
      ‖pack p (clipReply p G M (v z)) - pack p (u z)‖ ^ 2 else 0) ≤
      if active z then ‖pack p (v z) - pack p (u z)‖ ^ 2 else 0 := by
    split_ifs with hz
    · obtain ⟨hg, hc, hj⟩ := hcaps z hz
      exact pack_clip_contraction p hG hM hL (u z) (v z) hg hc hj
    · rfl
  have hn (z : X) : 0 ≤ (if active z then
      ‖pack p (clipReply p G M (v z)) - pack p (u z)‖ ^ 2 else 0) := by
    split_ifs <;> positivity
  have hi' := hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hn z)]
    exact hle z)
  exact ⟨hi', integral_mono hi' hi hle⟩

lemma shifted_sum_bound (m a : ℕ → ℝ) (T : ℕ) (hm : m 0 = 0)
    (ha : ∀ k, 0 ≤ a k) (hstep : ∀ k, m (k + 1) ≤ a k) :
    ∑ k ∈ Finset.range T, m k ≤ ∑ k ∈ Finset.range T, a k := by
  cases T with
  | zero => simp
  | succ T =>
    rw [Finset.sum_range_succ' m, hm, add_zero, Finset.sum_range_succ]
    have hs := Finset.sum_le_sum (s := Finset.range T) (fun k _ => hstep k)
    linarith [ha T]

def epochWeight (q T k : ℕ) : ℕ := min (q - k % q) (T - k)

lemma epochWeight_last {q T : ℕ} (hq : 0 < q) (hT : 0 < T) : epochWeight q T (T - 1) = 1 := by
  have hm := Nat.mod_lt (T - 1) hq
  unfold epochWeight
  omega

lemma epochWeight_next {q T k : ℕ} (hq : 0 < q) (hk : k + 1 < T) :
    if (k + 1) % q = 0 then epochWeight q T k = 1
    else epochWeight q T k = epochWeight q T (k + 1) + 1 := by
  have hm := Nat.mod_lt k hq
  have he := Nat.mod_add_mod k q 1
  by_cases hl : k % q + 1 < q
  · rw [Nat.mod_eq_of_lt hl] at he
    simp only [epochWeight]
    split_ifs <;> omega
  · have heq : k % q + 1 = q := by omega
    rw [heq, Nat.mod_self] at he
    simp only [← he, ↓reduceIte, epochWeight]
    omega

lemma reset_sum_bound (e d : ℕ → ℝ) (v : ℝ) (q T : ℕ) (hq : 0 < q)
    (hd : ∀ k < T, 0 ≤ d k)
    (hreset : ∀ k < T, k % q = 0 → e k ≤ v)
    (hinc : ∀ k, k + 1 < T → (k + 1) % q ≠ 0 → e (k + 1) ≤ e k + d (k + 1)) :
    ∑ k ∈ Finset.range T, e k ≤ T * v + q * ∑ k ∈ Finset.range T, d k := by
  by_cases hT : T = 0
  · simp [hT]
  have hTpos : 0 < T := by omega
  have hstep (k : ℕ) (hk : k + 1 < T) :
      (e k - v) + (epochWeight q T (k + 1) : ℝ) * (e (k + 1) - v) ≤
        (epochWeight q T k : ℝ) * (e k - v) + q * d (k + 1) := by
    have hw := epochWeight_next hq hk
    have hnonneg : (0 : ℝ) ≤ epochWeight q T (k + 1) := Nat.cast_nonneg _
    have hle : (epochWeight q T (k + 1) : ℝ) ≤ q := by
      exact_mod_cast (min_le_left (q - (k + 1) % q) (T - (k + 1))).trans (Nat.sub_le _ _)
    by_cases hr : (k + 1) % q = 0
    · simp only [hr, ↓reduceIte] at hw
      rw [hw, Nat.cast_one, one_mul]
      have hm := mul_nonpos_of_nonneg_of_nonpos hnonneg (sub_nonpos.mpr (hreset _ hk hr))
      have hh := mul_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q) (hd _ hk)
      linarith
    · simp only [hr, ↓reduceIte] at hw
      rw [hw, Nat.cast_add, Nat.cast_one]
      have hm := mul_le_mul_of_nonneg_left (hinc k hk hr) hnonneg
      have hh := mul_le_mul_of_nonneg_right hle (hd _ hk)
      nlinarith
  have hb : ∀ n < T,
      (∑ k ∈ Finset.range n, (e k - v)) + (epochWeight q T n : ℝ) * (e n - v) ≤
        q * ∑ k ∈ Finset.range (n + 1), d k := by
    intro n hn
    induction n with
    | zero =>
      simp only [Finset.sum_range_zero, Finset.sum_range_one, zero_add]
      have he := hreset 0 hTpos (Nat.zero_mod q)
      exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.mpr he)).trans
        (mul_nonneg (Nat.cast_nonneg q) (hd 0 hTpos))
    | succ n ih =>
      have hi := ih (by omega)
      have hs := hstep n hn
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith
  have hf := hb (T - 1) (by omega)
  rw [epochWeight_last hq hTpos, Nat.cast_one, one_mul, ← Finset.sum_range_succ] at hf
  have he : T - 1 + 1 = T := by omega
  rw [he] at hf
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hf
  linarith

lemma pilot_component_confidence {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (V : Ω → E) (hV : Measurable V) (hVi : Integrable V P) (u : E)
    (hmean : ∫ w, V w ∂P = u) (hV2 : Integrable (fun w => ‖V w - u‖ ^ 2) P)
    {σ t : ℝ} (hvar : (∫ w, ‖V w - u‖ ^ 2 ∂P) ≤ σ ^ 2) (ht : 0 < t)
    (k b : ℕ) (hb : 0 < b) (hsize : σ ^ 2 / (b : ℝ) ≤ t ^ 2 / 144) :
    (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin b => P)
      {z | t < ‖RobustGradient.pilotCenter (2 * t)
        (fun i => (1 / (b : ℝ)) • ∑ j, V (z i j)) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  have hsize' : (σ ^ 2 / (b : ℝ)) / ((2 * t) / 6) ^ 2 ≤ (1 / 16 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < (2 * t) / 6))).mpr
    nlinarith only [hsize]
  have hh := RobustGradient.pilot_means_failure_probability_le hV hVi u hmean hV2 hvar
    (show 0 < 2 * t by positivity) (show (0 : ℝ) < 1 / 16 by norm_num)
    (show (1 / 16 : ℝ) ≤ 1 by norm_num) k b hb hsize'
  have hsqrt : Real.sqrt (1 / 16 : ℝ) = 1 / 4 := by
    norm_num [Real.sqrt_div]
  simpa only [hsqrt, show 2 * (1 / 4 : ℝ) = 1 / 2 by norm_num,
    show 2 * t / 2 = t by ring] using hh

lemma dominated_second_moment {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F]
    (P : Measure Ω) (V : Ω → E) (W : Ω → F) (hV : Measurable V)
    (hW : Integrable (fun w => ‖W w‖ ^ 2) P) (hbound : ∀ w, ‖V w‖ ≤ ‖W w‖) :
    Integrable (fun w => ‖V w‖ ^ 2) P ∧
      (∫ w, ‖V w‖ ^ 2 ∂P) ≤ ∫ w, ‖W w‖ ^ 2 ∂P := by
  have hb (w : Ω) : ‖V w‖ ^ 2 ≤ ‖W w‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hbound w) 2
  have hi : Integrable (fun w => ‖V w‖ ^ 2) P := by
    apply hW.mono' (hV.norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun w => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖V w‖)] using hb w)
  exact ⟨hi, integral_mono hi hW hb⟩

lemma component_variance_bounds {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (P : Measure Ω) (g : Ω → Reply p) (hg : Measurable g) (u : Reply p)
    (h2 : Integrable (fun w => ‖pack p (g w) - pack p u‖ ^ 2) P) {σ : ℝ}
    (hv : (∫ w, ‖pack p (g w) - pack p u‖ ^ 2 ∂P) ≤ σ ^ 2) :
    (Integrable (fun w => ‖(g w).1 - u.1‖ ^ 2) P ∧
      (∫ w, ‖(g w).1 - u.1‖ ^ 2 ∂P) ≤ σ ^ 2) ∧
    (Integrable (fun w => ‖(g w).2.1 - u.2.1‖ ^ 2) P ∧
      (∫ w, ‖(g w).2.1 - u.2.1‖ ^ 2 ∂P) ≤ σ ^ 2) ∧
    (Integrable (fun w => ‖(g w).2.2 - u.2.2‖ ^ 2) P ∧
      (∫ w, ‖(g w).2.2 - u.2.2‖ ^ 2 ∂P) ≤ σ ^ 2) := by
  have h₁ := dominated_second_moment P (fun w => (g w).1 - u.1)
    (fun w => pack p (g w) - pack p u) (hg.fst.sub measurable_const) h2
    (fun w => (component_errors_le_pack p u (g w)).1)
  have h₂ := dominated_second_moment P (fun w => (g w).2.1 - u.2.1)
    (fun w => pack p (g w) - pack p u) (hg.snd.fst.sub measurable_const) h2
    (fun w => (component_errors_le_pack p u (g w)).2.1)
  have h₃ := dominated_second_moment P (fun w => (g w).2.2 - u.2.2)
    (fun w => pack p (g w) - pack p u) (hg.snd.snd.sub measurable_const) h2
    (fun w => (component_errors_le_pack p u (g w)).2.2)
  exact ⟨⟨h₁.1, h₁.2.trans hv⟩, ⟨h₂.1, h₂.2.trans hv⟩, ⟨h₃.1, h₃.2.trans hv⟩⟩

end LongTails.Proofs.StochasticEqualityMoments
