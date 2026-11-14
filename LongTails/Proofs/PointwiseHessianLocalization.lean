import LongTails.Proofs.HessianStableNewton
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.PointwiseHessianLocalization

open LongTails.Proofs.HessianStableNewton

lemma psd_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : E →L[ℝ] E} {B : ℝ} (hB : 0 ≤ B)
    (hsa : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫)
    (hpos : ∀ v, 0 ≤ qf H v) (hb : ∀ v, qf H v ≤ B * ‖v‖ ^ 2)
    (w : E) : ‖H w‖ ^ 2 ≤ B * qf H w := by
  have habs : ∀ v, |qf H v| ≤ 1 * qf H v := fun v => by
    rw [one_mul, abs_of_nonneg (hpos v)]
  have hp := polarization hsa hpos habs w (H w)
  rw [real_inner_self_eq_norm_sq, one_mul] at hp
  have hroot : Real.sqrt (qf H (H w)) ≤ Real.sqrt B * ‖H w‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (H w)), ← Real.sqrt_mul hB]
    exact Real.sqrt_le_sqrt (hb (H w))
  have hm := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg (qf H w))
  have hnorm : ‖H w‖ ≤ Real.sqrt (qf H w) * Real.sqrt B := by
    rcases eq_or_lt_of_le (norm_nonneg (H w)) with hz | hz
    · rw [← hz]; positivity
    · nlinarith
  have hs := pow_le_pow_left₀ (norm_nonneg (H w)) hnorm 2
  rw [mul_pow, Real.sq_sqrt (hpos w), Real.sq_sqrt hB] at hs
  nlinarith


lemma unit_interval_transport {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H D : ℝ → F) (hder : ∀ t, HasDerivAt H (D t) t)
    (B : ℝ → ℝ) (hBc : Continuous B)
    (hBn : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ B t)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖D t‖ ≤ B t)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖H t - H s‖ ≤ ∫ u in (0 : ℝ)..1, B u := by
  have hordered (a b : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1)
      (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a ≤ b) :
      ‖H b - H a‖ ≤ ∫ u in (0 : ℝ)..1, B u := by
    have hh := norm_sub_le_integral_of_norm_deriv_le_of_le hab
      ((continuous_iff_continuousAt.mpr (fun x => (hder x).continuousAt)).continuousOn)
      (fun x _ => (hder x).differentiableAt.differentiableWithinAt)
      (Filter.Eventually.of_forall (fun u hu => by
        rw [(hder u).deriv]
        exact hbound u ⟨ha.1.trans hu.1.le, hu.2.le.trans hb.2⟩))
      (hBc.intervalIntegrable a b)
    apply hh.trans
    apply intervalIntegral.integral_mono_interval ha.1 hab hb.2
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
      exact hBn u ⟨hu.1.le, hu.2⟩
    · exact hBc.intervalIntegrable 0 1
  rcases le_total s t with h | h
  · exact hordered s t hs ht h
  · rw [norm_sub_rev]
    exact hordered t s ht hs h

lemma integrated_psd_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (H : ℝ → E →L[ℝ] E)
    (hc : Continuous H) {r B : ℝ} (hr : 0 ≤ r) (hB : 0 ≤ B)
    (hsa : ∀ t u v, ⟪H t u, v⟫ = ⟪u, H t v⟫)
    (hpos : ∀ t v, 0 ≤ qf (H t) v)
    (hb : ∀ t ∈ Set.Icc 0 r, ‖H t‖ ≤ B) (u : E) :
    ‖∫ t in (0 : ℝ)..r, H t u‖ ^ 2 ≤
      B * r * ⟪∫ t in (0 : ℝ)..r, H t u, u⟫ := by
  let A : E →L[ℝ] E := ∫ t in (0 : ℝ)..r, H t
  have hi : IntervalIntegrable H MeasureTheory.volume 0 r := hc.intervalIntegrable 0 r
  have happ (v : E) : A v = ∫ t in (0 : ℝ)..r, H t v :=
    ContinuousLinearMap.intervalIntegral_apply hi v
  have hinner (v w : E) : ⟪A v, w⟫ = ∫ t in (0 : ℝ)..r, ⟪H t v, w⟫ := by
    rw [happ]
    have hv : IntervalIntegrable (fun t => H t v) MeasureTheory.volume 0 r :=
      (hc.clm_apply continuous_const).intervalIntegrable 0 r
    have hh := (innerSL ℝ w).intervalIntegral_comp_comm hv
    simpa only [innerSL_apply_apply, real_inner_comm] using hh.symm
  have hAs : ∀ v w, ⟪A v, w⟫ = ⟪v, A w⟫ := by
    intro v w
    calc
      ⟪A v, w⟫ = ∫ t in (0 : ℝ)..r, ⟪H t v, w⟫ := hinner v w
      _ = ∫ t in (0 : ℝ)..r, ⟪H t w, v⟫ := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact (hsa t v w).trans (real_inner_comm _ _)
      _ = ⟪A w, v⟫ := (hinner w v).symm
      _ = ⟪v, A w⟫ := real_inner_comm _ _
  have hAp : ∀ v, 0 ≤ qf A v := by
    intro v
    unfold qf
    rw [hinner]
    exact intervalIntegral.integral_nonneg_of_forall hr (fun t => hpos t v)
  have hAn : ‖A‖ ≤ B * r := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := H) (a := 0) (b := r) (C := B) (fun t ht => hb t (by
        rw [Set.uIoc_of_le hr] at ht
        exact ⟨ht.1.le, ht.2⟩))
    simpa [A, abs_of_nonneg hr] using hh
  have hAb (v : E) : qf A v ≤ (B * r) * ‖v‖ ^ 2 := by
    have hh := norm_inner_le_norm (𝕜 := ℝ) (A v) v
    have hn := A.le_opNorm v
    have hn' := mul_le_mul_of_nonneg_right hAn (norm_nonneg v)
    have hn'' := mul_le_mul_of_nonneg_right (hn.trans hn') (norm_nonneg v)
    have hv := le_abs_self ⟪A v, v⟫
    dsimp [qf]
    rw [Real.norm_eq_abs] at hh
    nlinarith
  have hh := psd_norm_sq (mul_nonneg hB hr) hAs hAp hAb u
  simpa only [qf, happ] using hh

lemma ray_gradient_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (H : ℝ → E →L[ℝ] E)
    (G : ℝ → E) (d : E) (hc : Continuous H)
    (hder : ∀ t, HasDerivAt G (H t d) t) (hzero : G 0 = 0)
    {K : ℝ} (hK : 0 ≤ K)
    (hsa : ∀ t u v, ⟪H t u, v⟫ = ⟪u, H t v⟫)
    (hpos : ∀ t v, 0 ≤ qf (H t) v)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖H t‖ ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖G t‖ ^ 2 ≤ K * ⟪G t, d⟫ := by
  have he : (∫ u in (0 : ℝ)..t, H u d) = G t := by
    have hi : IntervalIntegrable (fun u => H u d) MeasureTheory.volume 0 t :=
      (hc.clm_apply continuous_const).intervalIntegrable 0 t
    simpa [hzero] using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hder u) hi
  have hh := integrated_psd_norm_sq H hc ht.1 hK hsa hpos
    (fun u hu => hb u ⟨hu.1, hu.2.trans ht.2⟩) d
  rw [he] at hh
  rcases eq_or_lt_of_le ht.1 with hz | hz
  · subst t
    simp [hzero]
  · have hn : 0 ≤ K * ⟪G t, d⟫ := by
      apply nonneg_of_mul_nonneg_left _ hz
      nlinarith [sq_nonneg ‖G t‖]
    have hm := mul_nonneg (show 0 ≤ 1 - t by linarith [ht.2]) hn
    nlinarith

lemma young_of_sq_le {g K v b : ℝ} (hg : 0 ≤ g) (hK : 0 ≤ K)
    (hv : 0 ≤ v) (hb : 0 ≤ b) (h : g ^ 2 ≤ K * v) :
    2 * b * g ≤ K + b ^ 2 * v := by
  have hp := mul_nonneg (sq_nonneg b) (show 0 ≤ K * v - g ^ 2 by linarith)
  have hs := sq_nonneg (K - b ^ 2 * v)
  have hn : 0 ≤ b ^ 2 * v := mul_nonneg (sq_nonneg b) hv
  have hbg : 0 ≤ b * g := mul_nonneg hb hg
  nlinarith

lemma unit_integral_localization (g v : ℝ → ℝ) (hg : Continuous g)
    (hv : Continuous v) {K a b : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hgn : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g t)
    (hvn : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ v t)
    (hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1, (g t) ^ 2 ≤ K * v t)
    (htransport : K ≤ a + b * ∫ t in (0 : ℝ)..1, g t) :
    K ≤ 2 * a + b ^ 2 * ∫ t in (0 : ℝ)..1, v t := by
  have hgi : IntervalIntegrable g MeasureTheory.volume 0 1 := hg.intervalIntegrable 0 1
  have hvi : IntervalIntegrable v MeasureTheory.volume 0 1 := hv.intervalIntegrable 0 1
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (hgi.const_mul (2 * b)) ((intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => K) MeasureTheory.volume 0 1).add
      (hvi.const_mul (b ^ 2)))
    (fun t ht => young_of_sq_le (hgn t ht) hK (hvn t ht) hb (hpoint t ht))
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add intervalIntegrable_const (hvi.const_mul (b ^ 2)),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hi
  simp only [sub_zero, one_smul] at hi
  linarith

lemma quadratic_closure {K a b : ℝ} (hK : 0 ≤ K)
    (h : K ≤ a + b * Real.sqrt K) : K ≤ 2 * a + b ^ 2 := by
  have hs := Real.sq_sqrt hK
  have hy := sq_nonneg (Real.sqrt K - b)
  nlinarith

lemma rejected_fraction {q q' t t' : ℝ} (hq : 0 ≤ q)
    (ht : 0 < t) (htb : t ≤ 7 / 10) (ht' : 0 < t')
    (h : q * t ^ 2 = 1 - t) (h' : q' * t' ^ 2 = 1 - t')
    (hqq : 2 * q ≤ q') : t' ≤ 5 * t / 6 := by
  by_contra hn
  have hlt : 5 * t / 6 < t' := lt_of_not_ge hn
  have hs : 25 * t ^ 2 < 36 * t' ^ 2 := by nlinarith
  have hp := mul_nonneg hq (show 0 ≤ 36 * t' ^ 2 - 25 * t ^ 2 by linarith)
  have hp' := mul_nonneg (show 0 ≤ q' - 2 * q by linarith) (sq_nonneg t')
  nlinarith

lemma accepted_fraction {q q' t t' : ℝ} (hq : 0 ≤ q)
    (ht : 0 < t) (ht' : 0 < t')
    (h : q * t ^ 2 = 1 - t) (h' : q' * t' ^ 2 = 1 - t')
    (hqq : q / 2 ≤ q') : t' ≤ 3 * t / 2 := by
  by_contra hn
  have hlt : 3 * t / 2 < t' := lt_of_not_ge hn
  have hs : 2 * t ^ 2 < t' ^ 2 := by nlinarith
  have hp := mul_nonneg hq (show 0 ≤ t' ^ 2 - 2 * t ^ 2 by linarith)
  have hp' := mul_nonneg (show 0 ≤ 2 * q' - q by linarith) (sq_nonneg t')
  nlinarith

lemma fraction_sum (t : ℕ → ℝ) (accepted : ℕ → Bool)
    (ht : ∀ k, 0 ≤ t k)
    (ha : ∀ k, accepted k = true → t (k + 1) ≤ 3 * t k / 2)
    (hr : ∀ k, accepted k = false → t (k + 1) ≤ 5 * t k / 6)
    (n : ℕ) :
    ∑ k ∈ Finset.range n, t k ≤ 6 * t 0 +
      4 * ∑ k ∈ Finset.range n, if accepted k then t k else 0 := by
  have haux (m : ℕ) :
      (∑ k ∈ Finset.range m, t k) + 6 * t m ≤ 6 * t 0 +
        4 * ∑ k ∈ Finset.range m, if accepted k then t k else 0 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      cases he : accepted m with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
        have hh := hr m he
        linarith
      | true =>
        simp only [↓reduceIte]
        have hh := ha m he
        linarith
  have := haux n
  have := ht n
  linarith

end LongTails.Proofs.PointwiseHessianLocalization
