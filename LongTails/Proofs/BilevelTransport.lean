import LongTails.Proofs.BilevelImplicit

set_option maxSynthPendingDepth 5

namespace LongTails.Proofs.BilevelTransport

open Filter
open scoped Topology

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma tendsto_apply {ι : Type*} {l : Filter ι} {A : ι → E →L[ℝ] Y} {v : ι → E}
    {A0 : E →L[ℝ] Y} {v0 : E} (hA : Tendsto A l (𝓝 A0)) (hv : Tendsto v l (𝓝 v0)) :
    Tendsto (fun i => A i (v i)) l (𝓝 (A0 v0)) := by
  have hc : Continuous (fun p : (E →L[ℝ] Y) × E => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact (hc.tendsto (A0, v0)).comp (hA.prodMk_nhds hv)

lemma frozen_inverse_increment {H : ℝ → Y →L[ℝ] Y} {T : ℝ → E →L[ℝ] E →L[ℝ] Y}
    {U V : ℝ → E} {Z : ℝ → Y} (R : Y →L[ℝ] Y)
    (hR : ∀ v, R (H 0 v) = v) (hroot : ∀ t, H t (Z t) = -T t (U t) (V t)) (t : ℝ) :
    t⁻¹ • (Z t - Z 0) =
      -R (t⁻¹ • ((T t - T 0) (U t) (V t))) -
        R (T 0 (t⁻¹ • (U t - U 0)) (V t) + T 0 (U 0) (t⁻¹ • (V t - V 0)) +
          (t⁻¹ • (H t - H 0)) (Z t)) := by
  have he : H 0 (Z t - Z 0) =
      -((T t - T 0) (U t) (V t)) - T 0 (U t - U 0) (V t) -
        T 0 (U 0) (V t - V 0) - (H t - H 0) (Z t) := by
    simp only [map_sub, sub_apply]
    rw [hroot t, hroot 0]
    abel
  have hr := congrArg (fun v => t⁻¹ • R v) he
  rw [hR] at hr
  simp only [map_sub, map_neg, map_smul, map_add, smul_sub, smul_neg, smul_apply,
    sub_apply] at hr ⊢
  rw [hr]
  abel

lemma local_slope_bound {H : ℝ → Y →L[ℝ] Y} {T : ℝ → E →L[ℝ] E →L[ℝ] Y}
    {U V : ℝ → E} {Z : ℝ → Y} (R : Y →L[ℝ] Y)
    (hR : ∀ v, R (H 0 v) = v) (hroot : ∀ t, H t (Z t) = -T t (U t) (V t))
    {U' V' : E} {H' : Y →L[ℝ] Y}
    (hU : HasDerivAt U U' 0) (hV : HasDerivAt V V' 0) (hH : HasDerivAt H H' 0)
    (hZ : ContinuousAt Z 0) {A B : ℝ}
    (hA : ∀ t, t ≠ 0 → ‖R ((T t - T 0) (U t) (V t))‖ ≤ A * |t|)
    (hB : ‖R (T 0 U' (V 0) + T 0 (U 0) V' + H' (Z 0))‖ ≤ B)
    {r : ℝ} (hr : A + B < r) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖t⁻¹ • (Z t - Z 0)‖ < r := by
  let Bfun := fun t : ℝ => R (T 0 (t⁻¹ • (U t - U 0)) (V t) +
    T 0 (U 0) (t⁻¹ • (V t - V 0)) + (t⁻¹ • (H t - H 0)) (Z t))
  have hUs : Tendsto (fun t : ℝ => t⁻¹ • (U t - U 0)) (𝓝[≠] 0) (𝓝 U') := by
    simpa only [zero_add] using hU.tendsto_slope_zero
  have hVs : Tendsto (fun t : ℝ => t⁻¹ • (V t - V 0)) (𝓝[≠] 0) (𝓝 V') := by
    simpa only [zero_add] using hV.tendsto_slope_zero
  have hHs : Tendsto (fun t : ℝ => t⁻¹ • (H t - H 0)) (𝓝[≠] 0) (𝓝 H') := by
    simpa only [zero_add] using hH.tendsto_slope_zero
  have hBt : Tendsto Bfun (𝓝[≠] 0)
      (𝓝 (R (T 0 U' (V 0) + T 0 (U 0) V' + H' (Z 0)))) := by
    apply R.continuous.tendsto _ |>.comp
    exact ((tendsto_apply ((T 0).continuous.tendsto _ |>.comp hUs)
      (hV.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).add
      ((T 0 (U 0)).continuous.tendsto _ |>.comp hVs)).add
      (tendsto_apply hHs (hZ.tendsto.mono_left nhdsWithin_le_nhds))
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ‖Bfun t‖ < r - A :=
    hBt.norm.eventually (gt_mem_nhds (by linarith :
      ‖R (T 0 U' (V 0) + T 0 (U 0) V' + H' (Z 0))‖ < r - A))
  filter_upwards [hsmall, self_mem_nhdsWithin] with t ht ht0
  have htne : t ≠ 0 := ht0
  have hAn : ‖R (t⁻¹ • ((T t - T 0) (U t) (V t)))‖ ≤ A := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv]
    calc
      _ ≤ |t|⁻¹ * (A * |t|) := mul_le_mul_of_nonneg_left (hA t htne) (by positivity)
      _ = A := by field_simp
  rw [frozen_inverse_increment R hR hroot]
  have hn := norm_sub_le (-R (t⁻¹ • ((T t - T 0) (U t) (V t)))) (Bfun t)
  rw [norm_neg] at hn
  exact hn.trans_lt (by linarith)

lemma changing_tensor_bound (R : Y →L[ℝ] Y)
    (T0 T1 : E →L[ℝ] E →L[ℝ] Y) (u v : E)
    {q d : ℝ} (hd : 0 ≤ d)
    (hR : ‖R‖ ≤ q ^ 2) (hT : ‖T1 - T0‖ ≤ q ^ 2 * d)
    (hu : ‖u‖ ≤ q ^ 2) (hv : ‖v‖ ≤ q ^ 2) :
    ‖R ((T1 - T0) u v)‖ ≤ q ^ 8 * d := by
  calc
    _ ≤ ‖R‖ * ‖(T1 - T0) u v‖ := R.le_opNorm _
    _ ≤ ‖R‖ * (‖(T1 - T0) u‖ * ‖v‖) := by
      gcongr
      exact ((T1 - T0) u).le_opNorm v
    _ ≤ ‖R‖ * (‖T1 - T0‖ * ‖u‖ * ‖v‖) := by
      gcongr
      exact (T1 - T0).le_opNorm u
    _ ≤ q ^ 2 * (q ^ 2 * d * q ^ 2 * q ^ 2) := by gcongr
    _ = _ := by ring

end LongTails.Proofs.BilevelTransport
