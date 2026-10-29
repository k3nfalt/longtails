import LongTails.Proofs.PLMinimaxGeometry
import Mathlib.Analysis.SpecificLimits.Basic

open Set Metric Filter Topology
open scoped RealInnerProductSpace

namespace OracleTemplate.PLMinimax

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

lemma bounded_linearized_lift {F : W → W} {K : W →L[ℝ] W} {P : E →L[ℝ] W}
    {w : W} {C ρ : ℝ} (_hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (htaylor : ∀ s, ‖F (w + s) - K s‖ ≤ ρ * ‖s‖ ^ 2)
    (hsol : ∀ h, ∃ q, F q = P h ∧ ‖q - w‖ ≤ C * ‖h‖) (h : E) :
    ∃ v, K v = P h ∧ ‖v‖ ≤ C * ‖h‖ := by
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht : ∀ n, 0 < t n := fun n => by dsimp [t]; positivity
  choose q hq hqn using fun n : ℕ => hsol (t n • h)
  let v : ℕ → W := fun n => (t n)⁻¹ • (q n - w)
  have hv : ∀ n, ‖v n‖ ≤ C * ‖h‖ := by
    intro n
    have hh := hqn n
    rw [norm_smul, Real.norm_of_nonneg (ht n).le] at hh
    dsimp [v]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (ht n).le)]
    calc (t n)⁻¹ * ‖q n - w‖ ≤ (t n)⁻¹ * (C * (t n * ‖h‖)) :=
          mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (ht n).le)
      _ = C * ‖h‖ := by field_simp [ne_of_gt (ht n)]
  have hres : ∀ n, ‖K (v n) - P h‖ ≤ ρ * C ^ 2 * ‖h‖ ^ 2 * t n := by
    intro n
    have hh := htaylor (q n - w)
    rw [add_sub_cancel, hq n, map_smul] at hh
    have hvn := hv n
    have htv : q n - w = t n • v n := by
      dsimp [v]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (ht n)), one_smul]
    rw [htv, map_smul, ← smul_sub, norm_smul, Real.norm_of_nonneg (ht n).le,
      norm_smul, Real.norm_of_nonneg (ht n).le, norm_sub_rev] at hh
    have hs : ‖v n‖ ^ 2 ≤ C ^ 2 * ‖h‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg (v n)) hvn 2
      simpa only [mul_pow] using this
    have hh' : ‖K (v n) - P h‖ ≤ ρ * t n * ‖v n‖ ^ 2 := by
      have hp := ht n
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hρ (ht n).le)]
  obtain ⟨vstar, hvstar, a, ha, hlim⟩ :=
    (isCompact_closedBall (0 : W) (C * ‖h‖)).tendsto_subseq
      (fun n => by simpa [mem_closedBall, dist_eq_norm] using hv n)
  refine ⟨vstar, ?_, ?_⟩
  · have hl : Tendsto (fun n => ‖K (v (a n)) - P h‖) atTop (𝓝 ‖K vstar - P h‖) :=
      ((K.continuous.tendsto vstar).comp hlim |>.sub_const (P h)).norm
    have ht0 : Tendsto t atTop (𝓝 0) := by
      simpa [t] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hr := ((ht0.comp ha.tendsto_atTop).const_mul (ρ * C ^ 2 * ‖h‖ ^ 2))
    have hz : ‖K vstar - P h‖ ≤ 0 := by
      simpa using le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun n => hres (a n))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hz)
  · simpa [mem_closedBall, dist_eq_norm] using hvstar

omit [FiniteDimensional ℝ W] in
lemma primal_linear_lift (K : W →L[ℝ] W) (P : E →L[ℝ] W) (π : W →L[ℝ] E)
    {C : ℝ} (hker : ∀ v, K v = 0 → π v = 0)
    (hlift : ∀ h, ∃ v, K v = P h ∧ ‖v‖ ≤ C * ‖h‖) :
    ∃ Q : E →L[ℝ] E, (∀ h v, K v = P h → π v = Q h) ∧
      ∀ h, ∃ v, K v = P h ∧ π v = Q h ∧ ‖v‖ ≤ C * ‖h‖ := by
  choose R hR hRn using hlift
  have huniq : ∀ h v, K v = P h → π v = π (R h) := by
    intro h v hv
    have hh := hker (v - R h) (by simp [map_sub, hv, hR])
    simpa only [map_sub, sub_eq_zero] using hh
  let Q : E →ₗ[ℝ] E :=
    { toFun := fun h => π (R h)
      map_add' := fun a b => by
        have hh := huniq (a + b) (R a + R b) (by simp [hR])
        simpa only [map_add] using hh.symm
      map_smul' := fun a b => by
        have hh := huniq (a • b) (a • R b) (by simp [hR])
        simpa only [map_smul, RingHom.id_apply] using hh.symm }
  have hbound : ∀ h, ‖Q h‖ ≤ (‖π‖ * C) * ‖h‖ := by
    intro h
    calc ‖Q h‖ = ‖π (R h)‖ := rfl
      _ ≤ ‖π‖ * ‖R h‖ := π.le_opNorm (R h)
      _ ≤ ‖π‖ * (C * ‖h‖) := mul_le_mul_of_nonneg_left (hRn h) (norm_nonneg π)
      _ = (‖π‖ * C) * ‖h‖ := by ring
  refine ⟨Q.mkContinuous (‖π‖ * C) hbound, ?_, ?_⟩
  · exact huniq
  · intro h
    exact ⟨R h, hR h, rfl, hRn h⟩

lemma implicit_primal_derivative {F : W → W} {K : W →L[ℝ] W} {P : E →L[ℝ] W}
    {π : W →L[ℝ] E} {U : E → E} {z : E} {w : W} {B C ρ : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hw : π w = U z)
    (hker : ∀ v, K v = 0 → π v = 0)
    (htaylor : ∀ s, ‖F (w + s) - K s‖ ≤ ρ * ‖s‖ ^ 2)
    (hsol : ∀ h, ∃ q, F q = P h ∧ ‖q - w‖ ≤ C * ‖h‖)
    (herror : ∀ h q, ‖π q - U (z + h)‖ ≤ B * ‖F q - P h‖) :
    ∃ Q : E →L[ℝ] E, HasFDerivAt U Q z ∧
      (∀ h, ‖U (z + h) - U z - Q h‖ ≤ B * ρ * C ^ 2 * ‖h‖ ^ 2) ∧
      ∀ h v, K v = P h → π v = Q h := by
  obtain ⟨Q, hQ, hQlift⟩ := primal_linear_lift K P π
    hker (bounded_linearized_lift hC hρ htaylor hsol)
  have hrem : ∀ h, ‖U (z + h) - U z - Q h‖ ≤ B * ρ * C ^ 2 * ‖h‖ ^ 2 := by
    intro h
    obtain ⟨v, hv, hp, hn⟩ := hQlift h
    have he := herror h (w + v)
    have ht := htaylor v
    rw [hv] at ht
    have hsq : ‖v‖ ^ 2 ≤ C ^ 2 * ‖h‖ ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg v) hn 2
    have hres : ‖F (w + v) - P h‖ ≤ ρ * (C ^ 2 * ‖h‖ ^ 2) :=
      ht.trans (mul_le_mul_of_nonneg_left hsq hρ)
    have hn' : ‖π (w + v) - U (z + h)‖ = ‖U (z + h) - U z - Q h‖ := by
      rw [map_add, hw, hp, norm_sub_rev]
      congr 1
      abel
    rw [hn'] at he
    nlinarith [mul_le_mul_of_nonneg_left hres hB]
  exact ⟨Q, hasFDerivAt_of_quadratic_remainder hrem, hrem, hQ⟩

omit [FiniteDimensional ℝ W] in
lemma inverse_quadratic_derivative {U V : W → W} {Q R : W →L[ℝ] W}
    {x : W} {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hUV : ∀ w, U (V w) = w) (hRQ : ∀ w, R (Q w) = w)
    (hR : ∀ w, ‖R w‖ ≤ A * ‖w‖)
    (hV : ∀ h, ‖V (x + h) - V x‖ ≤ A * ‖h‖)
    (hU : ∀ d, ‖U (V x + d) - U (V x) - Q d‖ ≤ C * ‖d‖ ^ 2) :
    HasFDerivAt V R x ∧
      ∀ h, ‖V (x + h) - V x - R h‖ ≤ C * A ^ 3 * ‖h‖ ^ 2 := by
  have hb : ∀ h, ‖V (x + h) - V x - R h‖ ≤ C * A ^ 3 * ‖h‖ ^ 2 := by
    intro h
    let d := V (x + h) - V x
    have hd : V x + d = V (x + h) := by dsimp [d]; abel
    have ht := hU d
    rw [hd, hUV, hUV, add_sub_cancel_left, norm_sub_rev] at ht
    have hh := hR (Q d - h)
    rw [map_sub, hRQ] at hh
    have hs : ‖d‖ ^ 2 ≤ A ^ 2 * ‖h‖ ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hV h) 2
    have ht' := mul_le_mul_of_nonneg_left hs hC
    have hh' := mul_le_mul_of_nonneg_left (ht.trans ht') hA
    change ‖d - R h‖ ≤ _
    nlinarith
  exact ⟨hasFDerivAt_of_quadratic_remainder hb, hb⟩

lemma inverse_derivative_of_bounded_response {U V : W → W} {Q : W →L[ℝ] W}
    {x : W} {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hUV : ∀ w, U (V w) = w)
    (hV : ∀ h, ‖V (x + h) - V x‖ ≤ A * ‖h‖)
    (hU : ∀ d, ‖U (V x + d) - U (V x) - Q d‖ ≤ C * ‖d‖ ^ 2) :
    ∃ R : W →L[ℝ] W, HasFDerivAt V R x ∧
      (∀ h, ‖V (x + h) - V x - R h‖ ≤ C * A ^ 3 * ‖h‖ ^ 2) ∧
      (∀ h, R (Q h) = h) ∧ (∀ h, Q (R h) = h) ∧ (∀ h, ‖R h‖ ≤ A * ‖h‖) := by
  have hlift : ∀ h, ∃ v, Q v = h ∧ ‖v‖ ≤ A * ‖h‖ := by
    apply bounded_linearized_lift (F := fun d => U (V x + d) - x)
      (P := ContinuousLinearMap.id ℝ W) (w := 0) hA hC
    · intro d
      simpa [hUV] using hU d
    · intro h
      refine ⟨V (x + h) - V x, ?_, ?_⟩
      · simp [hUV]
      · simpa using hV h
  have hsur : Function.Surjective Q := fun h => by
    obtain ⟨v, hv, _⟩ := hlift h
    exact ⟨v, hv⟩
  have hinj : Function.Injective Q := LinearMap.injective_iff_surjective.mpr hsur
  obtain ⟨R, hR, hRl⟩ := primal_linear_lift Q (ContinuousLinearMap.id ℝ W)
    (ContinuousLinearMap.id ℝ W) (C := A)
    (fun v hv => by simpa using hinj (hv.trans Q.map_zero.symm)) hlift
  have hRQ : ∀ h, R (Q h) = h := fun h => (hR (Q h) h rfl).symm
  have hQR : ∀ h, Q (R h) = h := by
    intro h
    obtain ⟨v, hv, he, _⟩ := hRl h
    simpa only [ContinuousLinearMap.id_apply] using he ▸ hv
  have hRb : ∀ h, ‖R h‖ ≤ A * ‖h‖ := by
    intro h
    obtain ⟨v, _, he, hn⟩ := hRl h
    simpa only [ContinuousLinearMap.id_apply] using he ▸ hn
  obtain ⟨hd, hb⟩ := inverse_quadratic_derivative hA hC hUV hRQ hRb hV hU
  exact ⟨R, hd, hb, hRQ, hQR, hRb⟩

omit [FiniteDimensional ℝ W] in
lemma derivative_lipschitz_of_quadratic_remainder {G : E → W} {A : E → E →L[ℝ] W}
    {C : ℝ} (hC : 0 ≤ C)
    (hrem : ∀ x h, ‖G (x + h) - G x - A x h‖ ≤ C * ‖h‖ ^ 2) (x y : E) :
    ‖A y - A x‖ ≤ 6 * C * ‖y - x‖ := by
  by_cases he : y = x
  · simp [he]
  have hr : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let h := ‖y - x‖ • v
  have hh : ‖h‖ = ‖y - x‖ := by simp [h, norm_smul, hv]
  let B := G (y + h) - G y - A y h
  let D := G y - G x - A x (y - x)
  let R := G (y + h) - G x - A x (y - x + h)
  have hB : ‖B‖ ≤ C * ‖y - x‖ ^ 2 := by simpa [B, hh] using hrem y h
  have hD : ‖D‖ ≤ C * ‖y - x‖ ^ 2 := by simpa [D] using hrem x (y - x)
  have hR : ‖R‖ ≤ 4 * C * ‖y - x‖ ^ 2 := by
    have ht := hrem x (y - x + h)
    have heq : x + (y - x + h) = y + h := by abel
    rw [heq] at ht
    have hn : ‖y - x + h‖ ≤ 2 * ‖y - x‖ := by
      have := norm_add_le (y - x) h
      rw [hh] at this
      linarith
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    have ht' := mul_le_mul_of_nonneg_left hs hC
    change ‖R‖ ≤ _ at ht
    nlinarith
  have heq : (A y - A x) h = R - D - B := by
    simp only [R, D, B, sub_apply, map_add]
    abel
  have hn : ‖(A y - A x) h‖ ≤ 6 * C * ‖y - x‖ ^ 2 := by
    rw [heq]
    have h₁ := norm_sub_le (R - D) B
    have h₂ := norm_sub_le R D
    linarith
  have hn' : ‖y - x‖ * ‖(A y - A x) v‖ ≤ ‖y - x‖ * (6 * C * ‖y - x‖) := by
    simpa [h, norm_smul, mul_assoc, pow_two, mul_left_comm, mul_comm] using hn
  exact (mul_le_mul_iff_right₀ hr).mp hn'

end OracleTemplate.PLMinimax
