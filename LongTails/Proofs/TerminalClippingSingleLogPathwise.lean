import LongTails.Proofs.TerminalClippingSingleLogEnergy
import LongTails.Proofs.TerminalClippingSingleLogTuning

open scoped RealInnerProductSpace

namespace OracleTemplate.TerminalClippingSingleLog

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma pathwise {T : ℕ} {q M r k C b τ : ℝ} (ht : Tuning T q M r k C b τ)
    {K : Set E} {f : E → ℝ} (hf : ConvexOn ℝ K f) {x z c h μ : ℕ → E}
    {u : E} (hz0 : z 0 = u) (hu : ∀ y ∈ K, f u ≤ f y)
    (hxK : ∀ i, x i ∈ K) (hzK : ∀ i ≤ T, z i ∈ K)
    (hstart : ‖x 0-u‖ ≤ r*T)
    (hz : ∀ i < T, z (i+1) = mix ((T:ℝ)-i) (z i) (x (i+1)))
    (hproj : ∀ i < T, ‖x (i+1)-z i‖^2 ≤ ‖x i-(k*((T:ℝ)-i)) • c i-z i‖^2)
    (hstep : ∀ i < T, ‖x (i+1)-x i‖ ≤ k*((T:ℝ)-i)*‖c i‖)
    (hsub : ∀ i < T, f (x i)-f (z i) ≤ ⟪h i,x i-z i⟫)
    (hlip : ∀ i < T, f (x (i+1))-f (x i) ≤ M*‖x (i+1)-x i‖)
    (hbias : ∀ i < T, ‖h i-μ i‖ ≤ M^2/C)
    (hsq : ∀ j ≤ T, (∑ i ∈ Finset.range j, ‖c i‖^2/C^2) ≤ q+T*(2*M^2/C^2))
    (hmart : ∀ j ≤ T, (∑ i ∈ Finset.range j, -τ*⟪c i-μ i,
      clip b (direction ((T:ℝ)-i) k (x i) (z i))⟫) ≤ q+T*(τ^2*b^2*M^2)) :
    (∀ j ≤ T, ‖x j-x 0‖ < 4*(r*T)) ∧ f (x T)-f u ≤ 24*(r*T)*M*Real.sqrt (q/T) := by
  let m := fun i : ℕ => (T:ℝ)-i
  let d := fun i => direction (m i) k (x i) (z i)
  let D := fun i => -⟪c i-μ i,clip b (d i)⟫
  let H := fun j : ℕ => r^2 + 2*k^2*((j:ℝ)*M^2/2+∑ i ∈ Finset.range j, ‖c i‖^2) +
    j*(b*M^2/C) + ∑ i ∈ Finset.range j, D i
  have hk := ht.slope_pos
  have hr := ht.radius
  have hM := ht.scale
  have hT := ht.time
  have hC := ht.level_pos
  have hτ := ht.multiplier_pos
  have hb : 0 ≤ b := by rw [ht.direction_eq]; positivity
  have hH (j : ℕ) (hj : j ≤ T) : H j ≤ 2*r^2 := by
    have hj' : (j:ℝ) ≤ T := by exact_mod_cast hj
    have hs := hsq j hj
    rw [← Finset.sum_div] at hs
    have h1 := (div_le_iff₀ (sq_pos_of_pos hC)).mp hs
    have h2 : (∑ i ∈ Finset.range j, D i) ≤ (q+T*(τ^2*b^2*M^2))/τ := by
      apply (le_div_iff₀ hτ).mpr
      rw [mul_comm, Finset.mul_sum]
      simpa only [D, d, m, mul_neg, neg_mul] using hmart j hj
    apply le_trans _ ht.closes
    unfold H
    gcongr
  have hinc (j : ℕ) : H (j+1) = H j + 2*k^2*(M^2/2+‖c j‖^2) + b*M^2/C + D j := by
    simp only [H, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    ring
  have init : energy (m 0) (x 0) (z 0) ≤ r^2 := by
    simp only [m, energy, Nat.cast_zero, sub_zero, hz0]
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := pow_le_pow_left₀ (norm_nonneg _) hstart 2
    nlinarith [mul_nonneg (sq_nonneg r) hT.le]
  have inv (j : ℕ) (hj : j ≤ T) :
      energy (m j) (x j) (z j) + k*(f (z j)-f u) ≤ H j ∧
      ‖z j-x 0‖ ≤ r*T+(29/10)*r*j ∧ ‖x j-x 0‖ < 4*(r*T) := by
    induction j with
    | zero =>
      refine ⟨by simpa [H,hz0] using init, ?_, ?_⟩
      · simpa [hz0,norm_sub_rev u] using hstart
      · simp only [sub_self,norm_zero]; positivity
    | succ i ih =>
      have hi : i < T := by omega
      obtain ⟨hpre,hrz,_⟩ := ih hi.le
      have hm : 1 ≤ m i := by
        have hj' : (i:ℝ)+1 ≤ T := by exact_mod_cast hj
        dsimp [m]; linarith
      have hmn : m (i+1) = m i-1 := by simp [m]; ring
      have hZ := hz i hi
      have hp : energy (m i) (x i) (z i) ≤ 2*r^2 := by
        have hn := mul_nonneg hk.le (sub_nonneg.mpr (hu _ (hzK i hi.le)))
        linarith [hH i hi.le]
      have hd : ‖d i‖ ≤ b := ht.direction_eq ▸ direction_bound hr hm hk.le hp
      have hnoise : ⟪h i-c i,d i⟫ ≤ b*M^2/C + D i := by
        have hh := (real_inner_le_norm (h i-μ i) (d i)).trans
          (mul_le_mul (hbias i hi) hd (norm_nonneg _) (by positivity))
        rw [show h i-c i = (h i-μ i)-(c i-μ i) by abel, inner_sub_left]
        simp only [D, clip_eq_self hd]
        rw [show b*M^2/C = M^2/C*b by ring]
        linarith only [hh]
      have hw := weighted_step (u := u) hm hk hM.le hf (hzK i hi.le) (hxK (i+1))
        (hproj i hi) (hstep i hi) (hsub i hi) (hlip i hi)
      have hraw : energy (m i) (x (i+1)) (z i) + k*(f (z (i+1))-f u) ≤ H (i+1) := by
        rw [hinc]
        change energy (m i) _ _ + k*(f (mix (m i) (z i) (x (i+1)))-f u) ≤ _ at hw
        rw [← hZ] at hw
        dsimp only [d] at hnoise
        linarith
      have he : energy (m i) (x (i+1)) (z i) ≤ 2*r^2 := by
        have hn := mul_nonneg hk.le (sub_nonneg.mpr (hu _ (hzK _ hj)))
        linarith [hH (i+1) hj]
      refine ⟨?_,?_,?_⟩
      · apply le_trans _ hraw
        gcongr
        rw [hmn,hZ]
        exact mix_energy hm _ _
      · have hh := mix_displacement hr hm he
        rw [← hZ] at hh
        have hh' := norm_sub_le_norm_sub_add_norm_sub (z (i+1)) (z i) (x 0)
        push_cast
        linarith
      · have hh := energy_distance hr hm he
        have hh' := norm_sub_le_norm_sub_add_norm_sub (x (i+1)) (z i) (x 0)
        have hi' : (i:ℝ)+1 ≤ T := by exact_mod_cast hj
        have hri := mul_le_mul_of_nonneg_left hi' hr.le
        dsimp only [m] at hh
        nlinarith [mul_pos hr hT]
  refine ⟨fun j hj => (inv j hj).2.2, ?_⟩
  have htN : 0 < T := by exact_mod_cast hT
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero htN.ne'
  have hlast := hz l (by omega)
  norm_num [mix, Nat.cast_succ] at hlast
  have he := (inv (l+1) le_rfl).1.trans (hH _ le_rfl)
  rw [hlast] at he
  rw [← ht.accuracy]
  apply (le_div_iff₀ hk).mpr
  simpa [energy, mul_comm] using he

end OracleTemplate.TerminalClippingSingleLog
