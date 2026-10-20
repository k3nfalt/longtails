import LongTails.Setups.MatrixGeometry
import LongTails.Algorithms.ValidatedMuon
import LongTails.Proofs.MatrixSmooth
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.MuonMomentum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma ema_residual_bound {α c : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 ≤ c)
    {M G N V : ℕ → E} (hV0 : V 0 = 0)
    (hM : ∀ j, M (j + 1) = (1 - α) • M j + α • (G j + N j))
    (hV : ∀ j, V (j + 1) = (1 - α) • V j + α • N j)
    (hG : ∀ j, ‖G (j + 1) - G j‖ ≤ c) (j : ℕ) :
    ‖M j - G j - V j‖ ≤ (1 - α) ^ j * ‖M 0 - G 0‖ + c / α := by
  have hβ : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  have hfrac : α * (c / α) = c := by field_simp
  induction j with
  | zero => simpa [hV0] using (show ‖M 0 - G 0‖ ≤ ‖M 0 - G 0‖ + c / α by exact le_add_of_nonneg_right (div_nonneg hc hα.le))
  | succ j ih =>
    have he : M (j + 1) - G (j + 1) - V (j + 1) =
        (1 - α) • (M j - G j - V j) + (G j - G (j + 1)) := by
      rw [hM, hV]
      module
    rw [he]
    have hh := norm_add_le ((1 - α) • (M j - G j - V j)) (G j - G (j + 1))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ, norm_sub_rev (G j)] at hh
    have hm := mul_le_mul_of_nonneg_left ih hβ
    rw [pow_succ]
    nlinarith [hG j]

lemma ema_lagged_residual_bound {α c : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 ≤ c)
    {M G N V : ℕ → E} (hV0 : V 0 = 0)
    (hM : ∀ j, M (j + 1) = (1 - α) • M j + α • (G j + N j))
    (hV : ∀ j, V (j + 1) = (1 - α) • V j + α • N j)
    (hG : ∀ j, ‖G (j + 1) - G j‖ ≤ c) (j : ℕ) :
    ‖M (j + 1) - G j - V (j + 1)‖ ≤
      (1 - α) ^ (j + 1) * ‖M 0 - G 0‖ + c / α := by
  have he : M (j + 1) - G j - V (j + 1) = (1 - α) • (M j - G j - V j) := by
    rw [hM, hV]
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hα1)]
  have hb := mul_le_mul_of_nonneg_left (ema_residual_bound hα hα1 hc hV0 hM hV hG j)
    (sub_nonneg.mpr hα1)
  have hf : 0 ≤ c / α := div_nonneg hc hα.le
  rw [pow_succ]
  nlinarith

lemma ema_noise_sum {α : ℝ} {N V : ℕ → E} (hV0 : V 0 = 0)
    (hV : ∀ j, V (j + 1) = (1 - α) • V j + α • N j) (j : ℕ) :
    V j = ∑ i ∈ Finset.range j, (α * (1 - α) ^ (j - 1 - i)) • N i := by
  induction j with
  | zero => simpa using hV0
  | succ j ih =>
    rw [hV, ih, Finset.sum_range_succ, Finset.smul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have he : j + 1 - 1 - i = (j - 1 - i) + 1 := by
        have := Finset.mem_range.mp hi
        omega
      rw [he, pow_succ, smul_smul]
      congr 1
      ring
    · simp

lemma ema_weight_square_sum {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (j : ℕ) :
    (∑ i ∈ Finset.range j, (α * (1 - α) ^ i) ^ 2) ≤ α := by
  induction j with
  | zero => simpa using hα
  | succ j ih =>
    have he : (∑ i ∈ Finset.range (j + 1), (α * (1 - α) ^ i) ^ 2) =
        α ^ 2 + (1 - α) ^ 2 * ∑ i ∈ Finset.range j, (α * (1 - α) ^ i) ^ 2 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, mul_one]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      ring
    rw [he]
    have hb := mul_le_mul_of_nonneg_left ih (sq_nonneg (1 - α))
    nlinarith [mul_nonneg (sq_nonneg α) (sub_nonneg.mpr hα1)]

lemma ema_reverse_weight_square_sum {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (j : ℕ) :
    (∑ i ∈ Finset.range j, (α * (1 - α) ^ (j - 1 - i)) ^ 2) ≤ α := by
  rw [Finset.sum_range_reflect (fun i => (α * (1 - α) ^ i) ^ 2) j]
  exact ema_weight_square_sum hα hα1 j

lemma ema_sum_recurrence (α : ℝ) (N : ℕ → E) (j : ℕ) :
    (∑ i ∈ Finset.range (j + 1), (α * (1 - α) ^ (j + 1 - 1 - i)) • N i) =
      (1 - α) • (∑ i ∈ Finset.range j, (α * (1 - α) ^ (j - 1 - i)) • N i) +
        α • N j := by
  rw [Finset.sum_range_succ, Finset.smul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have he : j + 1 - 1 - i = (j - 1 - i) + 1 := by
      have := Finset.mem_range.mp hi
      omega
    rw [he, pow_succ, smul_smul]
    congr 1
    ring
  · simp

lemma ema_bounded_inputs {α C : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    {M Y : ℕ → E} (hM0 : M 0 = 0)
    (hM : ∀ i, M (i + 1) = (1 - α) • M i + α • Y i)
    (T : ℕ) (hY : ∀ i < T, ‖Y i‖ ≤ C) :
    ∀ t ≤ T, ‖M t‖ ≤ C := by
  intro t
  induction t with
  | zero => intro _; simpa [hM0] using hC
  | succ t ih =>
    intro ht
    have hm := ih (by omega)
    have hy := hY t (by omega)
    rw [hM]
    have hh := norm_add_le ((1 - α) • M t) (α • Y t)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hα1), abs_of_nonneg hα] at hh
    have h1 := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hα1)
    have h2 := mul_le_mul_of_nonneg_left hy hα
    nlinarith

open LongTails.Setups.MatrixGeometry

lemma matrix_dual_sub {m n : ℕ} (X Y : Space m n) :
    dualMap m n (X - Y) = dualMap m n X - dualMap m n Y := by
  ext U
  change inner ℝ (X - Y) ((operatorEquiv m n).symm U) =
    inner ℝ X ((operatorEquiv m n).symm U) - inner ℝ Y ((operatorEquiv m n).symm U)
  exact inner_sub_left _ _ _

lemma matrix_ema_lagged_residual_bound {m n : ℕ} {α c : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 ≤ c)
    {M G N V : ℕ → Space m n} (hV0 : V 0 = 0)
    (hM : ∀ j, M (j + 1) = (1 - α) • M j + α • (G j + N j))
    (hV : ∀ j, V (j + 1) = (1 - α) • V j + α • N j)
    (hG : ∀ j, nuclearNorm (G (j + 1) - G j) ≤ c) (j : ℕ) :
    nuclearNorm (M (j + 1) - G j - V (j + 1)) ≤
      (1 - α) ^ (j + 1) * nuclearNorm (M 0 - G 0) + c / α := by
  have hMd (i : ℕ) : dualMap m n (M (i + 1)) =
      (1 - α) • dualMap m n (M i) + α • (dualMap m n (G i) + dualMap m n (N i)) := by
    rw [hM, map_add, map_smul, map_smul, map_add]
  have hVd (i : ℕ) : dualMap m n (V (i + 1)) =
      (1 - α) • dualMap m n (V i) + α • dualMap m n (N i) := by
    rw [hV, map_add, map_smul, map_smul]
  have hGd (i : ℕ) : ‖dualMap m n (G (i + 1)) - dualMap m n (G i)‖ ≤ c := by
    rw [← matrix_dual_sub (G (i + 1)) (G i)]
    exact hG i
  have hh := ema_lagged_residual_bound
    (M := fun i => dualMap m n (M i)) (G := fun i => dualMap m n (G i))
    (N := fun i => dualMap m n (N i)) (V := fun i => dualMap m n (V i)) hα hα1 hc
    (show dualMap m n (V 0) = 0 by rw [hV0, map_zero]) hMd hVd hGd j
  change ‖dualMap m n (M (j + 1) - G j - V (j + 1))‖ ≤
    (1 - α) ^ (j + 1) * ‖dualMap m n (M 0 - G 0)‖ + c / α
  simpa only [matrix_dual_sub] using hh

open LongTails.Algorithms.ValidatedMuon LongTails.Algorithms.MatrixPolar

lemma trajectory_momentum {m n : ℕ} {Ω : Type*} (α η : ℝ)
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω)
    (state : Space m n × Space m n) (call t : ℕ) :
    (trajectory α η g ξ state call (t + 1)).2 =
      (1 - α) • (trajectory α η g ξ state call t).2 +
        α • g (trajectory α η g ξ state call t).1 (ξ (call + t)) := rfl

lemma trajectory_point {m n : ℕ} {Ω : Type*} (α η : ℝ)
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω)
    (state : Space m n × Space m n) (call t : ℕ) :
    (trajectory α η g ξ state call (t + 1)).1 =
      (trajectory α η g ξ state call t).1 -
        η • polar (trajectory α η g ξ state call (t + 1)).2 := rfl

lemma trajectory_step_spectral {m n : ℕ} {Ω : Type*} (α : ℝ) {η : ℝ} (hη : 0 ≤ η)
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω)
    (state : Space m n × Space m n) (call t : ℕ) :
    spectralNorm ((trajectory α η g ξ state call (t + 1)).1 -
      (trajectory α η g ξ state call t).1) ≤ η := by
  rw [trajectory_point]
  have he : (trajectory α η g ξ state call t).1 -
      η • polar (trajectory α η g ξ state call (t + 1)).2 -
      (trajectory α η g ξ state call t).1 =
      (-η) • polar (trajectory α η g ξ state call (t + 1)).2 := by module
  rw [he, MatrixSmooth.spectralNorm_smul, abs_neg, abs_of_nonneg hη]
  simpa using mul_le_mul_of_nonneg_left
    (show spectralNorm (polar (trajectory α η g ξ state call (t + 1)).2) ≤ 1 from polar_mem _) hη

lemma trajectory_gradient_increment {m n : ℕ} {Ω : Type*} {f : Space m n → ℝ}
    {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (α : ℝ) (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω)
    (state : Space m n × Space m n) (call t : ℕ) :
    nuclearNorm (gradient f (trajectory α η g ξ state call (t + 1)).1 -
      gradient f (trajectory α η g ξ state call t).1) ≤ L * η :=
  (hlip _ _).trans (mul_le_mul_of_nonneg_left
    (trajectory_step_spectral α hη g ξ state call t) hL)

lemma trajectory_gradient_bound {m n : ℕ} {Ω : Type*} {f : Space m n → ℝ}
    {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (α : ℝ) (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω)
    (state : Space m n × Space m n) (call t : ℕ) :
    nuclearNorm (gradient f (trajectory α η g ξ state call t).1) ≤
      nuclearNorm (gradient f state.1) + (t : ℝ) * (L * η) := by
  induction t with
  | zero => simp [trajectory]
  | succ t ih =>
    have he : gradient f (trajectory α η g ξ state call (t + 1)).1 =
        (gradient f (trajectory α η g ξ state call (t + 1)).1 -
          gradient f (trajectory α η g ξ state call t).1) +
          gradient f (trajectory α η g ξ state call t).1 := by abel
    calc
      _ = nuclearNorm ((gradient f (trajectory α η g ξ state call (t + 1)).1 -
          gradient f (trajectory α η g ξ state call t).1) +
          gradient f (trajectory α η g ξ state call t).1) := congrArg nuclearNorm he
      _ ≤ nuclearNorm (gradient f (trajectory α η g ξ state call (t + 1)).1 -
          gradient f (trajectory α η g ξ state call t).1) +
          nuclearNorm (gradient f (trajectory α η g ξ state call t).1) := nuclearNorm_add_le _ _
      _ ≤ L * η + (nuclearNorm (gradient f state.1) + (t : ℝ) * (L * η)) :=
        add_le_add (trajectory_gradient_increment hL hη hlip α g ξ state call t) ih
      _ = _ := by push_cast; ring

lemma cutoff_alignment_bound {m n : ℕ} {α c B : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hc : 0 ≤ c) (hB : 0 ≤ B)
    {M G N V : ℕ → Space m n} (hV0 : V 0 = 0)
    (hM : ∀ j, M (j + 1) = (1 - α) • M j + α • (G j + N j))
    (hV : ∀ j, V (j + 1) = (1 - α) • V j + α • N j)
    (hG : ∀ j, nuclearNorm (G (j + 1) - G j) ≤ c)
    (j : ℕ) (A : Prop) [Decidable A] (hremote : A → nuclearNorm (M 0 - G 0) ≤ B) :
    (if A then nuclearNorm (G j) - inner ℝ (G j) (polar (M (j + 1))) else 0) ≤
      2 * (1 - α) ^ (j + 1) * B + 2 * c / α + 2 * nuclearNorm (V (j + 1)) := by
  by_cases hA : A
  · rw [ite_eq_left hA]
    have he := matrix_ema_lagged_residual_bound hα hα1 hc hV0 hM hV hG j
    have hb := mul_le_mul_of_nonneg_left (hremote hA)
      (pow_nonneg (sub_nonneg.mpr hα1) (j + 1))
    have ht := nuclearNorm_add_le (M (j + 1) - G j - V (j + 1)) (V (j + 1))
    rw [sub_add_cancel] at ht
    have hd := (MatrixSmooth.polar_alignment_deficit (G j) (M (j + 1))).2.2
    calc
      _ ≤ 2 * ((1 - α) ^ (j + 1) * B + c / α + nuclearNorm (V (j + 1))) := by linarith
      _ = _ := by ring
  · rw [ite_eq_right hA]
    have hβ := sub_nonneg.mpr hα1
    have hn := nuclearNorm_nonneg (V (j + 1))
    positivity

lemma trajectory_cutoff_alignment_bound {m n : ℕ} {Ω : Type*} {f : Space m n → ℝ}
    {L α η B : ℝ} (hL : 0 ≤ L) (hα : 0 < α) (hα1 : α ≤ 1)
    (hη : 0 ≤ η) (hB : 0 ≤ B)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω)
    (state : Space m n × Space m n) (start j : ℕ)
    (A : Prop) [Decidable A]
    (hremote : A → nuclearNorm ((trajectory α η g ξ state 0 start).2 -
      gradient f (trajectory α η g ξ state 0 start).1) ≤ B) :
    (if A then nuclearNorm (gradient f (trajectory α η g ξ state 0 (start + j)).1) -
      inner ℝ (gradient f (trajectory α η g ξ state 0 (start + j)).1)
        (polar (trajectory α η g ξ state 0 (start + j + 1)).2) else 0) ≤
      2 * (1 - α) ^ (j + 1) * B + 2 * (L * η) / α +
        2 * nuclearNorm (∑ i ∈ Finset.range (j + 1),
          (α * (1 - α) ^ (j + 1 - 1 - i)) •
            (g (trajectory α η g ξ state 0 (start + i)).1 (ξ (start + i)) -
              gradient f (trajectory α η g ξ state 0 (start + i)).1)) := by
  let S := trajectory α η g ξ state 0
  let M := fun i => (S (start + i)).2
  let G := fun i => gradient f (S (start + i)).1
  let N := fun i => g (S (start + i)).1 (ξ (start + i)) - G i
  let V := fun t => ∑ i ∈ Finset.range t, (α * (1 - α) ^ (t - 1 - i)) • N i
  have hM (i : ℕ) : M (i + 1) = (1 - α) • M i + α • (G i + N i) := by
    dsimp [M, G, N, S]
    rw [show start + (i + 1) = start + i + 1 by omega, trajectory_momentum]
    simp only [Nat.zero_add]
    congr 1
    congr 1
    abel
  have hG (i : ℕ) : nuclearNorm (G (i + 1) - G i) ≤ L * η := by
    dsimp [G, S]
    rw [show start + (i + 1) = start + i + 1 by omega]
    exact trajectory_gradient_increment hL hη hlip α g ξ state 0 (start + i)
  have hh := cutoff_alignment_bound hα hα1 (mul_nonneg hL hη) hB
    (M := M) (G := G) (N := N) (V := V) (by simp [V]) hM
    (fun i => ema_sum_recurrence α N i) hG j A
    (by simpa [M, G, S] using hremote)
  simpa only [M, G, N, V, S, Nat.add_assoc] using hh

lemma trajectory_tracker_bound {m n : ℕ} {Ω : Type*} {f : Space m n → ℝ}
    {L α η R : ℝ} (hL : 0 ≤ L) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hη : 0 ≤ η) (hR : 0 ≤ R)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω) (x0 : Space m n) (T : ℕ)
    (hnoise : ∀ i < T, nuclearNorm
      (g (trajectory α η g ξ (x0, 0) 0 i).1 (ξ i) -
        gradient f (trajectory α η g ξ (x0, 0) 0 i).1) ≤ R) :
    ∀ t ≤ T, nuclearNorm ((trajectory α η g ξ (x0, 0) 0 t).2 -
      gradient f (trajectory α η g ξ (x0, 0) 0 t).1) ≤
        2 * (nuclearNorm (gradient f x0) + T * (L * η)) + R := by
  let S := trajectory α η g ξ (x0, 0) 0
  let G := nuclearNorm (gradient f x0) + T * (L * η)
  have hg (i : ℕ) (hi : i ≤ T) : nuclearNorm (gradient f (S i).1) ≤ G := by
    have hh := trajectory_gradient_bound hL hη hlip α g ξ (x0, 0) 0 i
    have hit : (i : ℝ) ≤ (T : ℝ) := by exact_mod_cast hi
    exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hit (mul_nonneg hL hη)))
  let M := fun i => dualMap m n (S i).2
  let Y := fun i => dualMap m n (g (S i).1 (ξ i))
  have hM (i : ℕ) : M (i + 1) = (1 - α) • M i + α • Y i := by
    dsimp [M, Y, S]
    rw [trajectory_momentum, map_add, map_smul, map_smul, Nat.zero_add]
  have hy (i : ℕ) (hi : i < T) : ‖Y i‖ ≤ G + R := by
    have hb := nuclearNorm_add_le
      (g (S i).1 (ξ i) - gradient f (S i).1) (gradient f (S i).1)
    rw [sub_add_cancel] at hb
    change nuclearNorm (g (S i).1 (ξ i)) ≤ G + R
    linarith [hnoise i hi, hg i hi.le]
  have hm := ema_bounded_inputs hα hα1
    (show 0 ≤ G + R from add_nonneg (add_nonneg (nuclearNorm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hL hη))) hR)
    (M := M) (Y := Y) (by simp [M, S, trajectory]) hM T hy
  intro t ht
  have hb := nuclearNorm_add_le (S t).2 (-gradient f (S t).1)
  rw [← sub_eq_add_neg, nuclearNorm_neg] at hb
  have hmt : nuclearNorm (S t).2 ≤ G + R := hm t ht
  change nuclearNorm ((S t).2 - gradient f (S t).1) ≤ 2 * G + R
  linarith [hg t ht]

end LongTails.Proofs.MuonMomentum
