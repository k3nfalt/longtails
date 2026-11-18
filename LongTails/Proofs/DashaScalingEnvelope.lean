import LongTails.Proofs.DashaScalingDescent
import LongTails.Proofs.DashaScalingRange
import LongTails.Proofs.DashaScalingParameters
import LongTails.Proofs.DashaCompression
import LongTails.Proofs.DashaInitialization

namespace LongTails.Proofs.DashaScalingEnvelope

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling

variable {p : Params}

noncomputable def maxLocal (c : Choice p) (s : Iterate p) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin p.n =>
    ‖LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i)‖)

lemma local_le_max (c : Choice p) (s : Iterate p) (i : Fin p.n) :
    ‖LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i)‖ ≤ maxLocal c s :=
  by
    unfold maxLocal
    exact Finset.le_sup' (fun j : Fin p.n =>
      ‖LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode j)‖) (Finset.mem_univ i)

lemma maxLocal_nonneg (c : Choice p) (s : Iterate p) : 0 ≤ maxLocal c s :=
  (norm_nonneg _).trans (local_le_max c s ⟨0, p.n.pos⟩)

lemma maxLocal_le (c : Choice p) (s : Iterate p) (M : ℝ)
    (h : ∀ i, ‖LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i)‖ ≤ M) :
    maxLocal c s ≤ M := by
  unfold maxLocal
  exact Finset.sup'_le _ _ (fun i _ => h i)

lemma estimate_le_max (c : Choice p) (s : Iterate p) : ‖estimate p c s‖ ≤ maxLocal c s := by
  rw [DashaScalingDescent.estimate_eq_mean]
  calc
    _ ≤ (1 / (p.n : ℝ)) * ∑ i,
        ‖LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i)‖ :=
      DashaScalingDescent.mean_norm _
    _ ≤ (1 / (p.n : ℝ)) * ∑ _ : Fin p.n, maxLocal c s :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => local_le_max c s i)) (by positivity)
    _ = _ := by simp [ne_of_gt (show (0 : ℝ) < p.n by exact_mod_cast p.n.pos)]

lemma distance_step (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (s : Iterate p) (seed : Sample p) :
    ‖(nextIterate p c f s seed).point - p.x0‖ ≤ ‖s.point - p.x0‖ + stepSize p c * maxLocal c s := by
  have hγ := DashaScalingParameters.stepSize_pos c hL hH
  change ‖s.point - stepSize p c • estimate p c s - p.x0‖ ≤ _
  have he : s.point - stepSize p c • estimate p c s - p.x0 =
      s.point - p.x0 - stepSize p c • estimate p c s := by module
  rw [he]
  calc
    _ ≤ ‖s.point - p.x0‖ + ‖stepSize p c • estimate p c s‖ := norm_sub_le _ _
    _ = ‖s.point - p.x0‖ + stepSize p c * ‖estimate p c s‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (estimate_le_max c s) hγ.le)

lemma initial_max_bound (c : Choice p) (hε : 0 < p.ε) (f : Functions p)
    (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G) (seed : Sample p) :
    maxLocal c (initialIterate p c f seed) ≤ p.G + spacing p c * Real.sqrt (p.d : ℝ) := by
  have hρ := DashaScalingParameters.spacing_pos c hε
  apply maxLocal_le
  intro i
  let q := LongTails.Algorithms.DashaQuantization.rounded p.d false (spacing p c)
    (gradient (f i) p.x0) (seed i).2
  have he : ‖q - gradient (f i) p.x0‖ ≤ spacing p c * Real.sqrt (p.d : ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hb := DashaInitialization.fine_error_sq p.d (spacing p c) hρ (gradient (f i) p.x0) (seed i).2
    nlinarith only [hb]
  change ‖q‖ ≤ _
  have ht : ‖q‖ ≤ ‖q - gradient (f i) p.x0‖ + ‖gradient (f i) p.x0‖ := by
    simpa using norm_add_le (q - gradient (f i) p.x0) (gradient (f i) p.x0)
  linarith [hG i]

lemma sparse_initial_max_bound (c initializer : Choice p) (hε : 0 < p.ε) (f : Functions p)
    (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G) (seed : Sample p) :
    maxLocal c (sparseInitialIterate p c initializer f seed) ≤
      2 * LongTails.Algorithms.DashaCyclic.multiplier initializer.block * p.G +
        spacing p c * Real.sqrt (p.d : ℝ) := by
  have hq : 0 ≤ LongTails.Algorithms.DashaCyclic.multiplier initializer.block := by
    unfold LongTails.Algorithms.DashaCyclic.multiplier
    positivity
  apply maxLocal_le
  intro i
  have hb := DashaCompression.compress_norm_bound initializer.block initializer.precision (spacing p c)
    (DashaScalingParameters.spacing_pos c hε) (gradient (f i) p.x0) (seed i)
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left (hG i) (show 0 ≤ 2 * LongTails.Algorithms.DashaCyclic.multiplier initializer.block by positivity)) le_rfl)

lemma maxLocal_step (c : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (s : Iterate p) (hstate : ∀ i, s.localGradient i = gradient (f i) s.point) (seed : Sample p) :
    let H := Real.sqrt (p.n : ℝ) * p.Lhat
    let q := LongTails.Algorithms.DashaCyclic.multiplier c.block
    maxLocal c (nextIterate p c f s seed) ≤ maxLocal c s +
      2 * q * ((1 + H * stepSize p c) * maxLocal c s + p.G + H * ‖s.point - p.x0‖) +
        spacing p c * Real.sqrt (p.d : ℝ) := by
  let H := Real.sqrt (p.n : ℝ) * p.Lhat
  let q := LongTails.Algorithms.DashaCyclic.multiplier c.block
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hq : 0 ≤ q := by dsimp [q, LongTails.Algorithms.DashaCyclic.multiplier]; positivity
  have hγ := DashaScalingParameters.stepSize_pos c hL hH
  have hlip (i : Fin p.n) (x y : Point p) : ‖gradient (f i) x - gradient (f i) y‖ ≤ H * ‖x - y‖ :=
    DashaScalingRange.local_norm_of_mean_square _ p.Lhat ‖x - y‖ hH.le (norm_nonneg _) (hs x y) i
  apply maxLocal_le
  intro i
  rw [DashaScalingDescent.next_local_code]
  simp only [hstate]
  have hh : ‖gradient (f i) s.point‖ ≤ p.G + H * ‖s.point - p.x0‖ := by
    have ht : ‖gradient (f i) s.point‖ ≤ ‖gradient (f i) s.point - gradient (f i) p.x0‖ +
        ‖gradient (f i) p.x0‖ := by
      simpa using norm_add_le (gradient (f i) s.point - gradient (f i) p.x0) (gradient (f i) p.x0)
    linarith [hlip i s.point p.x0, hG i]
  have hd : ‖gradient (f i) (s.point - stepSize p c • estimate p c s) - gradient (f i) s.point‖ ≤
      H * stepSize p c * maxLocal c s := by
    have ht := hlip i (s.point - stepSize p c • estimate p c s) s.point
    have he : s.point - stepSize p c • estimate p c s - s.point = -(stepSize p c) • estimate p c s := by module
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hγ] at ht
    have hm := mul_le_mul_of_nonneg_left (estimate_le_max c s) (show 0 ≤ H * stepSize p c by positivity)
    nlinarith only [ht, hm]
  apply DashaScalingRange.local_update_bound _ _ _ _ (momentum p c) (stepSize p c) H q
    (spacing p c * Real.sqrt (p.d : ℝ)) (maxLocal c s) p.G ‖s.point - p.x0‖
    (DashaScalingParameters.momentum_pos c).le (DashaScalingParameters.momentum_le_one c)
    hH0 hq (maxLocal_nonneg c s) (norm_nonneg _) hG0 (local_le_max c s i) hh hd
  exact DashaCompression.compress_norm_bound c.block c.precision (spacing p c)
    (DashaScalingParameters.spacing_pos c hε) _ (seed i)

noncomputable def envelope (c : Choice p) (s : Iterate p) : ℝ :=
  maxLocal c s + p.G + Real.sqrt (p.n : ℝ) * p.Lhat * ‖s.point - p.x0‖ +
    spacing p c * Real.sqrt (p.d : ℝ)

noncomputable def growth (c : Choice p) : ℝ :=
  (2 + 2 * LongTails.Algorithms.DashaCyclic.multiplier c.block) *
    (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c)

lemma envelope_step (c : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (s : Iterate p) (hstate : ∀ i, s.localGradient i = gradient (f i) s.point) (seed : Sample p) :
    envelope c (nextIterate p c f s seed) ≤ growth c * envelope c s := by
  have hγ := DashaScalingParameters.stepSize_pos c hL hH
  have hρ := DashaScalingParameters.spacing_pos c hε
  have hq : 0 ≤ LongTails.Algorithms.DashaCyclic.multiplier c.block := by
    unfold LongTails.Algorithms.DashaCyclic.multiplier
    positivity
  exact DashaScalingRange.state_bound_step (maxLocal c s) ‖s.point - p.x0‖
    (maxLocal c (nextIterate p c f s seed)) ‖(nextIterate p c f s seed).point - p.x0‖
    p.G (Real.sqrt (p.n : ℝ) * p.Lhat) (stepSize p c)
    (LongTails.Algorithms.DashaCyclic.multiplier c.block) (spacing p c * Real.sqrt (p.d : ℝ))
    (maxLocal_nonneg c s) (norm_nonneg _) hG0 (by positivity) hγ.le hq (by positivity)
    (maxLocal_step c hε hL hH hG0 f hs hG s hstate seed) (distance_step c hL hH f s seed)

lemma trajectory_envelope (c : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (seed : ℕ → Sample p) (k : ℕ) :
    envelope c (trajectory p c f seed k) ≤
      2 * (p.G + spacing p c * Real.sqrt (p.d : ℝ)) * growth c ^ k := by
  have hγ := DashaScalingParameters.stepSize_pos c hL hH
  have hC : 0 ≤ growth c := by
    dsimp [growth, LongTails.Algorithms.DashaCyclic.multiplier]
    positivity
  induction k with
  | zero =>
    have hi := initial_max_bound c hε f hG (seed 0)
    change maxLocal c (initialIterate p c f (seed 0)) + p.G +
      Real.sqrt (p.n : ℝ) * p.Lhat * ‖p.x0 - p.x0‖ + spacing p c * Real.sqrt (p.d : ℝ) ≤ _
    simp only [sub_self, norm_zero, mul_zero, add_zero, pow_zero, mul_one]
    linarith only [hi]
  | succ k ih =>
    have hb := envelope_step c hε hL hH hG0 f hs hG (trajectory p c f seed k)
      (DashaScalingDescent.trajectory_gradient c f seed k) (seed (k + 1))
    calc
      _ ≤ growth c * envelope c (trajectory p c f seed k) := hb
      _ ≤ growth c * (2 * (p.G + spacing p c * Real.sqrt (p.d : ℝ)) * growth c ^ k) :=
        mul_le_mul_of_nonneg_left ih hC
      _ = _ := by rw [pow_succ]; ring

lemma innovation_bound (c : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (s : Iterate p) (hstate : ∀ i, s.localGradient i = gradient (f i) s.point) (i : Fin p.n) :
    ‖gradient (f i) (s.point - stepSize p c • estimate p c s) - s.localGradient i -
      momentum p c • (LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i) -
        s.localGradient i)‖ ≤ (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c) * envelope c s := by
  let H := Real.sqrt (p.n : ℝ) * p.Lhat
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hγ := DashaScalingParameters.stepSize_pos c hL hH
  have hρ := DashaScalingParameters.spacing_pos c hε
  have hlip (i : Fin p.n) (x y : Point p) : ‖gradient (f i) x - gradient (f i) y‖ ≤ H * ‖x - y‖ :=
    DashaScalingRange.local_norm_of_mean_square _ p.Lhat ‖x - y‖ hH.le (norm_nonneg _) (hs x y) i
  simp only [hstate]
  have hh : ‖gradient (f i) s.point‖ ≤ p.G + H * ‖s.point - p.x0‖ := by
    have ht : ‖gradient (f i) s.point‖ ≤ ‖gradient (f i) s.point - gradient (f i) p.x0‖ +
        ‖gradient (f i) p.x0‖ := by
      simpa using norm_add_le (gradient (f i) s.point - gradient (f i) p.x0) (gradient (f i) p.x0)
    linarith [hlip i s.point p.x0, hG i]
  have hd : ‖gradient (f i) (s.point - stepSize p c • estimate p c s) - gradient (f i) s.point‖ ≤
      H * stepSize p c * maxLocal c s := by
    have ht := hlip i (s.point - stepSize p c • estimate p c s) s.point
    have he : s.point - stepSize p c • estimate p c s - s.point = -(stepSize p c) • estimate p c s := by module
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hγ] at ht
    have hm := mul_le_mul_of_nonneg_left (estimate_le_max c s) (show 0 ≤ H * stepSize p c by positivity)
    nlinarith only [ht, hm]
  exact DashaScalingRange.innovation_norm_bound _ _ _ (momentum p c) (stepSize p c) H
    (spacing p c * Real.sqrt (p.d : ℝ)) (maxLocal c s) p.G ‖s.point - p.x0‖
    (DashaScalingParameters.momentum_pos c).le (DashaScalingParameters.momentum_le_one c)
    hγ.le hH0 (by positivity) (maxLocal_nonneg c s) (norm_nonneg _) hG0 (local_le_max c s i) hh hd

lemma sparse_trajectory_envelope (c initializer : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (seed : ℕ → Sample p) (k : ℕ) :
    envelope c (sparseTrajectory p c initializer f seed k) ≤
      ((2 * LongTails.Algorithms.DashaCyclic.multiplier initializer.block + 1) * p.G +
        2 * spacing p c * Real.sqrt (p.d : ℝ)) * growth c ^ k := by
  have hγ := DashaScalingParameters.stepSize_pos c hL hH
  have hC : 0 ≤ growth c := by
    dsimp [growth, LongTails.Algorithms.DashaCyclic.multiplier]
    positivity
  induction k with
  | zero =>
    have hi := sparse_initial_max_bound c initializer hε f hG (seed 0)
    change maxLocal c (sparseInitialIterate p c initializer f (seed 0)) + p.G +
      Real.sqrt (p.n : ℝ) * p.Lhat * ‖p.x0 - p.x0‖ + spacing p c * Real.sqrt (p.d : ℝ) ≤ _
    simp only [sub_self, norm_zero, mul_zero, add_zero, pow_zero, mul_one]
    nlinarith only [hi]
  | succ k ih =>
    have hb := envelope_step c hε hL hH hG0 f hs hG (sparseTrajectory p c initializer f seed k)
      (DashaScalingDescent.sparse_trajectory_gradient c initializer f seed k) (seed (k + 1))
    calc
      _ ≤ growth c * envelope c (sparseTrajectory p c initializer f seed k) := hb
      _ ≤ growth c * (((2 * LongTails.Algorithms.DashaCyclic.multiplier initializer.block + 1) * p.G +
          2 * spacing p c * Real.sqrt (p.d : ℝ)) * growth c ^ k) := mul_le_mul_of_nonneg_left ih hC
      _ = _ := by rw [pow_succ]; ring

end LongTails.Proofs.DashaScalingEnvelope
