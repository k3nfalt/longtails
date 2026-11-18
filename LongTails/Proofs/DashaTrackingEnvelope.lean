import LongTails.Proofs.DashaScalingEnvelope

namespace LongTails.Proofs.DashaTrackingEnvelope

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling

variable {p : Params}

lemma local_error_bound (e change compressed : Point p) (a q δ E D : ℝ)
    (ha : 0 ≤ a) (hq : 0 ≤ q) (he : ‖e‖ ≤ E) (hd : ‖change‖ ≤ D)
    (hc : ‖compressed‖ ≤ 2 * q * ‖change - a • e‖ + 2 * δ) :
    ‖e + compressed - change‖ ≤ (1 + 2 * q * a) * E + (1 + 2 * q) * D + 2 * δ := by
  have hu : ‖change - a • e‖ ≤ D + a * E := by
    calc
      _ ≤ ‖change‖ + ‖a • e‖ := norm_sub_le _ _
      _ = ‖change‖ + a * ‖e‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      _ ≤ _ := add_le_add hd (mul_le_mul_of_nonneg_left he ha)
  have hm := mul_le_mul_of_nonneg_left hu (show 0 ≤ 2 * q by positivity)
  have ht := (norm_sub_le (e + compressed) change).trans
    (add_le_add (norm_add_le e compressed) le_rfl)
  nlinarith only [ht, hc, hm, he, hd]

lemma joint_step_bound (J E Jnext Enext H η q a δ : ℝ)
    (hJ : 0 ≤ J) (hE : 0 ≤ E) (hδ : 0 ≤ δ) (hH : 0 ≤ H) (hη : 0 ≤ η)
    (hq : 1 ≤ q) (ha : a ≤ 1)
    (hgradient : Jnext ≤ J + H * η * (J + E))
    (herror : Enext ≤ (1 + 2 * q * a) * E + (1 + 2 * q) * H * η * (J + E) + 2 * δ) :
    Jnext + Enext + 2 * δ ≤ (2 + 2 * q) * (1 + H * η) * (J + E + 2 * δ) := by
  have hq0 : 0 ≤ q := by linarith
  have hqa := mul_le_mul_of_nonneg_left ha (show 0 ≤ 2 * q * E by positivity)
  have hmore : 0 ≤ (1 + 2 * q) * J + E + 4 * q * δ + (4 + 4 * q) * H * η * δ := by positivity
  nlinarith only [hgradient, herror, hqa, hmore]

noncomputable def maxError (c : Choice p) (f : Functions p) (s : Iterate p) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin p.n =>
    ‖LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i) - gradient (f i) s.point‖)

lemma error_le_max (c : Choice p) (f : Functions p) (s : Iterate p) (i : Fin p.n) :
    ‖LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i) - gradient (f i) s.point‖ ≤ maxError c f s := by
  unfold maxError
  exact Finset.le_sup' (fun j : Fin p.n =>
    ‖LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode j) - gradient (f j) s.point‖) (Finset.mem_univ i)

lemma maxError_nonneg (c : Choice p) (f : Functions p) (s : Iterate p) :
    0 ≤ maxError c f s := (norm_nonneg _).trans (error_le_max c f s ⟨0, p.n.pos⟩)

lemma maxError_le (c : Choice p) (f : Functions p) (s : Iterate p) (E : ℝ)
    (h : ∀ i, ‖LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i) - gradient (f i) s.point‖ ≤ E) :
    maxError c f s ≤ E := by
  unfold maxError
  exact Finset.sup'_le _ _ (fun i _ => h i)

lemma initial_error_bound (c : Choice p) (hε : 0 < p.ε) (f : Functions p) (seed : Sample p) :
    maxError c f (initialIterate p c f seed) ≤ spacing p c * Real.sqrt (p.d : ℝ) := by
  have hρ := DashaScalingParameters.spacing_pos c hε
  apply maxError_le
  intro i
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact (DashaInitialization.fine_error_sq p.d (spacing p c)
    (DashaScalingParameters.spacing_pos c hε) (gradient (f i) p.x0) (seed i).2).trans (by ring_nf; rfl)

lemma estimate_error_bound (c : Choice p) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (s : Iterate p) :
    ‖estimate p c s - gradient (objective p f) s.point‖ ≤ maxError c f s := by
  rw [DashaScalingDescent.estimate_eq_mean, DashaScalingDescent.objective_gradient_eq f hg,
    ← smul_sub, ← Finset.sum_sub_distrib]
  calc
    _ ≤ (1 / (p.n : ℝ)) * ∑ i,
        ‖LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i) - gradient (f i) s.point‖ :=
      DashaScalingDescent.mean_norm _
    _ ≤ (1 / (p.n : ℝ)) * ∑ _ : Fin p.n, maxError c f s :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => error_le_max c f s i)) (by positivity)
    _ = _ := by simp [ne_of_gt (show (0 : ℝ) < p.n by exact_mod_cast p.n.pos)]

lemma estimate_bound (c : Choice p) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (s : Iterate p) :
    ‖estimate p c s‖ ≤ ‖gradient (objective p f) s.point‖ + maxError c f s := by
  have ht : ‖estimate p c s‖ ≤ ‖estimate p c s - gradient (objective p f) s.point‖ +
      ‖gradient (objective p f) s.point‖ := by
    simpa using norm_add_le (estimate p c s - gradient (objective p f) s.point) (gradient (objective p f) s.point)
  linarith [estimate_error_bound c f hg s]

noncomputable def envelope (c : Choice p) (f : Functions p) (s : Iterate p) : ℝ :=
  ‖gradient (objective p f) s.point‖ + maxError c f s + 2 * spacing p c * Real.sqrt (p.d : ℝ)

lemma local_change_bound (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (s : Iterate p) (i : Fin p.n) :
    ‖gradient (f i) (s.point - stepSize p c • estimate p c s) - gradient (f i) s.point‖ ≤
      Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c *
        (‖gradient (objective p f) s.point‖ + maxError c f s) := by
  have hη := DashaScalingParameters.stepSize_pos c hL hH
  have hl := DashaScalingRange.local_norm_of_mean_square
    (fun i => gradient (f i) (s.point - stepSize p c • estimate p c s) - gradient (f i) s.point)
    p.Lhat ‖s.point - stepSize p c • estimate p c s - s.point‖ hH.le (norm_nonneg _)
    (hs _ _) i
  have he : s.point - stepSize p c • estimate p c s - s.point = -(stepSize p c) • estimate p c s := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hη] at hl
  have hb := mul_le_mul_of_nonneg_left (estimate_bound c f hg s)
    (show 0 ≤ Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c by positivity)
  nlinarith only [hl, hb]

lemma maxError_step (c : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (s : Iterate p)
    (hstate : ∀ i, s.localGradient i = gradient (f i) s.point) (seed : Sample p) :
    maxError c f (nextIterate p c f s seed) ≤
      (1 + 2 * LongTails.Algorithms.DashaCyclic.multiplier c.block * momentum p c) * maxError c f s +
      (1 + 2 * LongTails.Algorithms.DashaCyclic.multiplier c.block) *
        (Real.sqrt (p.n : ℝ) * p.Lhat) * stepSize p c *
          (‖gradient (objective p f) s.point‖ + maxError c f s) +
      2 * spacing p c * Real.sqrt (p.d : ℝ) := by
  have hρ := DashaScalingParameters.spacing_pos c hε
  have hq : 0 ≤ LongTails.Algorithms.DashaCyclic.multiplier c.block := by
    unfold LongTails.Algorithms.DashaCyclic.multiplier
    positivity
  apply maxError_le
  intro i
  let e := LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i) - gradient (f i) s.point
  let change := gradient (f i) (s.point - stepSize p c • estimate p c s) - gradient (f i) s.point
  let v := LongTails.Algorithms.DashaCyclic.compress c.block c.precision (spacing p c)
    (change - momentum p c • e) (seed i)
  have hc : ‖v‖ ≤ 2 * LongTails.Algorithms.DashaCyclic.multiplier c.block *
      ‖change - momentum p c • e‖ + 2 * (spacing p c * Real.sqrt (p.d : ℝ)) := by
    have hb := DashaCompression.compress_norm_bound c.block c.precision (spacing p c) hρ
      (change - momentum p c • e) (seed i)
    dsimp [v]
    nlinarith only [hb, show 0 ≤ spacing p c * Real.sqrt (p.d : ℝ) by positivity]
  have hb := local_error_bound e change v (momentum p c)
    (LongTails.Algorithms.DashaCyclic.multiplier c.block) (spacing p c * Real.sqrt (p.d : ℝ))
    (maxError c f s) (Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c *
      (‖gradient (objective p f) s.point‖ + maxError c f s))
    (DashaScalingParameters.momentum_pos c).le hq (error_le_max c f s i)
    (local_change_bound c hL hH f hg hs s i) hc
  have he : LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c)
      ((nextIterate p c f s seed).localCode i) - gradient (f i) (nextIterate p c f s seed).point =
      e + v - change := by
    rw [DashaScalingDescent.next_local_code]
    simp only [hstate]
    dsimp [e, v, change, nextIterate]
    module
  rw [he]
  convert hb using 1
  ring

lemma gradient_step (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (s : Iterate p) (seed : Sample p) :
    ‖gradient (objective p f) (nextIterate p c f s seed).point‖ ≤
      ‖gradient (objective p f) s.point‖ + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c *
        (‖gradient (objective p f) s.point‖ + maxError c f s) := by
  have hd : ‖gradient (objective p f) (nextIterate p c f s seed).point -
      gradient (objective p f) s.point‖ ≤ Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c *
        (‖gradient (objective p f) s.point‖ + maxError c f s) := by
    rw [DashaScalingDescent.objective_gradient_eq f hg, DashaScalingDescent.objective_gradient_eq f hg,
      ← smul_sub, ← Finset.sum_sub_distrib]
    apply (DashaScalingDescent.mean_norm _).trans
    calc
      _ ≤ (1 / (p.n : ℝ)) * ∑ _ : Fin p.n, Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c *
          (‖gradient (objective p f) s.point‖ + maxError c f s) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => local_change_bound c hL hH f hg hs s i)) (by positivity)
      _ = _ := by simp [DashaScalingDescent.objective_gradient_eq f hg, ne_of_gt (show (0 : ℝ) < p.n by exact_mod_cast p.n.pos)]
  have ht : ‖gradient (objective p f) (nextIterate p c f s seed).point‖ ≤
      ‖gradient (objective p f) (nextIterate p c f s seed).point - gradient (objective p f) s.point‖ +
      ‖gradient (objective p f) s.point‖ := by
    simpa using norm_add_le (gradient (objective p f) (nextIterate p c f s seed).point - gradient (objective p f) s.point)
      (gradient (objective p f) s.point)
  linarith

lemma envelope_step (c : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (s : Iterate p)
    (hstate : ∀ i, s.localGradient i = gradient (f i) s.point) (seed : Sample p) :
    envelope c f (nextIterate p c f s seed) ≤ DashaScalingEnvelope.growth c * envelope c f s := by
  have hη := DashaScalingParameters.stepSize_pos c hL hH
  have hρ := DashaScalingParameters.spacing_pos c hε
  have hb := joint_step_bound ‖gradient (objective p f) s.point‖ (maxError c f s)
    ‖gradient (objective p f) (nextIterate p c f s seed).point‖
    (maxError c f (nextIterate p c f s seed)) (Real.sqrt (p.n : ℝ) * p.Lhat)
    (stepSize p c) (LongTails.Algorithms.DashaCyclic.multiplier c.block) (momentum p c)
    (spacing p c * Real.sqrt (p.d : ℝ)) (norm_nonneg _) (maxError_nonneg c f s)
    (by positivity) (by positivity) hη.le (DashaScalingParameters.multiplier_ge_one c)
    (DashaScalingParameters.momentum_le_one c) (gradient_step c hL hH f hg hs s seed)
    (by nlinarith only [maxError_step c hε hL hH f hg hs s hstate seed])
  dsimp [envelope, DashaScalingEnvelope.growth]
  nlinarith only [hb]

lemma trajectory_bound (c : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (J : ℝ) (hJ : ‖gradient (objective p f) p.x0‖ ≤ J)
    (seed : ℕ → Sample p) (k : ℕ) :
    envelope c f (trajectory p c f seed k) ≤
      (J + 3 * spacing p c * Real.sqrt (p.d : ℝ)) * DashaScalingEnvelope.growth c ^ k := by
  have hη := DashaScalingParameters.stepSize_pos c hL hH
  have hC : 0 ≤ DashaScalingEnvelope.growth c := by
    unfold DashaScalingEnvelope.growth LongTails.Algorithms.DashaCyclic.multiplier
    positivity
  induction k with
  | zero =>
    have hi := initial_error_bound c hε f (seed 0)
    change ‖gradient (objective p f) p.x0‖ + maxError c f (initialIterate p c f (seed 0)) +
      2 * spacing p c * Real.sqrt (p.d : ℝ) ≤ _
    simp only [pow_zero, mul_one]
    linarith
  | succ k ih =>
    have hb := envelope_step c hε hL hH f hg hs (trajectory p c f seed k)
      (DashaScalingDescent.trajectory_gradient c f seed k) (seed (k + 1))
    calc
      _ ≤ DashaScalingEnvelope.growth c * envelope c f (trajectory p c f seed k) := hb
      _ ≤ DashaScalingEnvelope.growth c * ((J + 3 * spacing p c * Real.sqrt (p.d : ℝ)) *
          DashaScalingEnvelope.growth c ^ k) := mul_le_mul_of_nonneg_left ih hC
      _ = _ := by rw [pow_succ]; ring

lemma estimate_le_envelope (c : Choice p) (hε : 0 < p.ε) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (s : Iterate p) :
    ‖estimate p c s‖ ≤ envelope c f s := by
  have hρ := DashaScalingParameters.spacing_pos c hε
  have hb := estimate_bound c f hg s
  unfold envelope
  linarith [show 0 ≤ spacing p c * Real.sqrt (p.d : ℝ) by positivity]

lemma innovation_bound (c : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (s : Iterate p)
    (hstate : ∀ i, s.localGradient i = gradient (f i) s.point) (i : Fin p.n) :
    ‖gradient (f i) (s.point - stepSize p c • estimate p c s) - s.localGradient i -
      momentum p c • (LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i) -
        s.localGradient i)‖ ≤ (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c) * envelope c f s := by
  have hη := DashaScalingParameters.stepSize_pos c hL hH
  have hρ := DashaScalingParameters.spacing_pos c hε
  have ha := DashaScalingParameters.momentum_pos c
  have ha1 := DashaScalingParameters.momentum_le_one c
  have he := error_le_max c f s i
  have hE := maxError_nonneg c f s
  have hd := local_change_bound c hL hH f hg hs s i
  simp only [hstate]
  have ht := norm_sub_le
    (gradient (f i) (s.point - stepSize p c • estimate p c s) - gradient (f i) s.point)
    (momentum p c • (LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i) - gradient (f i) s.point))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha] at ht
  have hm := mul_le_mul_of_nonneg_left he ha.le
  have hm1 := mul_le_mul_of_nonneg_right ha1 hE
  have hmore : 0 ≤ ‖gradient (objective p f) s.point‖ +
      2 * spacing p c * Real.sqrt (p.d : ℝ) *
        (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c) := by positivity
  unfold envelope
  nlinarith only [ht, hd, hm, hm1, hmore]

lemma aggregate_code_bound (c : Choice p) (hε : 0 < p.ε) (s : Iterate p) (B : ℝ)
    (hB : ‖estimate p c s‖ ≤ B) (j : Fin p.d) :
    |((∑ i, s.localCode i j : ℤ) : ℝ)| ≤ (p.n : ℝ) * B / spacing p c := by
  have hρ := DashaScalingParameters.spacing_pos c hε
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have he : ((∑ i, s.localCode i j : ℤ) : ℝ) = ((p.n : ℝ) / spacing p c) * (estimate p c s) j := by
    simp only [estimate, LongTails.Algorithms.DashaQuantization.reconstruct,
      PiLp.smul_apply, smul_eq_mul]
    field_simp [ne_of_gt hn, ne_of_gt hρ]
  rw [he, abs_mul, abs_of_pos (div_pos hn hρ)]
  calc
    _ ≤ ((p.n : ℝ) / spacing p c) * ‖estimate p c s‖ :=
      mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (estimate p c s) j) (by positivity)
    _ ≤ ((p.n : ℝ) / spacing p c) * B := mul_le_mul_of_nonneg_left hB (by positivity)
    _ = _ := by ring

lemma initial_aggregate_code_bound (c : Choice p) (hε : 0 < p.ε) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (J : ℝ) (hJ : ‖gradient (objective p f) p.x0‖ ≤ J) (seed : Sample p) (j : Fin p.d) :
    |((∑ i, (initialIterate p c f seed).localCode i j : ℤ) : ℝ)| ≤
      (p.n : ℝ) * (J + spacing p c * Real.sqrt (p.d : ℝ)) / spacing p c := by
  apply aggregate_code_bound c hε
  have hb := estimate_bound c f hg (initialIterate p c f seed)
  have hi := initial_error_bound c hε f seed
  change ‖estimate p c (initialIterate p c f seed)‖ ≤ _
  change ‖estimate p c (initialIterate p c f seed)‖ ≤
    ‖gradient (objective p f) p.x0‖ + maxError c f (initialIterate p c f seed) at hb
  linarith

lemma sparse_initial_error_bound (c initializer : Choice p) (hε : 0 < p.ε) (f : Functions p)
    (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G) (seed : Sample p) :
    maxError c f (sparseInitialIterate p c initializer f seed) ≤
      (2 * LongTails.Algorithms.DashaCyclic.multiplier initializer.block + 1) * p.G +
        spacing p c * Real.sqrt (p.d : ℝ) := by
  have hq : 0 ≤ LongTails.Algorithms.DashaCyclic.multiplier initializer.block := by
    unfold LongTails.Algorithms.DashaCyclic.multiplier
    positivity
  apply maxError_le
  intro i
  have hc := DashaCompression.compress_norm_bound initializer.block initializer.precision (spacing p c)
    (DashaScalingParameters.spacing_pos c hε) (gradient (f i) p.x0) (seed i)
  have ht := norm_sub_le
    (LongTails.Algorithms.DashaCyclic.compress initializer.block initializer.precision (spacing p c)
      (gradient (f i) p.x0) (seed i)) (gradient (f i) p.x0)
  have hm := mul_le_mul_of_nonneg_left (hG i) (show 0 ≤ 2 * LongTails.Algorithms.DashaCyclic.multiplier initializer.block by positivity)
  change ‖LongTails.Algorithms.DashaCyclic.compress initializer.block initializer.precision (spacing p c)
    (gradient (f i) p.x0) (seed i) - gradient (f i) p.x0‖ ≤ _
  nlinarith only [ht, hc, hm, hG i]

lemma sparse_trajectory_bound (c initializer : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (J : ℝ) (hJ : ‖gradient (objective p f) p.x0‖ ≤ J)
    (seed : ℕ → Sample p) (k : ℕ) :
    envelope c f (sparseTrajectory p c initializer f seed k) ≤
      (J + (2 * LongTails.Algorithms.DashaCyclic.multiplier initializer.block + 1) * p.G +
        3 * spacing p c * Real.sqrt (p.d : ℝ)) * DashaScalingEnvelope.growth c ^ k := by
  have hη := DashaScalingParameters.stepSize_pos c hL hH
  have hC : 0 ≤ DashaScalingEnvelope.growth c := by
    unfold DashaScalingEnvelope.growth LongTails.Algorithms.DashaCyclic.multiplier
    positivity
  induction k with
  | zero =>
    have hi := sparse_initial_error_bound c initializer hε f hG (seed 0)
    change ‖gradient (objective p f) p.x0‖ + maxError c f (sparseInitialIterate p c initializer f (seed 0)) +
      2 * spacing p c * Real.sqrt (p.d : ℝ) ≤ _
    simp only [pow_zero, mul_one]
    linarith
  | succ k ih =>
    have hb := envelope_step c hε hL hH f hg hs (sparseTrajectory p c initializer f seed k)
      (DashaScalingDescent.sparse_trajectory_gradient c initializer f seed k) (seed (k + 1))
    calc
      _ ≤ DashaScalingEnvelope.growth c * envelope c f (sparseTrajectory p c initializer f seed k) := hb
      _ ≤ DashaScalingEnvelope.growth c * ((J +
          (2 * LongTails.Algorithms.DashaCyclic.multiplier initializer.block + 1) * p.G +
          3 * spacing p c * Real.sqrt (p.d : ℝ)) * DashaScalingEnvelope.growth c ^ k) := mul_le_mul_of_nonneg_left ih hC
      _ = _ := by rw [pow_succ]; ring

end LongTails.Proofs.DashaTrackingEnvelope
