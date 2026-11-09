import LongTails.Proofs.RecoveryFractalEnergy
import LongTails.Proofs.RecoveryFractalRecovery
import LongTails.Proofs.RecoveryFractalTuning

namespace LongTails.Proofs.RecoveryFractalCompleted

open scoped RealInnerProductSpace
open OracleTemplate OracleTemplate.ScheduleBlock
open LongTails.Setups.SmoothHessianLipschitzGd LongTails.Algorithms.RecoveryFractalGd
open LongTails.Proofs.RecoveryFractalLocal LongTails.Proofs.RecoveryFractalSchedule
open LongTails.Proofs.RecoveryFractalExecution LongTails.Proofs.GdSnapshotDynamics
open LongTails.Proofs.AdaptiveSilverSplit LongTails.Proofs.RecoveryFractalEnergy
open LongTails.Proofs.RecoveryFractalRecovery

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

lemma trial_high_model_bound (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hk : 2 ≤ level p) (hG : 0 ≤ threshold p)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ p.E) (eig : ι → ℝ) (X : ℕ → p.E)
    (hc : ∀ j v, ⟪b j, fderiv ℝ (gradient f) (X 0) v⟫ = eig j * ⟪b j, v⟫)
    (heig : ∀ j, eig j ≤ p.L) (t : ℕ) (ht : t ≤ 2 * epochLength p)
    (hstep : ∀ i < t, X (i + 1) = X i - fractalStep p i • gradient f (X i))
    (hg : ∀ i < t, ‖gradient f (X i)‖ ≤ 8 * threshold p)
    (q : ℝ) (hq : 0 ≤ q)
    (hp : ∀ j, lowerCurvature p < eig j → |pr (fractalStep p) (eig j) t| ≤ q) :
    ‖proj b (fun j => if lowerCurvature p < eig j then (1 : ℝ) else 0)
      (gradient f (X 0) + fderiv ℝ (gradient f) (X 0) (X t - X 0))‖ ≤
      q * ‖gradient f (X 0)‖ +
      (t : ℝ) * (4 / lowerCurvature p) * (p.ρ * radius p * (8 * threshold p)) + errorBound p := by
  have herr := trial_positive_filter_error p hL hρ hk hG f hf hH b eig X hc heig t ht hstep hg
  have hhigh := high_filter_transfer b eig (lowerCurvature p) (lowerCurvature_pos p hL).le
    (fractalStep p) t (gradient f (X 0)) (gradient f (X t)) _ q hq herr hp
  let model := gradient f (X 0) + fderiv ℝ (gradient f) (X 0) (X t - X 0)
  let Q := proj b (fun j => if lowerCurvature p < eig j then (1 : ℝ) else 0)
  have hr : ‖model - gradient f (X t)‖ ≤ errorBound p := by
    have hh := trial_residual_bound p hL hρ hk hG f hf hH X t ht hstep hg
    calc
      _ = ‖gradient f (X t) - gradient f (X 0) -
          fderiv ℝ (gradient f) (X 0) (X t - X 0)‖ := by
        rw [norm_sub_rev]
        congr 1
        dsimp [model]
        abel
      _ ≤ _ := hh
  have hQr : ‖Q (model - gradient f (X t))‖ ≤ errorBound p :=
    ((high_mask_norm_le b eig (lowerCurvature p) (lowerCurvature_pos p hL).le _).trans
      (P_norm_le b eig _)).trans hr
  change ‖Q model‖ ≤ _
  calc
    _ ≤ ‖Q (model - gradient f (X t))‖ + ‖Q (gradient f (X t))‖ := by
      simpa only [map_sub] using norm_le_norm_sub_add (Q model) (Q (gradient f (X t)))
    _ ≤ errorBound p + (q * ‖gradient f (X 0)‖ +
        (t : ℝ) * (4 / lowerCurvature p) * (p.ρ * radius p * (8 * threshold p))) :=
      add_le_add hQr hhigh
    _ = _ := by ring

lemma midpoint_negative_persistence (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (H : E →L[ℝ] E) (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (L : ℝ) (hL : 0 ≤ L) (heig : ∀ j, -L ≤ eig j)
    (F : E → E) (z : E) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (X : ℕ → E) (n : ℕ)
    (hstep : ∀ i < 2 * n, X (i + 1) = X i - a i • F (X i))
    (hperiod : ∀ i < n, a (n + i) = a i)
    (B ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ i < 2 * n, ‖F (X i) - F z - H (X i - z)‖ ≤ B)
    (hnoise : B ^ 2 * Real.log (1 + L * ssum a n) ≤ ε ^ 2 / 64)
    (hmid : ε / 4 ≤ ‖(F z + H (X n - z)) - P b eig (F z + H (X n - z))‖) :
    ∀ i ≤ n, ε ^ 2 / 64 ≤
      ‖(F z + H (X (n + i) - z)) - P b eig (F z + H (X (n + i) - z))‖ ^ 2 := by
  intro i hi
  have hp := model_negative_persistence b eig H hc L hL heig F z a ha
    (fun j => X (n + j)) i (fun j hj => by
      rw [show n + (j + 1) = (n + j) + 1 by omega, hstep (n + j) (by omega), hperiod j (by omega)])
    B (fun j hj => herr (n + j) (by omega))
  simp only [Nat.add_zero] at hp
  have hsum : ssum a i ≤ ssum a n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi)
    intro j _ _
    exact ha j
  have hsi : 0 ≤ ssum a i := Finset.sum_nonneg fun j _ => ha j
  have hlog : Real.log (1 + L * ssum a i) ≤ Real.log (1 + L * ssum a n) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hn := (mul_le_mul_of_nonneg_left hlog (sq_nonneg B)).trans hnoise
  have hm := pow_le_pow_left₀ (show 0 ≤ ε / 4 by positivity) hmid 2
  nlinarith

open LongTails.Proofs.AdaptiveSilverDynamics

lemma completed_trial_descent_spectral (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hε : 0 ≤ p.ε) (hk : 2 ≤ level p)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ p.E) (eig : ι → ℝ) (X : ℕ → p.E)
    (hc : ∀ j v, ⟪b j, fderiv ℝ (gradient f) (X 0) v⟫ = eig j * ⟪b j, v⟫)
    (heig : ∀ j, -p.L ≤ eig j ∧ eig j ≤ p.L)
    (hstep : ∀ i < 2 * epochLength p, X (i + 1) = X i - fractalStep p i • gradient f (X i))
    (hg : ∀ i < 2 * epochLength p, ‖gradient f (X i)‖ ≤ 8 * threshold p)
    (h0 : ‖gradient f (X 0)‖ ≤ threshold p)
    (hmid : p.ε < ‖gradient f (X (epochLength p))‖)
    (hsmall : (2 * epochLength p : ℝ) * (4 / lowerCurvature p) *
      (p.ρ * radius p * (8 * threshold p)) + errorBound p ≤ threshold p)
    (hhigh : 1 / (256 * blockLength p) * threshold p +
      (2 * epochLength p : ℝ) * (4 / lowerCurvature p) *
        (p.ρ * radius p * (8 * threshold p)) + errorBound p ≤ 3 * p.ε / 256)
    (hE : errorBound p ≤ p.ε / 256)
    (hnoise : errorBound p ^ 2 * Real.log (1 + p.L * ssum (fractalStep p) (epochLength p)) ≤ p.ε ^ 2 / 64)
    (herror : 4 * threshold p * ssum (fractalStep p) (epochLength p) * errorBound p +
      ssum (fractalStep p) (epochLength p) * errorBound p ^ 2 + p.ρ * radius p ^ 3 ≤
      p.ε ^ 2 / (1024 * lowerCurvature p)) :
    f (X (2 * epochLength p)) - f (X 0) ≤ -(p.ε ^ 2) / (512 * lowerCurvature p) := by
  let H := fderiv ℝ (gradient f) (X 0)
  let g := gradient f (X 0)
  let d := fun i => X i - X 0
  let e := fun i => gradient f (X i) - g - H (d i)
  let c := fun j => if 0 ≤ eig j ∧ eig j ≤ lowerCurvature p then (1 : ℝ) else 0
  let ch := fun j => if lowerCurvature p < eig j then (1 : ℝ) else 0
  let gm := g + H (d (epochLength p))
  have hμ := lowerCurvature_pos p hL
  have hG : 0 ≤ threshold p := by unfold threshold; positivity
  have hB : 0 ≤ errorBound p := by unfold errorBound; positivity
  have hR : 0 ≤ radius p := by unfold radius; positivity
  have ha (i : ℕ) := (fractalStep_pos p hL hk i).le
  have hsym : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫ := fun u v => OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hf (X 0) u v
  have he (i : ℕ) (hi : i ≤ 2 * epochLength p) : ‖e i‖ ≤ errorBound p :=
    trial_residual_bound p hL hρ hk hG f hf hH X i hi
      (fun j hj => hstep j (hj.trans_le hi)) (fun j hj => hg j (hj.trans_le hi))
  have hd (i : ℕ) (hi : i < 2 * epochLength p) :
      d (i + 1) = d i - fractalStep p i • (g + H (d i) + e i) := by
    dsimp [d, e]
    rw [hstep i hi]
    module
  have hpos (i : ℕ) (hi : i ≤ 2 * epochLength p) : ‖proj b c (g + H (d i))‖ ≤ 2 * threshold p :=
    (low_mask_norm_le b eig (lowerCurvature p) _).trans
      (trial_positive_model p hL hρ hk hG f hf hH b eig X hc (fun j => (heig j).2) i hi
        (fun j hj => hstep j (hj.trans_le hi)) (fun j hj => hg j (hj.trans_le hi)) h0 hsmall)
  have hhi (t : ℕ) (ht : t = epochLength p ∨ t = 2 * epochLength p) :
      ‖proj b ch (g + H (d t))‖ ≤ 3 * p.ε / 256 := by
    have ht' : t ≤ 2 * epochLength p := by omega
    have hh := trial_high_model_bound p hL hρ hk hG f hf hH b eig X hc (fun j => (heig j).2) t ht'
      (fun j hj => hstep j (hj.trans_le ht')) (fun j hj => hg j (hj.trans_le ht'))
      (1 / (256 * blockLength p)) (by positivity) (fun j hj => by
        rcases ht with ht | ht
        · rw [ht]; exact epoch_filter_bound p hL hk hj.le (heig j).2
        · rw [ht]; exact two_epoch_filter p hL hk hj.le (heig j).2)
    have hinit := mul_le_mul_of_nonneg_left h0 (show 0 ≤ 1 / (256 * (blockLength p : ℝ)) by positivity)
    have htR : (t : ℝ) ≤ 2 * epochLength p := by exact_mod_cast ht'
    have hforce := mul_le_mul_of_nonneg_right htR
      (show 0 ≤ (4 / lowerCurvature p) * (p.ρ * radius p * (8 * threshold p)) by positivity)
    change ‖proj b ch (g + H (d t))‖ ≤ _ at hh
    nlinarith only [hh, hinit, hforce, hhigh]
  have hcase : p.ε / 4 ≤ ‖proj b c gm‖ ∨ p.ε / 4 ≤ ‖gm - P b eig gm‖ := by
    apply midpoint_model_dichotomy b eig (lowerCurvature p) hμ.le
      (gradient f (X (epochLength p))) gm p.ε hmid
    · have hh := he (epochLength p) (by omega)
      have heq : gradient f (X (epochLength p)) - gm = e (epochLength p) := by dsimp [gm, e]; abel
      rw [heq]
      linarith
    · have hh := hhi (epochLength p) (Or.inl rfl)
      change ‖proj b ch gm‖ ≤ _
      linarith
  have hS := (epoch_sum_bounds p hL hk).1
  have hlow := low_two_epoch_energy b eig H hc hsym (lowerCurvature p) hμ (fractalStep p) ha g d e
    (epochLength p) (by simp [d]) hd (fun i _ => epoch_periodic p i)
    (fun i _ => (step_bounds p hL hk i).2) hS (errorBound p) (threshold p) hB hG
    (fun i hi => he i hi.le) ((low_mask_norm_le b eig (lowerCurvature p) _).trans ((P_norm_le b eig _).trans h0))
    (hpos _ (by omega)) (hpos _ le_rfl)
  have hn := negative_two_epoch_energy b eig H hc hsym (fractalStep p) g d e (epochLength p)
    (errorBound p) 0 (by simp [d]) (fun i _ => ha i) hd (fun i hi => he i hi.le)
    (fun i _ => epoch_periodic p i) (fun i _ _ => sq_nonneg _)
  simp only [mul_zero, zero_div, zero_add] at hn
  have hstrong (hm : p.ε / 4 ≤ ‖gm - P b eig gm‖) :
      psiPart b eig H g (d (2 * epochLength p)) ≤ -(p.ε ^ 2) / (256 * lowerCurvature p) +
        ssum (fractalStep p) (epochLength p) * errorBound p ^ 2 := by
    have hp := midpoint_negative_persistence b eig H hc p.L hL.le (fun j => (heig j).1)
      (gradient f) (X 0) (fractalStep p) ha X (epochLength p) hstep (fun i _ => epoch_periodic p i)
      (errorBound p) p.ε hε (fun i hi => he i hi.le) hnoise hm
    have hq := negative_two_epoch_energy b eig H hc hsym (fractalStep p) g d e (epochLength p)
      (errorBound p) (p.ε ^ 2 / 64) (by simp [d]) (fun i _ => ha i) hd (fun i hi => he i hi.le)
      (fun i _ => epoch_periodic p i) (fun i hi hi' => by
        have hh := hp (i - epochLength p) (by omega)
        simpa only [Nat.add_sub_of_le hi] using hh)
    have hs := mul_le_mul_of_nonneg_right hS (sq_nonneg p.ε)
    simp only [div_eq_mul_inv, mul_inv_rev] at hq hs ⊢
    norm_num at hq hs ⊢
    nlinarith only [hq, hs]
  have hhighEnergy : maskEnergy (proj b ch) H g (d (2 * epochLength p)) ≤
      9 * p.ε ^ 2 / (131072 * lowerCurvature p) := by
    have hh := high_energy_upper b eig H hc (lowerCurvature p) hμ g (d (2 * epochLength p))
    have hs := pow_le_pow_left₀ (norm_nonneg _) (hhi (2 * epochLength p) (Or.inr rfl)) 2
    have hmul := mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr hμ.le)
    change maskEnergy (proj b ch) H g (d (2 * epochLength p)) ≤ _ at hh
    simp only [div_eq_mul_inv, mul_inv_rev] at hh ⊢
    norm_num at hh ⊢
    dsimp only [ch] at hmul
    simp only [map_add] at hmul
    nlinarith only [hh, hmul]
  have htotal := completed_energy_arithmetic (lowerCurvature p) p.ε ‖proj b c gm‖ ‖gm - P b eig gm‖
    (maskEnergy (proj b c) H g (d (2 * epochLength p)))
    (maskEnergy (proj b ch) H g (d (2 * epochLength p)))
    (psiPart b eig H g (d (2 * epochLength p)))
    (4 * threshold p * ssum (fractalStep p) (epochLength p) * errorBound p)
    (ssum (fractalStep p) (epochLength p) * errorBound p ^ 2) (p.ρ * radius p ^ 3)
    hμ hε hcase hlow hn hstrong hhighEnergy herror
  have hTaylor := taylor_cubic hf hρ hH (X 0) (X (2 * epochLength p))
  have hr : ‖d (2 * epochLength p)‖ ≤ radius p := by
    have hh := trial_radius p hL hk hG f X (2 * epochLength p) le_rfl hstep hg
    change ‖d (2 * epochLength p)‖ ≤ _ at hh
    linarith
  have hrem := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hr 3) hρ
  have hsplit := model_split b eig H hc g (d (2 * epochLength p))
  have hpossplit := positive_energy_split b eig H hc (lowerCurvature p) hμ.le g (d (2 * epochLength p))
  have hup := (abs_le.mp hTaylor).2
  change f (X (2 * epochLength p)) - f (X 0) - ⟪g, d (2 * epochLength p)⟫ -
    ⟪H (d (2 * epochLength p)), d (2 * epochLength p)⟫ / 2 ≤ _ at hup
  rw [hsym] at hup
  linarith only [hup, hrem, hsplit, hpossplit, htotal]

lemma completed_trial_descent (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hε : 0 ≤ p.ε) (hk : 2 ≤ level p)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (X : ℕ → p.E)
    (hstep : ∀ i < 2 * epochLength p, X (i + 1) = X i - fractalStep p i • gradient f (X i))
    (hg : ∀ i < 2 * epochLength p, ‖gradient f (X i)‖ ≤ 8 * threshold p)
    (h0 : ‖gradient f (X 0)‖ ≤ threshold p)
    (hmid : p.ε < ‖gradient f (X (epochLength p))‖)
    (hsmall : (2 * epochLength p : ℝ) * (4 / lowerCurvature p) *
      (p.ρ * radius p * (8 * threshold p)) + errorBound p ≤ threshold p)
    (hhigh : 1 / (256 * blockLength p) * threshold p +
      (2 * epochLength p : ℝ) * (4 / lowerCurvature p) *
        (p.ρ * radius p * (8 * threshold p)) + errorBound p ≤ 3 * p.ε / 256)
    (hE : errorBound p ≤ p.ε / 256)
    (hnoise : errorBound p ^ 2 * Real.log (1 + p.L * ssum (fractalStep p) (epochLength p)) ≤ p.ε ^ 2 / 64)
    (herror : 4 * threshold p * ssum (fractalStep p) (epochLength p) * errorBound p +
      ssum (fractalStep p) (epochLength p) * errorBound p ^ 2 + p.ρ * radius p ^ 3 ≤
      p.ε ^ 2 / (1024 * lowerCurvature p)) :
    f (X (2 * epochLength p)) - f (X 0) ≤ -(p.ε ^ 2) / (512 * lowerCurvature p) := by
  classical
  let H := fderiv ℝ (gradient f) (X 0)
  have hsym := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hf (X 0)
  let b := hsym.eigenvectorBasis rfl
  let eig := hsym.eigenvalues rfl
  have hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫ := by
    intro j v
    simpa only [OrthonormalBasis.repr_apply_apply, RCLike.ofReal_real_eq_id, id_eq,
      ContinuousLinearMap.coe_coe] using hsym.eigenvectorBasis_apply_self_apply rfl v j
  have heig : ∀ j, -p.L ≤ eig j ∧ eig j ≤ p.L :=
    fun j => eig_bounds hL.le hlip (X 0) hsym j
  exact completed_trial_descent_spectral p hL hρ hε hk f hf hH b eig X hc heig
    hstep hg h0 hmid hsmall hhigh hE hnoise herror

lemma completed_trial_execution (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hε : 0 ≤ p.ε) (hk : 2 ≤ level p)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (T : ℕ)
    (hr : (traj p f T).control.recovering = false)
    (hc : (traj p f T).control.phase = 0 ∨ 2 * epochLength p ≤ (traj p f T).control.phase)
    (hg : ∀ i < 2 * epochLength p, ‖gradient f (traj p f (T + i)).point‖ ≤ 8 * threshold p)
    (h0 : ‖gradient f (traj p f T).point‖ ≤ threshold p)
    (hmid : p.ε < ‖gradient f (traj p f (T + epochLength p)).point‖)
    (hsmall : (2 * epochLength p : ℝ) * (4 / lowerCurvature p) *
      (p.ρ * radius p * (8 * threshold p)) + errorBound p ≤ threshold p)
    (hhigh : 1 / (256 * blockLength p) * threshold p +
      (2 * epochLength p : ℝ) * (4 / lowerCurvature p) *
        (p.ρ * radius p * (8 * threshold p)) + errorBound p ≤ 3 * p.ε / 256)
    (hE : errorBound p ≤ p.ε / 256)
    (hnoise : errorBound p ^ 2 * Real.log (1 + p.L * ssum (fractalStep p) (epochLength p)) ≤ p.ε ^ 2 / 64)
    (herror : 4 * threshold p * ssum (fractalStep p) (epochLength p) * errorBound p +
      ssum (fractalStep p) (epochLength p) * errorBound p ^ 2 + p.ρ * radius p ^ 3 ≤
      p.ε ^ 2 / (1024 * lowerCurvature p)) :
    (traj p f (T + 2 * epochLength p)).control = ⟨2 * epochLength p, false, 0⟩ ∧
      f (traj p f (T + 2 * epochLength p)).point - f (traj p f T).point ≤
        -(p.ε ^ 2) / (512 * lowerCurvature p) := by
  have hG : 0 ≤ threshold p := by unfold threshold; positivity
  have ht := trial_trace p hk hG f T (2 * epochLength p) le_rfl hr hc h0 hg
  have hN : 0 < epochLength p := by
    unfold epochLength repetitions
    exact Nat.mul_pos (blockLength_pos p) (by omega)
  refine ⟨ht.1 _ (by omega) le_rfl, ?_⟩
  have hh := completed_trial_descent p hL hρ hε hk f hf hH hlip
    (fun i => (traj p f (T + i)).point) ht.2 hg (by simpa using h0) hmid
    hsmall hhigh hE hnoise herror
  simpa using hh

open LongTails.Proofs.RecoveryFractalTuning

lemma completed_trial_execution_tuned (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hε : 0 ≤ p.ε) (hk : 2 ≤ level p)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (T : ℕ)
    (hr : (traj p f T).control.recovering = false)
    (hc : (traj p f T).control.phase = 0 ∨ 2 * epochLength p ≤ (traj p f T).control.phase)
    (hg : ∀ i < 2 * epochLength p, ‖gradient f (traj p f (T + i)).point‖ ≤ 8 * threshold p)
    (h0 : ‖gradient f (traj p f T).point‖ ≤ threshold p)
    (hmid : p.ε < ‖gradient f (traj p f (T + epochLength p)).point‖)
 :
    (traj p f (T + 2 * epochLength p)).control = ⟨2 * epochLength p, false, 0⟩ ∧
      f (traj p f (T + 2 * epochLength p)).point - f (traj p f T).point ≤
        -(p.ε ^ 2) / (512 * lowerCurvature p) := by
  obtain ⟨hE, hsmall, hhigh⟩ := completed_small_conditions p hL hρ hε hk
  obtain ⟨hnoise, herror⟩ := completed_error_conditions p hL hρ hε hk
  exact completed_trial_execution p hL hρ hε hk f hf hH hlip T hr hc hg h0 hmid
    hsmall hhigh hE hnoise herror

end LongTails.Proofs.RecoveryFractalCompleted
