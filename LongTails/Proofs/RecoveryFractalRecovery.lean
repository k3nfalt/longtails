import LongTails.Proofs.RecoveryFractalTuning
import LongTails.Proofs.RecoveryFractalLocal
import LongTails.Proofs.GdNegativeSpectrum
import LongTails.Proofs.GdConvex

namespace LongTails.Proofs.RecoveryFractalRecovery

open OracleTemplate OracleTemplate.ScheduleBlock
open LongTails.Setups.SmoothHessianLipschitzGd
open LongTails.Algorithms.RecoveryFractalGd
open LongTails.Proofs.RecoveryFractalExecution
open LongTails.Proofs.AdaptiveSilverSplit
open LongTails.Proofs.GdSnapshotDynamics
open LongTails.Proofs.GdNegativeSpectrum
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma projection_norm_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (v : E) :
    ‖v‖ ^ 2 = ‖P b eig v‖ ^ 2 + ‖v - P b eig v‖ ^ 2 := by
  rw [norm_sq_coords b, norm_sq_coords b, norm_sq_coords b, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [inner_sub_right, P_coord']
  by_cases hj : 0 ≤ eig j <;> simp [cpos, hj]

lemma abort_negative_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (actual model : E) (G B : ℝ)
    (hG : 0 ≤ G) (habort : 8 * G < ‖actual‖) (herr : ‖actual - model‖ ≤ B)
    (hB : B ≤ G / 2) (hpos : ‖P b eig model‖ ≤ 2 * G) :
    49 * G ^ 2 < ‖model - P b eig model‖ ^ 2 := by
  have ht := norm_le_norm_sub_add actual model
  have hm : 15 * G / 2 < ‖model‖ := by linarith
  have hm2 := sq_lt_sq₀ (by positivity : 0 ≤ 15 * G / 2) (norm_nonneg model)
  have hs := projection_norm_split b eig model
  have hp := pow_le_pow_left₀ (norm_nonneg _) hpos 2
  have hsq := hm2.mpr hm
  nlinarith

lemma model_negative_persistence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (H : E →L[ℝ] E)
    (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (L : ℝ) (hL : 0 ≤ L) (heig : ∀ j, -L ≤ eig j)
    (F : E → E) (z : E) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (X : ℕ → E) (n : ℕ)
    (hstep : ∀ i < n, X (i + 1) = X i - a i • F (X i))
    (B : ℝ) (herr : ∀ i < n, ‖F (X i) - F z - H (X i - z)‖ ≤ B) :
    ‖(F z + H (X 0 - z)) - P b eig (F z + H (X 0 - z))‖ ^ 2 / 2 -
        B ^ 2 * Real.log (1 + L * ssum a n) ≤
      ‖(F z + H (X n - z)) - P b eig (F z + H (X n - z))‖ ^ 2 := by
  let model := fun i => F z + H (X i - z)
  let residual := fun i => F (X i) - F z - H (X i - z)
  let lam := fun j => max (-eig j) 0
  let U := fun i j => ⟪b j, model i - P b eig (model i)⟫
  let V := fun i j => -⟪b j, residual i - P b eig (residual i)⟫
  have hm (i : ℕ) (hi : i < n) :
      model (i + 1) = model i - a i • H (model i + residual i) := by
    dsimp [model, residual]
    rw [hstep i hi]
    exact model_gradient_step F H z (X i) (a i)
  have hu (i : ℕ) (hi : i < n) (j : ι) :
      U (i + 1) j = (1 + a i * lam j) * U i j - a i * lam j * V i j := by
    dsimp [U, V, lam]
    simp only [inner_sub_right, P_coord', hm i hi, inner_smul_right, hc, inner_add_right]
    by_cases hj : 0 ≤ eig j
    · simp [cpos, hj]
    · have hn : 0 ≤ -eig j := by linarith [lt_of_not_ge hj]
      simp only [cpos, hj, ite_false, zero_mul, sub_zero, max_eq_left hn]
      ring
  have hv (i : ℕ) (hi : i < n) : ∑ j, V i j ^ 2 ≤ B ^ 2 := by
    dsimp [V]
    simp only [neg_sq]
    rw [← norm_sq_coords b]
    exact pow_le_pow_left₀ (norm_nonneg _) ((Q_norm_le b eig _).trans (herr i hi)) 2
  have hl (j : ι) : lam j ≤ L := max_le (by linarith [heig j]) hL
  have hh := backward_transport_square_persistence L hL lam (fun j => le_max_right _ _) hl
    a ha U V n hu B hv
  dsimp [U] at hh
  rw [← norm_sq_coords b, ← norm_sq_coords b] at hh
  exact hh

lemma negative_actual_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (actual model : E) (B : ℝ)
    (herr : ‖actual - model‖ ≤ B) :
    (4 / 5 : ℝ) * ‖model - P b eig model‖ ^ 2 - 4 * B ^ 2 ≤ ‖actual‖ ^ 2 := by
  have he : model - P b eig model = (actual - P b eig actual) -
      ((actual - model) - P b eig (actual - model)) := by
    rw [map_sub]
    abel
  have hq : ‖model - P b eig model‖ ≤ ‖actual‖ + B := by
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (Q_norm_le b eig actual)
      ((Q_norm_le b eig (actual - model)).trans herr))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hq 2
  nlinarith [sq_nonneg (‖actual‖ / 2 - 2 * B)]

lemma recovery_gradient_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (H : E →L[ℝ] E)
    (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (L : ℝ) (hL : 0 ≤ L) (heig : ∀ j, -L ≤ eig j)
    (F : E → E) (z : E) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (X : ℕ → E) (n : ℕ)
    (hstep : ∀ i < n, X (i + 1) = X i - a i • F (X i))
    (B G : ℝ) (herr : ∀ i ≤ n, ‖F (X i) - F z - H (X i - z)‖ ≤ B)
    (hB : B ≤ G / 2) (hnoise : B ^ 2 * Real.log (1 + L * ssum a n) ≤ G ^ 2)
    (hstart : 49 * G ^ 2 ≤
      ‖(F z + H (X 0 - z)) - P b eig (F z + H (X 0 - z))‖ ^ 2) :
    16 * G ^ 2 ≤ ‖F (X n)‖ ^ 2 := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (herr 0 (Nat.zero_le n))
  have hp := model_negative_persistence b eig H hc L hL heig F z a ha X n hstep B
    (fun i hi => herr i hi.le)
  have he : ‖F (X n) - (F z + H (X n - z))‖ ≤ B := by
    convert herr n le_rfl using 1
    congr 1
    abel
  have hn := negative_actual_square b eig (F (X n)) (F z + H (X n - z)) B he
  have hs := pow_le_pow_left₀ hB0 hB 2
  nlinarith [sq_nonneg G]

lemma plain_travel_square (F : E → E) (L : ℝ) (X : ℕ → E) (n : ℕ)
    (hstep : ∀ i < n, X (i + 1) = X i - (1 / L) • F (X i)) :
    ‖X n - X 0‖ ^ 2 ≤ (n : ℝ) / L ^ 2 * ∑ i ∈ Finset.range n, ‖F (X i)‖ ^ 2 := by
  have he : X n - X 0 = -((1 / L) • ∑ i ∈ Finset.range n, F (X i)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := ih (fun i hi => hstep i (by omega))
      rw [hstep n (by omega), Finset.sum_range_succ, smul_add]
      rw [show X n - (1 / L) • F (X n) - X 0 = (X n - X 0) - (1 / L) • F (X n) by abel, hh]
      module
  have hn := norm_sum_le (Finset.range n) (fun i => F (X i))
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := Finset.range n) (f := fun _ => (1 : ℝ)) (g := fun i => ‖F (X i)‖ ^ 2)
    (r := fun i => ‖F (X i)‖) (fun _ _ => zero_le_one) (fun _ _ => sq_nonneg _)
    (fun _ _ => by simp)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hc
  rw [he, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  calc
    _ ≤ (1 / L) ^ 2 * ((n : ℝ) * ∑ i ∈ Finset.range n, ‖F (X i)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hn2.trans hc) (sq_nonneg _)
    _ = _ := by ring

lemma plain_travel_of_energy (F : E → E) (L G : ℝ) (hL : 0 < L) (hG : 0 ≤ G)
    (X : ℕ → E) (n M : ℕ) (hn : n ≤ M)
    (hstep : ∀ i < n, X (i + 1) = X i - (1 / L) • F (X i))
    (henergy : (∑ i ∈ Finset.range n, ‖F (X i)‖ ^ 2) ≤ 16 * M * G ^ 2) :
    ‖X n - X 0‖ ≤ 4 * M * G / L := by
  have hn' : (n : ℝ) ≤ M := by exact_mod_cast hn
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 4 * M * G / L)).mp
  calc
    _ ≤ (n : ℝ) / L ^ 2 * ∑ i ∈ Finset.range n, ‖F (X i)‖ ^ 2 :=
      plain_travel_square F L X n hstep
    _ ≤ (n : ℝ) / L ^ 2 * (16 * M * G ^ 2) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ ≤ (M : ℝ) / L ^ 2 * (16 * M * G ^ 2) := by gcongr
    _ = _ := by ring

lemma plain_objective_descent [CompleteSpace E] (f : E → ℝ) (hf : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L) (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (X : ℕ → E) (n : ℕ)
    (hstep : ∀ i < n, X (i + 1) = X i - (1 / L) • gradient f (X i)) :
    f (X n) ≤ f (X 0) - (∑ i ∈ Finset.range n, ‖gradient f (X i)‖ ^ 2) / (2 * L) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := ih (fun i hi => hstep i (by omega))
    have hd := OracleTemplate.Gradient.descent hL (fun x => (hf x).hasGradientAt) hlip (X n)
    rw [hstep n (by omega), Finset.sum_range_succ, add_div]
    linarith

lemma recovery_decrease (p : Params) (hL : 0 < p.L) (f : p.E → ℝ)
    (hf : Differentiable ℝ f)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (X : ℕ → p.E) (n : ℕ) (z : p.E)
    (hstep : ∀ i < n, X (i + 1) = X i - (1 / p.L) • gradient f (X i))
    (hprefix : f (X 0) - f z ≤ prefixIncrease p)
    (henergy : recoveryTarget p ≤ ∑ i ∈ Finset.range n, ‖gradient f (X i)‖ ^ 2) :
    f (X n) - f z ≤ -prefixIncrease p - 8 * epochLength p * threshold p ^ 2 / p.L := by
  have hd := plain_objective_descent f hf p.L hL hlip X n hstep
  have ht := div_le_div_of_nonneg_right henergy (show 0 ≤ 2 * p.L by positivity)
  have he : recoveryTarget p / (2 * p.L) =
      2 * prefixIncrease p + 8 * epochLength p * threshold p ^ 2 / p.L := by
    unfold recoveryTarget
    field_simp
    ring
  rw [he] at ht
  linarith only [hd, ht, hprefix]

lemma recovery_crosses (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hk : 2 ≤ level p) (hG : 0 < threshold p)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (T : ℕ) (z : p.E) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ p.E) (eig : ι → ℝ)
    (hc : ∀ j v, ⟪b j, fderiv ℝ (gradient f) z v⟫ = eig j * ⟪b j, v⟫)
    (heig : ∀ j, -p.L ≤ eig j) (M : ℕ)
    (hstart : rule p (traj p f T).control (gradient f (traj p f T).point) =
      (1 / p.L, recoveryControl p (‖gradient f (traj p f T).point‖ ^ 2)))
    (hdist : ‖(traj p f T).point - z‖ ≤ radius p / 2)
    (hneg : 49 * threshold p ^ 2 ≤
      ‖(gradient f z + fderiv ℝ (gradient f) z ((traj p f T).point - z)) -
        P b eig (gradient f z + fderiv ℝ (gradient f) z ((traj p f T).point - z))‖ ^ 2)
    (hbudget : recoveryTarget p ≤ 16 * M * threshold p ^ 2)
    (hradius : 4 * M * threshold p / p.L ≤ radius p / 2)
    (herror : errorBound p ≤ threshold p / 2)
    (hnoise : errorBound p ^ 2 * Real.log (1 + (M : ℝ)) ≤ threshold p ^ 2) :
    ∃ n, 1 ≤ n ∧ n ≤ M ∧ recoveryTarget p ≤ recoveryEnergy p f T n ∧
      (∀ i < n, recoveryEnergy p f T i < recoveryTarget p) ∧
      (traj p f (T + n)).control = idle := by
  let X := fun i => (traj p f (T + i)).point
  have hmono : Monotone (recoveryEnergy p f T) := by
    intro i j hij
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij)
    intro k _ _
    exact sq_nonneg _
  have hmu := lowerCurvature_pos p hL
  have hR : 0 ≤ radius p := by unfold radius; positivity
  have hE : 0 ≤ errorBound p := by unfold errorBound; positivity
  have hU : 0 ≤ prefixIncrease p := by unfold prefixIncrease; positivity
  have hN : 0 < epochLength p := by
    unfold epochLength repetitions
    exact Nat.mul_pos (blockLength_pos p) (by omega)
  have htarget : 0 < recoveryTarget p := by unfold recoveryTarget; positivity
  have hgd : Differentiable ℝ (gradient f) :=
    (OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one hf).differentiable (by norm_num)
  have hcross : recoveryTarget p ≤ recoveryEnergy p f T M := by
    by_contra hn
    have hsm : recoveryEnergy p f T M < recoveryTarget p := lt_of_not_ge hn
    have ht := recovery_trace p hk f T M hstart (fun i _ hi => (hmono hi.le).trans_lt hsm)
    have hstep : ∀ i < M, X (i + 1) = X i - (1 / p.L) • gradient f (X i) := ht.2
    have hball (j : ℕ) (hj : j ≤ M) : ‖X j - z‖ ≤ radius p := by
      have he : (∑ i ∈ Finset.range j, ‖gradient f (X i)‖ ^ 2) ≤
          16 * M * threshold p ^ 2 := (hmono hj).trans (hsm.le.trans hbudget)
      have htravel := plain_travel_of_energy (gradient f) p.L (threshold p) hL hG.le X j M hj
        (fun i hi => hstep i (hi.trans_le hj)) he
      have heq : X j - z = (X j - X 0) + (X 0 - z) := by abel
      have hx0 : ‖X 0 - z‖ ≤ radius p / 2 := by simpa [X] using hdist
      rw [heq]
      exact (norm_add_le _ _).trans (by linarith)
    have herr (j : ℕ) (hj : j ≤ M) :
        ‖gradient f (X j) - gradient f z - fderiv ℝ (gradient f) z (X j - z)‖ ≤ errorBound p :=
      (OracleTemplate.NonlinearTemporalDiscrepancy.gradient_linearization_bound hρ hgd hH z (X j)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hball j hj) 2) hρ)
    have hgrad (j : ℕ) (hj : j < M) : 16 * threshold p ^ 2 ≤ ‖gradient f (X j)‖ ^ 2 := by
      have hs : p.L * ssum (fun _ => 1 / p.L) j = (j : ℝ) := by
        simp only [ssum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
      have hlog : errorBound p ^ 2 * Real.log (1 + p.L * ssum (fun _ => 1 / p.L) j) ≤ threshold p ^ 2 := by
        rw [hs]
        have hj' : (j : ℝ) ≤ M := by exact_mod_cast hj.le
        exact (mul_le_mul_of_nonneg_left
          (Real.log_le_log (by positivity) (by linarith : 1 + (j : ℝ) ≤ 1 + (M : ℝ)))
          (sq_nonneg (errorBound p))).trans hnoise
      apply recovery_gradient_bound b eig (fderiv ℝ (gradient f) z) hc p.L hL.le heig
        (gradient f) z (fun _ => 1 / p.L) (fun _ => (one_div_pos.mpr hL).le) X j
        (fun i hi => hstep i (hi.trans hj)) (errorBound p) (threshold p)
        (fun i hi => herr i (hi.trans hj.le)) herror hlog
      simpa [X] using hneg
    have hsum := Finset.sum_le_sum (fun j (hj : j ∈ Finset.range M) => hgrad j (Finset.mem_range.mp hj))
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    change (M : ℝ) * (16 * threshold p ^ 2) ≤ recoveryEnergy p f T M at hsum
    nlinarith only [hsm, hbudget, hsum]
  have hex : ∃ n, recoveryTarget p ≤ recoveryEnergy p f T n := ⟨M, hcross⟩
  let n := Nat.find hex
  have hn : recoveryTarget p ≤ recoveryEnergy p f T n := Nat.find_spec hex
  have hnM : n ≤ M := Nat.find_min' hex hcross
  have hn0 : 1 ≤ n := by
    by_contra h
    have he : n = 0 := by omega
    rw [he, recoveryEnergy_zero] at hn
    linarith
  have hmin : ∀ i < n, recoveryEnergy p f T i < recoveryTarget p :=
    fun i hi => lt_of_not_ge (Nat.find_min hex hi)
  have ht := recovery_trace p hk f T n hstart (fun i _ hi => hmin i hi)
  refine ⟨n, hn0, hnM, hn, hmin, ?_⟩
  rw [ht.1 n hn0 le_rfl]
  simp [recoveryControl, hn]

lemma aborted_trial_recovers (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hk : 2 ≤ level p) (hG : 0 < threshold p)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (T t M : ℕ) (ht0 : 1 ≤ t) (ht : t ≤ 2 * epochLength p)
    (hr : (traj p f T).control.recovering = false)
    (hc : (traj p f T).control.phase = 0 ∨ 2 * epochLength p ≤ (traj p f T).control.phase)
    (h0 : ‖gradient f (traj p f T).point‖ ≤ threshold p)
    (hg : ∀ i < t, ‖gradient f (traj p f (T + i)).point‖ ≤ 8 * threshold p)
    (habort : 8 * threshold p < ‖gradient f (traj p f (T + t)).point‖)
    (hsmall : (2 * epochLength p : ℝ) * (4 / lowerCurvature p) *
      (p.ρ * radius p * (8 * threshold p)) + errorBound p ≤ threshold p)
    (hbudget : recoveryTarget p ≤ 16 * M * threshold p ^ 2)
    (hradius : 4 * M * threshold p / p.L ≤ radius p / 2)
    (herror : errorBound p ≤ threshold p / 2)
    (hnoise : errorBound p ^ 2 * Real.log (1 + (M : ℝ)) ≤ threshold p ^ 2) :
    ∃ n, 1 ≤ n ∧ n ≤ M ∧ (traj p f (T + t + n)).control = idle ∧
      f (traj p f (T + t + n)).point - f (traj p f T).point ≤
        -prefixIncrease p - 8 * epochLength p * threshold p ^ 2 / p.L := by
  classical
  let X := fun i => (traj p f (T + i)).point
  have htrace := trial_trace p hk hG.le f T t ht hr hc h0 hg
  have hstep : ∀ i < t, X (i + 1) = X i - fractalStep p i • gradient f (X i) := htrace.2
  have hinit : ‖gradient f (X 0)‖ ≤ threshold p := by simpa [X] using h0
  have hsym := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hf (X 0)
  let b := hsym.eigenvectorBasis rfl
  let eig := hsym.eigenvalues rfl
  have hcoeff : ∀ j v, ⟪b j, fderiv ℝ (gradient f) (X 0) v⟫ = eig j * ⟪b j, v⟫ := by
    intro j v
    simpa only [OrthonormalBasis.repr_apply_apply, RCLike.ofReal_real_eq_id, id_eq,
      ContinuousLinearMap.coe_coe] using hsym.eigenvectorBasis_apply_self_apply rfl v j
  have heig : ∀ j, -p.L ≤ eig j ∧ eig j ≤ p.L := fun j => eig_bounds hL.le hlip (X 0) hsym j
  have hmodel := LongTails.Proofs.RecoveryFractalLocal.trial_positive_model p hL hρ hk hG.le
    f hf hH b eig X hcoeff (fun j => (heig j).2) t ht hstep hg hinit hsmall
  have herr := LongTails.Proofs.RecoveryFractalLocal.trial_residual_bound p hL hρ hk hG.le
    f hf hH X t ht hstep hg
  have he : ‖gradient f (X t) -
      (gradient f (X 0) + fderiv ℝ (gradient f) (X 0) (X t - X 0))‖ ≤ errorBound p := by
    convert herr using 1
    congr 1
    abel
  have hn := abort_negative_square b eig (gradient f (X t))
    (gradient f (X 0) + fderiv ℝ (gradient f) (X 0) (X t - X 0))
    (threshold p) (errorBound p) hG.le habort he herror hmodel
  have hdist := LongTails.Proofs.RecoveryFractalLocal.trial_radius p hL hk hG.le f X t ht hstep hg
  have hstart : rule p (traj p f (T + t)).control (gradient f (traj p f (T + t)).point) =
      (1 / p.L, recoveryControl p (‖gradient f (traj p f (T + t)).point‖ ^ 2)) := by
    rw [htrace.1 t ht0 le_rfl]
    exact rule_abort p hk _ rfl (by change t ≠ 0; omega) _ habort
  obtain ⟨n, hn0, hnM, hnenergy, hnmin, hncontrol⟩ := recovery_crosses p hL hρ hk hG f hf hH
    (T + t) (X 0) b eig hcoeff (fun j => (heig j).1) M hstart hdist hn.le
    hbudget hradius herror hnoise
  have hrec := recovery_trace p hk f (T + t) n hstart (fun i _ hi => hnmin i hi)
  let Y := fun i => (traj p f (T + t + i)).point
  have hprefix : f (Y 0) - f (X 0) ≤ prefixIncrease p := by
    simpa only [Y, X, Nat.add_zero] using
      LongTails.Proofs.RecoveryFractalLocal.trial_prefix_increase p hL hρ hk hG.le
        f hf hH hlip X t ht hstep hg hinit hsmall
  have hdec := recovery_decrease p hL f (hf.differentiable (by norm_num)) hlip Y n (X 0)
    hrec.2 hprefix hnenergy
  refine ⟨n, hn0, hnM, hncontrol, ?_⟩
  simpa only [Y, X, Nat.add_zero] using hdec

open LongTails.Proofs.RecoveryFractalTuning

lemma aborted_trial_recovers_tuned (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hk : 2 ≤ level p) (hε : 0 < p.ε)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (T t : ℕ) (ht0 : 1 ≤ t) (ht : t ≤ 2 * epochLength p)
    (hr : (traj p f T).control.recovering = false)
    (hc : (traj p f T).control.phase = 0 ∨ 2 * epochLength p ≤ (traj p f T).control.phase)
    (h0 : ‖gradient f (traj p f T).point‖ ≤ threshold p)
    (hg : ∀ i < t, ‖gradient f (traj p f (T + i)).point‖ ≤ 8 * threshold p)
    (habort : 8 * threshold p < ‖gradient f (traj p f (T + t)).point‖)
 :
    ∃ n, 1 ≤ n ∧ n ≤ recoveryLength p ∧ (traj p f (T + t + n)).control = idle ∧
      f (traj p f (T + t + n)).point - f (traj p f T).point ≤
        -((t + n : ℕ) : ℝ) * threshold p ^ 2 / p.L := by
  have hn : 0 < (blockLength p : ℝ) := by exact_mod_cast blockLength_pos p
  have hG : 0 < threshold p := by unfold threshold; positivity
  have hsmall := (completed_small_conditions p hL hρ hε.le hk).2.1
  obtain ⟨hbudget, hradius, herror, hnoise⟩ := recovery_parameter_conditions p hL hρ hε.le hk
  obtain ⟨n, hn0, hnM, hcontrol, hdec⟩ := aborted_trial_recovers p hL hρ hk hG f hf hH hlip
    T t (recoveryLength p) ht0 ht hr hc h0 hg habort hsmall hbudget hradius herror hnoise
  refine ⟨n, hn0, hnM, hcontrol, ?_⟩
  have hcost := abort_group_cost p hL hρ hε.le t n ht hnM
  simp only [div_eq_mul_inv] at hdec hcost ⊢
  nlinarith only [hdec, hcost]

end LongTails.Proofs.RecoveryFractalRecovery
