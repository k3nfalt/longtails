import LongTails.Proofs.BirchResourceHardwareLower
import LongTails.Proofs.BirchResourceHardInstance

namespace LongTails.Proofs.BirchResourceMatchingLower

open Finset Set MeasureTheory
open OracleTemplate.Rennala (Point)
open LongTails.Setups
open LongTails.Proofs.BirchResourceHardRun
open LongTails.Proofs.BirchResourceHardLower
open LongTails.Proofs.BirchResourceHardwareLower
open LongTails.Proofs.BirchResourceHardInstance
open LongTails.Proofs.BirchResourceLowerWindow
open LongTails.Proofs.BirchResourceChain (Supported)
open LongTails.Setups.UscgConstant (dualNorm)

structure OutputTrace {Packet : Type*} (p : BirchNonEuclidean.Params)
    (run : Scheduler Packet) (N : ℕ) (hε : 0 < p.ε) where
  point : (ℕ → Bool) → Point p.d
  elapsed : (ℕ → Bool) → ℝ
  elapsedMeasurable : Measurable elapsed
  elapsedIntegrable : Integrable elapsed (streamLaw p hε : Measure (ℕ → Bool))
  elapsedNonneg : ∀ ξ, 0 ≤ elapsed ξ
  finish : ∀ ξ i s, i < N → observed run ξ i = some s → s.finish ≤ elapsed ξ
  support : ∀ ξ, Supported (point ξ) (level run ξ N)
  errorIntegrable : Integrable (fun ξ => dualNorm p.N (gradient (objectiveInstance p).f (point ξ)) ^ 2)
    (streamLaw p hε : Measure (ℕ → Bool))
  accuracy : (∫ ξ, dualNorm p.N (gradient (objectiveInstance p).f (point ξ)) ^ 2
    ∂(streamLaw p hε : Measure (ℕ → Bool))) ≤ p.ε

lemma routed_lower {Route Device : Type*} [Fintype Route] [DecidableEq Route] [DecidableEq Device]
    (p : BirchNonEuclidean.Params) (hn : Distortion p.N) (hL : 0 < p.L) (hε : 0 < p.ε)
    (hD : 0 < p.d) (hardware : BirchRoutedTime.Profile Route Device) (J : ℕ)
    (hp : hardware.Valid J) {run : Scheduler ℕ} {N : ℕ} (hc : Causal run N)
    (exec : RoutedExecution hardware run N) (out : OutputTrace p run N hε) :
    let Φ := sInf (routedPrices hardware (1 / chance p))
    (p.d : ℝ) * Φ / 72 ≤ ∫ ξ, out.elapsed ξ ∂(streamLaw p hε : Measure (ℕ → Bool)) := by
  let Φ := sInf (routedPrices hardware (1 / chance p))
  let ℓ := Φ / 9
  by_cases hℓ : 0 < ℓ
  · have hq := chance_pos p hε
    have h := clock_lower hc hD (sampleLaw p hε) (streamLaw p hε) (stream_iid p hε)
      (by rwa [chance_real]) (fun _ => 0) hℓ (by norm_num : (0 : ℝ) < 1) hε out.elapsed
      (fun ξ => dualNorm p.N (gradient (objectiveInstance p).f (out.point ξ)) ^ 2)
      out.elapsedMeasurable out.elapsedIntegrable out.errorIntegrable out.elapsedNonneg
      (fun _ => sq_nonneg _) (fun ξ i hi s hs => out.finish ξ i s hi hs) ?_
      (fun ξ h => missing_coordinate p hn hL hε _ _ h (out.support ξ))
      out.accuracy ?_
    · change (p.d : ℝ) * Φ / 72 ≤ _
      dsimp only [ℓ] at h
      linarith only [h]
    · intro ξ _
      have hz (m : ℕ) : cost run N m (fun _ => 0) ξ = 0 := by
        unfold cost
        cases reachSlot run ξ N (m + 1) <;> simp
      simp [hz]
      positivity
    · intro m _ ξ
      rw [chance_real]
      simpa only [Nat.cast_zero] using routed_count hardware J hp hc exec (chance p) hq ℓ hℓ rfl m ξ
  · have h := integral_nonneg (show 0 ≤ out.elapsed from out.elapsedNonneg) (μ := (streamLaw p hε : Measure (ℕ → Bool)))
    change (p.d : ℝ) * Φ / 72 ≤ _
    apply le_trans _ h
    apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by dsimp only [ℓ] at hℓ; linarith)

lemma power_lower_of_transition_budget {Mode Device Packet : Type*} [Fintype Mode]
    (p : BirchNonEuclidean.Params) (hn : Distortion p.N) (hL : 0 < p.L) (hε : 0 < p.ε)
    (hD : 0 < p.d) (hardware : BirchPowerTime.Profile Mode Device) (hp : hardware.Valid)
    {run : Scheduler Packet} {N : ℕ} (hc : Causal run N)
    (exec : PowerExecution hardware run N) (out : OutputTrace p run N hε)
    (U : ℝ) (hU : 0 < U)
    (hwork : ∀ ξ, p.d ≤ level run ξ N →
      ∑ i : Fin p.d, cost run N i (fun j => hardware.samples (exec.mode j)) ξ ≤ p.d * U / 4) :
    let Φ := sInf (powerPrices hardware ⌊U⌋₊ (1 / chance p))
    (p.d : ℝ) * Φ / 72 ≤ ∫ ξ, out.elapsed ξ ∂(streamLaw p hε : Measure (ℕ → Bool)) := by
  let Φ := sInf (powerPrices hardware ⌊U⌋₊ (1 / chance p))
  let ℓ := Φ / 9
  by_cases hℓ : 0 < ℓ
  · have hq := chance_pos p hε
    let size := fun j => hardware.samples (exec.mode j)
    have h := clock_lower hc hD (sampleLaw p hε) (streamLaw p hε) (stream_iid p hε)
      (by rwa [chance_real]) size hℓ hU hε out.elapsed
      (fun ξ => dualNorm p.N (gradient (objectiveInstance p).f (out.point ξ)) ^ 2)
      out.elapsedMeasurable out.elapsedIntegrable out.errorIntegrable out.elapsedNonneg
      (fun _ => sq_nonneg _) (fun ξ i hi s hs => out.finish ξ i s hi hs) ?_
      (fun ξ h => missing_coordinate p hn hL hε _ _ h (out.support ξ))
      out.accuracy ?_
    · change (p.d : ℝ) * Φ / 72 ≤ _
      dsimp only [ℓ] at h
      linarith only [h]
    · exact hwork
    · intro m _ ξ
      rw [chance_real]
      exact power_count hardware hp hc exec (chance p) hq ℓ U hℓ hU.le rfl m ξ
  · have h := integral_nonneg (show 0 ≤ out.elapsed from out.elapsedNonneg) (μ := (streamLaw p hε : Measure (ℕ → Bool)))
    change (p.d : ℝ) * Φ / 72 ≤ _
    apply le_trans _ h
    apply div_nonpos_of_nonpos_of_nonneg _ (by norm_num)
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by dsimp only [ℓ] at hℓ; linarith)

lemma power_lower {Mode Device Packet : Type*} [Fintype Mode] [DecidableEq Packet]
    (p : BirchNonEuclidean.Params) (hn : Distortion p.N) (hL : 0 < p.L) (hε : 0 < p.ε)
    (hD : 0 < p.d) (hardware : BirchPowerTime.Profile Mode Device) (hp : hardware.Valid)
    {run : Scheduler Packet} {N : ℕ} (hc : Causal run N)
    (exec : PowerExecution hardware run N) (out : OutputTrace p run N hε)
    (W : ℕ) (hW : 0 < W) (hcap : ∀ ξ, ∑ j ∈ exec.charged ξ, hardware.samples (exec.mode j) ≤ W) :
    let U := 4 * (W : ℝ) / p.d
    let Φ := sInf (powerPrices hardware ⌊U⌋₊ (1 / chance p))
    (p.d : ℝ) * Φ / 72 ≤ ∫ ξ, out.elapsed ξ ∂(streamLaw p hε : Measure (ℕ → Bool)) := by
  let U := 4 * (W : ℝ) / p.d
  have hU : 0 < U := by dsimp only [U]; positivity
  refine power_lower_of_transition_budget p hn hL hε hD hardware hp hc exec out U hU ?_
  intro ξ hr
  have hsum := sum_cost_le hc (fun j => hardware.samples (exec.mode j)) (exec.charged ξ) ξ hr
    (fun i hi s hs => (exec.observedPacket ξ i s hi hs).1)
  refine hsum.trans ?_
  have he : (p.d : ℝ) * U / 4 = W := by
    have hne : (p.d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
    dsimp [U]
    field_simp
  rw [he]
  exact_mod_cast hcap ξ

lemma power_unrestricted_lower {Mode Device Packet : Type*} [Fintype Mode]
    (p : BirchNonEuclidean.Params) (hn : Distortion p.N) (hL : 0 < p.L) (hε : 0 < p.ε)
    (hD : 0 < p.d) (hardware : BirchPowerTime.Profile Mode Device) (hp : hardware.Valid)
    {run : Scheduler Packet} {N : ℕ} (hc : Causal run N)
    (exec : PowerExecution hardware run N) (out : OutputTrace p run N hε)
    (M : ℕ) (hM : 0 < M) (hmax : ∀ mode, hardware.samples mode ≤ M) :
    let Φ := sInf (powerPrices hardware (4 * M) (1 / chance p))
    (p.d : ℝ) * Φ / 72 ≤ ∫ ξ, out.elapsed ξ ∂(streamLaw p hε : Measure (ℕ → Bool)) := by
  classical
  let U := (4 : ℝ) * M
  have hU : 0 < U := by dsimp only [U]; positivity
  have hfloor : ⌊U⌋₊ = 4 * M := by
    change ⌊(4 : ℝ) * M⌋₊ = _
    rw [← Nat.cast_ofNat (R := ℝ) (n := 4), ← Nat.cast_mul, Nat.floor_natCast]
  have hwork (ξ : ℕ → Bool) (_ : p.d ≤ level run ξ N) :
      ∑ i : Fin p.d, cost run N i (fun j => hardware.samples (exec.mode j)) ξ ≤ p.d * U / 4 := by
    have hle (i : Fin p.d) : cost run N i (fun j => hardware.samples (exec.mode j)) ξ ≤ M := by
      unfold cost
      cases reachSlot run ξ N (i.val + 1) with
      | none => simp
      | some s => exact Nat.cast_le.mpr (hmax _)
    refine (sum_le_sum (fun i (_ : i ∈ Finset.univ) => hle i)).trans ?_
    simp [U, nsmul_eq_mul]
    linarith
  have h := power_lower_of_transition_budget p hn hL hε hD hardware hp hc exec out U hU hwork
  simpa only [hfloor] using h

end LongTails.Proofs.BirchResourceMatchingLower
