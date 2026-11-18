import LongTails.Algorithms.DashaDistributedTrackedParameters
import LongTails.Proofs.DashaDistributedCapacity
import LongTails.Proofs.DashaTrackingEnvelope
import LongTails.Proofs.DashaDistributedModularTransport

namespace LongTails.Proofs.DashaDistributedTrackingCapacity

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaDistributedTrackedParameters
open LongTails.Proofs.DashaDistributedExecution
open LongTails.Proofs.DashaDistributedCapacity

variable {p : Params}

lemma initial_global_bound (hL : 0 < p.L) (hH : 0 < p.Lhat) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (lower : ℝ) (hlower : ∀ x, lower ≤ objective p f x)
    (hgap : objective p f p.x0 - lower ≤ p.Δ) :
    ‖gradient (objective p f) p.x0‖ ≤ globalInitialBound p := by
  apply le_min (DashaScalingDescent.initial_gradient_norm f hg hG)
  have hb := DashaScalingDescent.initial_gradient_gap f hg hL hH hlip hs lower hlower hgap
  exact (Real.le_sqrt (norm_nonneg _) ((sq_nonneg _).trans hb)).mpr hb

lemma trackingRadius_nonneg (cfg : Config p) (hε : 0 < p.ε) (hG : 0 ≤ p.G) :
    0 ≤ trackingInitialEnvelope p cfg.choice cfg.initializer := by
  have hρ := DashaScalingParameters.spacing_pos cfg.choice hε
  cases hi : cfg.initializer <;>
    simp only [trackingInitialEnvelope, globalInitialBound, LongTails.Algorithms.DashaCyclic.multiplier] <;>
    positivity

lemma ideal_envelope (cfg : Config p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (hJ : ‖gradient (objective p f) p.x0‖ ≤ globalInitialBound p)
    (seed : ℕ → Sample p) (k : ℕ) :
    DashaTrackingEnvelope.envelope cfg.choice f (idealTrajectory p cfg f seed k) ≤
      trackingInitialEnvelope p cfg.choice cfg.initializer * DashaScalingEnvelope.growth cfg.choice ^ k := by
  cases hi : cfg.initializer with
  | none =>
      rw [idealTrajectory_none cfg f seed hi k]
      simpa only [trackingInitialEnvelope, hi, add_zero] using
        DashaTrackingEnvelope.trajectory_bound cfg.choice hε hL hH f hg hs (globalInitialBound p) hJ seed k
  | some initializer =>
      rw [idealTrajectory_some cfg f seed initializer hi k]
      simpa only [trackingInitialEnvelope, hi] using
        DashaTrackingEnvelope.sparse_trajectory_bound cfg.choice initializer hε hL hH f hg hs hG
          (globalInitialBound p) hJ seed k

lemma aggregate_bound (cfg : Config p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (hJ : ‖gradient (objective p f) p.x0‖ ≤ globalInitialBound p)
    (seed : ℕ → Sample p) (k K : ℕ) (hk : k ≤ K) (j : Fin p.d) :
    |((∑ i, (idealTrajectory p cfg f seed k).localCode i j : ℤ) : ℝ)| ≤
      (p.n : ℝ) * trackingInitialEnvelope p cfg.choice cfg.initializer *
        DashaScalingEnvelope.growth cfg.choice ^ K / spacing p cfg.choice := by
  have hr := trackingRadius_nonneg cfg hε hG0
  have he := (DashaTrackingEnvelope.estimate_le_envelope cfg.choice hε f hg
    (idealTrajectory p cfg f seed k)).trans (ideal_envelope cfg hε hL hH f hg hs hG hJ seed k)
  have hm := mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (growth_ge_one cfg.choice hL hH) hk) hr
  have hb := DashaTrackingEnvelope.aggregate_code_bound cfg.choice hε
    (idealTrajectory p cfg f seed k) _ (he.trans hm) j
  convert hb using 1
  ring

lemma stepInput_bound (cfg : Config p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (hJ : ‖gradient (objective p f) p.x0‖ ≤ globalInitialBound p)
    (seed : ℕ → Sample p) (k : ℕ) (i : Fin p.n) (j : Fin p.d) :
    |LongTails.Algorithms.DashaCyclic.multiplier cfg.choice.block * stepInput cfg f seed k i j / spacing p cfg.choice| ≤
      trackingInputBound p cfg.choice cfg.initializer * DashaScalingEnvelope.growth cfg.choice ^ k := by
  have hρ := DashaScalingParameters.spacing_pos cfg.choice hε
  have hη := DashaScalingParameters.stepSize_pos cfg.choice hL hH
  have hq : 0 ≤ LongTails.Algorithms.DashaCyclic.multiplier cfg.choice.block := by
    unfold LongTails.Algorithms.DashaCyclic.multiplier
    positivity
  have hfactor : 0 ≤ 1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p cfg.choice := by positivity
  have hin : ‖stepInput cfg f seed k i‖ ≤
      (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p cfg.choice) * DashaTrackingEnvelope.envelope cfg.choice f (idealTrajectory p cfg f seed k) :=
    DashaTrackingEnvelope.innovation_bound cfg.choice hε hL hH f hg hs _ (ideal_gradient cfg f seed k) i
  have he := ideal_envelope cfg hε hL hH f hg hs hG hJ seed k
  calc
    _ ≤ LongTails.Algorithms.DashaCyclic.multiplier cfg.choice.block * ‖stepInput cfg f seed k i‖ / spacing p cfg.choice :=
      scaled_coordinate_bound _ _ hq hρ _ j
    _ ≤ LongTails.Algorithms.DashaCyclic.multiplier cfg.choice.block *
        ((1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p cfg.choice) *
          (trackingInitialEnvelope p cfg.choice cfg.initializer * DashaScalingEnvelope.growth cfg.choice ^ k)) / spacing p cfg.choice :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hin.trans (mul_le_mul_of_nonneg_left he hfactor)) hq) hρ.le
    _ = _ := by unfold trackingInputBound; ring

lemma inputRadius_nonneg (cfg : Config p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) : 0 ≤ trackingInputBound p cfg.choice cfg.initializer := by
  have hρ := DashaScalingParameters.spacing_pos cfg.choice hε
  have hη := DashaScalingParameters.stepSize_pos cfg.choice hL hH
  have hR := trackingRadius_nonneg cfg hε hG0
  unfold trackingInputBound LongTails.Algorithms.DashaCyclic.multiplier
  positivity

lemma step_exponent_bound (cfg : Config p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (hJ : ‖gradient (objective p f) p.x0‖ ≤ globalInitialBound p)
    (seed : ℕ → Sample p) (k K : ℕ) (hk : k ≤ K) (i : Fin p.n) (j : Fin p.d) :
    LongTails.Algorithms.DashaFloat.exponent cfg.choice.precision
      (LongTails.Algorithms.DashaCyclic.multiplier cfg.choice.block * stepInput cfg f seed k i j / spacing p cfg.choice) <
      2 ^ (Nat.size (Nat.size ⌈trackingInputBound p cfg.choice cfg.initializer⌉₊ + K * Nat.size ⌈DashaScalingEnvelope.growth cfg.choice⌉₊)) :=
  DashaFloat.exponent_real_geometric_bound _ k K _ _ _ (inputRadius_nonneg cfg hε hL hH hG0)
    (growth_ge_one cfg.choice hL hH) hk (stepInput_bound cfg hε hL hH f hg hs hG hJ seed k i j)

lemma initial_modular_capacity (cfg : Config p) (hε : 0 < p.ε) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hJ : ‖gradient (objective p f) p.x0‖ ≤ globalInitialBound p)
    (hi : cfg.initializer = none)
    (hw : cfg.initialWidth = Nat.size ⌈modularInitialBound p cfg.choice⌉₊ + 1)
    (seed : ℕ → Sample p) (j : Fin p.d) :
    -(LongTails.Algorithms.DashaQuantization.center cfg.initialWidth : ℤ) ≤
        ∑ i, (idealTrajectory p cfg f seed 0).localCode i j ∧
      (∑ i, (idealTrajectory p cfg f seed 0).localCode i j) +
        LongTails.Algorithms.DashaQuantization.center cfg.initialWidth <
        LongTails.Algorithms.DashaModular.modulus cfg.initialWidth := by
  have hb := DashaTrackingEnvelope.initial_aggregate_code_bound cfg.choice hε f hg
    (globalInitialBound p) hJ (seed 0) j
  have he : idealTrajectory p cfg f seed 0 = initialIterate p cfg.choice f (seed 0) := by
    simp only [idealTrajectory, idealInitial, hi]
  rw [he, hw]
  exact integer_capacity _ _ hb

lemma transportExact (cfg : Config p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (hJ : ‖gradient (objective p f) p.x0‖ ≤ globalInitialBound p)
    (hmain : cfg.exponentWidth = Nat.size (Nat.size ⌈trackingInputBound p cfg.choice cfg.initializer⌉₊ +
      cfg.iterations * Nat.size ⌈DashaScalingEnvelope.growth cfg.choice⌉₊))
    (hinit : cfg.initialWidth = if cfg.modularInitialization && cfg.initializer.isNone then
      Nat.size ⌈modularInitialBound p cfg.choice⌉₊ + 1 else match cfg.initializer with
        | none => Nat.size ⌈p.G / spacing p cfg.choice + 1⌉₊ + 1
        | some initializer => Nat.size (Nat.size ⌈LongTails.Algorithms.DashaCyclic.multiplier initializer.block *
            p.G / spacing p cfg.choice⌉₊))
    (hroot : cfg.broadcastWidth = Nat.size ⌈(p.n : ℝ) * trackingInitialEnvelope p cfg.choice cfg.initializer *
      DashaScalingEnvelope.growth cfg.choice ^ (cfg.iterations : ℕ) / spacing p cfg.choice⌉₊ + 1)
    (seed : ℕ → Sample p) : TransportExact cfg f seed := by
  have hcap (hm : modularAt p cfg 0 = true) (j : Fin p.d) := by
    obtain ⟨hi, _⟩ := DashaDistributedModularTransport.modular_initial cfg 0 hm
    have hflag : cfg.modularInitialization = true := by simpa only [modularAt, hi, Option.isNone_none,
      Bool.and_true, decide_true] using hm
    have hw : cfg.initialWidth = Nat.size ⌈modularInitialBound p cfg.choice⌉₊ + 1 := by
      simpa only [hi, hflag, Option.isNone_none, Bool.true_and, ite_true] using hinit
    exact initial_modular_capacity cfg hε f hg hJ hi hw seed j
  apply DashaDistributedModularTransport.transportExact_of_packets cfg f seed
  · intro k hk i suffix
    cases k with
    | zero =>
        cases hi : cfg.initializer with
        | none =>
            cases hm : cfg.modularInitialization with
            | false =>
                have hw : cfg.initialWidth = Nat.size ⌈p.G / spacing p cfg.choice + 1⌉₊ + 1 := by
                  simpa only [hi, hm, Bool.false_and, Bool.false_eq_true, ite_false] using hinit
                have hd := decode_integer_frame p.d (p.G / spacing p cfg.choice + 1)
                  (LongTails.Algorithms.DashaQuantization.indices p.d false (spacing p cfg.choice)
                    (gradient (f i) p.x0) (seed 0 i).2) suffix
                  (initial_index_bound cfg hε f hG (seed 0) i)
                simpa [uplinkReceive, workerMessage, uplinkMessage, hi, hm, hw, wireIncrement, modularAt,
                  increment, previousCode, idealTrajectory, idealInitial, initialIterate,
                  LongTails.Algorithms.DashaQuantization.message] using hd
            | true =>
                have hd := DashaModular.decode_encode p.d cfg.initialWidth
                  (LongTails.Algorithms.DashaQuantization.indices p.d false (spacing p cfg.choice)
                    (gradient (f i) p.x0) (seed 0 i).2) suffix
                simpa [uplinkReceive, workerMessage, uplinkMessage, hi, hm, wireIncrement, modularAt,
                  increment, previousCode, idealTrajectory, idealInitial, initialIterate] using hd
        | some initializer =>
            have hw : cfg.initialWidth = Nat.size (Nat.size ⌈LongTails.Algorithms.DashaCyclic.multiplier initializer.block *
                p.G / spacing p cfg.choice⌉₊) := by simpa only [hi, Option.isNone_some, Bool.and_false,
                  Bool.false_eq_true, ite_false] using hinit
            have hd := DashaPackets.receive_message initializer.block initializer.precision cfg.initialWidth
              (spacing p cfg.choice) (gradient (f i) p.x0) (seed 0 i) suffix
              (fun j => by rw [hw]; exact initial_exponent_bound cfg initializer hε hG0 f hG i j)
            simpa [uplinkReceive, workerMessage, uplinkMessage, hi, wireIncrement, modularAt, increment, previousCode,
              idealTrajectory, idealInitial, sparseInitialIterate] using hd
    | succ k =>
        have hd := DashaPackets.receive_message cfg.choice.block cfg.choice.precision cfg.exponentWidth
          (spacing p cfg.choice) (stepInput cfg f seed k i) (seed (k + 1) i) suffix
          (fun j => by rw [hmain]; exact step_exponent_bound cfg hε hL hH hG0 f hg hs hG hJ seed k cfg.iterations (by omega) i j)
        have hinc : increment cfg f seed (k + 1) i =
            LongTails.Algorithms.DashaCyclic.compressedIndex cfg.choice.block (seed (k + 1) i).1 cfg.choice.precision
              (spacing p cfg.choice) (stepInput cfg f seed k i) (seed (k + 1) i).2 := by
          funext j
          simp [increment, previousCode, idealTrajectory, nextIterate, stepInput]
        simp only [wireIncrement, modularAt, Nat.succ_ne_zero, decide_false, Bool.and_false,
          Bool.false_eq_true, ite_false]
        rw [hinc]
        simpa only [uplinkReceive, Nat.succ_ne_zero, ite_false, workerMessage, uplinkMessage,
          previousCode, previousGradient, stepInput] using hd
  · intro k hk suffix
    unfold broadcastMessage
    rw [hroot]
    exact decode_integer_frame _ _ _ suffix
      (aggregate_bound cfg hε hL hH hG0 f hg hs hG hJ seed k cfg.iterations hk.le)
  · intro hm j
    exact (hcap hm j).1
  · intro hm j
    exact (hcap hm j).2

end LongTails.Proofs.DashaDistributedTrackingCapacity
