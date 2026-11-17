import LongTails.Proofs.DashaDistributedTermination
import LongTails.Proofs.DashaScalingEnvelope

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DashaDistributedCapacity

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaDistributed
open LongTails.Algorithms.DashaScaling
open LongTails.Proofs.DashaDistributedExecution
open LongTails.Proofs.DashaScalingEnvelope

variable {p : Params}

lemma decode_frame (d width : ℕ) (bits suffix : List Bool) (hlen : bits.length = d * width) :
    LongTails.Algorithms.DashaQuantization.decode d width (bits ++ suffix) =
      LongTails.Algorithms.DashaQuantization.decode d width bits := by
  unfold LongTails.Algorithms.DashaQuantization.decode
  rw [← hlen, List.take_left, List.take_length]

lemma integer_capacity (B : ℝ) (z : ℤ) (hz : |(z : ℝ)| ≤ B) :
    -(LongTails.Algorithms.DashaQuantization.center (Nat.size ⌈B⌉₊ + 1) : ℤ) ≤ z ∧
      z + LongTails.Algorithms.DashaQuantization.center (Nat.size ⌈B⌉₊ + 1) < (2 ^ (Nat.size ⌈B⌉₊ + 1) : ℕ) := by
  have hbound : |(z : ℝ)| < (2 : ℝ) ^ Nat.size ⌈B⌉₊ :=
    lt_of_le_of_lt (hz.trans (Nat.le_ceil B)) (by exact_mod_cast Nat.lt_size_self ⌈B⌉₊)
  have hzb : |z| < (2 ^ Nat.size ⌈B⌉₊ : ℕ) := by exact_mod_cast hbound
  have hc : LongTails.Algorithms.DashaQuantization.center (Nat.size ⌈B⌉₊ + 1) = 2 ^ Nat.size ⌈B⌉₊ := by
    simp [LongTails.Algorithms.DashaQuantization.center, pow_succ]
  rw [hc]
  have hab := abs_lt.mp hzb
  simp only [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
  omega

lemma decode_integer_frame (d : ℕ) (B : ℝ) (z : Fin d → ℤ) (suffix : List Bool)
    (hz : ∀ j, |(z j : ℝ)| ≤ B) :
    LongTails.Algorithms.DashaQuantization.decode d (Nat.size ⌈B⌉₊ + 1)
      (LongTails.Algorithms.DashaQuantization.encode d (Nat.size ⌈B⌉₊ + 1) z ++ suffix) = z := by
  rw [decode_frame _ _ _ _ (DashaQuantization.encode_length _ _ _)]
  exact DashaQuantization.decode_encode _ _ _ (fun j => (integer_capacity B (z j) (hz j)).1)
    (fun j => (integer_capacity B (z j) (hz j)).2)

lemma idealTrajectory_none (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (hi : cfg.initializer = none) (k : ℕ) :
    idealTrajectory p cfg f seed k = trajectory p cfg.choice f seed k := by
  induction k with
  | zero => simp [idealTrajectory, idealInitial, hi, trajectory]
  | succ k ih => simp only [idealTrajectory, trajectory, ih]

lemma idealTrajectory_some (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (initializer : Choice p) (hi : cfg.initializer = some initializer) (k : ℕ) :
    idealTrajectory p cfg f seed k = sparseTrajectory p cfg.choice initializer f seed k := by
  induction k with
  | zero => simp [idealTrajectory, idealInitial, hi, sparseTrajectory]
  | succ k ih => simp only [idealTrajectory, sparseTrajectory, ih]

noncomputable def initialRadius (cfg : Config p) : ℝ :=
  match cfg.initializer with
  | none => 2 * (p.G + spacing p cfg.choice * Real.sqrt (p.d : ℝ))
  | some initializer => (2 * LongTails.Algorithms.DashaCyclic.multiplier initializer.block + 1) * p.G +
      2 * spacing p cfg.choice * Real.sqrt (p.d : ℝ)

lemma ideal_envelope (cfg : Config p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (seed : ℕ → Sample p) (k : ℕ) :
    envelope cfg.choice (idealTrajectory p cfg f seed k) ≤ initialRadius cfg * growth cfg.choice ^ k := by
  cases hi : cfg.initializer with
  | none =>
      rw [idealTrajectory_none cfg f seed hi k]
      simpa only [initialRadius, hi] using trajectory_envelope cfg.choice hε hL hH hG0 f hs hG seed k
  | some initializer =>
      rw [idealTrajectory_some cfg f seed initializer hi k]
      simpa only [initialRadius, hi] using sparse_trajectory_envelope cfg.choice initializer hε hL hH hG0 f hs hG seed k

lemma growth_ge_one (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat) : 1 ≤ growth c := by
  have hη := DashaScalingParameters.stepSize_pos c hL hH
  have hq : 0 ≤ LongTails.Algorithms.DashaCyclic.multiplier c.block := by
    unfold LongTails.Algorithms.DashaCyclic.multiplier
    positivity
  have ht : 0 ≤ Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p c := by positivity
  unfold growth
  nlinarith

lemma initialRadius_nonneg (cfg : Config p) (hε : 0 < p.ε) (hG : 0 ≤ p.G) : 0 ≤ initialRadius cfg := by
  have hρ := DashaScalingParameters.spacing_pos cfg.choice hε
  cases hi : cfg.initializer with
  | none => simp only [initialRadius, hi]; positivity
  | some initializer => simp only [initialRadius, hi, LongTails.Algorithms.DashaCyclic.multiplier]; positivity

lemma localCode_abs_bound (c : Choice p) (hε : 0 < p.ε) (s : Iterate p) (i : Fin p.n) (j : Fin p.d) :
    |((s.localCode i j : ℤ) : ℝ)| ≤ maxLocal c s / spacing p c := by
  have hρ := DashaScalingParameters.spacing_pos c hε
  have hc : |spacing p c * (s.localCode i j : ℝ)| ≤
      ‖LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i)‖ :=
    PiLp.norm_apply_le (LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i)) j
  rw [abs_mul, abs_of_pos hρ] at hc
  apply (le_div_iff₀ hρ).mpr
  nlinarith [local_le_max c s i]

lemma ideal_code_bound (cfg : Config p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (seed : ℕ → Sample p) (k : ℕ) (i : Fin p.n) (j : Fin p.d) :
    |((idealTrajectory p cfg f seed k).localCode i j : ℝ)| ≤
      initialRadius cfg * growth cfg.choice ^ k / spacing p cfg.choice := by
  have hρ := DashaScalingParameters.spacing_pos cfg.choice hε
  have he := ideal_envelope cfg hε hL hH hG0 f hs hG seed k
  have hm : maxLocal cfg.choice (idealTrajectory p cfg f seed k) ≤
      envelope cfg.choice (idealTrajectory p cfg f seed k) := by
    unfold envelope
    have ht : 0 ≤ Real.sqrt (p.n : ℝ) * p.Lhat * ‖(idealTrajectory p cfg f seed k).point - p.x0‖ := by positivity
    have hd : 0 ≤ spacing p cfg.choice * Real.sqrt (p.d : ℝ) := by positivity
    linarith
  exact (localCode_abs_bound cfg.choice hε _ i j).trans (div_le_div_of_nonneg_right (hm.trans he) hρ.le)

lemma scaled_coordinate_bound (q ρ : ℝ) (hq : 0 ≤ q) (hρ : 0 < ρ) (x : Point p) (j : Fin p.d) :
    |q * x j / ρ| ≤ q * ‖x‖ / ρ := by
  rw [abs_div, abs_mul, abs_of_nonneg hq, abs_of_pos hρ]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) hq) hρ.le

lemma initial_index_bound (cfg : Config p) (hε : 0 < p.ε) (f : Functions p)
    (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G) (seed : Sample p) (i : Fin p.n) (j : Fin p.d) :
    |((LongTails.Algorithms.DashaQuantization.indices p.d false (spacing p cfg.choice)
      (gradient (f i) p.x0) (seed i).2 j : ℤ) : ℝ)| ≤ p.G / spacing p cfg.choice + 1 := by
  have hρ := DashaScalingParameters.spacing_pos cfg.choice hε
  have he := DashaQuantization.scalar_initial_error ((gradient (f i) p.x0) j / spacing p cfg.choice) ((seed i).2 j)
  have hc := scaled_coordinate_bound (p := p) 1 (spacing p cfg.choice) (by norm_num) hρ (gradient (f i) p.x0) j
  simp only [one_mul] at hc
  have hb := div_le_div_of_nonneg_right (hG i) hρ.le
  have ht : |((LongTails.Algorithms.DashaQuantization.scalarIndex false
      ((gradient (f i) p.x0) j / spacing p cfg.choice) ((seed i).2 j) : ℤ) : ℝ)| ≤
      |((LongTails.Algorithms.DashaQuantization.scalarIndex false
        ((gradient (f i) p.x0) j / spacing p cfg.choice) ((seed i).2 j) : ℤ) : ℝ) -
        (gradient (f i) p.x0) j / spacing p cfg.choice| + |(gradient (f i) p.x0) j / spacing p cfg.choice| :=
    by simpa only [sub_zero] using (abs_sub_le
      ((LongTails.Algorithms.DashaQuantization.scalarIndex false
        ((gradient (f i) p.x0) j / spacing p cfg.choice) ((seed i).2 j) : ℤ) : ℝ)
      ((gradient (f i) p.x0) j / spacing p cfg.choice) 0)
  change |((LongTails.Algorithms.DashaQuantization.scalarIndex false _ _ : ℤ) : ℝ)| ≤ _
  linarith

lemma aggregate_code_bound (cfg : Config p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (seed : ℕ → Sample p) (k K : ℕ) (hk : k ≤ K) (j : Fin p.d) :
    |((∑ i, (idealTrajectory p cfg f seed k).localCode i j : ℤ) : ℝ)| ≤
      (p.n : ℝ) * initialRadius cfg * growth cfg.choice ^ K / spacing p cfg.choice := by
  have hρ := DashaScalingParameters.spacing_pos cfg.choice hε
  have hR := initialRadius_nonneg cfg hε hG0
  have hC := growth_ge_one cfg.choice hL hH
  have hm : initialRadius cfg * growth cfg.choice ^ k / spacing p cfg.choice ≤
      initialRadius cfg * growth cfg.choice ^ K / spacing p cfg.choice :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC hk) hR) hρ.le
  calc
    _ = |∑ i, ((idealTrajectory p cfg f seed k).localCode i j : ℝ)| := by norm_cast
    _ ≤ ∑ i, |((idealTrajectory p cfg f seed k).localCode i j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin p.n, initialRadius cfg * growth cfg.choice ^ K / spacing p cfg.choice :=
      Finset.sum_le_sum (fun i _ => (ideal_code_bound cfg hε hL hH hG0 f hs hG seed k i j).trans hm)
    _ = _ := by simp; ring

noncomputable def stepInput (cfg : Config p) (f : Functions p) (seed : ℕ → Sample p)
    (k : ℕ) (i : Fin p.n) : Point p :=
  gradient (f i) (idealTrajectory p cfg f seed (k + 1)).point -
    (idealTrajectory p cfg f seed k).localGradient i - momentum p cfg.choice •
      (LongTails.Algorithms.DashaQuantization.reconstruct (spacing p cfg.choice)
        ((idealTrajectory p cfg f seed k).localCode i) - (idealTrajectory p cfg f seed k).localGradient i)

noncomputable def inputRadius (cfg : Config p) : ℝ :=
  LongTails.Algorithms.DashaCyclic.multiplier cfg.choice.block *
    (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p cfg.choice) * initialRadius cfg / spacing p cfg.choice

lemma stepInput_bound (cfg : Config p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (seed : ℕ → Sample p) (k : ℕ) (i : Fin p.n) (j : Fin p.d) :
    |LongTails.Algorithms.DashaCyclic.multiplier cfg.choice.block * stepInput cfg f seed k i j / spacing p cfg.choice| ≤
      inputRadius cfg * growth cfg.choice ^ k := by
  have hρ := DashaScalingParameters.spacing_pos cfg.choice hε
  have hη := DashaScalingParameters.stepSize_pos cfg.choice hL hH
  have hq : 0 ≤ LongTails.Algorithms.DashaCyclic.multiplier cfg.choice.block := by
    unfold LongTails.Algorithms.DashaCyclic.multiplier
    positivity
  have hfactor : 0 ≤ 1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p cfg.choice := by positivity
  have hin : ‖stepInput cfg f seed k i‖ ≤
      (1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p cfg.choice) * envelope cfg.choice (idealTrajectory p cfg f seed k) :=
    innovation_bound cfg.choice hε hL hH hG0 f hs hG _ (ideal_gradient cfg f seed k) i
  have he := ideal_envelope cfg hε hL hH hG0 f hs hG seed k
  calc
    _ ≤ LongTails.Algorithms.DashaCyclic.multiplier cfg.choice.block * ‖stepInput cfg f seed k i‖ / spacing p cfg.choice :=
      scaled_coordinate_bound _ _ hq hρ _ j
    _ ≤ LongTails.Algorithms.DashaCyclic.multiplier cfg.choice.block *
        ((1 + Real.sqrt (p.n : ℝ) * p.Lhat * stepSize p cfg.choice) *
          (initialRadius cfg * growth cfg.choice ^ k)) / spacing p cfg.choice :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (hin.trans (mul_le_mul_of_nonneg_left he hfactor)) hq) hρ.le
    _ = _ := by unfold inputRadius; ring

lemma inputRadius_nonneg (cfg : Config p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) : 0 ≤ inputRadius cfg := by
  have hρ := DashaScalingParameters.spacing_pos cfg.choice hε
  have hη := DashaScalingParameters.stepSize_pos cfg.choice hL hH
  have hR := initialRadius_nonneg cfg hε hG0
  unfold inputRadius LongTails.Algorithms.DashaCyclic.multiplier
  positivity

lemma step_exponent_bound (cfg : Config p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (seed : ℕ → Sample p) (k K : ℕ) (hk : k ≤ K) (i : Fin p.n) (j : Fin p.d) :
    LongTails.Algorithms.DashaFloat.exponent cfg.choice.precision
      (LongTails.Algorithms.DashaCyclic.multiplier cfg.choice.block * stepInput cfg f seed k i j / spacing p cfg.choice) <
      2 ^ (Nat.size (Nat.size ⌈inputRadius cfg⌉₊ + K * Nat.size ⌈growth cfg.choice⌉₊)) :=
  DashaFloat.exponent_real_geometric_bound _ k K _ _ _ (inputRadius_nonneg cfg hε hL hH hG0)
    (growth_ge_one cfg.choice hL hH) hk (stepInput_bound cfg hε hL hH hG0 f hs hG seed k i j)

lemma initial_exponent_bound (cfg : Config p) (initializer : Choice p) (hε : 0 < p.ε)
    (hG0 : 0 ≤ p.G) (f : Functions p) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (i : Fin p.n) (j : Fin p.d) :
    LongTails.Algorithms.DashaFloat.exponent initializer.precision
      (LongTails.Algorithms.DashaCyclic.multiplier initializer.block * (gradient (f i) p.x0) j / spacing p cfg.choice) <
      2 ^ (Nat.size (Nat.size ⌈LongTails.Algorithms.DashaCyclic.multiplier initializer.block * p.G / spacing p cfg.choice⌉₊)) := by
  have hρ := DashaScalingParameters.spacing_pos cfg.choice hε
  have hq : 0 ≤ LongTails.Algorithms.DashaCyclic.multiplier initializer.block := by
    unfold LongTails.Algorithms.DashaCyclic.multiplier
    positivity
  have hb := (scaled_coordinate_bound _ _ hq hρ (gradient (f i) p.x0) j).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hG i) hq) hρ.le)
  have he := DashaFloat.exponent_real_geometric_bound initializer.precision 0 0 _
    (LongTails.Algorithms.DashaCyclic.multiplier initializer.block * p.G / spacing p cfg.choice) 1
    (by positivity) le_rfl le_rfl (by simpa only [pow_zero, mul_one] using hb)
  simpa only [Nat.zero_mul, Nat.add_zero] using he

lemma transportExact (cfg : Config p) (hmod : cfg.modularInitialization = false) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hG0 : 0 ≤ p.G) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (hmain : cfg.exponentWidth = Nat.size (Nat.size ⌈inputRadius cfg⌉₊ + cfg.iterations * Nat.size ⌈growth cfg.choice⌉₊))
    (hinit : cfg.initialWidth = match cfg.initializer with
      | none => Nat.size ⌈p.G / spacing p cfg.choice + 1⌉₊ + 1
      | some initializer => Nat.size (Nat.size ⌈LongTails.Algorithms.DashaCyclic.multiplier initializer.block *
          p.G / spacing p cfg.choice⌉₊))
    (hroot : cfg.broadcastWidth = Nat.size ⌈(p.n : ℝ) * initialRadius cfg * growth cfg.choice ^ (cfg.iterations : ℕ) /
      spacing p cfg.choice⌉₊ + 1) (seed : ℕ → Sample p) : TransportExact cfg f seed := by
  apply transportExact_of_nonmodular cfg f seed hmod
  · intro k hk i suffix
    cases k with
    | zero =>
        cases hi : cfg.initializer with
        | none =>
            have hw : cfg.initialWidth = Nat.size ⌈p.G / spacing p cfg.choice + 1⌉₊ + 1 := by simpa only [hi] using hinit
            have hd := decode_integer_frame p.d (p.G / spacing p cfg.choice + 1)
              (LongTails.Algorithms.DashaQuantization.indices p.d false (spacing p cfg.choice)
                (gradient (f i) p.x0) (seed 0 i).2) suffix
              (initial_index_bound cfg hε f hG (seed 0) i)
            simpa [uplinkReceive, workerMessage, uplinkMessage, hmod, hi, hw, increment, previousCode,
              idealTrajectory, idealInitial, initialIterate, LongTails.Algorithms.DashaQuantization.message] using hd
        | some initializer =>
            have hw : cfg.initialWidth = Nat.size (Nat.size ⌈LongTails.Algorithms.DashaCyclic.multiplier initializer.block *
                p.G / spacing p cfg.choice⌉₊) := by simpa only [hi] using hinit
            have hd := DashaPackets.receive_message initializer.block initializer.precision cfg.initialWidth
              (spacing p cfg.choice) (gradient (f i) p.x0) (seed 0 i) suffix
              (fun j => by rw [hw]; exact initial_exponent_bound cfg initializer hε hG0 f hG i j)
            simpa [uplinkReceive, workerMessage, uplinkMessage, hi, increment, previousCode,
              idealTrajectory, idealInitial, sparseInitialIterate] using hd
    | succ k =>
        have hd := DashaPackets.receive_message cfg.choice.block cfg.choice.precision cfg.exponentWidth
          (spacing p cfg.choice) (stepInput cfg f seed k i) (seed (k + 1) i) suffix
          (fun j => by rw [hmain]; exact step_exponent_bound cfg hε hL hH hG0 f hs hG seed k cfg.iterations (by omega) i j)
        have hinc : increment cfg f seed (k + 1) i =
            LongTails.Algorithms.DashaCyclic.compressedIndex cfg.choice.block (seed (k + 1) i).1 cfg.choice.precision
              (spacing p cfg.choice) (stepInput cfg f seed k i) (seed (k + 1) i).2 := by
          funext j
          simp [increment, previousCode, idealTrajectory, nextIterate, stepInput]
        rw [hinc]
        simpa only [uplinkReceive, Nat.succ_ne_zero, ite_false, workerMessage, uplinkMessage,
          previousCode, previousGradient, stepInput] using hd
  · intro k hk suffix
    unfold broadcastMessage
    rw [hroot]
    exact decode_integer_frame _ _ _ suffix
      (aggregate_code_bound cfg hε hL hH hG0 f hs hG seed k cfg.iterations hk.le)

end LongTails.Proofs.DashaDistributedCapacity
