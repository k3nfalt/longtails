import LongTails.Algorithms.DistributedBatchedSgd
import LongTails.Proofs.DistributedSmoothNonconvex
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.DistributedSampling
import LongTails.Proofs.WeakGradientConvolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.DistributedBatchedSgd

open LongTails.Setups.DistributedSmoothNonconvex
open LongTails.Algorithms.DistributedBatchedSgd

variable {p : Params}

lemma floor_half (a : ℝ) (ha : 2 ≤ a) : a / 2 ≤ (⌊a⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one a
  have hfloor : 1 ≤ ⌊a⌋₊ := by
    apply Nat.le_floor
    norm_num
    linarith
  have hfloor' : (1 : ℝ) ≤ ⌊a⌋₊ := by exact_mod_cast hfloor
  nlinarith

lemma parallel_batch_capacity {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (hh : ∀ i, 0 < h i) (workers : Finset ι) (t B : ℝ)
    (ht : ∀ i ∈ workers, 2 * h i ≤ t)
    (hB : B ≤ t / 2 * ∑ i ∈ workers, 1 / h i) :
    B ≤ ∑ i, (⌊t / h i⌋₊ : ℝ) := by
  have hi (i : ι) (hi : i ∈ workers) : t / 2 * (1 / h i) ≤ (⌊t / h i⌋₊ : ℝ) := by
    have htwo : 2 ≤ t / h i := (le_div_iff₀ (hh i)).mpr (ht i hi)
    convert floor_half (t / h i) htwo using 1
    ring
  calc
    B ≤ t / 2 * ∑ i ∈ workers, 1 / h i := hB
    _ = ∑ i ∈ workers, t / 2 * (1 / h i) := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ workers, (⌊t / h i⌋₊ : ℝ) := Finset.sum_le_sum hi
    _ ≤ ∑ i, (⌊t / h i⌋₊ : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Nat.cast_nonneg _)

lemma batchTime_minimizes (hn : 0 < p.n) :
    ∃ i : Fin p.n, batchTime p = candidateTime p i ∧
      ∀ j : Fin p.n, batchTime p ≤ candidateTime p j := by
  classical
  cases h : (List.finRange p.n).argmin (candidateTime p) with
  | none =>
      have hempty := List.argmin_eq_none.mp h
      have hmem : (⟨0, hn⟩ : Fin p.n) ∈ List.finRange p.n := by simp
      simp [hempty] at hmem
  | some i =>
      refine ⟨i, by simp only [batchTime, h, Option.map_some, Option.getD_some], ?_⟩
      intro j
      simpa only [batchTime, h, Option.map_some, Option.getD_some] using
        (List.le_of_mem_argmin (by simp : j ∈ List.finRange p.n)
          (by simp [h] : i ∈ (List.finRange p.n).argmin (candidateTime p)))

lemma throughput_pos (hh : ∀ i, 0 < p.h i) (i : Fin p.n) : 0 < throughput p i := by
  have hsum : (p.h i)⁻¹ ≤ throughput p i := by
    unfold throughput
    have h := Finset.single_le_sum
      (f := fun j => if p.h j ≤ p.h i then (p.h j)⁻¹ else 0)
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin p.n))) => by positivity)
      (Finset.mem_univ i)
    simpa using h
  exact (inv_pos.mpr (hh i)).trans_le hsum

lemma candidate_has_capacity (hh : ∀ i, 0 < p.h i) (i : Fin p.n) :
    (targetBatch p : ℝ) ≤ ∑ j, (⌊(candidateTime p i : ℝ) / (p.h j : ℝ)⌋₊ : ℝ) := by
  classical
  let workers := Finset.univ.filter fun j => p.h j ≤ p.h i
  have hh' (j : Fin p.n) : 0 < (p.h j : ℝ) := by exact_mod_cast hh j
  have hH : 0 < (throughput p i : ℝ) := by exact_mod_cast throughput_pos hh i
  have hsum : (∑ j ∈ workers, 1 / (p.h j : ℝ)) = (throughput p i : ℝ) := by
    simp [workers, throughput, Finset.sum_filter, one_div, apply_ite]
  have ht : (candidateTime p i : ℝ) =
      2 * max (p.h i : ℝ) ((targetBatch p : ℝ) / (throughput p i : ℝ)) := by
    simp [candidateTime]
  apply parallel_batch_capacity (fun j => (p.h j : ℝ)) hh' workers (candidateTime p i) (targetBatch p)
  · intro j hj
    have hji : (p.h j : ℝ) ≤ (p.h i : ℝ) := by
      exact_mod_cast (Finset.mem_filter.mp hj).2
    rw [ht]
    linarith [le_max_left (p.h i : ℝ) ((targetBatch p : ℝ) / (throughput p i : ℝ))]
  · rw [hsum]
    apply (div_le_iff₀ hH).mp
    rw [ht]
    linarith [le_max_right (p.h i : ℝ) ((targetBatch p : ℝ) / (throughput p i : ℝ))]

lemma configured_batch_large (hn : 0 < p.n) (hh : ∀ i, 0 < p.h i) :
    targetBatch p ≤ totalBatch p (config p) := by
  obtain ⟨i, hi, _⟩ := batchTime_minimizes hn
  have h := candidate_has_capacity hh i
  rw [← hi] at h
  exact_mod_cast h

lemma worker_time_le_computationTime (cfg : Config p) (i : Fin p.n) :
    cfg.batch i * p.h i ≤ computationTime p cfg := by
  have hacc (workers : List (Fin p.n)) (t : DistributedTemplate.Time) :
      t ≤ workers.foldl (fun acc j => max acc (cfg.batch j * p.h j)) t := by
    induction workers generalizing t with
    | nil => exact le_rfl
    | cons j rest ih => exact (le_max_left _ _).trans (ih _)
  have hmem (workers : List (Fin p.n)) (t : DistributedTemplate.Time) (hi : i ∈ workers) :
      cfg.batch i * p.h i ≤ workers.foldl (fun acc j => max acc (cfg.batch j * p.h j)) t := by
    induction workers generalizing t with
    | nil => simp at hi
    | cons j rest ih =>
        rcases List.mem_cons.mp hi with rfl | hi
        · exact (le_max_right _ _).trans (hacc rest _)
        · exact ih _ hi
  exact hmem (List.finRange p.n) 0 (by simp)

lemma configured_worker_time (hh : ∀ i, 0 < p.h i) (i : Fin p.n) :
    (config p).batch i * p.h i ≤ batchTime p := by
  have hh' : 0 < (p.h i : ℝ) := by exact_mod_cast hh i
  have hf := Nat.floor_le
    (by positivity : 0 ≤ (batchTime p : ℝ) / (p.h i : ℝ))
  have hb := (le_div_iff₀ hh').mp hf
  change (⌊(batchTime p : ℝ) / (p.h i : ℝ)⌋₊ : DistributedTemplate.Time) * p.h i ≤ batchTime p
  exact_mod_cast hb

lemma computationTime_le (cfg : Config p) (bound : DistributedTemplate.Time)
    (hworkers : ∀ i, cfg.batch i * p.h i ≤ bound) : computationTime p cfg ≤ bound := by
  have hfold (workers : List (Fin p.n)) (t : DistributedTemplate.Time) (ht : t ≤ bound) :
      workers.foldl (fun acc i => max acc (cfg.batch i * p.h i)) t ≤ bound := by
    induction workers generalizing t with
    | nil => exact ht
    | cons i rest ih => exact ih _ (max_le ht (hworkers i))
  exact hfold _ 0 zero_le

lemma configured_computation_time (hh : ∀ i, 0 < p.h i) :
    computationTime p (config p) ≤ batchTime p :=
  computationTime_le (config p) (batchTime p) (configured_worker_time hh)

lemma configured_time_bound (hn : 0 < p.n) (hh : ∀ i, 0 < p.h i) (i : Fin p.n) :
    timeBudget p (config p) ≤ (iterations p : ℕ) *
      (candidateTime p i + 2 * (p.l + p.b * (p.d * (config p).width + DistributedTemplate.clockBits : ℕ))) := by
  obtain ⟨_, _, hmin⟩ := batchTime_minimizes hn
  have hc := (configured_computation_time hh).trans (hmin i)
  unfold timeBudget roundTime
  simp only [config, add_zero]
  exact mul_le_mul_of_nonneg_left (add_le_add_left hc _) (by positivity)

lemma gradient_bound {f : Point p → ℝ} (hL : 0 < p.L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ)
    (x : Point p) :
    ‖gradient f x‖ ≤ Real.sqrt (2 * p.L * p.Δ) + p.L * ‖x - p.x0‖ := by
  have hinit := LongTails.Proofs.DistributedSmoothNonconvex.initial_gradient_bound
    hL hg hlip lower hlower hgap
  have hnorm := Real.le_sqrt_of_sq_le hinit
  have htri : ‖gradient f x‖ ≤ ‖gradient f x - gradient f p.x0‖ + ‖gradient f p.x0‖ := by
    simpa using norm_add_le (gradient f x - gradient f p.x0) (gradient f p.x0)
  linarith [hlip x p.x0]

lemma radius_pos (hL : 0 ≤ p.L) (hε : 0 < p.ε) (x : Point p) : 0 < radius p x := by
  unfold radius
  have hnorm : 0 ≤ p.L * ‖x - p.x0‖ := mul_nonneg hL (norm_nonneg _)
  have hnoise : 0 ≤ 32 * p.σ ^ 2 / Real.sqrt p.ε := by positivity
  linarith [Real.sqrt_nonneg (2 * p.L * p.Δ), Real.sqrt_pos.mpr hε]

lemma levels_pos (cfg : Config p) : 0 < 2 ^ (cfg.width : ℕ) - 1 := by
  have hpow : 1 < 2 ^ (cfg.width : ℕ) := one_lt_pow₀ (by decide) cfg.width.ne_zero
  omega

lemma configured_levels (hL : 0 ≤ p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    1 + 8192 * p.d * ((iterations p : ℕ) : ℝ) ^ 2 +
      16 * p.d * (1280 * p.L * p.Δ / p.ε + 160 + 163840 * (p.σ ^ 2 / p.ε) ^ 2 +
        2560 * (iterations p : ℕ) * p.L * p.Δ / p.ε) ≤
      ((2 ^ ((config p).width : ℕ) - 1 : ℕ) : ℝ) ^ 2 := by
  let q : ℝ := 1 + 8192 * p.d * ((iterations p : ℕ) : ℝ) ^ 2 +
    16 * p.d * (1280 * p.L * p.Δ / p.ε + 160 + 163840 * (p.σ ^ 2 / p.ε) ^ 2 +
      2560 * (iterations p : ℕ) * p.L * p.Δ / p.ε)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hn := Nat.lt_size_self ⌈Real.sqrt q⌉₊
  have hp : 2 ^ (Nat.size ⌈Real.sqrt q⌉₊ + 1) = 2 ^ Nat.size ⌈Real.sqrt q⌉₊ * 2 := pow_succ _ _
  have hnat : ⌈Real.sqrt q⌉₊ ≤ 2 ^ (Nat.size ⌈Real.sqrt q⌉₊ + 1) - 1 := by omega
  have hsqrt : Real.sqrt q ≤ ((2 ^ ((config p).width : ℕ) - 1 : ℕ) : ℝ) :=
    (Nat.le_ceil (Real.sqrt q)).trans (by exact_mod_cast hnat)
  have hs := mul_self_le_mul_self (Real.sqrt_nonneg q) hsqrt
  nlinarith [Real.sq_sqrt hq]

lemma configured_iterations (hε : 0 < p.ε) :
    16 * p.L * p.Δ ≤ (iterations p : ℕ) * p.ε := by
  have hc := Nat.le_ceil (16 * p.L * p.Δ / p.ε)
  have hm : (⌈16 * p.L * p.Δ / p.ε⌉₊ : ℝ) ≤ (iterations p : ℕ) := by
    exact_mod_cast (le_max_right 1 ⌈16 * p.L * p.Δ / p.ε⌉₊)
  exact (div_le_iff₀ hε).mp (hc.trans hm)

lemma configured_variance (hn : 0 < p.n) (hh : ∀ i, 0 < p.h i) (hε : 0 < p.ε) :
    4 * p.σ ^ 2 / totalBatch p (config p) ≤ p.ε / 64 := by
  have hbatch := configured_batch_large hn hh
  have hpos : 0 < totalBatch p (config p) := by
    have hone : 1 ≤ targetBatch p := le_max_left _ _
    omega
  have hc := Nat.le_ceil (256 * p.σ ^ 2 / p.ε)
  have hm : (⌈256 * p.σ ^ 2 / p.ε⌉₊ : ℝ) ≤ totalBatch p (config p) := by
    exact_mod_cast ((le_max_right 1 ⌈256 * p.σ ^ 2 / p.ε⌉₊).trans hbatch)
  have hmul := (div_le_iff₀ hε).mp (hc.trans hm)
  apply (div_le_iff₀ (by exact_mod_cast hpos : (0 : ℝ) < totalBatch p (config p))).mpr
  nlinarith

lemma configured_tuning (hn : 0 < p.n) (hh : ∀ i, 0 < p.h i)
    (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    let K : ℕ := iterations p
    let M : ℝ := (2 ^ ((config p).width : ℕ) - 1 : ℕ)
    let a := 4 * p.σ ^ 2 / totalBatch p (config p) + p.ε / 256 +
      40 * p.d * (32 * p.L * p.Δ + 4 * p.ε + 4096 * p.σ ^ 4 / p.ε) / M ^ 2
    let c := 640 * p.d * p.L ^ 2 / M ^ 2
    8 * (K : ℝ) ^ 2 * c ≤ p.L ^ 2 ∧
      a + 4 * c * K * p.Δ / p.L ≤ p.ε / 4 ∧ 4 * p.L * p.Δ ≤ K * p.ε := by
  intro K M a c
  let V := 1280 * p.L * p.Δ / p.ε + 160 + 163840 * (p.σ ^ 2 / p.ε) ^ 2 +
    2560 * K * p.L * p.Δ / p.ε
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast levels_pos (config p)
  have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM
  have hB : (totalBatch p (config p) : ℝ) ≠ 0 := by
    have hlarge := configured_batch_large hn hh
    have htarget : 1 ≤ targetBatch p := le_max_left _ _
    have hpos : 0 < totalBatch p (config p) := by omega
    exact_mod_cast (Nat.ne_of_gt hpos)
  have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
  have hlevels := configured_levels hL.le hΔ hε
  change 1 + 8192 * p.d * (K : ℝ) ^ 2 + 16 * p.d * V ≤ M ^ 2 at hlevels
  have hkterm : 0 ≤ (p.d : ℝ) * (K : ℝ) ^ 2 := by positivity
  have hvterm : 0 ≤ (p.d : ℝ) * V := mul_nonneg hd hV
  have hratio : 5120 * p.d * (K : ℝ) ^ 2 / M ^ 2 ≤ 1 := by
    apply (div_le_one hM2).mpr
    nlinarith
  have hquant : (p.d : ℝ) * V / M ^ 2 ≤ 1 / 16 := by
    apply (div_le_iff₀ hM2).mpr
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have heq : 8 * (K : ℝ) ^ 2 * c = p.L ^ 2 * (5120 * p.d * (K : ℝ) ^ 2 / M ^ 2) := by
      dsimp [c]
      ring
    rw [heq]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio (sq_nonneg p.L)
  · have heq : a + 4 * c * K * p.Δ / p.L =
        4 * p.σ ^ 2 / totalBatch p (config p) + p.ε / 256 + p.ε * ((p.d : ℝ) * V / M ^ 2) := by
      dsimp [a, c, V]
      field_simp [ne_of_gt hL, ne_of_gt hε, ne_of_gt hM, hB]
      ring
    rw [heq]
    have hvar := configured_variance hn hh hε
    have hscaled := mul_le_mul_of_nonneg_left hquant hε.le
    linarith
  · have hi := configured_iterations hε
    have hgap : 0 ≤ p.L * p.Δ := mul_nonneg hL.le hΔ
    linarith

lemma spacing_pos (cfg : Config p) (hL : 0 ≤ p.L) (hε : 0 < p.ε) (x : Point p) :
    0 < spacing p cfg x := by
  unfold spacing
  exact div_pos (mul_pos (by norm_num) (radius_pos hL hε x)) (by exact_mod_cast levels_pos cfg)

lemma encode_length (cfg : Config p) (x g : Point p) :
    (encode p cfg x g).length = p.d * cfg.width :=
  LongTails.Proofs.DistributedQuantization.message_length _ _ _ _

lemma decode_encode (cfg : Config p) (x g : Point p) :
    decode p cfg x (encode p cfg x g) =
      LongTails.Algorithms.DistributedQuantization.receive p.d cfg.width (spacing p cfg x) (encode p cfg x g) := by
  unfold decode
  rw [← encode_length cfg x g, List.take_length]

lemma decode_append (cfg : Config p) (x : Point p) (bits suffix : List Bool)
    (hlength : bits.length = p.d * cfg.width) :
    decode p cfg x (bits ++ suffix) = decode p cfg x bits := by
  simp only [decode, ← hlength, List.take_left, List.take_length]

lemma encoding_error (cfg : Config p) (hL : 0 ≤ p.L) (hε : 0 < p.ε) (x g : Point p) :
    ‖decode p cfg x (encode p cfg x g) - OracleTemplate.clip (radius p x) g‖ ^ 2 ≤
      p.d * spacing p cfg x ^ 2 := by
  rw [decode_encode]
  apply LongTails.Proofs.DistributedQuantization.message_error
    p.d cfg.width (spacing p cfg x) (spacing_pos cfg hL hε x)
  intro i
  have hi : |OracleTemplate.clip (radius p x) g i| ≤ radius p x := by
    have hi := PiLp.norm_apply_le (OracleTemplate.clip (radius p x) g) i
    have hi' : |OracleTemplate.clip (radius p x) g i| ≤ ‖OracleTemplate.clip (radius p x) g‖ := by
      simpa only [Real.norm_eq_abs] using hi
    exact hi'.trans (OracleTemplate.norm_clip_le (radius_pos hL hε x).le g)
  have he : spacing p cfg x * ((2 ^ (cfg.width : ℕ) - 1 : ℕ) : ℝ) / 2 = radius p x := by
    unfold spacing
    have hM : ((2 ^ (cfg.width : ℕ) - 1 : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (levels_pos cfg))
    rw [div_mul_cancel₀ _ hM]
    ring
  rwa [he]

lemma measurable_encoded_gradient (cfg : Config p) :
    Measurable (fun z : Point p × Point p => decode p cfg z.1 (encode p cfg z.1 z.2)) := by
  simp only [decode_encode]
  have hs : Measurable (spacing p cfg) := by unfold spacing radius; fun_prop
  have hr : Measurable (radius p) := by unfold radius; fun_prop
  have hc : Measurable (fun z : Point p × Point p => OracleTemplate.clip (radius p z.1) z.2) := by
    unfold OracleTemplate.clip
    exact Measurable.ite (measurableSet_le measurable_snd.norm (hr.comp measurable_fst))
      measurable_snd (((hr.comp measurable_fst).div measurable_snd.norm).smul measurable_snd)
  exact (LongTails.Proofs.DistributedQuantization.measurable_roundTrip_joint p.d cfg.width).comp
    ((hs.comp measurable_fst).prodMk hc)

lemma measurable_batchMean (cfg : Config p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) (i : Fin p.n) :
    Measurable (fun z : Point p × Samples p => batchMean p cfg g z.1 k z.2 i) := by
  unfold batchMean
  apply Measurable.fun_const_smul
  apply Finset.measurable_sum
  intro j _
  exact (hg i).comp (measurable_fst.prodMk
    ((measurable_pi_apply (k * cfg.batch i + j)).comp
      ((measurable_pi_apply i).comp measurable_snd)))

lemma measurable_estimate (cfg : Config p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) :
    Measurable (fun z : Point p × Samples p => estimate p cfg g z.1 k z.2) := by
  have hlocal (i : Fin p.n) : Measurable (fun z : Point p × Samples p =>
      decode p cfg z.1 (encode p cfg z.1 (batchMean p cfg g z.1 k z.2 i))) := by
    have hm := (measurable_encoded_gradient cfg).comp
      (measurable_fst.prodMk (measurable_batchMean cfg g hg k i))
    simpa only [Function.comp_def, id_eq] using hm
  have hsum : Measurable (fun z : Point p × Samples p =>
      ∑ i, ((cfg.batch i : ℝ) / totalBatch p cfg) •
        decode p cfg z.1 (encode p cfg z.1 (batchMean p cfg g z.1 k z.2 i))) :=
    Finset.measurable_sum _ (fun i _ => (hlocal i).fun_const_smul ((cfg.batch i : ℝ) / totalBatch p cfg))
  have hm := (measurable_encoded_gradient cfg).comp (measurable_fst.prodMk hsum)
  simpa only [Function.comp_def, estimate] using hm

lemma measurable_trajectory (cfg : Config p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) :
    Measurable (fun samples : Samples p => trajectory p cfg g samples k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      exact ih.sub (((measurable_estimate cfg g hg k).comp
        (ih.prodMk measurable_id)).fun_const_smul (1 / p.L))

lemma measurable_trajectory_of_coordinates (cfg : Config p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (K : ℕ)
    (m : MeasurableSpace (Samples p))
    (hsamples : ∀ i j, j < K * cfg.batch i →
      @Measurable (Samples p) p.Ω m p.measurableΩ (fun samples => samples i j)) :
    @Measurable (Samples p) (Point p) m inferInstance
      (fun samples => trajectory p cfg g samples K) := by
  let : MeasurableSpace (Samples p) := m
  revert hsamples
  induction K with
  | zero => intro _; exact measurable_const
  | succ k ih =>
      intro hsamples
      have hx := ih (fun i j hj => hsamples i j
        (hj.trans_le (Nat.mul_le_mul_right _ (Nat.le_succ k))))
      have hmean (i : Fin p.n) : Measurable (fun samples =>
          batchMean p cfg g (trajectory p cfg g samples k) k samples i) := by
        unfold batchMean
        apply Measurable.fun_const_smul
        apply Finset.measurable_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have ht : k * cfg.batch i + j < (k + 1) * cfg.batch i := by
          simpa only [Nat.add_mul, one_mul] using Nat.add_lt_add_left hj' (k * cfg.batch i)
        exact (hg i).comp (hx.prodMk (hsamples i _ ht))
      have hlocal (i : Fin p.n) : Measurable (fun samples =>
          decode p cfg (trajectory p cfg g samples k)
            (encode p cfg (trajectory p cfg g samples k)
              (batchMean p cfg g (trajectory p cfg g samples k) k samples i))) := by
        have hm := (measurable_encoded_gradient cfg).comp (hx.prodMk (hmean i))
        simpa only [Function.comp_def, id_eq] using hm
      have hsum := Finset.measurable_sum Finset.univ
        (fun i _ => (hlocal i).fun_const_smul ((cfg.batch i : ℝ) / totalBatch p cfg))
      have hestimate := (measurable_encoded_gradient cfg).comp (hx.prodMk hsum)
      exact hx.sub (hestimate.fun_const_smul (1 / p.L))

lemma trajectory_tail_independent (cfg : Config p) (P : Measure (Samples p))
    [IsProbabilityMeasure P] (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hworkers : iIndepFun (fun i (samples : Samples p) => samples i) P)
    (hIID : ∀ i, LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (samples : Samples p) => samples i k) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) :
    IndepFun (fun samples => trajectory p cfg g samples k) (DistributedSampling.tail p cfg k) P := by
  let m : Fin p.n × ℕ → MeasurableSpace (Samples p) := fun v =>
    MeasurableSpace.comap (fun samples : Samples p => samples v.1 v.2) p.measurableΩ
  let past : Set (Fin p.n × ℕ) := {v | v.2 < k * cfg.batch v.1}
  let future : Set (Fin p.n × ℕ) := {v | k * cfg.batch v.1 ≤ v.2}
  have hm (v : Fin p.n × ℕ) : m v ≤ (inferInstance : MeasurableSpace (Samples p)) := by
    have hm : Measurable (fun samples : Samples p => samples v.1 v.2) := by fun_prop
    exact hm.comap_le
  have hind : iIndep m P := DistributedSampling.independent_coordinates p P μ hworkers hIID
  have hd : Disjoint past future :=
    Set.disjoint_left.mpr (fun v hv hw => Nat.not_lt_of_ge hw hv)
  have hpair := indep_iSup_of_disjoint hm hind hd
  have hx := measurable_trajectory_of_coordinates cfg g hg k (⨆ v ∈ past, m v)
    (fun i j hj => Measurable.of_comap_le
      (le_iSup_of_le (i, j) (le_iSup_of_le hj le_rfl)))
  apply indep_of_indep_of_le hpair hx.comap_le
  change (inferInstance : MeasurableSpace (Samples p)).comap (DistributedSampling.tail p cfg k) ≤ _
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, DistributedSampling.tail]
  exact iSup_le (fun i => iSup_le (fun j =>
    le_iSup_of_le (i, k * cfg.batch i + j)
      (le_iSup_of_le (Nat.le_add_right _ _) le_rfl)))

lemma finite_range_encoded {Ω : Type*} (cfg : Config p) (x g : Ω → Point p)
    (hx : (Set.range x).Finite) :
    (Set.range (fun ω => decode p cfg (x ω) (encode p cfg (x ω) (g ω)))).Finite := by
  classical
  let codes : Set (LongTails.Algorithms.DistributedQuantization.Grid p.d cfg.width) := Set.univ
  have hfinite := (hx.prod codes.toFinite).image (fun z =>
    LongTails.Algorithms.DistributedQuantization.reconstruct (spacing p cfg z.1) z.2)
  apply hfinite.subset
  rintro _ ⟨ω, rfl⟩
  refine ⟨(x ω, LongTails.Algorithms.DistributedQuantization.quantize p.d cfg.width
    (spacing p cfg (x ω)) (OracleTemplate.clip (radius p (x ω)) (g ω))), ?_, ?_⟩
  · exact ⟨⟨ω, rfl⟩, Set.mem_univ _⟩
  · dsimp only
    rw [decode_encode]
    exact (LongTails.Proofs.DistributedQuantization.receive_message _ _ _ _).symm

lemma finite_range_estimate (cfg : Config p)
    (g : Fin p.n → Point p → p.Ω → Point p) (x : Samples p → Point p)
    (hx : (Set.range x).Finite) (k : ℕ) :
    (Set.range (fun samples => estimate p cfg g (x samples) k samples)).Finite :=
  finite_range_encoded cfg x _ hx

lemma finite_range_trajectory (cfg : Config p)
    (g : Fin p.n → Point p → p.Ω → Point p) (k : ℕ) :
    (Set.range (fun samples => trajectory p cfg g samples k)).Finite := by
  induction k with
  | zero => exact Set.finite_range_const
  | succ k ih =>
      have he := finite_range_estimate cfg g (fun samples => trajectory p cfg g samples k) ih k
      have hp := (ih.prod he).image (fun z => z.1 - (1 / p.L) • z.2)
      apply hp.subset
      rintro _ ⟨samples, rfl⟩
      exact ⟨(trajectory p cfg g samples k,
        estimate p cfg g (trajectory p cfg g samples k) k samples),
        ⟨⟨samples, rfl⟩, ⟨samples, rfl⟩⟩, rfl⟩

lemma measurable_output (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) : Measurable (output p cfg g) :=
  measurable_from_prod_countable_right (fun i => measurable_trajectory cfg g hg i.val)

lemma finite_range_output (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p) :
    (Set.range (output p cfg g)).Finite := by
  have hf := Set.finite_iUnion (fun i : Fin cfg.iterations => finite_range_trajectory cfg g i.val)
  apply hf.subset
  rintro _ ⟨⟨i, samples⟩, rfl⟩
  exact Set.mem_iUnion.mpr ⟨i, ⟨samples, rfl⟩⟩

lemma integrable_finite_range {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → E)
    (hm : Measurable f) (hf : (Set.range f).Finite) : Integrable f P := by
  obtain ⟨C, hC⟩ := (hf.image (fun x => ‖x‖)).bddAbove
  exact (integrable_const C).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => hC ⟨f ω, ⟨ω, rfl⟩, rfl⟩)

lemma output_gradient_integral (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (f : Point p → ℝ)
    (hf : Measurable (gradient f)) (P : Measure (Samples p)) [IsProbabilityMeasure P] :
    let Q := (PMF.uniformOfFintype (Fin cfg.iterations)).toMeasure.prod P
    Integrable (fun seed => ‖gradient f (output p cfg g seed)‖ ^ 2) Q ∧
      (∫ seed, ‖gradient f (output p cfg g seed)‖ ^ 2 ∂Q) =
        (1 / (cfg.iterations : ℕ)) *
          ∑ k ∈ Finset.range cfg.iterations, ∫ samples, ‖gradient f (trajectory p cfg g samples k)‖ ^ 2 ∂P := by
  let Q := (PMF.uniformOfFintype (Fin cfg.iterations)).toMeasure.prod P
  have hm := (hf.comp (measurable_output cfg g hg)).norm.pow_const 2
  have hfinite := (finite_range_output cfg g).image (fun v => ‖gradient f v‖ ^ 2)
  have hI : Integrable (fun seed => ‖gradient f (output p cfg g seed)‖ ^ 2) Q :=
    integrable_finite_range Q _ hm (hfinite.subset (by
      rintro _ ⟨seed, rfl⟩; exact ⟨output p cfg g seed, ⟨seed, rfl⟩, rfl⟩))
  refine ⟨hI, ?_⟩
  rw [integral_prod _ hI, integral_fintype hI.integral_prod_left]
  have hmass (i : Fin cfg.iterations) :
      (PMF.uniformOfFintype (Fin cfg.iterations)).toMeasure.real {i} =
        1 / (cfg.iterations : ℕ) := by
    simp [measureReal_def, PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _)]
  simp only [hmass, smul_eq_mul, ← Finset.mul_sum, output]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => ∫ samples, ‖gradient f (trajectory p cfg g samples k)‖ ^ 2 ∂P) _

lemma independent_finite_range_bound (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (x : Samples p → Point p) (hx : Measurable x) (hfinite : (Set.range x).Finite)
    (fresh : Samples p → Samples p) (hfresh : MeasurePreserving fresh P P)
    (hind : IndepFun x fresh P) (F : Point p × Samples p → ℝ) (H : Point p → ℝ)
    (hF : Measurable F) (hH : Measurable H) (hn : ∀ z, 0 ≤ F z)
    (hi : ∀ v, Integrable (fun samples => F (v, samples)) P)
    (hb : ∀ v, (∫ samples, F (v, samples) ∂P) ≤ H v) :
    Integrable (fun samples => F (x samples, fresh samples)) P ∧
      (∫ samples, F (x samples, fresh samples) ∂P) ≤ ∫ samples, H (x samples) ∂P := by
  have : IsProbabilityMeasure (P.map x) :=
    (Measure.isProbabilityMeasure_map_iff hx.aemeasurable).mpr inferInstance
  have hHi := integrable_finite_range P (H ∘ x) (hH.comp hx)
    (hfinite.image H |>.subset (by rintro _ ⟨samples, rfl⟩; exact ⟨x samples, ⟨samples, rfl⟩, rfl⟩))
  have hHm : Integrable H (P.map x) :=
    (integrable_map_measure hH.aestronglyMeasurable hx.aemeasurable).mpr hHi
  obtain ⟨hFI, hFB⟩ := LongTails.Proofs.WeakGradientConvolution.nonnegative_fiber_integral_bound
    hF.stronglyMeasurable hn (Filter.Eventually.of_forall hi) hHm (Filter.Eventually.of_forall hb)
  have hlaw : HasLaw (fun samples => (x samples, fresh samples)) ((P.map x).prod P) P := by
    refine ⟨(hx.prodMk hfresh.measurable).aemeasurable, ?_⟩
    rw [hind.map_prod_eq_prod_map_map hx.aemeasurable hfresh.measurable.aemeasurable, hfresh.map_eq]
  have hxl : HasLaw x (P.map x) P := ⟨hx.aemeasurable, rfl⟩
  exact ⟨hlaw.integrable_comp hFI,
    (hlaw.integral_comp hFI.aestronglyMeasurable).trans_le
      (hFB.trans_eq (hxl.integral_comp hHm.aestronglyMeasurable).symm)⟩

lemma clipping_residual (R : ℝ) (u g : Point p) (hR : ‖u‖ < R) :
    ‖OracleTemplate.clip R g - g‖ ≤ ‖g - u‖ ^ 2 / (R - ‖u‖) := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  rw [norm_sub_rev, OracleTemplate.clip_residual_norm hRpos.le]
  by_cases hg : ‖g‖ ≤ R
  · rw [max_eq_left (sub_nonpos.mpr hg)]
    positivity
  · rw [max_eq_right (by linarith : 0 ≤ ‖g‖ - R)]
    apply (le_div_iff₀ (sub_pos.mpr hR)).mpr
    have htri : ‖g‖ ≤ ‖g - u‖ + ‖u‖ := by
      simpa using norm_add_le (g - u) u
    have ha : 0 ≤ ‖g‖ - R := by linarith
    have hb : ‖g‖ - R ≤ ‖g - u‖ := by linarith
    have hc : R - ‖u‖ ≤ ‖g - u‖ := by linarith
    have hprod := mul_le_mul hb hc (sub_pos.mpr hR).le (norm_nonneg (g - u))
    nlinarith

lemma clipping_bias {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (R : ℝ) (u : Point p) (hR : ‖u‖ < R)
    (g : Ω → Point p) (hg : Measurable g) (hgi : Integrable g P)
    (herror : Integrable (fun ω => ‖g ω - u‖ ^ 2) P)
    (hmean : ∫ ω, g ω ∂P = u) :
    ‖(∫ ω, OracleTemplate.clip R (g ω) ∂P) - u‖ ≤
      (∫ ω, ‖g ω - u‖ ^ 2 ∂P) / (R - ‖u‖) := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  have hclip : Integrable (fun ω => OracleTemplate.clip R (g ω)) P :=
    (integrable_const R).mono' ((OracleTemplate.measurable_clip R).comp hg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => OracleTemplate.norm_clip_le hRpos.le (g ω))
  have hresidual := hclip.sub hgi
  calc
    _ = ‖∫ ω, OracleTemplate.clip R (g ω) - g ω ∂P‖ := by
      rw [integral_sub hclip hgi, hmean]
    _ ≤ ∫ ω, ‖OracleTemplate.clip R (g ω) - g ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ‖g ω - u‖ ^ 2 / (R - ‖u‖) ∂P :=
      integral_mono hresidual.norm (herror.div_const _) (fun ω => clipping_residual R u (g ω) hR)
    _ = _ := integral_div _ _

lemma quantized_gradient_control {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (R δ V : ℝ) (u : Point p) (hR : ‖u‖ < R) (_hδ : 0 ≤ δ)
    (g : Ω → Point p) (hg : Measurable g) (hgi : Integrable g P)
    (herror : Integrable (fun ω => ‖g ω - u‖ ^ 2) P)
    (hmean : ∫ ω, g ω ∂P = u) (hV : ∫ ω, ‖g ω - u‖ ^ 2 ∂P ≤ V)
    (Q : Point p → Point p) (hQ : Measurable Q)
    (hquant : ∀ v, ‖Q v - OracleTemplate.clip R v‖ ≤ δ) :
    Integrable (fun ω => Q (g ω)) P ∧
      Integrable (fun ω => ‖Q (g ω) - u‖ ^ 2) P ∧
      (∫ ω, ‖Q (g ω) - u‖ ^ 2 ∂P) ≤ 2 * V + 2 * δ ^ 2 ∧
      ‖(∫ ω, Q (g ω) ∂P) - u‖ ≤ V / (R - ‖u‖) + δ := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg _) hR
  have hclip : Integrable (fun ω => OracleTemplate.clip R (g ω)) P :=
    (integrable_const R).mono' ((OracleTemplate.measurable_clip R).comp hg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => OracleTemplate.norm_clip_le hRpos.le (g ω))
  have hres : Integrable (fun ω => Q (g ω) - OracleTemplate.clip R (g ω)) P :=
    (integrable_const δ).mono'
      (((hQ.comp hg).sub ((OracleTemplate.measurable_clip R).comp hg)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => hquant (g ω))
  have hQi : Integrable (fun ω => Q (g ω)) P := by
    convert hres.add hclip using 1
    ext ω
    simp
  have hpoint (ω : Ω) : ‖Q (g ω) - u‖ ^ 2 ≤ 2 * ‖g ω - u‖ ^ 2 + 2 * δ ^ 2 := by
    have hclipnorm := OracleTemplate.norm_clip_sub_le hRpos.le hR.le (g ω)
    have hclip2 := mul_self_le_mul_self (norm_nonneg _) hclipnorm
    have hquant2 := mul_self_le_mul_self (norm_nonneg _) (hquant (g ω))
    have hsum := LongTails.Proofs.DistributedSmoothNonconvex.norm_add_square
      (Q (g ω) - OracleTemplate.clip R (g ω)) (OracleTemplate.clip R (g ω) - u)
    have he : Q (g ω) - OracleTemplate.clip R (g ω) + (OracleTemplate.clip R (g ω) - u) =
        Q (g ω) - u := by abel
    rw [he] at hsum
    nlinarith
  have hbound : Integrable (fun ω => 2 * ‖g ω - u‖ ^ 2 + 2 * δ ^ 2) P := by
    convert (herror.const_mul 2).add (integrable_const (2 * δ ^ 2)) using 1
  have hQ2 : Integrable (fun ω => ‖Q (g ω) - u‖ ^ 2) P :=
    hbound.mono' (((hQ.comp hg).sub_const u).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs, abs_sq] using hpoint ω)
  refine ⟨hQi, hQ2, ?_, ?_⟩
  · have h := integral_mono hQ2 hbound hpoint
    rw [integral_add (herror.const_mul 2) (integrable_const _), integral_const_mul,
      integral_const] at h
    simp only [probReal_univ, one_smul] at h
    linarith
  · have hdelta : ‖(∫ ω, Q (g ω) ∂P) - ∫ ω, OracleTemplate.clip R (g ω) ∂P‖ ≤ δ := by
      rw [← integral_sub hQi hclip]
      calc
        _ ≤ ∫ ω, ‖Q (g ω) - OracleTemplate.clip R (g ω)‖ ∂P := norm_integral_le_integral_norm _
        _ ≤ ∫ _ : Ω, δ ∂P := integral_mono hres.norm (integrable_const _) (fun ω => hquant (g ω))
        _ = δ := by simp
    have hb := clipping_bias P R u hR g hg hgi herror hmean
    have htri := norm_sub_le_norm_sub_add_norm_sub (∫ ω, Q (g ω) ∂P) (∫ ω, OracleTemplate.clip R (g ω) ∂P) u
    have hfrac := div_le_div_of_nonneg_right hV (sub_pos.mpr hR).le
    linarith

lemma independent_biased_sum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (X : ι → Ω → Point p) (v b : ι → ℝ)
    (hind : iIndepFun X P)
    (hXi : ∀ i, Integrable (X i) P)
    (hX2 : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ 2) P)
    (hv : ∀ i, ∫ ω, ‖X i ω‖ ^ 2 ∂P ≤ v i)
    (hb : ∀ i, ‖∫ ω, X i ω ∂P‖ ≤ b i) :
    Integrable (fun ω => ‖∑ i, X i ω‖ ^ 2) P ∧
      ∫ ω, ‖∑ i, X i ω‖ ^ 2 ∂P ≤ (∑ i, v i) + (∑ i, b i) ^ 2 := by
  classical
  have hbi (i : ι) : 0 ≤ b i := (norm_nonneg _).trans (hb i)
  have hi (i j : ι) : Integrable (fun ω => ⟪X i ω, X j ω⟫) P := by
    by_cases hij : i = j
    · subst j
      simpa only [real_inner_self_eq_norm_sq] using hX2 i
    · exact (hind.indepFun hij).integrable_bilin (hXi i) (hXi j) (innerSL ℝ)
  have he (ω : Ω) : ‖∑ i, X i ω‖ ^ 2 = ∑ i, ∑ j, ⟪X i ω, X j ω⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
  have hI : Integrable (fun ω => ‖∑ i, X i ω‖ ^ 2) P := by
    simp_rw [he]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))
  refine ⟨hI, ?_⟩
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
  calc
    _ ≤ ∑ i, ∑ j, ((if i = j then v i else 0) + b i * b j) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · subst j
        simp only [ite_true, real_inner_self_eq_norm_sq]
        nlinarith [hv i, sq_nonneg (b i)]
      · have h := (hind.indepFun hij).integral_bilin (hXi i) (hXi j) (innerSL ℝ)
        change (∫ ω, ⟪X i ω, X j ω⟫ ∂P) =
          ⟪∫ ω, X i ω ∂P, ∫ ω, X j ω ∂P⟫ at h
        rw [h, ite_eq_right hij, zero_add]
        exact (real_inner_le_norm _ _).trans
          (mul_le_mul (hb i) (hb j) (norm_nonneg _) (hbi i))
    _ = (∑ i, v i) + (∑ i, b i) ^ 2 := by
      simp only [Finset.sum_add_distrib]
      simp [← Finset.mul_sum, ← Finset.sum_mul, pow_two]

lemma independent_weighted_error {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → Point p)
    (u : Point p) (w v b : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hind : iIndepFun X P) (hXi : ∀ i, Integrable (X i) P)
    (hX2 : ∀ i, Integrable (fun ω => ‖X i ω - u‖ ^ 2) P)
    (hv : ∀ i, ∫ ω, ‖X i ω - u‖ ^ 2 ∂P ≤ v i)
    (hb : ∀ i, ‖(∫ ω, X i ω ∂P) - u‖ ≤ b i) :
    Integrable (fun ω => ‖(∑ i, w i • X i ω) - u‖ ^ 2) P ∧
      ∫ ω, ‖(∑ i, w i • X i ω) - u‖ ^ 2 ∂P ≤
        (∑ i, w i ^ 2 * v i) + (∑ i, w i * b i) ^ 2 := by
  classical
  let Y := fun i ω => w i • (X i ω - u)
  have hYi (i) : Integrable (Y i) P := by
    simpa only [Y, Pi.sub_apply] using! ((hXi i).sub (integrable_const u)).fun_smul (w i)
  have hY2 (i) : Integrable (fun ω => ‖Y i ω‖ ^ 2) P := by
    simpa only [Y, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using
      (hX2 i).const_mul (w i ^ 2)
  have hYv (i) : ∫ ω, ‖Y i ω‖ ^ 2 ∂P ≤ w i ^ 2 * v i := by
    simp only [Y, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hv i) (sq_nonneg _)
  have hYb (i) : ‖∫ ω, Y i ω ∂P‖ ≤ w i * b i := by
    simp only [Y, integral_smul, integral_sub (hXi i) (integrable_const u),
      integral_const, probReal_univ, one_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (hw i)]
    exact mul_le_mul_of_nonneg_left (hb i) (hw i)
  have hYind : iIndepFun Y P := hind.comp
    (fun i y => w i • (y - u)) (fun i => (measurable_id.sub_const u).fun_const_smul (w i))
  have he (ω) : ∑ i, Y i ω = (∑ i, w i • X i ω) - u := by
    simp only [Y, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
  simpa only [he] using independent_biased_sum P Y
    (fun i => w i ^ 2 * v i) (fun i => w i * b i) hYind hYi hY2 hYv hYb

lemma batch_weights_sum {ι : Type*} [Fintype ι] (b : ι → ℕ) (hB : 0 < ∑ i, b i) :
    (∑ i, (b i : ℝ) / (∑ j, b j : ℕ)) = 1 := by
  rw [← Finset.sum_div]
  have he : (∑ i, (b i : ℝ)) = ((∑ i, b i : ℕ) : ℝ) := by simp
  rw [he]
  exact div_self (by exact_mod_cast (Nat.ne_of_gt hB))

lemma batch_weights_square {ι : Type*} [Fintype ι] (b : ι → ℕ) (hB : 0 < ∑ i, b i) :
    (∑ i, ((b i : ℝ) / (∑ j, b j : ℕ)) ^ 2) ≤ 1 := by
  have hsum := batch_weights_sum b hB
  have hpoint (i : ι) : ((b i : ℝ) / (∑ j, b j : ℕ)) ^ 2 ≤ (b i : ℝ) / (∑ j, b j : ℕ) := by
    have hBi : b i ≤ ∑ j, b j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hpos : (0 : ℝ) < (∑ j, b j : ℕ) := by exact_mod_cast hB
    have hle : (b i : ℝ) / (∑ j, b j : ℕ) ≤ 1 :=
      (div_le_one hpos).mpr (by exact_mod_cast hBi)
    have hnonneg : (0 : ℝ) ≤ (b i : ℝ) / (∑ j, b j : ℕ) := by positivity
    nlinarith
  exact (Finset.sum_le_sum (fun i _ => hpoint i)).trans_eq hsum

lemma batch_weights_variance {ι : Type*} [Fintype ι] (b : ι → ℕ) (hB : 0 < ∑ i, b i) :
    (∑ i, ((b i : ℝ) / (∑ j, b j : ℕ)) ^ 2 / b i) = 1 / (∑ j, b j : ℕ) := by
  have hpos : ((∑ j, b j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hB)
  have he (i : ι) : ((b i : ℝ) / (∑ j, b j : ℕ)) ^ 2 / b i =
      (b i : ℝ) / ((∑ j, b j : ℕ) : ℝ) ^ 2 := by
    by_cases hi : b i = 0
    · simp [hi]
    · have hi' : (b i : ℝ) ≠ 0 := by exact_mod_cast hi
      field_simp [hi', hpos]
  simp_rw [he]
  rw [← Finset.sum_div]
  simp only [← Nat.cast_sum]
  field_simp [hpos]

lemma batch_weights_bias {ι : Type*} [Fintype ι] (b : ι → ℕ) (hB : 0 < ∑ i, b i) :
    (∑ i, ((b i : ℝ) / (∑ j, b j : ℕ)) / b i) ≤ 1 := by
  have hpoint (i : ι) : ((b i : ℝ) / (∑ j, b j : ℕ)) / b i ≤
      (b i : ℝ) / (∑ j, b j : ℕ) := by
    by_cases hi : b i = 0
    · simp [hi]
    · have hb : (1 : ℝ) ≤ b i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
      exact div_le_self (by positivity) hb
  exact (Finset.sum_le_sum (fun i _ => hpoint i)).trans_eq (batch_weights_sum b hB)

lemma compression_error {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (R δ V : ℝ) (u : Point p) (hR : ‖u‖ ≤ R)
    (_hδ : 0 ≤ δ) (g : Ω → Point p) (hg : Measurable g)
    (herror : Integrable (fun ω => ‖g ω - u‖ ^ 2) P)
    (hV : ∫ ω, ‖g ω - u‖ ^ 2 ∂P ≤ V)
    (Q : Point p → Point p) (hQ : Measurable Q)
    (hquant : ∀ v, ‖Q v - OracleTemplate.clip R v‖ ≤ δ) :
    Integrable (fun ω => ‖Q (g ω) - u‖ ^ 2) P ∧
      (∫ ω, ‖Q (g ω) - u‖ ^ 2 ∂P) ≤ 2 * V + 2 * δ ^ 2 := by
  have hRnonneg := (norm_nonneg u).trans hR
  have hpoint (ω : Ω) : ‖Q (g ω) - u‖ ^ 2 ≤ 2 * ‖g ω - u‖ ^ 2 + 2 * δ ^ 2 := by
    have hc := OracleTemplate.norm_clip_sub_le hRnonneg hR (g ω)
    have ht := norm_sub_le_norm_sub_add_norm_sub (Q (g ω)) (OracleTemplate.clip R (g ω)) u
    have hn : ‖Q (g ω) - u‖ ≤ δ + ‖g ω - u‖ := by linarith [hquant (g ω)]
    have hs := mul_self_le_mul_self (norm_nonneg _) hn
    nlinarith [sq_nonneg (δ - ‖g ω - u‖)]
  have hbound : Integrable (fun ω => 2 * ‖g ω - u‖ ^ 2 + 2 * δ ^ 2) P := by
    convert (herror.const_mul 2).add (integrable_const (2 * δ ^ 2)) using 1
  have hQ2 : Integrable (fun ω => ‖Q (g ω) - u‖ ^ 2) P :=
    hbound.mono' (((hQ.comp hg).sub_const u).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs, abs_sq] using hpoint ω)
  refine ⟨hQ2, ?_⟩
  have h := integral_mono hQ2 hbound hpoint
  rw [integral_add (herror.const_mul 2) (integrable_const _), integral_const_mul,
    integral_const] at h
  simp only [probReal_univ, one_smul] at h
  linarith

lemma batched_aggregate_error {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → Point p)
    (u : Point p) (b : ι → ℕ) (hB : 0 < ∑ i, b i)
    (σ δ D : ℝ) (hδ : 0 ≤ δ) (hD : 0 < D)
    (hind : iIndepFun X P) (hXi : ∀ i, Integrable (X i) P)
    (hX2 : ∀ i, Integrable (fun ω => ‖X i ω - u‖ ^ 2) P)
    (hv : ∀ i, ∫ ω, ‖X i ω - u‖ ^ 2 ∂P ≤ 2 * (σ ^ 2 / b i) + 2 * δ ^ 2)
    (hb : ∀ i, ‖(∫ ω, X i ω ∂P) - u‖ ≤ (σ ^ 2 / b i) / D + δ) :
    Integrable (fun ω => ‖(∑ i, ((b i : ℝ) / (∑ j, b j : ℕ)) • X i ω) - u‖ ^ 2) P ∧
      (∫ ω, ‖(∑ i, ((b i : ℝ) / (∑ j, b j : ℕ)) • X i ω) - u‖ ^ 2 ∂P) ≤
        2 * σ ^ 2 / (∑ i, b i : ℕ) + 4 * δ ^ 2 + 2 * (σ ^ 2 / D) ^ 2 := by
  let w := fun i => (b i : ℝ) / (∑ j, b j : ℕ)
  have hw (i) : 0 ≤ w i := by dsimp [w]; positivity
  obtain ⟨hI, hE⟩ := independent_weighted_error P X u w
    (fun i => 2 * (σ ^ 2 / b i) + 2 * δ ^ 2)
    (fun i => (σ ^ 2 / b i) / D + δ) hw (batch_weights_sum b hB) hind hXi hX2 hv hb
  have hvar : (∑ i, w i ^ 2 * (2 * (σ ^ 2 / b i) + 2 * δ ^ 2)) ≤
      2 * σ ^ 2 / (∑ i, b i : ℕ) + 2 * δ ^ 2 := by
    have he : (∑ i, w i ^ 2 * (2 * (σ ^ 2 / b i) + 2 * δ ^ 2)) =
        2 * σ ^ 2 * (∑ i, w i ^ 2 / b i) + 2 * δ ^ 2 * ∑ i, w i ^ 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, batch_weights_variance b hB]
    have hsq := batch_weights_square b hB
    change (∑ i, w i ^ 2) ≤ 1 at hsq
    simp only [div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * δ ^ 2)]
  have hbias : (∑ i, w i * ((σ ^ 2 / b i) / D + δ)) ≤ σ ^ 2 / D + δ := by
    have he : (∑ i, w i * ((σ ^ 2 / b i) / D + δ)) =
        (σ ^ 2 / D) * (∑ i, w i / b i) + δ * ∑ i, w i := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, batch_weights_sum b hB]
    have hs := batch_weights_bias b hB
    change (∑ i, w i / b i) ≤ 1 at hs
    have hc : 0 ≤ σ ^ 2 / D := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hs hc]
  have hnonneg : 0 ≤ ∑ i, w i * ((σ ^ 2 / b i) / D + δ) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (by positivity))
  have hsq := mul_self_le_mul_self hnonneg hbias
  refine ⟨hI, ?_⟩
  nlinarith [sq_nonneg (σ ^ 2 / D - δ)]

lemma broadcast_error {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → Point p)
    (u : Point p) (b : ι → ℕ) (hB : 0 < ∑ i, b i)
    (σ δ R : ℝ) (hδ : 0 ≤ δ) (hR : ‖u‖ < R)
    (hind : iIndepFun X P) (hXm : ∀ i, Measurable (X i))
    (hXi : ∀ i, Integrable (X i) P)
    (hX2 : ∀ i, Integrable (fun ω => ‖X i ω - u‖ ^ 2) P)
    (hv : ∀ i, ∫ ω, ‖X i ω - u‖ ^ 2 ∂P ≤ 2 * (σ ^ 2 / b i) + 2 * δ ^ 2)
    (hb : ∀ i, ‖(∫ ω, X i ω ∂P) - u‖ ≤ (σ ^ 2 / b i) / (R - ‖u‖) + δ)
    (Q : Point p → Point p) (hQ : Measurable Q)
    (hquant : ∀ v, ‖Q v - OracleTemplate.clip R v‖ ≤ δ) :
    Integrable (fun ω => ‖Q (∑ i, ((b i : ℝ) / (∑ j, b j : ℕ)) • X i ω) - u‖ ^ 2) P ∧
      (∫ ω, ‖Q (∑ i, ((b i : ℝ) / (∑ j, b j : ℕ)) • X i ω) - u‖ ^ 2 ∂P) ≤
        4 * σ ^ 2 / (∑ i, b i : ℕ) + 10 * δ ^ 2 + 4 * (σ ^ 2 / (R - ‖u‖)) ^ 2 := by
  obtain ⟨hI, hE⟩ := batched_aggregate_error P X u b hB σ δ (R - ‖u‖)
    hδ (sub_pos.mpr hR) hind hXi hX2 hv hb
  have hm : Measurable (fun ω => ∑ i, ((b i : ℝ) / (∑ j, b j : ℕ)) • X i ω) :=
    Finset.measurable_sum _ (fun i _ => (hXm i).fun_const_smul ((b i : ℝ) / (∑ j, b j : ℕ)))
  obtain ⟨hQI, hQE⟩ := compression_error P R δ
    (2 * σ ^ 2 / (∑ i, b i : ℕ) + 4 * δ ^ 2 + 2 * (σ ^ 2 / (R - ‖u‖)) ^ 2)
    u hR.le hδ _ hm hI hE Q hQ hquant
  exact ⟨hQI, by linear_combination hQE⟩

lemma radius_margin (hL : 0 ≤ p.L) (_hε : 0 < p.ε) (x u : Point p)
    (hu : ‖u‖ ≤ Real.sqrt (2 * p.L * p.Δ) + p.L * ‖x - p.x0‖) :
    Real.sqrt p.ε + 32 * p.σ ^ 2 / Real.sqrt p.ε ≤ radius p x - ‖u‖ := by
  unfold radius
  have hG : 0 ≤ Real.sqrt (2 * p.L * p.Δ) + p.L * ‖x - p.x0‖ :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hL (norm_nonneg _))
  linarith

lemma radius_bias_bound (hL : 0 ≤ p.L) (hε : 0 < p.ε) (x u : Point p)
    (hu : ‖u‖ ≤ Real.sqrt (2 * p.L * p.Δ) + p.L * ‖x - p.x0‖) :
    4 * (p.σ ^ 2 / (radius p x - ‖u‖)) ^ 2 ≤ p.ε / 256 := by
  have hs := Real.sqrt_pos.mpr hε
  have hs2 := Real.sq_sqrt hε.le
  have hm := radius_margin hL hε x u hu
  have hnoise : 0 ≤ 32 * p.σ ^ 2 / Real.sqrt p.ε := by positivity
  have hD : 0 < radius p x - ‖u‖ := by linarith
  have hm' : 32 * p.σ ^ 2 / Real.sqrt p.ε ≤ radius p x - ‖u‖ := by linarith
  have hm'' := (div_le_iff₀ hs).mp hm'
  have hfrac : p.σ ^ 2 / (radius p x - ‖u‖) ≤ Real.sqrt p.ε / 32 := by
    apply (div_le_iff₀ hD).mpr
    nlinarith
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ p.σ ^ 2 / (radius p x - ‖u‖)) hfrac
  nlinarith

lemma radius_square (hL : 0 ≤ p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) (x : Point p) :
    radius p x ^ 2 ≤ 32 * p.L * p.Δ + 16 * p.L ^ 2 * ‖x - p.x0‖ ^ 2 +
      4 * p.ε + 4096 * p.σ ^ 4 / p.ε := by
  have hs := Real.sq_sqrt hε.le
  have hG := Real.sq_sqrt (by positivity : 0 ≤ 2 * p.L * p.Δ)
  have hnoise : (32 * p.σ ^ 2 / Real.sqrt p.ε) ^ 2 = 1024 * p.σ ^ 4 / p.ε := by
    rw [div_pow, hs]
    ring
  have hab := sq_nonneg (2 * Real.sqrt (2 * p.L * p.Δ) - 2 * p.L * ‖x - p.x0‖)
  have hcd := sq_nonneg (Real.sqrt p.ε - 32 * p.σ ^ 2 / Real.sqrt p.ε)
  have habcd := sq_nonneg (2 * Real.sqrt (2 * p.L * p.Δ) + 2 * p.L * ‖x - p.x0‖ -
    (Real.sqrt p.ε + 32 * p.σ ^ 2 / Real.sqrt p.ε))
  unfold radius
  calc
    _ ≤ 4 * ((2 * Real.sqrt (2 * p.L * p.Δ)) ^ 2 + (2 * p.L * ‖x - p.x0‖) ^ 2 +
        (Real.sqrt p.ε) ^ 2 + (32 * p.σ ^ 2 / Real.sqrt p.ε) ^ 2) := by
      nlinarith only [hab, hcd, habcd]
    _ = _ := by rw [hnoise, hs, mul_pow, hG]; ring

lemma quantized_batch_control {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (cfg : Config p) (hL : 0 ≤ p.L) (hε : 0 < p.ε)
    (x u : Point p) (hu : ‖u‖ < radius p x)
    (g : Ω → Point p) (hg : Measurable g) (hgi : Integrable g μ)
    (herror : Integrable (fun ω => ‖g ω - u‖ ^ 2) μ)
    (hmean : ∫ ω, g ω ∂μ = u) (hV : ∫ ω, ‖g ω - u‖ ^ 2 ∂μ ≤ p.σ ^ 2)
    (B : ℕ) (hB : 0 < B) :
    let Q := fun v => decode p cfg x (encode p cfg x v)
    let mean := fun ξ : Fin B → Ω => (1 / (B : ℝ)) • ∑ j, g (ξ j)
    let P := Measure.pi (fun _ : Fin B => μ)
    let δ := Real.sqrt (p.d * spacing p cfg x ^ 2)
    Integrable (fun ξ => Q (mean ξ)) P ∧
      Integrable (fun ξ => ‖Q (mean ξ) - u‖ ^ 2) P ∧
      (∫ ξ, ‖Q (mean ξ) - u‖ ^ 2 ∂P) ≤ 2 * (p.σ ^ 2 / B) + 2 * δ ^ 2 ∧
      ‖(∫ ξ, Q (mean ξ) ∂P) - u‖ ≤ (p.σ ^ 2 / B) / (radius p x - ‖u‖) + δ := by
  dsimp only
  obtain ⟨hmi, hmean'⟩ := OracleTemplate.LightTail.finite_mean_integral hgi B hB
  obtain ⟨hmi2, hvar⟩ := OracleTemplate.RobustGradient.finite_mean_variance
    hg hgi u herror hmean B hB
  have hm : Measurable (fun ξ : Fin B → Ω => (1 / (B : ℝ)) • ∑ j, g (ξ j)) := by
    apply Measurable.fun_const_smul
    exact Finset.measurable_sum _ (fun j _ => hg.comp (measurable_pi_apply j))
  have hQ : Measurable (fun v => decode p cfg x (encode p cfg x v)) :=
    by
      have hm := (measurable_encoded_gradient cfg).comp
        ((measurable_const : Measurable (fun _ : Point p => x)).prodMk measurable_id)
      simpa only [Function.comp_def, id_eq] using hm
  apply quantized_gradient_control (Measure.pi (fun _ : Fin B => μ)) (radius p x)
    (Real.sqrt (p.d * spacing p cfg x ^ 2)) (p.σ ^ 2 / B) u hu (Real.sqrt_nonneg _)
    _ hm hmi hmi2 (hmean'.trans hmean) _ _ hQ
  · intro v
    exact Real.le_sqrt_of_sq_le (encoding_error cfg hL hε x v)
  · rw [hvar]
    exact div_le_div_of_nonneg_right hV (Nat.cast_nonneg _)

lemma worker_quantized_control (cfg : Config p) (P : Measure (Samples p))
    [IsProbabilityMeasure P] (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hIID : ∀ i, LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (samples : Samples p) => samples i k) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Point p → ℝ)
    (hsg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ)
    (hL : 0 ≤ p.L) (hε : 0 < p.ε) (x : Point p) (hu : ‖gradient f x‖ < radius p x)
    (k : ℕ) (i : Fin p.n) (hi : 0 < cfg.batch i) :
    let X := fun samples => decode p cfg x (encode p cfg x (batchMean p cfg g x k samples i))
    let δ := Real.sqrt (p.d * spacing p cfg x ^ 2)
    Integrable X P ∧ Integrable (fun samples => ‖X samples - gradient f x‖ ^ 2) P ∧
      (∫ samples, ‖X samples - gradient f x‖ ^ 2 ∂P) ≤
        2 * (p.σ ^ 2 / cfg.batch i) + 2 * δ ^ 2 ∧
      ‖(∫ samples, X samples ∂P) - gradient f x‖ ≤
        (p.σ ^ 2 / cfg.batch i) / (radius p x - ‖gradient f x‖) + δ := by
  let F := fun ξ : Fin (cfg.batch i) → p.Ω => decode p cfg x
    (encode p cfg x ((1 / (cfg.batch i : ℝ)) • ∑ j, g i x (ξ j)))
  have hcontrol := quantized_batch_control (μ i : Measure _) cfg hL hε x (gradient f x) hu
    (g i x) ((hsg i).measurable.comp measurable_prodMk_left) ((hsg i).integrable x)
    ((hsg i).variance_integrable x) ((hsg i).unbiased x) ((hsg i).variance x) (cfg.batch i) hi
  change Integrable F _ ∧ Integrable (fun ξ => ‖F ξ - gradient f x‖ ^ 2) _ ∧ _ at hcontrol
  obtain ⟨hF, hF2, hvar, hbias⟩ := hcontrol
  have hlaw := DistributedSampling.worker_batch_law p cfg P μ hIID k i
  have he (samples : Samples p) :
      F (fun j => samples i (k * cfg.batch i + j.val)) =
      decode p cfg x (encode p cfg x (batchMean p cfg g x k samples i)) := by
    simp only [F, batchMean, one_div]
    congr 3
    exact Fin.sum_univ_eq_sum_range (fun j => g i x (samples i (k * cfg.batch i + j))) _
  have hi1 := hlaw.integrable_comp hF
  have hi2 := hlaw.integrable_comp hF2
  have he1 := hlaw.integral_comp hF.aestronglyMeasurable
  have he2 := hlaw.integral_comp hF2.aestronglyMeasurable
  simp only [Function.comp_def, he] at hi1 hi2 he1 he2
  exact ⟨hi1, hi2, he2.trans_le hvar, by rw [he1]; exact hbias⟩

lemma fixed_estimate_error (cfg : Config p) (P : Measure (Samples p))
    [IsProbabilityMeasure P] (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hworkers : iIndepFun (fun i (samples : Samples p) => samples i) P)
    (hIID : ∀ i, LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (samples : Samples p) => samples i k) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Point p → ℝ)
    (hsg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ)
    (hL : 0 ≤ p.L) (hε : 0 < p.ε) (hB : 0 < totalBatch p cfg) (x : Point p)
    (hu : ‖gradient f x‖ ≤ Real.sqrt (2 * p.L * p.Δ) + p.L * ‖x - p.x0‖) (k : ℕ) :
    Integrable (fun samples => ‖estimate p cfg g x k samples - gradient f x‖ ^ 2) P ∧
      (∫ samples, ‖estimate p cfg g x k samples - gradient f x‖ ^ 2 ∂P) ≤
        4 * p.σ ^ 2 / totalBatch p cfg + 10 * p.d * spacing p cfg x ^ 2 + p.ε / 256 := by
  let δ := Real.sqrt (p.d * spacing p cfg x ^ 2)
  let Q := fun v => decode p cfg x (encode p cfg x v)
  let F := fun i (ξ : ℕ → p.Ω) => if 0 < cfg.batch i then
    Q ((cfg.batch i : ℝ)⁻¹ • ∑ j ∈ Finset.range (cfg.batch i), g i x (ξ (k * cfg.batch i + j)))
    else gradient f x
  let X := fun i (samples : Samples p) => F i (samples i)
  have hQ : Measurable Q :=
    by
      have hm := (measurable_encoded_gradient cfg).comp
        ((measurable_const : Measurable (fun _ : Point p => x)).prodMk measurable_id)
      simpa only [Function.comp_def, id_eq] using hm
  have hFm (i : Fin p.n) : Measurable (F i) := by
    dsimp [F]
    split_ifs
    · apply hQ.comp
      apply Measurable.fun_const_smul
      apply Finset.measurable_sum
      intro j _
      exact ((hsg i).measurable.comp measurable_prodMk_left).comp (measurable_pi_apply _)
    · exact measurable_const
  have hXm (i : Fin p.n) : Measurable (X i) := (hFm i).comp (measurable_pi_apply i)
  have hD : ‖gradient f x‖ < radius p x := by
    have hm := radius_margin hL hε x (gradient f x) hu
    have hn : 0 ≤ 32 * p.σ ^ 2 / Real.sqrt p.ε := by positivity
    linarith [Real.sqrt_pos.mpr hε]
  have hcontrol (i : Fin p.n) :
      Integrable (X i) P ∧ Integrable (fun samples => ‖X i samples - gradient f x‖ ^ 2) P ∧
        (∫ samples, ‖X i samples - gradient f x‖ ^ 2 ∂P) ≤
          2 * (p.σ ^ 2 / cfg.batch i) + 2 * δ ^ 2 ∧
        ‖(∫ samples, X i samples ∂P) - gradient f x‖ ≤
          (p.σ ^ 2 / cfg.batch i) / (radius p x - ‖gradient f x‖) + δ := by
    by_cases hi : 0 < cfg.batch i
    · simpa only [X, F, ite_eq_left hi, Q, batchMean, δ] using
        worker_quantized_control cfg P μ hIID g f hsg hL hε x hD k i hi
    · have hz : cfg.batch i = 0 := by omega
      simp only [X, F, ite_eq_right hi, hz, Nat.cast_zero, div_zero, zero_div,
        zero_add, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), integral_zero,
        integral_const, probReal_univ, one_smul]
      exact ⟨integrable_const _, integrable_const _, by positivity, Real.sqrt_nonneg _⟩
  have hquant (v : Point p) : ‖Q v - OracleTemplate.clip (radius p x) v‖ ≤ δ :=
    Real.le_sqrt_of_sq_le (encoding_error cfg hL hε x v)
  have hind : iIndepFun X P := hworkers.comp F hFm
  obtain ⟨hI, hE⟩ := broadcast_error P X (gradient f x) cfg.batch hB p.σ δ (radius p x)
    (Real.sqrt_nonneg _) hD hind hXm (fun i => (hcontrol i).1)
    (fun i => (hcontrol i).2.1) (fun i => (hcontrol i).2.2.1)
    (fun i => (hcontrol i).2.2.2) Q hQ hquant
  have he (samples : Samples p) :
      Q (∑ i, ((cfg.batch i : ℝ) / (∑ j, cfg.batch j : ℕ)) • X i samples) =
        estimate p cfg g x k samples := by
    apply congrArg Q
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 < cfg.batch i
    · simp only [X, F, ite_eq_left hi, Q, batchMean, totalBatch]
    · have hz : cfg.batch i = 0 := by omega
      simp [hz]
  simp only [he] at hI hE
  have hδ2 : δ ^ 2 = p.d * spacing p cfg x ^ 2 := Real.sq_sqrt (by positivity)
  have hbias := radius_bias_bound hL hε x (gradient f x) hu
  refine ⟨hI, ?_⟩
  change (∫ samples, ‖estimate p cfg g x k samples - gradient f x‖ ^ 2 ∂P) ≤
    4 * p.σ ^ 2 / totalBatch p cfg + 10 * δ ^ 2 +
      4 * (p.σ ^ 2 / (radius p x - ‖gradient f x‖)) ^ 2 at hE
  rw [hδ2] at hE
  nlinarith

lemma estimate_tail (cfg : Config p) (g : Fin p.n → Point p → p.Ω → Point p)
    (x : Point p) (k : ℕ) (samples : Samples p) :
    estimate p cfg g x 0 (DistributedSampling.tail p cfg k samples) =
      estimate p cfg g x k samples := by
  simp only [estimate, batchMean, DistributedSampling.tail, zero_mul, zero_add]

lemma adaptive_estimate_error (cfg : Config p) (P : Measure (Samples p))
    [IsProbabilityMeasure P] (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hworkers : iIndepFun (fun i (samples : Samples p) => samples i) P)
    (hIID : ∀ i, LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (samples : Samples p) => samples i k) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Point p → ℝ)
    (hsg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ)
    (hL : 0 < p.L) (hε : 0 < p.ε) (hB : 0 < totalBatch p cfg)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ) (k : ℕ) :
    let x := fun samples => trajectory p cfg g samples k
    Integrable (fun samples => ‖estimate p cfg g (x samples) k samples - gradient f (x samples)‖ ^ 2) P ∧
      (∫ samples, ‖estimate p cfg g (x samples) k samples - gradient f (x samples)‖ ^ 2 ∂P) ≤
        ∫ samples, 4 * p.σ ^ 2 / totalBatch p cfg +
          10 * p.d * spacing p cfg (x samples) ^ 2 + p.ε / 256 ∂P := by
  let x := fun samples => trajectory p cfg g samples k
  have hgm (i : Fin p.n) := (hsg i).measurable
  have hx : Measurable x := measurable_trajectory cfg g hgm k
  have hgradLip : LipschitzWith ⟨p.L, hL.le⟩ (gradient f) :=
    LipschitzWith.of_dist_le_mul (fun v w => by simpa only [dist_eq_norm, NNReal.coe_mk] using! hlip v w)
  have hgrad := hgradLip.continuous.measurable
  let F := fun z : Point p × Samples p => ‖estimate p cfg g z.1 0 z.2 - gradient f z.1‖ ^ 2
  let H := fun v : Point p => 4 * p.σ ^ 2 / totalBatch p cfg +
    10 * p.d * spacing p cfg v ^ 2 + p.ε / 256
  have hF : Measurable F :=
    ((measurable_estimate cfg g hgm 0).sub (hgrad.comp measurable_fst)).norm.pow_const 2
  have hH : Measurable H := by unfold H spacing radius; fun_prop
  have hfixed (v : Point p) := fixed_estimate_error cfg P μ hworkers hIID g f hsg
    hL.le hε hB v (gradient_bound hL hg hlip lower hlower hgap v) 0
  have hcontrol := independent_finite_range_bound P x hx (finite_range_trajectory cfg g k)
    (DistributedSampling.tail p cfg k) (DistributedSampling.tail_preserving p cfg P μ hworkers hIID k)
    (trajectory_tail_independent cfg P μ hworkers hIID g hgm k) F H hF hH
    (fun _ => sq_nonneg _) (fun v => (hfixed v).1) (fun v => (hfixed v).2)
  simpa only [F, H, estimate_tail] using hcontrol

lemma adaptive_linear_error (cfg : Config p) (P : Measure (Samples p))
    [IsProbabilityMeasure P] (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hworkers : iIndepFun (fun i (samples : Samples p) => samples i) P)
    (hIID : ∀ i, LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (samples : Samples p) => samples i k) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Point p → ℝ)
    (hsg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ)
    (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) (hB : 0 < totalBatch p cfg)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ) (k : ℕ) :
    let M : ℝ := (2 ^ (cfg.width : ℕ) - 1 : ℕ)
    let a := 4 * p.σ ^ 2 / totalBatch p cfg + p.ε / 256 +
      40 * p.d * (32 * p.L * p.Δ + 4 * p.ε + 4096 * p.σ ^ 4 / p.ε) / M ^ 2
    let c := 640 * p.d * p.L ^ 2 / M ^ 2
    let x := fun samples => trajectory p cfg g samples k
    Integrable (fun samples => ‖estimate p cfg g (x samples) k samples - gradient f (x samples)‖ ^ 2) P ∧
      (∫ samples, ‖estimate p cfg g (x samples) k samples - gradient f (x samples)‖ ^ 2 ∂P) ≤
        a + c * ∫ samples, ‖x samples - p.x0‖ ^ 2 ∂P := by
  let M : ℝ := (2 ^ (cfg.width : ℕ) - 1 : ℕ)
  let a := 4 * p.σ ^ 2 / totalBatch p cfg + p.ε / 256 +
    40 * p.d * (32 * p.L * p.Δ + 4 * p.ε + 4096 * p.σ ^ 4 / p.ε) / M ^ 2
  let c := 640 * p.d * p.L ^ 2 / M ^ 2
  let x := fun samples => trajectory p cfg g samples k
  let H := fun v : Point p => 4 * p.σ ^ 2 / totalBatch p cfg +
    10 * p.d * spacing p cfg v ^ 2 + p.ε / 256
  have hgm (i : Fin p.n) := (hsg i).measurable
  have hx : Measurable x := measurable_trajectory cfg g hgm k
  have hfinite : (Set.range x).Finite := finite_range_trajectory cfg g k
  have hH : Measurable H := by unfold H spacing radius; fun_prop
  have hHi : Integrable (fun samples => H (x samples)) P := integrable_finite_range P _
    (hH.comp hx) ((hfinite.image H).subset (by
      rintro _ ⟨samples, rfl⟩; exact ⟨x samples, ⟨samples, rfl⟩, rfl⟩))
  have hd : Integrable (fun samples => ‖x samples - p.x0‖ ^ 2) P := integrable_finite_range P _
    ((hx.sub_const p.x0).norm.pow_const 2)
    ((hfinite.image (fun v => ‖v - p.x0‖ ^ 2)).subset (by
      rintro _ ⟨samples, rfl⟩; exact ⟨x samples, ⟨samples, rfl⟩, rfl⟩))
  have hpoint (v : Point p) : H v ≤ a + c * ‖v - p.x0‖ ^ 2 := by
    have hs := mul_le_mul_of_nonneg_left (radius_square hL.le hΔ hε v)
      (by positivity : 0 ≤ 40 * p.d / M ^ 2)
    have he : 10 * p.d * spacing p cfg v ^ 2 = 40 * p.d / M ^ 2 * radius p v ^ 2 := by
      unfold spacing M
      ring
    dsimp [H, a, c]
    rw [he]
    linear_combination hs
  obtain ⟨hI, hE⟩ := adaptive_estimate_error cfg P μ hworkers hIID g f hsg hL hε hB
    hg hlip lower hlower hgap k
  have hbound := integral_mono hHi ((integrable_const a).add (hd.const_mul c))
    (fun samples => hpoint (x samples))
  simp only [Pi.add_apply] at hbound
  rw [integral_add (integrable_const _) (hd.const_mul _), integral_const, integral_const_mul] at hbound
  simp only [probReal_univ, one_smul] at hbound
  exact ⟨hI, hE.trans hbound⟩

lemma output_accuracy_of_tuning (cfg : Config p) (P : Measure (Samples p))
    [IsProbabilityMeasure P] (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hworkers : iIndepFun (fun i (samples : Samples p) => samples i) P)
    (hIID : ∀ i, LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (samples : Samples p) => samples i k) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Point p → ℝ)
    (hsg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ)
    (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) (hB : 0 < totalBatch p cfg)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ) :
    let K : ℕ := cfg.iterations
    let M : ℝ := (2 ^ (cfg.width : ℕ) - 1 : ℕ)
    let a := 4 * p.σ ^ 2 / totalBatch p cfg + p.ε / 256 +
      40 * p.d * (32 * p.L * p.Δ + 4 * p.ε + 4096 * p.σ ^ 4 / p.ε) / M ^ 2
    let c := 640 * p.d * p.L ^ 2 / M ^ 2
    let Q := (PMF.uniformOfFintype (Fin cfg.iterations)).toMeasure.prod P
    8 * (K : ℝ) ^ 2 * c ≤ p.L ^ 2 →
    a + 4 * c * K * p.Δ / p.L ≤ p.ε / 4 →
    4 * p.L * p.Δ ≤ K * p.ε →
    Measurable (output p cfg g) ∧
      Integrable (fun seed => ‖gradient f (output p cfg g seed)‖ ^ 2) Q ∧
      (∫ seed, ‖gradient f (output p cfg g seed)‖ ^ 2 ∂Q) ≤ p.ε := by
  intro K M a c Q hsmall hbase hbudget
  have hgm (i : Fin p.n) := (hsg i).measurable
  have hgradLip : LipschitzWith ⟨p.L, hL.le⟩ (gradient f) :=
    LipschitzWith.of_dist_le_mul (fun v w => by simpa only [dist_eq_norm, NNReal.coe_mk] using! hlip v w)
  have hgrad := hgradLip.continuous.measurable
  have hx (k : ℕ) : Measurable (fun samples => trajectory p cfg g samples k) :=
    measurable_trajectory cfg g hgm k
  have hgi (k : ℕ) : Integrable (fun samples => ‖gradient f (trajectory p cfg g samples k)‖ ^ 2) P :=
    integrable_finite_range P _ ((hgrad.comp (hx k)).norm.pow_const 2)
      (((finite_range_trajectory cfg g k).image (fun v => ‖gradient f v‖ ^ 2)).subset (by
        rintro _ ⟨samples, rfl⟩
        exact ⟨trajectory p cfg g samples k, ⟨samples, rfl⟩, rfl⟩))
  have herr (k : ℕ) := adaptive_linear_error cfg P μ hworkers hIID g f hsg hL hΔ hε hB
    hg hlip lower hlower hgap k
  have hsum := LongTails.Proofs.DistributedSmoothNonconvex.expected_gradient_feedback P
    hL hg hlip lower hlower hgap (fun samples k => trajectory p cfg g samples k)
    (fun samples k => estimate p cfg g (trajectory p cfg g samples k) k samples)
    (fun _ => rfl) (fun _ _ => rfl) K a c (by dsimp [c]; positivity)
    (fun k _ => hx k) (fun k _ => hgi k) (fun k _ => (herr k).1)
    (fun k _ => (herr k).2) hsmall hbase hbudget
  obtain ⟨hI, hE⟩ := output_gradient_integral cfg g hgm f hgrad P
  refine ⟨measurable_output cfg g hgm, hI, ?_⟩
  rw [hE]
  have hK : (0 : ℝ) < K := by exact_mod_cast cfg.iterations.pos
  have hscaled := mul_le_mul_of_nonneg_left hsum (one_div_pos.mpr hK).le
  simpa only [one_div_mul_cancel (ne_of_gt hK), ← mul_assoc, one_mul] using hscaled

lemma configured_output_accuracy (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hworkers : iIndepFun (fun i (samples : Samples p) => samples i) P)
    (hIID : ∀ i, LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (samples : Samples p) => samples i k) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Point p → ℝ)
    (hsg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ)
    (hn : 0 < p.n) (hh : ∀ i, 0 < p.h i) (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ) :
    let Q := (PMF.uniformOfFintype (Fin (config p).iterations)).toMeasure.prod P
    Measurable (output p (config p) g) ∧
      Integrable (fun seed => ‖gradient f (output p (config p) g seed)‖ ^ 2) Q ∧
      (∫ seed, ‖gradient f (output p (config p) g seed)‖ ^ 2 ∂Q) ≤ p.ε := by
  have hB : 0 < totalBatch p (config p) := by
    have hlarge := configured_batch_large hn hh
    have htarget : 1 ≤ targetBatch p := le_max_left _ _
    omega
  obtain ⟨hsmall, hbase, hbudget⟩ := configured_tuning hn hh hL hΔ hε
  exact output_accuracy_of_tuning (config p) P μ hworkers hIID g f hsg hL hΔ hε hB
    hg hlip lower hlower hgap hsmall hbase hbudget

end LongTails.Proofs.DistributedBatchedSgd
