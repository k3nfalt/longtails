import LongTailsOnline.Proofs.TaskAllocationPhases
import LongTailsOnline.Proofs.TaskAllocationSchedule

namespace LongTailsOnline.Proofs.TaskAllocation

open LongTailsOnline.Setups.StationaryTaskAllocation
open LongTailsOnline.Algorithms.ParallelTaskAllocation

lemma level_le_balanced {k B : ℕ} {u : Worker k → ℝ} (hu : ∀ i, u i ≤ 1) :
    level (B := B) u ≤ (B : ℝ) / (k + 1) + 1 := by
  let c := ⌈(B : ℝ) / (k + 1)⌉₊
  have hn : (0 : ℝ) < k + 1 := by positivity
  have hcount : B ≤ (k + 1) * c := by
    have hh := (div_le_iff₀ hn).mp (Nat.le_ceil ((B : ℝ) / (k + 1)))
    have hh' : (B : ℝ) ≤ (((k + 1) * c : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      simpa only [c, mul_comm] using hh
    exact Nat.cast_le.mp hh'
  have hsum : B ≤ ∑ _i : Worker k, c := by simpa using hcount
  obtain ⟨a, ha⟩ := exists_allocation_le (fun _ : Worker k => c) hsum
  calc
    _ ≤ loss u a := upperOracle_le u a
    _ ≤ c := by
      apply (loss_le_iff _ _ _).mpr
      intro i
      exact (mul_le_mul_of_nonneg_left (hu i) (Nat.cast_nonneg _)).trans
        (by simpa only [mul_one] using (show ((a.val i).val : ℝ) ≤ c by exact_mod_cast ha i))
    _ ≤ _ := (Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg _) hn.le)).le

lemma quota_expression_upper {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {θ u : ℝ} (hθ : 0 < θ) (hu : 0 ≤ u) (C : ℕ) :
    (quota p θ u C : ℝ) ≤
      256 * scale p * u * (C : ℝ) ^ 2 / θ ^ 2 + 32 * scale p * C / θ + 2 := by
  have hχ := scale_ge_one hB hT
  unfold quota
  split_ifs with hC
  · subst C
    norm_num
  · have hnonneg : 0 ≤ 256 * scale p * u * (C : ℝ) ^ 2 / θ ^ 2 +
        32 * scale p * C / θ := by positivity
    have hh := Nat.ceil_lt_add_one hnonneg
    push_cast
    linarith

noncomputable def quotaLoadBound (p : Public) (θ V : ℝ) : ℝ :=
  256 * scale p * (V + θ) ^ 2 / θ ^ 2 + 32 * scale p * (V + θ) / θ + 2

noncomputable def quotaCapacityBound (p : Public) (θ V : ℝ) : ℝ :=
  256 * scale p * (V + θ) / θ ^ 2 + 32 * scale p / θ + 2

lemma quota_geometry_bounds {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {μ : Worker p.k → ℝ} (ci : Intervals p.k) (hci : ValidIntervals μ ci)
    {θ : ℝ} (hθ : 0 < θ)
    (hD : ∀ i, uncertainty p.B (level (B := p.B) ci.2) ci.1 ci.2 i ≤ θ) :
    let V := level (B := p.B) ci.2
    let C := capacity p.B V ci.1
    let q := fun i => quota p θ (ci.2 i) (C i)
    (∀ i, (q i : ℝ) * ci.2 i ≤ quotaLoadBound p θ V) ∧
      (∀ i, (q i : ℝ) ≤ quotaCapacityBound p θ V * C i) := by
  dsimp only
  let V := level (B := p.B) ci.2
  let C := capacity p.B V ci.1
  have hχ := scale_ge_one hB hT
  have hu (i) : 0 ≤ ci.2 i := (hci i).1.trans ((hci i).2.1.trans (hci i).2.2.1)
  have hV : 0 ≤ V := loss_nonneg hu _
  have hload (i) : (C i : ℝ) * ci.2 i ≤ V + θ := by
    have hcap := capacity_load_le (B := p.B) (fun i => (hci i).1) hV i
    have hi := hD i
    change (C i : ℝ) * (ci.2 i - ci.1 i) ≤ θ at hi
    change (C i : ℝ) * ci.1 i ≤ V at hcap
    nlinarith
  constructor
  · intro i
    calc
      _ ≤ (256 * scale p * ci.2 i * (C i : ℝ) ^ 2 / θ ^ 2 +
          32 * scale p * C i / θ + 2) * ci.2 i :=
        mul_le_mul_of_nonneg_right (quota_expression_upper hB hT hθ (hu i) (C i)) (hu i)
      _ = 256 * scale p * ((C i : ℝ) * ci.2 i) ^ 2 / θ ^ 2 +
          32 * scale p * ((C i : ℝ) * ci.2 i) / θ + 2 * ci.2 i := by ring
      _ ≤ quotaLoadBound p θ V := by
        unfold quotaLoadBound
        gcongr
        · exact mul_nonneg (Nat.cast_nonneg _) (hu i)
        · exact hload i
        · exact hload i
        · linarith [(hci i).2.2.2]
  · intro i
    change (quota p θ (ci.2 i) (C i) : ℝ) ≤ quotaCapacityBound p θ V * C i
    by_cases hzero : C i = 0
    · simp only [quota, hzero, ite_true, Nat.cast_zero, mul_zero]
      exact le_rfl
    · have hC : (1 : ℝ) ≤ C i := by exact_mod_cast Nat.pos_of_ne_zero hzero
      calc
        _ ≤ 256 * scale p * ci.2 i * (C i : ℝ) ^ 2 / θ ^ 2 +
            32 * scale p * C i / θ + 2 := quota_expression_upper hB hT hθ (hu i) (C i)
        _ = (256 * scale p * ((C i : ℝ) * ci.2 i) / θ ^ 2 +
            32 * scale p / θ) * C i + 2 := by ring
        _ ≤ (256 * scale p * (V + θ) / θ ^ 2 + 32 * scale p / θ) * C i + 2 * C i := by
          gcongr
          · exact hload i
          · linarith
        _ = quotaCapacityBound p θ V * C i := by unfold quotaCapacityBound; ring

lemma quota_sum_bound {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {μ : Worker p.k → ℝ} (ci : Intervals p.k) (hci : ValidIntervals μ ci)
    (hμ : ∀ i, 0 < μ i) {θ : ℝ} (hθ : 0 < θ)
    (hD : ∀ i, uncertainty p.B (level (B := p.B) ci.2) ci.1 ci.2 i ≤ θ)
    (hV : 0 < level (B := p.B) ci.2) :
    (∑ i, (quota p θ (ci.2 i) (capacity p.B (level (B := p.B) ci.2) ci.1 i) : ℝ)) ≤
      quotaLoadBound p θ (level (B := p.B) ci.2) * (p.B + (p.k + 1 : ℝ)) /
        level (B := p.B) ci.2 := by
  let V := level (B := p.B) ci.2
  let Q := quotaLoadBound p θ V
  have hu (i) : 0 < ci.2 i := (hμ i).trans_le (hci i).2.2.1
  have hχ := scale_ge_one hB hT
  have hQ : 0 ≤ Q := by dsimp only [Q, quotaLoadBound]; positivity
  have hq := (quota_geometry_bounds hB hT ci hci hθ hD).1
  have hh := optimum_harmonic_bound (B := p.B) hu
  rw [← level_eq_optimum] at hh
  calc
    _ ≤ ∑ i, Q * (ci.2 i)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [div_eq_mul_inv] using (le_div_iff₀ (hu i)).mpr (hq i)
    _ = Q * (∑ i, (ci.2 i)⁻¹) := (Finset.mul_sum _ _ _).symm
    _ ≤ Q * (p.B + (p.k + 1 : ℝ)) / V := by
      apply (le_div_iff₀ hV).mpr
      have hprod := mul_le_mul_of_nonneg_left hh hQ
      push_cast at hprod
      nlinarith

lemma coarse_quota_bounds {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {θ V : ℝ} (hθ : 0 < θ) (hV : 0 ≤ V) (hVθ : V ≤ θ) :
    quotaLoadBound p θ V ≤ 1100 * scale p ∧
      quotaCapacityBound p θ V ≤ 550 * scale p / θ + 2 := by
  have hχ := scale_ge_one hB hT
  constructor
  · calc
      _ ≤ 256 * scale p * (2 * θ) ^ 2 / θ ^ 2 + 32 * scale p * (2 * θ) / θ + 2 := by
        unfold quotaLoadBound
        gcongr <;> linarith
      _ = 1088 * scale p + 2 := by field_simp; ring
      _ ≤ _ := by linarith
  · calc
      _ ≤ 256 * scale p * (2 * θ) / θ ^ 2 + 32 * scale p / θ + 2 := by
        unfold quotaCapacityBound
        gcongr
        linarith
      _ = 544 * scale p / θ + 2 := by field_simp; ring
      _ ≤ _ := by gcongr; norm_num

lemma fine_quota_bounds {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {θ V : ℝ} (hθ : 0 < θ) (hθV : θ ≤ V) :
    quotaLoadBound p θ V ≤ 1100 * scale p * V ^ 2 / θ ^ 2 ∧
      quotaCapacityBound p θ V ≤ 550 * scale p * V / θ ^ 2 + 2 := by
  have hχ := scale_ge_one hB hT
  have hV : 0 < V := hθ.trans_le hθV
  have hθVsq : θ ^ 2 ≤ V ^ 2 := by nlinarith
  have hVθ : V * θ ≤ V ^ 2 := by nlinarith
  have hχVθ := mul_le_mul_of_nonneg_left hVθ (by linarith : 0 ≤ scale p)
  have hχθsq := mul_le_mul_of_nonneg_left hθVsq (by linarith : 0 ≤ scale p)
  have hθsqχ : θ ^ 2 ≤ scale p * V ^ 2 := by
    exact hθVsq.trans (by nlinarith [sq_nonneg V])
  constructor
  · calc
      _ ≤ 256 * scale p * (2 * V) ^ 2 / θ ^ 2 + 32 * scale p * (2 * V) / θ + 2 := by
        unfold quotaLoadBound
        gcongr <;> linarith
      _ = (1024 * scale p * V ^ 2 + 64 * scale p * V * θ + 2 * θ ^ 2) / θ ^ 2 := by
        field_simp
        ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg θ)
        nlinarith
  · calc
      _ ≤ 256 * scale p * (2 * V) / θ ^ 2 + 32 * scale p / θ + 2 := by
        unfold quotaCapacityBound
        gcongr
        linarith
      _ = (512 * scale p * V + 32 * scale p * θ) / θ ^ 2 + 2 := by
        field_simp
        ring
      _ ≤ _ := by
        gcongr
        nlinarith

noncomputable def quotaMaximum (p : Public) : ℕ :=
  ⌈256 * scale p * (p.B : ℝ) ^ 2 * (p.T : ℝ) ^ 2 +
    32 * scale p * p.B * p.T⌉₊ + 1

noncomputable def groupLimit (p : Public) : ℕ := 1 + Nat.log2 (quotaMaximum p)

def phaseLimit (p : Public) : ℕ := 1 + Nat.log2 (p.B * p.T)

lemma phase_index_lt_limit {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {h : ℕ} (hactive : accuracy p < precision p h) : h < phaseLimit p := by
  have hTpos : (0 : ℝ) < p.T := by exact_mod_cast hT
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  have hratio : 1 / (p.T : ℝ) < (p.B : ℝ) / (2 : ℝ) ^ h :=
    (inv_horizon_le_accuracy hB hT).trans_lt hactive
  have hpow : (2 : ℝ) ^ h < (p.B : ℝ) * p.T := by
    have hh := (div_lt_div_iff₀ hTpos hpowpos).mp hratio
    simpa only [one_mul] using hh
  have hpowNat : 2 ^ h ≤ p.B * p.T := (show 2 ^ h < p.B * p.T by exact_mod_cast hpow).le
  have hlog := (Nat.le_log2 (Nat.ne_of_gt (Nat.mul_pos hB hT))).mpr hpowNat
  unfold phaseLimit
  omega

lemma quota_le_maximum {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {θ u : ℝ} (hθ : accuracy p < θ) (hu1 : u ≤ 1)
    {C : ℕ} (hC : C ≤ p.B) : quota p θ u C ≤ quotaMaximum p := by
  have hχ := scale_ge_one hB hT
  have hTpos : (0 : ℝ) < p.T := by exact_mod_cast hT
  have hθpos : 0 < θ := (accuracy_pos hB hT).trans hθ
  have hθinv : 1 / (p.T : ℝ) ≤ θ := (inv_horizon_le_accuracy hB hT).trans hθ.le
  have hCr : (C : ℝ) ≤ p.B := by exact_mod_cast hC
  unfold quota quotaMaximum
  split_ifs
  · omega
  · apply Nat.add_le_add_right _ 1
    apply Nat.ceil_mono
    calc
      _ ≤ 256 * scale p * 1 * (p.B : ℝ) ^ 2 / (1 / (p.T : ℝ)) ^ 2 +
          32 * scale p * p.B / (1 / (p.T : ℝ)) := by
        gcongr
      _ = _ := by field_simp

lemma groups_le_limit {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {θ : ℝ} (hθ : accuracy p < θ) (u : Worker p.k → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : ℝ) 1) (C : Counts p.k) (hC : ∀ i, C i ≤ p.B) :
    1 + Finset.univ.sup (fun i => Nat.log2 (quota p θ (u i) (C i))) ≤ groupLimit p := by
  have hmax : quotaMaximum p ≠ 0 := by unfold quotaMaximum; omega
  unfold groupLimit
  apply Nat.add_le_add_left
  apply Finset.sup_le
  intro i _
  have hq := quota_le_maximum hB hT hθ (hu i).2 (hC i)
  by_cases hzero : quota p θ (u i) (C i) = 0
  · simp only [hzero, Nat.log2_zero]
    exact Nat.zero_le _
  · exact (Nat.le_log2 hmax).mpr ((Nat.log2_self_le hzero).trans hq)

lemma balanced_geometry {p : Public} (hB : 0 < p.B) :
    1 + (p.k + 1 : ℝ) / p.B ≤ 2 * imbalance p ∧
      (p.B : ℝ) / (p.k + 1) + 1 ≤ 2 * imbalance p ∧
      ((p.B : ℝ) / (p.k + 1) + 1) * (1 + (p.k + 1 : ℝ) / p.B) ≤
        2 * imbalance p := by
  have hd := imbalance_ge_two hB
  have hBpos : (0 : ℝ) < p.B := by exact_mod_cast hB
  have hn : (0 : ℝ) < p.k + 1 := by positivity
  have hprod : ((p.B : ℝ) / (p.k + 1) + 1) * (1 + (p.k + 1 : ℝ) / p.B) =
      imbalance p + 2 := by unfold imbalance; field_simp; ring
  refine ⟨?_, ?_, by rw [hprod]; linarith⟩
  · have hh : 0 ≤ (p.B : ℝ) / (p.k + 1) := by positivity
    unfold imbalance at *
    linarith
  · have hh : 0 ≤ (p.k + 1 : ℝ) / p.B := by positivity
    unfold imbalance at *
    linarith

noncomputable def frozenPlanCost {k B : ℕ} (μ u : Worker k → ℝ) (θ : ℝ)
    (plan : Plan k) : ℝ :=
  if level (B := B) u ≤ θ then (plan.map (explorationLoad u)).sum +
    plan.length * (level (B := B) u - optimum (B := B) μ) else plan.length * (2 * θ)

set_option maxHeartbeats 2000000 in
lemma frozen_plan_cost_bound {p : Public} (hB : 0 < p.B) (hT : 0 < p.T)
    {μ : Worker p.k → ℝ} (ci : Intervals p.k) (hci : ValidIntervals μ ci)
    (hμ : ∀ i, 0 < μ i) {θ : ℝ} (hθ : accuracy p < θ)
    (hD : ∀ i, uncertainty p.B (level (B := p.B) ci.2) ci.1 ci.2 i ≤ θ)
    (hV : accuracy p < level (B := p.B) ci.2) :
    frozenPlanCost (B := p.B) μ ci.2 θ
      (schedule p.B (fun i => quota p θ (ci.2 i)
        (capacity p.B (level (B := p.B) ci.2) ci.1 i))
          (capacity p.B (level (B := p.B) ci.2) ci.1)) ≤
      100000 * scale p * groupLimit p * imbalance p * (1 + 1 / accuracy p) := by
  let V := level (B := p.B) ci.2
  let C := capacity p.B V ci.1
  let q := fun i => quota p θ (ci.2 i) (C i)
  let J := (1 + Finset.univ.sup (fun i => Nat.log2 (q i)) : ℕ)
  let Q := quotaLoadBound p θ V
  let A := quotaCapacityBound p θ V
  let N : ℝ := (schedule p.B q C).length
  let E := ((schedule p.B q C).map (explorationLoad ci.2)).sum
  let S : ℝ := 1 + (p.k + 1 : ℝ) / p.B
  let G : ℝ := (p.B : ℝ) / (p.k + 1) + 1
  have hχ := scale_ge_one hB hT
  have hd := imbalance_ge_two hB
  have hacc := accuracy_pos hB hT
  have hθpos : 0 < θ := hacc.trans hθ
  have hVpos : 0 < V := hacc.trans hV
  have hBpos : (0 : ℝ) < p.B := by exact_mod_cast hB
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hS : 1 ≤ S := by
    have hh : 0 ≤ (p.k + 1 : ℝ) / p.B := by positivity
    dsimp only [S]
    linarith
  have hgeometry := balanced_geometry hB
  have hSbound : S ≤ 2 * imbalance p := hgeometry.1
  have hGbound : G ≤ 2 * imbalance p := hgeometry.2.1
  have hVbound : V ≤ G := level_le_balanced (fun i => (hci i).2.2.2)
  have hVS : V * S ≤ 2 * imbalance p :=
    (mul_le_mul_of_nonneg_right hVbound (by linarith)).trans hgeometry.2.2
  have hC (i) : 0 < q i → 0 < C i := by
    intro hi
    by_contra hnot
    have hz : C i = 0 := by omega
    have hzq : q i = 0 := by simp only [q, quota, hz, ite_true]
    omega
  have hCB (i) : C i ≤ p.B := capacity_le_batch _ _ _ _
  have hQ : 0 ≤ Q := by dsimp only [Q, quotaLoadBound]; positivity
  have hA : 0 ≤ A := by dsimp only [A, quotaCapacityBound]; positivity
  have hquota := quota_geometry_bounds hB hT ci hci hθpos hD
  have hsum := quota_sum_bound hB hT ci hci hμ hθpos hD hVpos
  have hround := schedule_round_bound hB q C hC hCB hA hquota.2
  have hround' : N ≤ (J : ℝ) * (4 * Q * (p.B + (p.k + 1 : ℝ)) / (V * p.B) +
      2 * A + 2) := by
    have hsum' : (∑ i, (q i : ℝ)) ≤ Q * (p.B + (p.k + 1 : ℝ)) / V := hsum
    calc
      _ ≤ (J : ℝ) * (4 * (∑ i, (q i : ℝ)) / p.B + 2 * A + 2) := hround
      _ ≤ (J : ℝ) * (4 * (Q * (p.B + (p.k + 1 : ℝ)) / V) / p.B + 2 * A + 2) := by
        gcongr
      _ = _ := by ring
  have hexpl : E ≤ (J : ℝ) * (4 * Q * S) := by
    have hh := schedule_exploration_bound hB q C hC
      (fun i => (hci i).1.trans ((hci i).2.1.trans (hci i).2.2.1)) hQ hquota.1
    simpa only [E, J, S, mul_comm, mul_left_comm, mul_assoc] using hh
  have hJlimit : J ≤ groupLimit p := groups_le_limit hB hT hθ ci.2
    (fun i => ⟨(hci i).1.trans ((hci i).2.1.trans (hci i).2.2.1), (hci i).2.2.2⟩) C hCB
  have hJlimit' : (J : ℝ) ≤ groupLimit p := by exact_mod_cast hJlimit
  have hμ0 : 0 ≤ optimum (B := p.B) μ := optimum_nonneg (fun i => (hμ i).le)
  have hχd : imbalance p ≤ scale p * imbalance p := by nlinarith
  change (if V ≤ θ then E + N * (V - optimum (B := p.B) μ) else N * (2 * θ)) ≤ _
  by_cases hcoarse : V ≤ θ
  · rw [ite_eq_left hcoarse]
    have hcoarseq := coarse_quota_bounds hB hT hθpos hVpos.le hcoarse
    have hAV : (2 * A + 2) * V ≤ 1100 * scale p + 6 * V := by
      calc
        _ ≤ (2 * (550 * scale p / θ + 2) + 2) * V := by gcongr; exact hcoarseq.2
        _ = 1100 * scale p * (V / θ) + 6 * V := by ring
        _ ≤ 1100 * scale p * 1 + 6 * V := by
          gcongr
          exact (div_le_one hθpos).mpr hcoarse
        _ = _ := by ring
    have hVN : V * N ≤ (J : ℝ) * (4 * Q * S + (2 * A + 2) * V) := by
      calc
        _ ≤ V * ((J : ℝ) * (4 * Q * (p.B + (p.k + 1 : ℝ)) / (V * p.B) +
            2 * A + 2)) := mul_le_mul_of_nonneg_left hround' hVpos.le
        _ = _ := by dsimp only [S]; field_simp; ring
    have hcost : E + N * (V - optimum (B := p.B) μ) ≤
        (J : ℝ) * (8 * Q * S + (2 * A + 2) * V) := by nlinarith
    have hinner : 8 * Q * S + (2 * A + 2) * V ≤ 25000 * scale p * imbalance p := by
      have hQS : Q * S ≤ 1100 * scale p * (2 * imbalance p) :=
        mul_le_mul hcoarseq.1 hSbound (by linarith) (by positivity)
      have hχle : scale p ≤ scale p * imbalance p := by nlinarith
      nlinarith
    calc
      _ ≤ (J : ℝ) * (25000 * scale p * imbalance p) :=
        hcost.trans (mul_le_mul_of_nonneg_left hinner hJ)
      _ ≤ (groupLimit p : ℝ) * (25000 * scale p * imbalance p) := by gcongr
      _ ≤ _ := by
        have hi : 1 ≤ 1 + 1 / accuracy p := by
          have hh : 0 ≤ 1 / accuracy p := by positivity
          linarith
        nlinarith [mul_nonneg
          (show 0 ≤ (groupLimit p : ℝ) * scale p * imbalance p by positivity)
          (sub_nonneg.mpr hi)]
  · rw [ite_eq_right hcoarse]
    have hfine := fine_quota_bounds hB hT hθpos (le_of_not_ge hcoarse)
    have hcost : N * (2 * θ) ≤ (J : ℝ) *
        (8800 * scale p * V * S / θ + 2200 * scale p * V / θ + 12 * θ) := by
      calc
        _ ≤ ((J : ℝ) * (4 * Q * (p.B + (p.k + 1 : ℝ)) / (V * p.B) +
            2 * A + 2)) * (2 * θ) := mul_le_mul_of_nonneg_right hround' (by positivity)
        _ ≤ ((J : ℝ) *
            (4 * (1100 * scale p * V ^ 2 / θ ^ 2) * (p.B + (p.k + 1 : ℝ)) /
              (V * p.B) + 2 * (550 * scale p * V / θ ^ 2 + 2) + 2)) * (2 * θ) := by
          gcongr
          · exact hfine.1
          · exact hfine.2
        _ = _ := by dsimp only [S]; field_simp; ring
    have hVθ : θ ≤ V := le_of_not_ge hcoarse
    have hinner : 8800 * scale p * V * S / θ + 2200 * scale p * V / θ + 12 * θ ≤
        25000 * scale p * imbalance p * (1 + 1 / accuracy p) := by
      have hVle : V ≤ 2 * imbalance p := hVbound.trans hGbound
      have hVSχ := mul_le_mul_of_nonneg_left hVS (by linarith : 0 ≤ scale p)
      have hVχ := mul_le_mul_of_nonneg_left hVle (by linarith : 0 ≤ scale p)
      have hinv : 1 / θ ≤ 1 / accuracy p := one_div_le_one_div_of_le hacc hθ.le
      have hh : 8800 * scale p * V * S / θ + 2200 * scale p * V / θ ≤
          22000 * scale p * imbalance p / accuracy p := by
        calc
          _ ≤ (8800 * (2 * scale p * imbalance p) +
              2200 * (2 * scale p * imbalance p)) / θ := by
            rw [← add_div]
            apply div_le_div_of_nonneg_right _ hθpos.le
            nlinarith
          _ = 22000 * scale p * imbalance p * (1 / θ) := by ring
          _ ≤ 22000 * scale p * imbalance p * (1 / accuracy p) := by gcongr
          _ = _ := by ring
      have hθbound : 12 * θ ≤ 24 * scale p * imbalance p := by nlinarith
      calc
        _ ≤ 22000 * scale p * imbalance p / accuracy p + 24 * scale p * imbalance p :=
          add_le_add hh hθbound
        _ ≤ 25000 * scale p * imbalance p / accuracy p + 25000 * scale p * imbalance p := by
          apply add_le_add
          · apply div_le_div_of_nonneg_right _ hacc.le
            nlinarith
          · nlinarith
        _ = _ := by ring
    calc
      _ ≤ (J : ℝ) * (25000 * scale p * imbalance p * (1 + 1 / accuracy p)) :=
        hcost.trans (mul_le_mul_of_nonneg_left hinner hJ)
      _ ≤ (groupLimit p : ℝ) * (25000 * scale p * imbalance p * (1 + 1 / accuracy p)) :=
        mul_le_mul_of_nonneg_right hJlimit' (by positivity)
      _ ≤ _ := by
        have hpos : 0 ≤ scale p * groupLimit p * imbalance p * (1 + 1 / accuracy p) := by
          positivity
        nlinarith

end LongTailsOnline.Proofs.TaskAllocation
