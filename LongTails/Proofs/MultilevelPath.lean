import LongTails.Proofs.MultilevelPacketMoments
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace LongTails.Proofs.MultilevelPath

open LongTails.Setups.DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelPipeline
open LongTails.Algorithms.MultilevelWorkerSchedule
open LongTails.Algorithms.MultilevelTransport (Bits)
open LongTails.Algorithms.DistributedQuantization (receive)
open MultilevelTimetable MultilevelInformation MultilevelPacketMoments MultilevelTrajectory MultilevelWorkerSchedule

noncomputable def top (p : Params) (k : ℕ) : Job :=
  if 2^(height p) ≤ k then activeJob (height p) k else none

noncomputable def fine (p : Params) (k : ℕ) :=
  (Finset.range (height p)).filter fun j => 2^j ≤ k

noncomputable def path (p : Params) (k : ℕ) : Finset Job :=
  insert (top p k) ((fine p k).image (fun j => activeJob j k))

noncomputable def weight (p : Params) (k r : ℕ) : ℝ :=
  let a := (entry p r).1
  if a ∈ path p k then ((reservations p a).card : ℝ)⁻¹ else 0

lemma top_not_fine (p : Params) (k : ℕ) : top p k ∉ (fine p k).image (fun j => activeJob j k) := by
  intro h
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
  have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  unfold top at he
  split at he <;> simp_all [activeJob]

lemma path_cells (p : Params) {k : ℕ} (hk : k ≤ wanted p) : path p k ⊆ cells p := by
  intro a h
  rcases Finset.mem_insert.mp h with rfl | h
  · unfold top
    split
    · rename_i he
      exact level_cells p le_rfl ((active_due _ k he).trans hk)
    · simp [cells]
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hj,hw⟩ := Finset.mem_filter.mp hj
    exact level_cells p (Finset.mem_range.mp hj).le ((active_due _ k hw).trans hk)

lemma path_sum {A : Type*} [AddCommMonoid A] (p : Params) (k : ℕ) (F : Job → A) :
    ∑ a ∈ path p k, F a = F (top p k) +
      ∑ j ∈ Finset.range (height p), if 2^j ≤ k then F (activeJob j k) else 0 := by
  rw [path,Finset.sum_insert (top_not_fine p k), Finset.sum_image, fine, Finset.sum_filter]
  intro a _ b _ he
  simpa [activeJob] using congrArg (fun x : Job => x.map Prod.fst) he

lemma path_size (p : Params) (k : ℕ) : (path p k).card ≤ height p + 1 := by
  have hi := Finset.card_image_le (s := fine p k) (f := fun j => activeJob j k)
  have hf := Finset.card_filter_le (s := Finset.range (height p)) (fun j => 2^j ≤ k)
  rw [path,Finset.card_insert_of_notMem (top_not_fine _ _)]
  apply Nat.add_le_add_right
  exact hi.trans (by simpa [fine] using hf)

lemma samples_number (p : Params) (hh : ∀ i, 0 < p.h i) {job : Job} (hj : job ∈ cells p) :
    (reservations p job).card = match job with
      | none => fullBatch p
      | some (j,_) => multilevelBatch (height p) (fullBatch p) j := by
  cases job with
  | none =>
    exact (reserve_spec _ _ (available_capacity _ (physical_pos p hh) _ _ _ (by simp [warmTime]))).2
  | some u => exact job_samples _ (physical_pos p hh) _ _ _ _ (in_level hj).1 _

lemma samples_pos (p : Params) (hh : ∀ i, 0 < p.h i) {job : Job} (hj : job ∈ cells p) :
    0 < (reservations p job).card := by
  rw [samples_number _ hh hj]
  cases job with
  | none => exact full_units p
  | some u =>
    rcases u with ⟨j,s⟩
    simp only [multilevelBatch]
    split
    · exact full_units p
    · unfold edgeBatch
      positivity

lemma sum_rows {A : Type*} [AddCommMonoid A] (p : Params) (s : Finset Job) (hs : s ⊆ cells p)
    (F : Entry p → A) :
    (∑ i ∈ Finset.range (table p).length, if (entry p i).1 ∈ s then F (entry p i) else 0) =
      ∑ job ∈ s, ∑ z ∈ reservations p job, F (job,z) := by
  classical
  rw [← Finset.sum_filter, Finset.sum_sigma']
  let forward (i : ℕ) : (j : Job) × Slot (physical p) := ⟨(entry p i).1,(entry p i).2⟩
  let back (z : (j : Job) × Slot (physical p)) := (table p).idxOf (z.1,z.2)
  have hmem {i : ℕ} (hi : i < (table p).length) : entry p i ∈ table p := by
    rw [entry_at p hi]; exact List.getElem_mem ..
  have hback {z : (j : Job) × Slot (physical p)} (hz : z ∈ s.sigma (reservations p)) :
      (z.1,z.2) ∈ table p :=
    mem_table.mpr ⟨hs (Finset.mem_sigma.mp hz).1,(Finset.mem_sigma.mp hz).2⟩
  apply Finset.sum_bij' (fun i _ => forward i) (fun z _ => back z)
  · intro i hi
    obtain ⟨h₁,h₂⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_sigma.mpr ⟨h₂,(mem_table.mp (hmem (Finset.mem_range.mp h₁))).2⟩
  · intro z hz
    have he := entry_of_mem p (hback hz)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (List.idxOf_lt_length_of_mem (hback hz)),
      by simpa [back,he] using (Finset.mem_sigma.mp hz).1⟩
  · intro i hi
    have hl := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    simp [back,forward,entry_at p hl,(table_nodup p).idxOf_getElem]
  · intro z hz
    cases z with
    | mk j a =>
      have he := entry_of_mem p (hback hz)
      simp [forward,back,he]
  · intro i _; rfl

lemma average_representation (p : Params) (b : ℕ → Bits) {k : ℕ} (hk : k ≤ wanted p) :
    estimate p b k = ∑ i ∈ Finset.range (table p).length,
      weight p k i • receive p.d (width p) (valueSpacing p) (b i) := by
  let F := fun e : Entry p => ((reservations p e.1).card : ℝ)⁻¹ •
    receive p.d (width p) (valueSpacing p) (b ((table p).idxOf e))
  have h := sum_rows p (path p k) (path_cells p hk) F
  change average p b (top p k) + _ = _
  rw [← path_sum p k (average p b)]
  calc
    _ = ∑ a ∈ path p k, ∑ z ∈ reservations p a, F (a,z) := by simp [average,F,Finset.smul_sum]
    _ = _ := h.symm.trans (Finset.sum_congr rfl (by
      intro i hi
      have hidx : (table p).idxOf (entry p i) = i := by
        simp [entry_at p (Finset.mem_range.mp hi),(table_nodup p).idxOf_getElem]
      by_cases hm : (entry p i).1 ∈ path p k <;> simp [weight,F,hidx,hm]))

lemma weighted_jobs {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Params) (hh : ∀ i, 0 < p.h i) {k : ℕ} (hk : k ≤ wanted p) (F : Job → E) :
    (∑ i ∈ Finset.range (table p).length, weight p k i • F (entry p i).1) =
      ∑ job ∈ path p k, F job := by
  let v := fun job => ((reservations p job).card:ℝ)⁻¹
  have h := sum_rows p (path p k) (path_cells p hk) (fun e => v e.1 • F e.1)
  calc
    _ = _ := (Finset.sum_congr rfl (fun i _ => by
      by_cases hm : (entry p i).1 ∈ path p k <;> simp [weight,v,hm])).trans h
    _ = _ := Finset.sum_congr rfl fun job hj => by
      have hc : ((reservations p job).card:ℝ) ≠ 0 := by exact_mod_cast (samples_pos p hh (path_cells p hk hj)).ne'
      simp [v,← Nat.cast_smul_eq_nsmul ℝ,smul_smul,hc]

lemma weight_sum (p : Params) (hh : ∀ i, 0 < p.h i) {k : ℕ} (hk : k ≤ wanted p) :
    ∑ i ∈ Finset.range (table p).length, weight p k i = ((path p k).card : ℝ) := by
  simpa only [smul_eq_mul,mul_one,Finset.sum_const,nsmul_eq_mul] using weighted_jobs p hh hk (fun _ => (1:ℝ))

lemma weight_nonneg (p : Params) (k i : ℕ) : 0 ≤ weight p k i := by
  dsimp only [weight]
  split <;> positivity

lemma variance_weight (p : Params) (hh : ∀ i, 0 < p.h i) {k : ℕ} (hk : k ≤ wanted p) :
    (∑ i ∈ Finset.range (table p).length, weight p k i ^ 2 * units p (entry p i).1) ≤ 17 := by
  let v := fun job => ((reservations p job).card:ℝ)⁻¹ * (units p job : ℝ)
  have hw := weighted_jobs p hh hk v
  have he (i : ℕ) : weight p k i ^ 2 * units p (entry p i).1 = weight p k i • v (entry p i).1 := by
    by_cases hm : (entry p i).1 ∈ path p k <;> simp [weight,v,hm,pow_two,mul_assoc]
  simp_rw [he]
  rw [hw,path_sum]
  have hS : (fullBatch p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (full_units p))
  have htop : v (top p k) = 1 := by
    have ht := path_cells p hk (Finset.mem_insert_self (top p k) _)
    unfold top at ht ⊢
    split <;> rename_i h
    · simp only [h,ite_true] at ht
      dsimp only [v]
      rw [samples_number p hh ht]
      simp [activeJob,multilevelBatch,units,hS]
    · simp only [h,ite_false] at ht
      simp [v,samples_number p hh ht,units,hS]
  rw [htop]
  have heach (j : ℕ) (hj : j ∈ Finset.range (height p)) :
      (if 2^j ≤ k then v (activeJob j k) else 0) ≤ 16/(height p+1 : ℕ) := by
    by_cases he : 2^j ≤ k
    · have hlt := Finset.mem_range.mp hj
      have ht := level_cells p hlt.le ((active_due j k he).trans hk)
      simp only [he,ite_true,v,samples_number p hh ht,activeJob,units,multilevelBatch,hlt.ne,ite_false,edgeBatch,
        Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
      apply le_of_eq
      field_simp
    · simp [he]
      positivity
  have hs := Finset.sum_le_sum heach
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  have hpos : (0:ℝ) < (height p+1:ℕ) := by positivity
  have hmul : (height p:ℝ) * (16 / (height p+1:ℕ)) ≤ 16 := by
    rw [← mul_div_assoc, div_le_iff₀ hpos]
    push_cast
    linarith
  linarith

lemma target_telescope (p : Params) (b : ℕ → Bits) (k : ℕ) (G : Point p → Point p) :
    ∑ job ∈ path p k, target p b job G = G (gridPoint p b (anchor 1 k)) := by
  let F := fun j => G (gridPoint p b (anchor (2^j) k))
  have ht : target p b (top p k) G = F (height p) := by
    unfold top
    split
    · simp [F,activeJob,snapshot,target,source,anchor]
    · rename_i hn
      have hz : k / 2^height p = 0 := Nat.div_eq_of_lt (lt_of_not_ge hn)
      simp [F,snapshot,target,source,anchor,hz]
  have he (j : ℕ) (hj : j < height p) :
      (if 2^j ≤ k then target p b (activeJob j k) G else 0) = F j - F (j+1) := by
    by_cases h : 2^j ≤ k
    · have hpar := parent_at_release (2^j) k (by positivity) h
      simp [F,h,activeJob,target,snapshot,hj.ne,source,parent,hpar,show 2^(j+1)=2*2^j by ring,anchor]
    · have hz : k / 2^j = 0 := Nat.div_eq_of_lt (lt_of_not_ge h)
      have hz' : k / 2^(j+1) = 0 := Nat.div_eq_of_lt ((lt_of_not_ge h).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))
      simp [F,h,anchor,hz,hz']
  rw [path_sum,ht,Finset.sum_congr rfl (fun j hj => he j (Finset.mem_range.mp hj)),Finset.sum_range_sub']
  simp [F]

lemma stale (p : Params) (f : Point p → ℝ) (hL : 0 < p.L) (he : 0 < p.ε)
    (hlip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ p.L*‖x-y‖)
    (b : ℕ → Bits) {k : ℕ} (hk : k ≤ wanted p) :
    ‖gradient f (gridPoint p b (anchor 1 k)) - gradient f (iterate p b k)‖ ≤ 2*precision p := by
  have ha := anchor_le 1 k
  have hd := displacement p b (stride_pos p hL he).le (anchor 1 k) (k-anchor 1 k)
  rw [Nat.add_sub_of_le ha, norm_sub_rev] at hd
  have hone : k-anchor 1 k ≤ 1 := by simp [anchor]; omega
  have hv := hd.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hone : ((k-anchor 1 k:ℕ):ℝ) ≤ (1:ℕ)) (stride_pos p hL he).le)
  have hq := point_error p hL he b (anchor 1 k) (ha.trans hk)
  have h := norm_sub_le_norm_sub_add_norm_sub (gridPoint p b (anchor 1 k)) (iterate p b (anchor 1 k)) (iterate p b k)
  have hid : p.L * stride p = precision p := by unfold stride; field_simp
  refine (hlip _ _).trans ((mul_le_mul_of_nonneg_left (h.trans (add_le_add hq hv)) hL.le).trans ?_)
  simp only [Nat.cast_one,one_mul,mul_add,hid]
  linarith

end LongTails.Proofs.MultilevelPath
