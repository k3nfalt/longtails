import LongTails.Proofs.HeavyTailedSospInvariants

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open LongTails.Proofs.HeavyTailedSospExecution
open LongTails.Proofs.HeavyTailedProductProcess

namespace LongTails.Proofs.HeavyTailedSospEpoch

def IsReset (p : Params) : Phase p → Prop
  | .reset .. => True
  | _ => False

def ResetAligned (p : Params) (c : Config) (s : State p) : Prop :=
  IsReset p s.phase → s.virtualIndex % max 1 c.epoch = 0

lemma startCycle_not_reset (p : Params) (c : Config) (s : State p) :
    ¬ IsReset p (startCycle p c s).phase := by
  unfold startCycle
  split_ifs <;> simp [IsReset]

lemma resume_not_reset (p : Params) (c : Config) (s : State p) (r : Resume p) :
    ¬ IsReset p (resume p c s r).phase := by
  cases r with
  | startCycle => exact startCycle_not_reset p c s
  | detect => simp [resume, IsReset]
  | ncRest n v =>
    simp only [resume]
    split_ifs
    · exact startCycle_not_reset p c _
    · simp [IsReset]

lemma completeTransport_aligned (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) :
    ResetAligned p c (completeTransport p c s v z r) := by
  unfold completeTransport
  dsimp only
  split_ifs with h
  · exact fun _ => h
  · exact fun hr => (resume_not_reset p c _ r hr).elim

lemma transportReply_aligned (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p) :
    ResetAligned p c (transportReply p c s v i z reply r) := by
  unfold transportReply
  split_ifs
  · exact fun hr => hr.elim
  · exact completeTransport_aligned p c s v (z + reply) r

lemma probeReply_not_reset (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) :
    ¬ IsReset p (probeReply p c s trial accepted probe reply).phase := by
  unfold probeReply
  dsimp only
  split_ifs <;> simp [IsReset]

lemma update_aligned (p : Params) (c : Config) (s : State p) (a : Aux p c)
    (reply : Space p) (hs : ResetAligned p c s) :
    ResetAligned p c (update p c s a reply) := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [update, hp]
    split_ifs
    · exact fun _ => hs (by simp [hp, IsReset])
    · exact fun hr => (resume_not_reset p c _ r hr).elim
  | transport v i z r =>
    simp only [update, hp]
    exact transportReply_aligned p c s v i z reply r
  | probeInit t accepted =>
    simp only [update, hp]
    exact fun hr => (probeReply_not_reset p c s t accepted _ reply hr).elim
  | probe t accepted probe =>
    simp only [update, hp]
    exact fun hr => (probeReply_not_reset p c s t accepted probe reply hr).elim
  | validate t accepted v values =>
    simp only [update, hp]
    split_ifs
    all_goals first
      | exact fun hr => hr.elim
      | (split
         · exact fun hr => (startCycle_not_reset p c _ hr).elim
         · exact fun hr => hr.elim)
  | ncInit v =>
    simp only [update, hp]
    exact transportReply_aligned p c s _ 0 0 reply _
  | done => simpa [update, hp] using hs

lemma completeTransport_reset_index (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) :
    (completeTransport p c s v z r).virtualIndex = s.virtualIndex + 1 := by
  exact LongTails.Proofs.HeavyTailedSospInvariants.completeTransport_virtualIndex p c s v z r

lemma transportReply_reset_index (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p)
    (hr : IsReset p (transportReply p c s v i z reply r).phase) :
    (transportReply p c s v i z reply r).virtualIndex = s.virtualIndex + 1 := by
  unfold transportReply at hr ⊢
  split_ifs at hr ⊢
  · exact hr.elim
  · exact completeTransport_reset_index p c s v (z + reply) r

lemma update_enter_reset (p : Params) (c : Config) (s : State p) (a : Aux p c)
    (reply : Space p) (hs : ¬ IsReset p s.phase)
    (hr : IsReset p (update p c s a reply).phase) :
    (update p c s a reply).virtualIndex = s.virtualIndex + 1 := by
  cases hp : s.phase with
  | reset i z r => exact (hs (by simp [hp, IsReset])).elim
  | transport v i z r =>
    simp only [update, hp] at hr ⊢
    exact transportReply_reset_index p c s v i z reply r hr
  | probeInit t accepted =>
    simp only [update, hp] at hr
    exact (probeReply_not_reset p c s t accepted _ reply hr).elim
  | probe t accepted probe =>
    simp only [update, hp] at hr
    exact (probeReply_not_reset p c s t accepted probe reply hr).elim
  | validate t accepted v values =>
    simp only [update, hp] at hr
    split_ifs at hr
    all_goals first
      | exact hr.elim
      | (split at hr
         · exact (startCycle_not_reset p c _ hr).elim
         · exact hr.elim)
  | ncInit v =>
    simp only [update, hp] at hr ⊢
    exact transportReply_reset_index p c s _ 0 0 reply _ hr
  | done => exact (hs (by simpa [update, hp] using hr)).elim

lemma trajectory_aligned (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (hs : ResetAligned p c s) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    ResetAligned p c (trajectory (sampleStep p c g H) n s ξ) := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [trajectory_succ_last]
    exact update_aligned p c _ _ _ ih

lemma interior_not_reset (p : Params) (c : Config) (s : State p) (base : ℕ)
    (ha : ResetAligned p c s) (hb : base % max 1 c.epoch = 0)
    (hlo : base < s.virtualIndex) (hhi : s.virtualIndex < base + max 1 c.epoch) :
    ¬ IsReset p s.phase := by
  intro hr
  have hm := ha hr
  have he : s.virtualIndex = base + (s.virtualIndex - base) := by omega
  have hd : s.virtualIndex - base < max 1 c.epoch := by omega
  rw [he, Nat.add_mod, hb, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hd] at hm
  omega

lemma trajectory_virtualIndex_ge (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    s.virtualIndex ≤ (trajectory (sampleStep p c g H) n s ξ).virtualIndex := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [trajectory_succ_last]
    exact ih.trans (LongTails.Proofs.HeavyTailedSospInvariants.update_virtualIndex p c _ _ _).1


lemma trajectory_virtualIndex_le (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    (trajectory (sampleStep p c g H) n s ξ).virtualIndex ≤ s.virtualIndex + n := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    rw [trajectory_succ_last]
    change (update p c _ _ _).virtualIndex ≤ _
    exact (LongTails.Proofs.HeavyTailedSospInvariants.update_virtualIndex p c _ _ _).2.trans (by omega)

lemma epoch_no_reset (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (ha : ResetAligned p c s) (hs : ¬ IsReset p s.phase)
    (hb : s.virtualIndex % max 1 c.epoch = 0)
    (n : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hn : (trajectory (sampleStep p c g H) n s ξ).virtualIndex <
      s.virtualIndex + max 1 c.epoch) :
    ¬ IsReset p (trajectory (sampleStep p c g H) n s ξ).phase := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [trajectory_succ_last] at hn ⊢
    have hmono : (trajectory (sampleStep p c g H) n s ξ).virtualIndex ≤
        (sampleStep p c g H (trajectory (sampleStep p c g H) n s ξ) (ξ n)).virtualIndex :=
      (LongTails.Proofs.HeavyTailedSospInvariants.update_virtualIndex p c _ _ _).1
    have hprev : (trajectory (sampleStep p c g H) n s ξ).virtualIndex <
        s.virtualIndex + max 1 c.epoch := lt_of_le_of_lt hmono hn
    intro hr
    have he := update_enter_reset p c _ (ξ n).1 _ (ih hprev) hr
    have hlo := trajectory_virtualIndex_ge p c g H s n ξ
    have hal := trajectory_aligned p c g H s ha (n + 1) ξ
    rw [trajectory_succ_last] at hal
    exact interior_not_reset p c _ s.virtualIndex hal hb (by
      change s.virtualIndex < (update p c _ _ _).virtualIndex
      rw [he]
      omega) hn hr

def epochFlag (p : Params) : Phase p → ℕ
  | .reset i _ _ => if i = 0 then 0 else 1
  | _ => 1

def epochCharge (p : Params) : Phase p → ℕ
  | .reset i _ _ => if i = 0 then 1 else 0
  | _ => 0

def epochProgress (p : Params) (c : Config) (s : State p) : ℕ :=
  s.virtualIndex / max 1 c.epoch + epochFlag p s.phase

@[simp] lemma startCycle_epochProgress (p : Params) (c : Config) (s : State p) :
    epochProgress p c (startCycle p c s) = s.virtualIndex / max 1 c.epoch + 1 := by
  unfold startCycle
  split_ifs <;> simp [epochProgress, epochFlag]

@[simp] lemma resume_epochProgress (p : Params) (c : Config) (s : State p) (r : Resume p) :
    epochProgress p c (resume p c s r) = s.virtualIndex / max 1 c.epoch + 1 := by
  cases r with
  | startCycle => exact startCycle_epochProgress p c s
  | detect => rfl
  | ncRest n v =>
    simp only [resume]
    split_ifs
    · exact startCycle_epochProgress p c _
    · rfl

lemma completeTransport_epochProgress (p : Params) (c : Config) (s : State p)
    (v z : Space p) (r : Resume p) :
    epochProgress p c (completeTransport p c s v z r) = s.virtualIndex / max 1 c.epoch + 1 := by
  unfold completeTransport
  dsimp only
  split_ifs with h
  · simp only [epochProgress, epochFlag, ↓reduceIte, Nat.add_zero]
    exact Nat.succ_div_of_mod_eq_zero h
  · rw [resume_epochProgress]
    rw [Nat.succ_div_of_mod_ne_zero h]

lemma transportReply_epochProgress (p : Params) (c : Config) (s : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p) :
    epochProgress p c (transportReply p c s v i z reply r) = s.virtualIndex / max 1 c.epoch + 1 := by
  unfold transportReply
  split_ifs
  · rfl
  · exact completeTransport_epochProgress p c s v (z + reply) r

lemma probeReply_epochProgress (p : Params) (c : Config) (s : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) :
    epochProgress p c (probeReply p c s trial accepted probe reply) = s.virtualIndex / max 1 c.epoch + 1 := by
  unfold probeReply
  dsimp only
  split_ifs <;> rfl

lemma update_epochProgress (p : Params) (c : Config) (s : State p) (a : Aux p c)
    (reply : Space p) :
    epochProgress p c (update p c s a reply) = epochProgress p c s + epochCharge p s.phase := by
  cases hp : s.phase with
  | reset i z r =>
    simp only [update, hp]
    split_ifs
    · by_cases hi : i = 0 <;> simp [epochProgress, hp, epochFlag, epochCharge, hi]
    · rw [resume_epochProgress]
      by_cases hi : i = 0 <;> simp [epochProgress, hp, epochFlag, epochCharge, hi]
  | transport v i z r =>
    simp only [update, hp]
    rw [transportReply_epochProgress]
    simp [epochProgress, hp, epochFlag, epochCharge]
  | probeInit t accepted =>
    simp only [update, hp]
    rw [probeReply_epochProgress]
    simp [epochProgress, hp, epochFlag, epochCharge]
  | probe t accepted probe =>
    simp only [update, hp]
    rw [probeReply_epochProgress]
    simp [epochProgress, hp, epochFlag, epochCharge]
  | validate t accepted v values =>
    simp only [update, hp]
    split_ifs
    all_goals solve
      | simp [epochProgress, hp, epochFlag, epochCharge]
      | (split
         · rw [startCycle_epochProgress]; simp [epochProgress, hp, epochFlag, epochCharge]
         · simp [epochProgress, hp, epochFlag, epochCharge])
  | ncInit v =>
    simp only [update, hp]
    rw [transportReply_epochProgress]
    simp [epochProgress, hp, epochFlag, epochCharge]
  | done => simp [update, hp, epochCharge]

lemma trajectory_epochProgress (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    epochProgress p c (trajectory (sampleStep p c g H) n s ξ) = epochProgress p c s +
      ∑ k ∈ Finset.range n, epochCharge p (trajectory (sampleStep p c g H) k s ξ).phase := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    rw [trajectory_succ_last]
    change epochProgress p c (update p c _ _ _) = _
    rw [update_epochProgress, ih, Finset.sum_range_succ, Nat.add_assoc]

lemma completed_epoch_count (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target n : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) n (initial p target) ξ).phase = .done) :
    (∑ k ∈ Finset.range n, epochCharge p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase) =
      (trajectory (sampleStep p c g H) n (initial p target) ξ).virtualIndex / max 1 c.epoch + 1 := by
  have hh := trajectory_epochProgress p c g H (initial p target) n ξ
  have hfinal : epochProgress p c (trajectory (sampleStep p c g H) n (initial p target) ξ) =
      (trajectory (sampleStep p c g H) n (initial p target) ξ).virtualIndex / max 1 c.epoch + 1 := by
    rw [epochProgress, hdone]
    rfl
  have hinit : epochProgress p c (initial p target) = 0 := by simp [epochProgress, initial, epochFlag]
  rw [hfinal, hinit, Nat.zero_add] at hh
  exact hh.symm



lemma prefix_epoch_charge_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    max 1 c.epoch * (∑ k ∈ Finset.range n, epochCharge p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase) ≤
      (trajectory (sampleStep p c g H) n (initial p target) ξ).virtualIndex + max 1 c.epoch := by
  let sn := trajectory (sampleStep p c g H) n (initial p target) ξ
  have hh := trajectory_epochProgress p c g H (initial p target) n ξ
  have hinit : epochProgress p c (initial p target) = 0 := by
    simp [epochProgress, initial, epochFlag]
  rw [hinit, Nat.zero_add] at hh
  have hflag : epochFlag p sn.phase ≤ 1 := by
    cases sn.phase <;> simp only [epochFlag]
    all_goals solve | omega | (split_ifs <;> omega)
  change sn.virtualIndex / max 1 c.epoch + epochFlag p sn.phase = _ at hh
  have hsum : (∑ k ∈ Finset.range n, epochCharge p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase) ≤
      sn.virtualIndex / max 1 c.epoch + 1 := by omega
  have hmul := Nat.mul_le_mul_left (max 1 c.epoch) hsum
  rw [Nat.mul_add, Nat.mul_one] at hmul
  have hdiv := Nat.mod_add_div sn.virtualIndex (max 1 c.epoch)
  change _ ≤ sn.virtualIndex + max 1 c.epoch
  omega

lemma unit_charge_prefix (f : ℕ → ℕ) (hf : ∀ i, f i ≤ 1) (n e : ℕ)
    (he : e < ∑ i ∈ Finset.range n, f i) :
    ∃ k < n, f k = 1 ∧ (∑ i ∈ Finset.range k, f i) = e := by
  induction n with
  | zero => simp at he
  | succ n ih =>
    rw [Finset.sum_range_succ] at he
    by_cases hprev : e < ∑ i ∈ Finset.range n, f i
    · obtain ⟨k, hk, hcharge, hsum⟩ := ih hprev
      exact ⟨k, by omega, hcharge, hsum⟩
    · have hh := hf n
      exact ⟨n, by omega, by omega, by omega⟩

lemma epochCharge_le_one (p : Params) (ph : Phase p) : epochCharge p ph ≤ 1 := by
  cases ph <;> simp only [epochCharge]
  all_goals solve | omega | (split_ifs <;> omega)

lemma epochCharge_reset (p : Params) (ph : Phase p) (hc : epochCharge p ph = 1) :
    ∃ z r, ph = .reset 0 z r := by
  cases ph <;> simp only [epochCharge] at hc
  all_goals try omega
  split_ifs at hc with hi
  · subst hi
    exact ⟨_, _, rfl⟩


lemma marked_epochFlag (p : Params) (ph : Phase p)
    (hm : LongTails.Proofs.HeavyTailedSospInvariants.markCharge p ph = 1) : epochFlag p ph = 1 := by
  cases ph <;> simp_all [epochFlag, LongTails.Proofs.HeavyTailedSospInvariants.markCharge]

lemma marked_epoch_start (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target n : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hm : LongTails.Proofs.HeavyTailedSospInvariants.markCharge p
      (trajectory (sampleStep p c g H) n (initial p target) ξ).phase = 1) :
    ∃ k < n, epochCharge p (trajectory (sampleStep p c g H) k (initial p target) ξ).phase = 1 ∧
      (trajectory (sampleStep p c g H) k (initial p target) ξ).virtualIndex / max 1 c.epoch =
        (trajectory (sampleStep p c g H) n (initial p target) ξ).virtualIndex / max 1 c.epoch := by
  let X := fun i => trajectory (sampleStep p c g H) i (initial p target) ξ
  have hinit : epochProgress p c (initial p target) = 0 := by
    simp [epochProgress, initial, epochFlag]
  have hn := trajectory_epochProgress p c g H (initial p target) n ξ
  rw [hinit, Nat.zero_add] at hn
  have hflag := marked_epochFlag p _ hm
  rw [epochProgress, hflag] at hn
  change (X n).virtualIndex / max 1 c.epoch + 1 =
    ∑ i ∈ Finset.range n, epochCharge p (X i).phase at hn
  obtain ⟨k, hk, hc, hsum⟩ := unit_charge_prefix
    (fun i => epochCharge p (X i).phase) (fun i => epochCharge_le_one p _) n
    ((X n).virtualIndex / max 1 c.epoch) (by omega)
  refine ⟨k, hk, hc, ?_⟩
  obtain ⟨z, r, hph⟩ := epochCharge_reset p (X k).phase hc
  have hkledger := trajectory_epochProgress p c g H (initial p target) k ξ
  rw [hinit, Nat.zero_add] at hkledger
  change epochProgress p c (X k) = _ at hkledger
  rw [epochProgress, hph] at hkledger
  simp only [epochFlag, ↓reduceIte, Nat.add_zero] at hkledger
  exact hkledger.trans hsum

def ZeroReset (p : Params) : Phase p → Prop
  | .reset i z _ => i = 0 → z = 0
  | _ => True

lemma startCycle_zeroReset (p : Params) (c : Config) (state : State p) :
    ZeroReset p (startCycle p c state).phase := by
  unfold startCycle
  split_ifs <;> simp [ZeroReset]

lemma resume_zeroReset (p : Params) (c : Config) (state : State p) (r : Resume p) :
    ZeroReset p (resume p c state r).phase := by
  cases r with
  | startCycle => exact startCycle_zeroReset p c state
  | detect => trivial
  | ncRest n v =>
    simp only [resume]
    split_ifs
    · exact startCycle_zeroReset p c _
    · simp [ZeroReset]

lemma completeTransport_zeroReset (p : Params) (c : Config) (state : State p)
    (v z : Space p) (r : Resume p) :
    ZeroReset p (completeTransport p c state v z r).phase := by
  unfold completeTransport
  dsimp only
  split_ifs
  · simp [ZeroReset]
  · exact resume_zeroReset p c _ r

lemma transportReply_zeroReset (p : Params) (c : Config) (state : State p)
    (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p) :
    ZeroReset p (transportReply p c state v i z reply r).phase := by
  unfold transportReply
  split_ifs
  · simp [ZeroReset]
  · exact completeTransport_zeroReset p c state v (z + reply) r

lemma probeReply_zeroReset (p : Params) (c : Config) (state : State p)
    (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) :
    ZeroReset p (probeReply p c state trial accepted probe reply).phase := by
  unfold probeReply
  dsimp only
  split_ifs <;> trivial

lemma update_zeroReset (p : Params) (c : Config) (state : State p)
    (a : Aux p c) (reply : Space p) :
    ZeroReset p (update p c state a reply).phase := by
  cases hp : state.phase <;> simp only [update, hp]
  · split_ifs
    · simp [ZeroReset]
    · exact resume_zeroReset p c _ _
  · exact transportReply_zeroReset p c _ _ _ _ _ _
  · exact probeReply_zeroReset p c _ _ _ _ _
  · exact probeReply_zeroReset p c _ _ _ _ _
  · split_ifs
    all_goals first
      | trivial
      | (split
         · exact startCycle_zeroReset p c _
         · trivial)
  · exact transportReply_zeroReset p c _ _ _ _ _ _
  · trivial

lemma trajectory_zeroReset (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (hs : ZeroReset p s.phase) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    ZeroReset p (trajectory (sampleStep p c g H) n s ξ).phase := by
  cases n with
  | zero => exact hs
  | succ n =>
    rw [trajectory_succ_last]
    exact update_zeroReset p c _ _ _


lemma reachable_epoch_start (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target n : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hc : epochCharge p (trajectory (sampleStep p c g H) n (initial p target) ξ).phase = 1) :
    ∃ r, (trajectory (sampleStep p c g H) n (initial p target) ξ).phase = .reset 0 0 r ∧
      (trajectory (sampleStep p c g H) n (initial p target) ξ).virtualIndex % max 1 c.epoch = 0 := by
  obtain ⟨z, r, hph⟩ := epochCharge_reset p _ hc
  have hz := trajectory_zeroReset p c g H (initial p target)
    (by simp [initial, ZeroReset]) n ξ
  rw [hph] at hz
  have hz0 : z = 0 := hz rfl
  subst z
  have ha := trajectory_aligned p c g H (initial p target)
    (by simp [ResetAligned, initial]) n ξ
  exact ⟨r, hph, ha (by simp [hph, IsReset])⟩

end LongTails.Proofs.HeavyTailedSospEpoch
