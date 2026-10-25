import LongTails.Proofs.HeavyTailedSospNoise
import LongTails.Proofs.GapStrongGrowthIteration

open MeasureTheory
open LongTails.Proofs.HeavyTailedProductProcess
open OracleTemplate.ContinuizedSimilarQuasar
open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open LongTails.Proofs.HeavyTailedSospExecution

namespace LongTails.Proofs.HeavyTailedSospEpochIntegration


lemma trajectory_finite {S Ω : Type*} (advance : S → Ω → S)
    (n : ℕ) (s : S) (ξ : ℕ → Ω) :
    trajectory advance n s ξ = iterateSamples advance n s (fun i => ξ i) := by
  induction n generalizing s ξ with
  | zero => rfl
  | succ n ih => exact ih _ _


lemma finite_iterate_stream {S Ω : Type*} (advance : S → Ω → S)
    (n : ℕ) (hn : 0 < n) (s : S) (η : Fin n → Ω) :
    ∃ ξ : ℕ → Ω, iterateSamples advance n s η = trajectory advance n s ξ := by
  let ξ : ℕ → Ω := fun i => η ⟨i % n, Nat.mod_lt i hn⟩
  refine ⟨ξ, ?_⟩
  rw [trajectory_finite]
  congr 1
  funext i
  simp [ξ, Nat.mod_eq_of_lt i.isLt]


lemma finite_iterate_invariant {S Ω : Type*} (advance : S → Ω → S) (Inv : S → Prop)
    (hp : ∀ s ω, Inv s → Inv (advance s ω)) (n : ℕ) (s : S) (hs : Inv s)
    (η : Fin n → Ω) : Inv (iterateSamples advance n s η) := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih => exact ih _ (hp s (η 0) hs) (fun i => η i.succ)

lemma finite_initial_invariants (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (target n : ℕ) (η : Fin n → Aux p c × p.Ω) :
    let sn := iterateSamples (sampleStep p c g H) n (initial p target) η
    HeavyTailedSospInvariants.PhaseValid p c sn.phase ∧
      HeavyTailedSospGeometry.PhaseBound p c.h sn.phase ∧
      HeavyTailedSospEpoch.ZeroReset p sn.phase ∧ HeavyTailedSospEpoch.ResetAligned p c sn := by
  apply finite_iterate_invariant (sampleStep p c g H)
    (fun sn => HeavyTailedSospInvariants.PhaseValid p c sn.phase ∧
      HeavyTailedSospGeometry.PhaseBound p c.h sn.phase ∧
      HeavyTailedSospEpoch.ZeroReset p sn.phase ∧ HeavyTailedSospEpoch.ResetAligned p c sn)
  · intro sn z hv
    exact ⟨HeavyTailedSospInvariants.update_valid p c sn z.1 _ hv.1,
      HeavyTailedSospGeometry.update_bound p c sn z.1 _ hd hh hs hseg hv.2.1,
      HeavyTailedSospEpoch.update_zeroReset p c sn z.1 _,
      HeavyTailedSospEpoch.update_aligned p c sn z.1 _ hv.2.2.2⟩
  · exact ⟨HeavyTailedSospInvariants.initial_valid p c target,
      HeavyTailedSospGeometry.initial_bound p c target,
      by simp [initial, HeavyTailedSospEpoch.ZeroReset],
      by simp [initial, HeavyTailedSospEpoch.ResetAligned]⟩

lemma trajectory_add {S Ω : Type*} (advance : S → Ω → S)
    (m n : ℕ) (s : S) (ξ : ℕ → Ω) :
    trajectory advance (m + n) s ξ =
      trajectory advance n (trajectory advance m s ξ) (fun k => ξ (m + k)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ, trajectory_succ_last, ih, trajectory_succ_last]


lemma reset_finishes_before_mark (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (k t : ℕ) (ξ : ℕ → Aux p c × p.Ω) (hkt : k ≤ t) (r : Resume p)
    (hr : (trajectory (sampleStep p c g H) k s ξ).phase = .reset 0 0 r)
    (hm : HeavyTailedSospInvariants.markCharge p
      (trajectory (sampleStep p c g H) t s ξ).phase = 1) : k + max 1 c.resetBatch ≤ t := by
  by_contra hbad
  have hlen : t - k < max 1 c.resetBatch := by omega
  have hx : trajectory (sampleStep p c g H) t s ξ =
      trajectory (sampleStep p c g H) (t - k)
        (trajectory (sampleStep p c g H) k s ξ) (fun i => ξ (k + i)) := by
    simpa only [Nat.add_sub_of_le hkt] using
      trajectory_add (sampleStep p c g H) k (t - k) s ξ
  have hs : trajectory (sampleStep p c g H) k s ξ =
      { trajectory (sampleStep p c g H) k s ξ with phase := .reset 0 0 r } := by
    rw [← hr]
  have hlocal := HeavyTailedSospReset.reset_prefix p c g H
    (trajectory (sampleStep p c g H) k s ξ) r (fun i => ξ (k + i)) (t - k) hlen
  rw [← hs] at hlocal
  rw [hx, hlocal] at hm
  simp [HeavyTailedSospInvariants.markCharge] at hm



lemma reset_suffix_virtualIndex (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (k : ℕ) (ξ : ℕ → Aux p c × p.Ω) (r : Resume p)
    (hr : (trajectory (sampleStep p c g H) k s ξ).phase = .reset 0 0 r) :
    (trajectory (sampleStep p c g H) (k + max 1 c.resetBatch) s ξ).virtualIndex =
      (trajectory (sampleStep p c g H) k s ξ).virtualIndex := by
  have hs : trajectory (sampleStep p c g H) k s ξ =
      { trajectory (sampleStep p c g H) k s ξ with phase := .reset 0 0 r } := by
    rw [← hr]
  have hlocal := HeavyTailedSospReset.reset_complete p c g H
    (trajectory (sampleStep p c g H) k s ξ) r (fun i => ξ (k + i))
  rw [← hs] at hlocal
  rw [trajectory_add, hlocal, HeavyTailedSospReset.resume_virtualIndex]

lemma marked_reset_owner (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target t : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hm : HeavyTailedSospInvariants.markCharge p
      (trajectory (sampleStep p c g H) t (initial p target) ξ).phase = 1) :
    ∃ k < t, ∃ r,
      HeavyTailedSospEpoch.epochCharge p
        (trajectory (sampleStep p c g H) k (initial p target) ξ).phase = 1 ∧
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase = .reset 0 0 r ∧
      k + max 1 c.resetBatch ≤ t ∧
      (trajectory (sampleStep p c g H) t (initial p target) ξ).virtualIndex <
        (trajectory (sampleStep p c g H) k (initial p target) ξ).virtualIndex + max 1 c.epoch := by
  obtain ⟨k, hkt, hc, hdiv⟩ := HeavyTailedSospEpoch.marked_epoch_start p c g H target t ξ hm
  obtain ⟨r, hr, hmod⟩ := HeavyTailedSospEpoch.reachable_epoch_start p c g H target k ξ hc
  refine ⟨k, hkt, r, hc, hr,
    reset_finishes_before_mark p c g H (initial p target) k t ξ hkt.le r hr hm, ?_⟩
  have htk := Nat.mod_add_div
    (trajectory (sampleStep p c g H) t (initial p target) ξ).virtualIndex (max 1 c.epoch)
  have hkk := Nat.mod_add_div
    (trajectory (sampleStep p c g H) k (initial p target) ξ).virtualIndex (max 1 c.epoch)
  have hsmall := Nat.mod_lt
    (trajectory (sampleStep p c g H) t (initial p target) ξ).virtualIndex
    (show 0 < max 1 c.epoch by omega)
  rw [hmod, Nat.zero_add, hdiv] at hkk
  omega


lemma finite_sum_injection_bound {I J : Type*} [DecidableEq J]
    (A : Finset I) (B : Finset J) (f : I → ℝ) (g : J → ℝ) (φ : I → J)
    (hφ : ∀ i ∈ A, φ i ∈ B) (hinj : ∀ i ∈ A, ∀ j ∈ A, φ i = φ j → i = j)
    (hweight : ∀ i ∈ A, f i ≤ g (φ i)) (hnon : ∀ j ∈ B, 0 ≤ g j) :
    (∑ i ∈ A, f i) ≤ ∑ j ∈ B, g j := by
  calc
    _ ≤ ∑ i ∈ A, g (φ i) := Finset.sum_le_sum hweight
    _ = ∑ j ∈ A.image φ, g j := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro j hj; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj; exact hφ i hi)
      (fun j hj _ => hnon j hj)

lemma offset_cover_sum (N B : ℕ) (A K : Finset ℕ) (f : ℕ → ℝ) (g : ℕ × ℕ → ℝ)
    (hA : ∀ t ∈ A, t < N) (hf : ∀ w, 0 ≤ g w)
    (hcover : ∀ t ∈ A, ∃ k ∈ K, k + B ≤ t ∧ f t ≤ g (k, t - (k + B))) :
    (∑ t ∈ A, f t) ≤ ∑ k ∈ K, ∑ i ∈ Finset.range N, g (k, i) := by
  classical
  let owner : ℕ → ℕ := fun t => if ht : t ∈ A then (hcover t ht).choose else 0
  have howner (t : ℕ) (ht : t ∈ A) : owner t ∈ K ∧ owner t + B ≤ t ∧
      f t ≤ g (owner t, t - (owner t + B)) := by
    simpa [owner, ht] using (hcover t ht).choose_spec
  have hh := finite_sum_injection_bound A (K ×ˢ Finset.range N) f g
    (fun t => (owner t, t - (owner t + B)))
    (fun t ht => Finset.mem_product.mpr ⟨(howner t ht).1,
      Finset.mem_range.mpr (lt_of_le_of_lt (Nat.sub_le _ _) (hA t ht))⟩)
    (by
      intro t ht u hu heq
      have hk := congrArg Prod.fst heq
      have hi := congrArg Prod.snd heq
      have ht' := (howner t ht).2.1
      have hu' := (howner u hu).2.1
      dsimp only at hk hi
      omega)
    (fun t ht => (howner t ht).2.2) (fun w _ => hf w)
  simpa only [Finset.sum_product] using hh


lemma global_epoch_cover (p : Params) (c : Config)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    let X := fun t => trajectory (sampleStep p c g H) t (initial p target) ξ
    let Y := fun k i => trajectory (sampleStep p c g H) i (X (k + max 1 c.resetBatch))
      (fun j => ξ (k + max 1 c.resetBatch + j))
    (∑ t ∈ Finset.range N, if HeavyTailedSospInvariants.markCharge p (X t).phase = 1 then
      ‖(X t).estimate - G (X t).point‖ else 0) ≤
      ∑ k ∈ Finset.range N, if HeavyTailedSospEpoch.epochCharge p (X k).phase = 1 then
        ∑ i ∈ Finset.range N, if HeavyTailedSospInvariants.markCharge p (Y k i).phase = 1 ∧
          (Y k i).virtualIndex < (X (k + max 1 c.resetBatch)).virtualIndex + max 1 c.epoch then
          ‖(Y k i).estimate - G (Y k i).point‖ else 0 else 0 := by
  classical
  intro X Y
  let A := (Finset.range N).filter (fun t => HeavyTailedSospInvariants.markCharge p (X t).phase = 1)
  let K := (Finset.range N).filter (fun k => HeavyTailedSospEpoch.epochCharge p (X k).phase = 1)
  let f := fun t => ‖(X t).estimate - G (X t).point‖
  let F := fun w : ℕ × ℕ => if HeavyTailedSospInvariants.markCharge p (Y w.1 w.2).phase = 1 ∧
      (Y w.1 w.2).virtualIndex < (X (w.1 + max 1 c.resetBatch)).virtualIndex + max 1 c.epoch then
      ‖(Y w.1 w.2).estimate - G (Y w.1 w.2).point‖ else 0
  have hcover (t : ℕ) (ht : t ∈ A) : ∃ k ∈ K, k + max 1 c.resetBatch ≤ t ∧
      f t ≤ F (k, t - (k + max 1 c.resetBatch)) := by
    obtain ⟨htN, hmark⟩ := Finset.mem_filter.mp ht
    obtain ⟨k, hkt, r, hc, hr, hfinished, hwithin⟩ := marked_reset_owner p c g H target t ξ hmark
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (hkt.trans (Finset.mem_range.mp htN)), hc⟩, hfinished, ?_⟩
    have hxy : Y k (t - (k + max 1 c.resetBatch)) = X t := by
      dsimp only [Y, X]
      symm
      simpa only [Nat.add_sub_of_le hfinished] using
        trajectory_add (sampleStep p c g H) (k + max 1 c.resetBatch)
          (t - (k + max 1 c.resetBatch)) (initial p target) ξ
    have hV := reset_suffix_virtualIndex p c g H (initial p target) k ξ r hr
    change (X (k + max 1 c.resetBatch)).virtualIndex = (X k).virtualIndex at hV
    change (X t).virtualIndex < (X k).virtualIndex + max 1 c.epoch at hwithin
    change HeavyTailedSospInvariants.markCharge p (X t).phase = 1 at hmark
    dsimp only [F]
    rw [hxy, hV]
    simp only [hmark, hwithin, and_self, ↓reduceIte]
    exact le_rfl
  have hh := offset_cover_sum N (max 1 c.resetBatch) A K f F
    (fun t ht => Finset.mem_range.mp (Finset.mem_filter.mp ht).1)
    (by intro w; dsimp only [F]; split_ifs <;> positivity) hcover
  simpa only [A, K, f, F, Finset.sum_filter] using hh

lemma global_endpoint_sum_bound (p : Params) (c : Config)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    let X := fun t => trajectory (sampleStep p c g H) t (initial p target) ξ
    (∑ t ∈ Finset.range N, if HeavyTailedSospInvariants.markCharge p (X t).phase = 1 then
      ‖(X t).estimate - G (X t).point‖ else 0) ≤
      ∑ k ∈ Finset.range N, if HeavyTailedSospEpoch.epochCharge p (X k).phase = 1 then
        ∑ j ∈ Finset.Icc 1 (max 1 c.epoch),
          ‖HeavyTailedSospStopped.endpointError p c (X (k + max 1 c.resetBatch)).virtualIndex G
            (trajectory (HeavyTailedSospStopped.step p c (X (k + max 1 c.resetBatch)).virtualIndex
              j g H) N (X (k + max 1 c.resetBatch), 0)
              (fun i => ξ (k + max 1 c.resetBatch + i))).1‖ else 0 := by
  intro X
  refine (global_epoch_cover p c G g H target N ξ).trans ?_
  apply Finset.sum_le_sum
  intro k hk
  split_ifs
  · exact HeavyTailedSospStopped.epoch_endpoint_sum_bound p c G g H
      (X (k + max 1 c.resetBatch)) N (fun i => ξ (k + max 1 c.resetBatch + i))
  · exact le_rfl


noncomputable def epochEndpoint (p : Params) (c : Config) (ordinal n : ℕ)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (ξ : ℕ → Aux p c × p.Ω) : Space p :=
  let sn := trajectory (sampleStep p c g H) (max 1 c.resetBatch) s ξ
  HeavyTailedSospStopped.endpointError p c sn.virtualIndex G
    (trajectory (HeavyTailedSospStopped.step p c sn.virtualIndex ordinal g H) n (sn, 0)
      (fun k => ξ (max 1 c.resetBatch + k))).1


lemma epochEndpoint_reset_eq (p : Params) (c : Config) (ordinal n : ℕ)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (r : Resume p) (ξ : ℕ → Aux p c × p.Ω) :
    epochEndpoint p c ordinal n G g H { s with phase := .reset 0 0 r } ξ =
      HeavyTailedSospStopped.endpointError p c s.virtualIndex G
        (trajectory (HeavyTailedSospStopped.step p c s.virtualIndex ordinal g H) n
          (trajectory (sampleStep p c g H) (max 1 c.resetBatch)
            { s with phase := .reset 0 0 r } ξ, 0)
          (fun k => ξ (max 1 c.resetBatch + k))).1 := by
  have hV : (trajectory (sampleStep p c g H) (max 1 c.resetBatch)
      { s with phase := .reset 0 0 r } ξ).virtualIndex = s.virtualIndex := by
    rw [HeavyTailedSospReset.reset_complete, HeavyTailedSospReset.resume_virtualIndex]
  simp only [epochEndpoint, hV]

lemma epochEndpoint_suffix (p : Params) (c : Config) (ordinal n : ℕ)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (k : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    epochEndpoint p c ordinal n G g H (trajectory (sampleStep p c g H) k s ξ)
      (fun i => ξ (k + i)) =
      let sn := trajectory (sampleStep p c g H) (k + max 1 c.resetBatch) s ξ
      HeavyTailedSospStopped.endpointError p c sn.virtualIndex G
        (trajectory (HeavyTailedSospStopped.step p c sn.virtualIndex ordinal g H) n (sn, 0)
          (fun i => ξ (k + max 1 c.resetBatch + i))).1 := by
  simp only [epochEndpoint, ← trajectory_add, Nat.add_assoc]

set_option maxHeartbeats 800000 in
lemma measurable_endpoint_trajectory (p : Params) (c : Config) (ordinal n : ℕ)
    (G : Space p → Space p) (hG : Measurable G)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H)) :
    Measurable (fun w : State p × (ℕ → Aux p c × p.Ω) =>
      HeavyTailedSospStopped.endpointError p c w.1.virtualIndex G
        (trajectory (HeavyTailedSospStopped.step p c w.1.virtualIndex ordinal g H) n (w.1, 0) w.2).1) := by
  have hparam : Measurable (fun w : ℕ × (State p × (ℕ → Aux p c × p.Ω)) =>
      HeavyTailedSospStopped.endpointError p c w.1 G
        (trajectory (HeavyTailedSospStopped.step p c w.1 ordinal g H) n (w.2.1, 0) w.2.2).1) := by
    apply measurable_from_prod_countable_right
    intro base
    have hstate : Measurable (fun w : State p × (ℕ → Aux p c × p.Ω) =>
        trajectory (HeavyTailedSospStopped.step p c base ordinal g H) n (w.1, 0) w.2) :=
      (trajectory_measurable (HeavyTailedSospStopped.measurable_step p c base ordinal g H hg hH) n).comp
        ((measurable_fst.prodMk (measurable_const (a := (0 : ℕ)))).prodMk measurable_snd)
    exact (HeavyTailedSospStopped.measurable_endpointError p c base G hG).comp hstate.fst
  have hin : Measurable (fun w : State p × (ℕ → Aux p c × p.Ω) => (w.1.virtualIndex, w)) :=
    ((HeavyTailedSospMeasurable.measurable_virtualIndex p).comp measurable_fst).prodMk measurable_id
  exact hparam.comp hin

set_option maxHeartbeats 800000 in
lemma measurable_epochEndpoint (p : Params) (c : Config) (ordinal n : ℕ)
    (G : Space p → Space p) (hG : Measurable G)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (epochEndpoint p c ordinal n G g H)) := by
  have hpost : Measurable (fun w : State p × (ℕ → Aux p c × p.Ω) =>
      trajectory (sampleStep p c g H) (max 1 c.resetBatch) w.1 w.2) :=
    trajectory_measurable (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH)
      (max 1 c.resetBatch)
  have htail : Measurable (fun w : State p × (ℕ → Aux p c × p.Ω) =>
      fun k => w.2 (max 1 c.resetBatch + k)) :=
    Measurable.of_eval (fun k => (measurable_pi_apply (max 1 c.resetBatch + k)).comp measurable_snd)
  simpa only [epochEndpoint, Function.uncurry_def, Function.comp_def] using
    (measurable_endpoint_trajectory p c ordinal n G hG g hg H hH).comp (hpost.prodMk htail)

lemma measurable_epochCharge (p : Params) : Measurable (HeavyTailedSospEpoch.epochCharge p) := by
  have hh : Measurable (Function.uncurry (fun ph (_ : Unit) => HeavyTailedSospEpoch.epochCharge p ph)) := by
    apply HeavyTailedSospMeasurable.measurable_phase_uncurry p
    · dsimp only [HeavyTailedSospEpoch.epochCharge]
      apply Measurable.ite
      · exact measurableSet_eq_fun (by fun_prop) measurable_const
      · exact measurable_const
      · exact measurable_const
    all_goals exact measurable_const
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))


noncomputable def chargedEndpoint (p : Params) (c : Config) (ordinal n : ℕ)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (ξ : ℕ → Aux p c × p.Ω) : ℝ :=
  if HeavyTailedSospEpoch.epochCharge p s.phase = 1 then
    ‖epochEndpoint p c ordinal n G g H s ξ‖ else 0

lemma measurable_chargedEndpoint (p : Params) (c : Config) (ordinal n : ℕ)
    (G : Space p → Space p) (hG : Measurable G)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (chargedEndpoint p c ordinal n G g H)) := by
  apply Measurable.ite
  · exact measurableSet_eq_fun ((measurable_epochCharge p).comp
      ((HeavyTailedSospMeasurable.measurable_phase p).comp measurable_fst)) measurable_const
  · exact (measurable_epochEndpoint p c ordinal n G hG g hg H hH).norm
  · exact measurable_const

lemma chargedEndpoint_nonneg (p : Params) (c : Config) (ordinal n : ℕ)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (ξ : ℕ → Aux p c × p.Ω) : 0 ≤ chargedEndpoint p c ordinal n G g H s ξ := by
  unfold chargedEndpoint
  split_ifs <;> positivity

lemma charged_endpoint_fiber_bound (p : Params) (c : Config) (ordinal n : ℕ)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (P : Measure (ℕ → Aux p c × p.Ω)) (s : State p) (e : ℝ)
    (hv : HeavyTailedSospInvariants.PhaseValid p c s.phase)
    (hb : HeavyTailedSospGeometry.PhaseBound p c.h s.phase)
    (hz : HeavyTailedSospEpoch.ZeroReset p s.phase)
    (ha : HeavyTailedSospEpoch.ResetAligned p c s)
    (hreset : ∀ r, HeavyTailedSospInvariants.ResumeValid p c r →
      HeavyTailedSospGeometry.ResumeBound p c.h r → s.virtualIndex % max 1 c.epoch = 0 →
      Integrable (fun ξ => ‖epochEndpoint p c ordinal n G g H { s with phase := .reset 0 0 r } ξ‖) P ∧
        (∫ ξ, ‖epochEndpoint p c ordinal n G g H { s with phase := .reset 0 0 r } ξ‖ ∂P) ≤ e) :
    Integrable (chargedEndpoint p c ordinal n G g H s) P ∧
      (∫ ξ, chargedEndpoint p c ordinal n G g H s ξ ∂P) ≤
        if HeavyTailedSospEpoch.epochCharge p s.phase = 1 then e else 0 := by
  by_cases hc : HeavyTailedSospEpoch.epochCharge p s.phase = 1
  · obtain ⟨z, r, hr⟩ := HeavyTailedSospEpoch.epochCharge_reset p s.phase hc
    have hz0 : z = 0 := by
      rw [hr] at hz
      exact hz rfl
    subst z
    have hrv : HeavyTailedSospInvariants.ResumeValid p c r := by
      rw [hr] at hv
      exact hv.2
    have hrb : HeavyTailedSospGeometry.ResumeBound p c.h r := by
      simpa only [hr, HeavyTailedSospGeometry.PhaseBound] using hb
    have hmod := ha (by simp [hr, HeavyTailedSospEpoch.IsReset])
    have hs : { s with phase := .reset 0 0 r } = s := by rw [← hr]
    have hh := hreset r hrv hrb hmod
    rw [hs] at hh
    have hfun : chargedEndpoint p c ordinal n G g H s =
        fun ξ => ‖epochEndpoint p c ordinal n G g H s ξ‖ := by
      funext ξ
      simp only [chargedEndpoint, hc, ↓reduceIte]
    rw [hfun]
    simpa only [hc, ↓reduceIte] using hh
  · have hfun : chargedEndpoint p c ordinal n G g H s = fun _ => 0 := by
      funext ξ
      simp only [chargedEndpoint, hc, ↓reduceIte]
    rw [hfun]
    simp [hc]


noncomputable def markedErrorTotal (p : Params) (c : Config)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (target n : ℕ)
    (ξ : ℕ → Aux p c × p.Ω) : ℝ :=
  ∑ k ∈ Finset.range n, if HeavyTailedSospInvariants.markCharge p
      (trajectory (sampleStep p c g H) k (initial p target) ξ).phase = 1 then
    ‖(trajectory (sampleStep p c g H) k (initial p target) ξ).estimate -
      G (trajectory (sampleStep p c g H) k (initial p target) ξ).point‖ else 0

lemma measurable_markedErrorTotal (p : Params) (c : Config)
    (G : Space p → Space p) (hG : Measurable G)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (target n : ℕ) : Measurable (markedErrorTotal p c G g H target n) := by
  apply Finset.measurable_sum
  intro k hk
  have hX : Measurable (fun ξ : ℕ → Aux p c × p.Ω =>
      trajectory (sampleStep p c g H) k (initial p target) ξ) :=
    (trajectory_measurable (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) k).comp
      ((measurable_const (a := initial p target)).prodMk measurable_id)
  apply Measurable.ite
  · exact measurableSet_eq_fun ((HeavyTailedSospStopped.measurable_markCharge p).comp
      ((HeavyTailedSospMeasurable.measurable_phase p).comp hX)) measurable_const
  · exact (((HeavyTailedSospMeasurable.measurable_estimate p).comp hX).sub
      (hG.comp ((HeavyTailedSospMeasurable.measurable_point p).comp hX))).norm
  · exact measurable_const

lemma virtualIndex_integrable (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (Q : Measure (Aux p c × p.Ω)) [IsProbabilityMeasure Q] (target n : ℕ) :
    Integrable (fun ξ : ℕ → Aux p c × p.Ω =>
      ((trajectory (sampleStep p c g H) n (initial p target) ξ).virtualIndex : ℝ))
      (Measure.infinitePi fun _ : ℕ => Q) := by
  have hX : Measurable (fun ξ : ℕ → Aux p c × p.Ω =>
      trajectory (sampleStep p c g H) n (initial p target) ξ) :=
    (trajectory_measurable (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) n).comp
      ((measurable_const (a := initial p target)).prodMk measurable_id)
  have hm : Measurable (fun ξ : ℕ → Aux p c × p.Ω =>
      ((trajectory (sampleStep p c g H) n (initial p target) ξ).virtualIndex : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      ((HeavyTailedSospMeasurable.measurable_virtualIndex p).comp hX)
  apply (integrable_const (n : ℝ)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have hh := HeavyTailedSospEpoch.trajectory_virtualIndex_le p c g H (initial p target) n ξ
  simp only [initial, Nat.zero_add] at hh
  exact_mod_cast hh

lemma fresh_continuation_bound {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (advance : S → Ω → S)
    (ha : Measurable (Function.uncurry advance)) (n : ℕ) (s : S)
    (F : S × (ℕ → Ω) → ℝ) (hF : Measurable F) (hnon : ∀ w, 0 ≤ F w)
    (W : (Fin n → Ω) → ℝ)
    (hW : Integrable W (Measure.pi fun _ : Fin n => P))
    (hi : ∀ η, Integrable (fun ξ => F (iterateSamples advance n s η, ξ))
      (Measure.infinitePi fun _ : ℕ => P))
    (hb : ∀ η, (∫ ξ, F (iterateSamples advance n s η, ξ)
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ W η) :
    Integrable (fun ξ => F (trajectory advance n s ξ, fun k => ξ (n + k)))
      (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, F (trajectory advance n s ξ, fun k => ξ (n + k))
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ ∫ η, W η ∂Measure.pi (fun _ : Fin n => P) := by
  let F' := fun w : (Fin n → Ω) × (ℕ → Ω) => F (iterateSamples advance n s w.1, w.2)
  have hprefix : Measurable (fun η : Fin n → Ω => iterateSamples advance n s η) :=
    (OracleTemplate.GapStrongGrowth.iterateSamples_measurable ha n).comp
      ((measurable_const (a := s)).prodMk measurable_id)
  have hFm : Measurable F' := hF.comp ((hprefix.comp measurable_fst).prodMk measurable_snd)
  have hprod := WeakGradientConvolution.nonnegative_fiber_integral_bound
    (P := Measure.pi fun _ : Fin n => P) (Q := Measure.infinitePi fun _ : ℕ => P)
    hFm.stronglyMeasurable (fun w => hnon _) (Filter.Eventually.of_forall hi) hW
    (Filter.Eventually.of_forall hb)
  have hsplit := OracleTemplate.StochasticGeneralized.splitStream_preserving P n
  have heq : (fun ξ => F (trajectory advance n s ξ, fun k => ξ (n + k))) =
      F' ∘ OracleTemplate.StochasticGeneralized.splitStream n := by
    funext ξ
    change F (trajectory advance n s ξ, _) = F (iterateSamples advance n s (fun i => ξ i), _)
    rw [trajectory_finite]
    rfl
  rw [heq]
  refine ⟨hsplit.integrable_comp_of_integrable hprod.1, ?_⟩
  simpa only [Function.comp_def, hsplit.integral_comp' F'] using hprod.2


lemma prefix_charged_endpoint_bound (p : Params) (c : Config) (ordinal n k target : ℕ)
    (G : Space p → Space p) (hG : Measurable G)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (Q : Measure (Aux p c × p.Ω)) [IsProbabilityMeasure Q]
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h) (e : ℝ)
    (hreset : ∀ (s : State p) (r : Resume p), HeavyTailedSospInvariants.ResumeValid p c r →
      HeavyTailedSospGeometry.ResumeBound p c.h r → s.virtualIndex % max 1 c.epoch = 0 →
      Integrable (fun ξ => ‖epochEndpoint p c ordinal n G g H { s with phase := .reset 0 0 r } ξ‖)
        (Measure.infinitePi fun _ : ℕ => Q) ∧
      (∫ ξ, ‖epochEndpoint p c ordinal n G g H { s with phase := .reset 0 0 r } ξ‖
        ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤ e) :
    let X := fun ξ => trajectory (sampleStep p c g H) k (initial p target) ξ
    let F := fun ξ => chargedEndpoint p c ordinal n G g H (X ξ) (fun i => ξ (k + i))
    Integrable F (Measure.infinitePi fun _ : ℕ => Q) ∧
      (∫ ξ, F ξ ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
        ∫ ξ, (if HeavyTailedSospEpoch.epochCharge p (X ξ).phase = 1 then e else 0)
          ∂Measure.infinitePi (fun _ : ℕ => Q) := by
  intro X F
  let W := fun η : Fin k → Aux p c × p.Ω =>
    if HeavyTailedSospEpoch.epochCharge p
      (iterateSamples (sampleStep p c g H) k (initial p target) η).phase = 1 then e else 0
  have hprefix : Measurable (fun η : Fin k → Aux p c × p.Ω =>
      iterateSamples (sampleStep p c g H) k (initial p target) η) :=
    (OracleTemplate.GapStrongGrowth.iterateSamples_measurable
      (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) k).comp
      ((measurable_const (a := initial p target)).prodMk measurable_id)
  have hset : MeasurableSet {η : Fin k → Aux p c × p.Ω |
      HeavyTailedSospEpoch.epochCharge p
        (iterateSamples (sampleStep p c g H) k (initial p target) η).phase = 1} :=
    measurableSet_eq_fun ((measurable_epochCharge p).comp
      ((HeavyTailedSospMeasurable.measurable_phase p).comp hprefix)) measurable_const
  have hW : Integrable W (Measure.pi fun _ : Fin k => Q) := by
    have hcst : Integrable (fun _ : Fin k → Aux p c × p.Ω => e)
        (Measure.pi fun _ : Fin k => Q) := integrable_const e
    have heq : W = {η : Fin k → Aux p c × p.Ω |
        HeavyTailedSospEpoch.epochCharge p
          (iterateSamples (sampleStep p c g H) k (initial p target) η).phase = 1}.indicator (fun _ => e) := by
      funext η
      simp [W, Set.indicator_apply]
    rw [heq]
    exact hcst.indicator hset
  have hWm : Measurable W := Measurable.ite hset measurable_const measurable_const
  have hfiber (η : Fin k → Aux p c × p.Ω) :=
    finite_initial_invariants p c g H hd hh hs hseg target k η
  have hb (η : Fin k → Aux p c × p.Ω) := charged_endpoint_fiber_bound p c ordinal n G g H
    (Measure.infinitePi fun _ : ℕ => Q)
    (iterateSamples (sampleStep p c g H) k (initial p target) η) e
    (hfiber η).1 (hfiber η).2.1 (hfiber η).2.2.1 (hfiber η).2.2.2
    (hreset _)
  have hsplit := fresh_continuation_bound Q (sampleStep p c g H)
    (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) k (initial p target)
    (Function.uncurry (chargedEndpoint p c ordinal n G g H))
    (measurable_chargedEndpoint p c ordinal n G hG g hg H hH)
    (fun w => chargedEndpoint_nonneg p c ordinal n G g H w.1 w.2) W hW
    (fun η => (hb η).1) (fun η => (hb η).2)
  refine ⟨hsplit.1, hsplit.2.trans_eq ?_⟩
  have hpre := OracleTemplate.StochasticGeneralized.prefix_preserving Q k
  rw [← hpre.map_eq, integral_map hpre.measurable.aemeasurable hWm.aestronglyMeasurable]
  simp only [W, X, trajectory_finite]


lemma expected_marked_error_bound (p : Params) (c : Config)
    (G : Space p → Space p) (hG : Measurable G)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (Q : Measure (Aux p c × p.Ω)) [IsProbabilityMeasure Q]
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h) (target N : ℕ) (e : ℝ) (he : 0 ≤ e)
    (hreset : ∀ j ∈ Finset.Icc 1 (max 1 c.epoch), ∀ (s : State p) (r : Resume p),
      HeavyTailedSospInvariants.ResumeValid p c r → HeavyTailedSospGeometry.ResumeBound p c.h r →
      s.virtualIndex % max 1 c.epoch = 0 →
      Integrable (fun ξ => ‖epochEndpoint p c j N G g H { s with phase := .reset 0 0 r } ξ‖)
        (Measure.infinitePi fun _ : ℕ => Q) ∧
      (∫ ξ, ‖epochEndpoint p c j N G g H { s with phase := .reset 0 0 r } ξ‖
        ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤ e) :
    Integrable (markedErrorTotal p c G g H target N) (Measure.infinitePi fun _ : ℕ => Q) ∧
      (∫ ξ, markedErrorTotal p c G g H target N ξ ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
        e * ((∫ ξ, ((trajectory (sampleStep p c g H) N (initial p target) ξ).virtualIndex : ℝ)
          ∂Measure.infinitePi (fun _ : ℕ => Q)) + max 1 c.epoch) := by
  let X := fun k ξ => trajectory (sampleStep p c g H) k (initial p target) ξ
  let F := fun k j ξ => chargedEndpoint p c j N G g H (X k ξ) (fun i => ξ (k + i))
  let W := fun k ξ => if HeavyTailedSospEpoch.epochCharge p (X k ξ).phase = 1 then e else 0
  let U := fun ξ => ∑ k ∈ Finset.range N, ∑ j ∈ Finset.Icc 1 (max 1 c.epoch), F k j ξ
  let V := fun ξ => ((X N ξ).virtualIndex : ℝ)
  have hpref (k j : ℕ) (hj : j ∈ Finset.Icc 1 (max 1 c.epoch)) :=
    prefix_charged_endpoint_bound p c j N k target G hG g hg H hH Q hd hh hs hseg e (hreset j hj)
  have hFi (k j : ℕ) (hj : j ∈ Finset.Icc 1 (max 1 c.epoch)) :
      Integrable (F k j) (Measure.infinitePi fun _ : ℕ => Q) := (hpref k j hj).1
  have hWi (k : ℕ) : Integrable (W k) (Measure.infinitePi fun _ : ℕ => Q) := by
    have hX : Measurable (X k) :=
      (trajectory_measurable (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) k).comp
        ((measurable_const (a := initial p target)).prodMk measurable_id)
    have hset : MeasurableSet {ξ : ℕ → Aux p c × p.Ω |
        HeavyTailedSospEpoch.epochCharge p (X k ξ).phase = 1} :=
      measurableSet_eq_fun ((measurable_epochCharge p).comp
        ((HeavyTailedSospMeasurable.measurable_phase p).comp hX)) measurable_const
    have hcst : Integrable (fun _ : ℕ → Aux p c × p.Ω => e)
        (Measure.infinitePi fun _ : ℕ => Q) := integrable_const e
    have heq : W k = {ξ : ℕ → Aux p c × p.Ω |
        HeavyTailedSospEpoch.epochCharge p (X k ξ).phase = 1}.indicator (fun _ => e) := by
      funext ξ
      simp [W, Set.indicator_apply]
    rw [heq]
    exact hcst.indicator hset
  have hUi : Integrable U (Measure.infinitePi fun _ : ℕ => Q) :=
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun j hj => hFi k j hj))
  have hWsum : Integrable (fun ξ => ∑ k ∈ Finset.range N,
      ∑ _j ∈ Finset.Icc 1 (max 1 c.epoch), W k ξ) (Measure.infinitePi fun _ : ℕ => Q) :=
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun _ _ => hWi k))
  have hVi : Integrable V (Measure.infinitePi fun _ : ℕ => Q) :=
    virtualIndex_integrable p c g hg H hH Q target N
  have hRi := (hVi.add (integrable_const ((max 1 c.epoch : ℕ) : ℝ))).const_mul e
  have hcount (ξ : ℕ → Aux p c × p.Ω) :
      (∑ k ∈ Finset.range N, ∑ _j ∈ Finset.Icc 1 (max 1 c.epoch), W k ξ) ≤
        e * (V ξ + max 1 c.epoch) := by
    have hw (k : ℕ) : W k ξ = (HeavyTailedSospEpoch.epochCharge p (X k ξ).phase : ℝ) * e := by
      by_cases hc : HeavyTailedSospEpoch.epochCharge p (X k ξ).phase = 1
      · simp [W, hc]
      · have hzero : HeavyTailedSospEpoch.epochCharge p (X k ξ).phase = 0 := by
          have hb := HeavyTailedSospEpoch.epochCharge_le_one p (X k ξ).phase
          omega
        simp [W, hzero]
    have hcard : (Finset.Icc 1 (max 1 c.epoch)).card = max 1 c.epoch := by simp
    have hsum : (∑ k ∈ Finset.range N, ∑ _j ∈ Finset.Icc 1 (max 1 c.epoch), W k ξ) =
        (((max 1 c.epoch : ℕ) : ℝ) * ∑ k ∈ Finset.range N,
          (HeavyTailedSospEpoch.epochCharge p (X k ξ).phase : ℝ)) * e := by
      simp_rw [hw]
      simp only [Finset.sum_const, hcard, nsmul_eq_mul,
        ← Finset.mul_sum, ← Finset.sum_mul, mul_assoc]
    have hnat := HeavyTailedSospEpoch.prefix_epoch_charge_bound p c g H target N ξ
    have hreal : ((max 1 c.epoch : ℕ) : ℝ) * (∑ k ∈ Finset.range N,
        (HeavyTailedSospEpoch.epochCharge p (X k ξ).phase : ℝ)) ≤ V ξ + max 1 c.epoch := by
      dsimp only [V, X]
      exact_mod_cast hnat
    rw [hsum]
    simpa only [mul_comm e] using mul_le_mul_of_nonneg_right hreal he
  have hcover (ξ : ℕ → Aux p c × p.Ω) : markedErrorTotal p c G g H target N ξ ≤ U ξ := by
    simpa only [markedErrorTotal, U, F, X, chargedEndpoint, epochEndpoint_suffix, Finset.sum_ite_irrel, Finset.sum_const_zero] using
      global_endpoint_sum_bound p c G g H target N ξ
  have hnon (ξ : ℕ → Aux p c × p.Ω) : 0 ≤ markedErrorTotal p c G g H target N ξ := by
    apply Finset.sum_nonneg
    intro k hk
    split_ifs <;> positivity
  have hEi : Integrable (markedErrorTotal p c G g H target N)
      (Measure.infinitePi fun _ : ℕ => Q) := hUi.mono'
    (measurable_markedErrorTotal p c G hG g hg H hH target N).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnon ξ)]
      exact hcover ξ))
  refine ⟨hEi, ?_⟩
  calc
    _ ≤ ∫ ξ, U ξ ∂Measure.infinitePi (fun _ : ℕ => Q) := integral_mono hEi hUi hcover
    _ ≤ ∫ ξ, ∑ k ∈ Finset.range N, ∑ _j ∈ Finset.Icc 1 (max 1 c.epoch), W k ξ
        ∂Measure.infinitePi (fun _ : ℕ => Q) := by
      rw [show U = fun ξ => ∑ k ∈ Finset.range N,
        ∑ j ∈ Finset.Icc 1 (max 1 c.epoch), F k j ξ from rfl]
      rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun j hj => hFi k j hj)),
        integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun _ _ => hWi k))]
      apply Finset.sum_le_sum
      intro k hk
      rw [integral_finsetSum _ (fun j hj => hFi k j hj), integral_finsetSum _ (fun _ _ => hWi k)]
      exact Finset.sum_le_sum (fun j hj => (hpref k j hj).2)
    _ ≤ ∫ ξ, e * (V ξ + max 1 c.epoch) ∂Measure.infinitePi (fun _ : ℕ => Q) :=
      integral_mono hWsum hRi hcount
    _ = _ := by
      rw [integral_const_mul, integral_add hVi (integrable_const _), integral_const]
      simp [V, X]

lemma prefix_moment_transfer {E Ω : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (F : (Fin n → Ω) → E)
    (hF : Measurable F) {α M : ℝ}
    (hi : Integrable (fun ξ : ℕ → Ω => ‖F (fun i => ξ i)‖ ^ α)
      (Measure.infinitePi fun _ : ℕ => P))
    (hb : (∫ ξ : ℕ → Ω, ‖F (fun i => ξ i)‖ ^ α
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ M) :
    Integrable (fun η => ‖F η‖ ^ α) (Measure.pi fun _ : Fin n => P) ∧
      (∫ η, ‖F η‖ ^ α ∂Measure.pi (fun _ : Fin n => P)) ≤ M := by
  have hpre := OracleTemplate.StochasticGeneralized.prefix_preserving P n
  refine ⟨(hpre.integrable_comp (hF.norm.pow_const α).aestronglyMeasurable).mp hi, ?_⟩
  rw [← hpre.map_eq]
  rw [integral_map hpre.measurable.aemeasurable (hF.norm.pow_const α).aestronglyMeasurable]
  exact hb


lemma norm_integral_bound {E Ω : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Ω → E) (hF : Measurable F)
    {α M : ℝ} (hα : 1 < α) (hi : Integrable (fun ω => ‖F ω‖ ^ α) P)
    (hb : (∫ ω, ‖F ω‖ ^ α ∂P) ≤ M) :
    Integrable (fun ω => ‖F ω‖) P ∧ (∫ ω, ‖F ω‖ ∂P) ≤ M ^ (1 / α) := by
  refine ⟨?_, ?_⟩
  · simpa using integrable_norm_rpow_of_le hF.aestronglyMeasurable
      (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ α) hα.le hi
  · exact (HeavyTailedMomentBounds.integral_norm_le_root_moment hα
      hF.aestronglyMeasurable hi).trans
      (Real.rpow_le_rpow (integral_nonneg (fun ω => Real.rpow_nonneg (norm_nonneg _) _))
        hb (by positivity))


lemma fresh_continuation_root_bound {S E Ω : Type*} [MeasurableSpace S]
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (advance : S → Ω → S)
    (ha : Measurable (Function.uncurry advance)) (n : ℕ) (s : S)
    (F : S × (ℕ → Ω) → ℝ) (hF : Measurable F) (hnon : ∀ w, 0 ≤ F w)
    (E0 : S → E) (hE0 : Measurable E0) {α M K : ℝ} (hα : 1 < α)
    (hpi : Integrable (fun η : Fin n → Ω => ‖E0 (iterateSamples advance n s η)‖ ^ α)
      (Measure.pi fun _ : Fin n => P))
    (hpb : (∫ η : Fin n → Ω, ‖E0 (iterateSamples advance n s η)‖ ^ α
      ∂Measure.pi (fun _ : Fin n => P)) ≤ M)
    (hi : ∀ η, Integrable (fun ξ => F (iterateSamples advance n s η, ξ))
      (Measure.infinitePi fun _ : ℕ => P))
    (hb : ∀ η, (∫ ξ, F (iterateSamples advance n s η, ξ)
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ ‖E0 (iterateSamples advance n s η)‖ + K) :
    Integrable (fun ξ => F (trajectory advance n s ξ, fun k => ξ (n + k)))
      (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, F (trajectory advance n s ξ, fun k => ξ (n + k))
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ M ^ (1 / α) + K := by
  have hEm : Measurable (fun η : Fin n → Ω => E0 (iterateSamples advance n s η)) :=
    hE0.comp ((OracleTemplate.GapStrongGrowth.iterateSamples_measurable ha n).comp
      ((measurable_const (a := s)).prodMk measurable_id))
  have hroot := norm_integral_bound (Measure.pi fun _ : Fin n => P) _ hEm hα hpi hpb
  have hsplit := fresh_continuation_bound P advance ha n s F hF hnon
    (fun η => ‖E0 (iterateSamples advance n s η)‖ + K)
    (hroot.1.add (integrable_const K)) hi hb
  refine ⟨hsplit.1, hsplit.2.trans ?_⟩
  rw [integral_add hroot.1 (integrable_const K), integral_const]
  simpa using add_le_add hroot.2 (le_refl K)

lemma measurable_estimator_error (p : LongTails.Setups.HeavyTailedHessianVector.Params)
    (c : LongTails.Algorithms.HeavyTailedSosp.Config)
    (G : LongTails.Setups.HeavyTailedHessianVector.Space p → LongTails.Setups.HeavyTailedHessianVector.Space p)
    (hG : Measurable G) : Measurable (HeavyTailedSospEstimator.error p c G) := by
  have hpartial : Measurable (Function.uncurry
      (fun ph x => HeavyTailedSospEstimator.partialError p c G x ph)) := by
    apply HeavyTailedSospMeasurable.measurable_phase_uncurry p
    all_goals simp only [HeavyTailedSospEstimator.partialError]
    all_goals fun_prop
  exact ((HeavyTailedSospMeasurable.measurable_estimate p).sub
    (hG.comp (HeavyTailedSospMeasurable.measurable_point p))).add
    (hpartial.comp ((HeavyTailedSospMeasurable.measurable_phase p).prodMk
      (HeavyTailedSospMeasurable.measurable_point p)))


lemma finite_reset_conditions (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (r : Resume p) (hh : 0 ≤ c.h)
    (hv : HeavyTailedSospInvariants.ResumeValid p c r)
    (hb : HeavyTailedSospGeometry.ResumeBound p c.h r)
    (η : Fin (max 1 c.resetBatch) → Aux p c × p.Ω) :
    let sn := iterateSamples (sampleStep p c g H) (max 1 c.resetBatch)
      { s with phase := .reset 0 0 r } η
    HeavyTailedSospInvariants.PhaseValid p c sn.phase ∧
      HeavyTailedSospGeometry.PhaseBound p c.h sn.phase ∧
      HeavyTailedSospEstimator.ZeroPartial p sn.phase ∧
      ¬ HeavyTailedSospEpoch.IsReset p sn.phase ∧
      sn.virtualIndex = s.virtualIndex ∧
      HeavyTailedSospInvariants.transportPartial p sn.phase = 0 := by
  intro sn
  obtain ⟨ξ, heq⟩ := finite_iterate_stream (sampleStep p c g H) (max 1 c.resetBatch)
    (by omega) { s with phase := .reset 0 0 r } η
  dsimp only [sn]
  rw [heq, HeavyTailedSospReset.reset_complete]
  exact ⟨HeavyTailedSospInvariants.resume_valid p c _ r hv,
    HeavyTailedSospGeometry.resume_bound p c _ r hh hb,
    HeavyTailedSospEstimator.resume_zeroPartial p c _ r,
    HeavyTailedSospEpoch.resume_not_reset p c _ r,
    HeavyTailedSospReset.resume_virtualIndex p c _ r,
    HeavyTailedSospInvariants.resume_transportPartial p c _ r⟩

lemma finite_reset_moment (p : Params) (c : Config) (P : Measure p.Ω) [IsProbabilityMeasure P]
    (G : Space p → Space p) (hG : Measurable G)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (s : State p) (r : Resume p) {α κ : ℝ} (hα : 1 ≤ α) (hα2 : α ≤ 2)
    (hi : Integrable (fun ω => g s.point ω - G s.point) P)
    (hm : (∫ ω, g s.point ω - G s.point ∂P) = 0)
    (hpi : Integrable (fun ω => ‖g s.point ω - G s.point‖ ^ α) P)
    (hb : (∫ ω, ‖g s.point ω - G s.point‖ ^ α ∂P) ≤ κ) :
    let Q := (auxLaw p c).toMeasure.prod P
    let E := fun η : Fin (max 1 c.resetBatch) → Aux p c × p.Ω =>
      HeavyTailedSospEstimator.error p c G (iterateSamples (sampleStep p c g H)
        (max 1 c.resetBatch) { s with phase := .reset 0 0 r } η)
    Integrable (fun η => ‖E η‖ ^ α) (Measure.pi fun _ : Fin (max 1 c.resetBatch) => Q) ∧
      (∫ η, ‖E η‖ ^ α ∂Measure.pi (fun _ : Fin (max 1 c.resetBatch) => Q)) ≤
        6 * κ / ((max 1 c.resetBatch : ℕ) : ℝ) ^ (α - 1) := by
  intro Q E
  have hEm : Measurable E := (measurable_estimator_error p c G hG).comp
    ((OracleTemplate.GapStrongGrowth.iterateSamples_measurable
      (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) (max 1 c.resetBatch)).comp
      ((measurable_const (a := ({ s with phase := .reset 0 0 r } : State p))).prodMk measurable_id))
  have hmoment := HeavyTailedSospReset.reset_execution_moment p c P g H s r (G s.point)
    (by
      have hgm : StronglyMeasurable (g s.point) :=
        (hg.comp ((measurable_const (a := s.point)).prodMk measurable_id)).stronglyMeasurable
      let : MeasurableSpace (Space p) := WithLp.measurableSpace 2 (Fin p.d → ℝ)
      exact hgm.measurable) hα hα2 hi hm hpi hb
  have heq (ξ : ℕ → Aux p c × p.Ω) : E (fun i => ξ i) =
      (trajectory (sampleStep p c g H) (max 1 c.resetBatch)
        { s with phase := .reset 0 0 r } ξ).estimate - G s.point := by
    dsimp only [E]
    rw [← trajectory_finite, HeavyTailedSospEstimator.reset_error_identity,
      HeavyTailedSospReset.reset_complete_estimate]
  apply prefix_moment_transfer Q (max 1 c.resetBatch) E hEm
  · simpa only [heq] using hmoment.1
  · simpa only [heq] using hmoment.2

lemma reset_endpoint_integral_bound (p : Params) (c : Config) (ordinal : ℕ)
    (P : Measure p.Ω) [IsProbabilityMeasure P] (G : Space p → Space p)
    (hG : Differentiable ℝ G) (hD : Continuous (fderiv ℝ G))
    {ρ σ α : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hd : 0 < p.d)
    (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h) (hα : 1 < α) (hα2 : α ≤ 2)
    (hLip : ∀ x y, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ ρ * ‖x - y‖)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (hi : ∀ y v, Integrable (fun ω => H y ω v) P)
    (hm : ∀ y v, (∫ ω, H y ω v ∂P) = fderiv ℝ G y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖H y ω v - fderiv ℝ G y v‖ ^ α) P)
    (hb : ∀ y v, (∫ ω, ‖H y ω v - fderiv ℝ G y v‖ ^ α ∂P) ≤ σ ^ α * ‖v‖ ^ α)
    (n : ℕ) (s : State p) (r : Resume p)
    (hv : HeavyTailedSospInvariants.ResumeValid p c r)
    (hbound : HeavyTailedSospGeometry.ResumeBound p c.h r)
    (halign : s.virtualIndex % max 1 c.epoch = 0) {κ : ℝ}
    (hgi : Integrable (fun ω => g s.point ω - G s.point) P)
    (hgm : (∫ ω, g s.point ω - G s.point ∂P) = 0)
    (hgpi : Integrable (fun ω => ‖g s.point ω - G s.point‖ ^ α) P)
    (hgb : (∫ ω, ‖g s.point ω - G s.point‖ ^ α ∂P) ≤ κ) :
    let Q := (auxLaw p c).toMeasure.prod P
    let E := fun ξ => HeavyTailedSospStopped.endpointError p c s.virtualIndex G
      (trajectory (HeavyTailedSospStopped.step p c s.virtualIndex ordinal g H) n
        (trajectory (sampleStep p c g H) (max 1 c.resetBatch)
          { s with phase := .reset 0 0 r } ξ, 0)
        (fun k => ξ (max 1 c.resetBatch + k))).1
    Integrable (fun ξ => ‖E ξ‖) (Measure.infinitePi fun _ : ℕ => Q) ∧
      (∫ ξ, ‖E ξ‖ ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
        (6 * κ / ((max 1 c.resetBatch : ℕ) : ℝ) ^ (α - 1)) ^ (1 / α) +
        (6 * ((max 1 c.epoch * max 1 c.transportBatch : ℕ) : ℝ) *
          (((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ ^ α *
            ((ρ * c.h ^ 2) ^ α + 6 * σ ^ α * c.h ^ α))) ^ (1 / α) := by
  intro Q E
  let F := fun w : State p × (ℕ → Aux p c × p.Ω) =>
    ‖HeavyTailedSospStopped.endpointError p c s.virtualIndex G
      (trajectory (HeavyTailedSospStopped.step p c s.virtualIndex ordinal g H) n (w.1, 0) w.2).1‖
  have hFm : Measurable F := (HeavyTailedSospStopped.measurable_endpointError p c
    s.virtualIndex G hG.continuous.measurable).norm.comp
      (((trajectory_measurable (HeavyTailedSospStopped.measurable_step p c s.virtualIndex ordinal
        g H hg hH) n).comp
        ((measurable_fst.prodMk (measurable_const (a := (0 : ℕ)))).prodMk measurable_snd)).fst)
  have hreset := finite_reset_moment p c P G hG.continuous.measurable g hg H hH s r
    hα.le hα2 hgi hgm hgpi hgb
  have htail (η : Fin (max 1 c.resetBatch) → Aux p c × p.Ω) :=
    finite_reset_conditions p c g H s r hh hv hbound η
  have htailbound (η : Fin (max 1 c.resetBatch) → Aux p c × p.Ω) :
      Integrable (fun ξ => F (iterateSamples (sampleStep p c g H) (max 1 c.resetBatch)
        { s with phase := .reset 0 0 r } η, ξ)) (Measure.infinitePi fun _ : ℕ => Q) ∧
      (∫ ξ, F (iterateSamples (sampleStep p c g H) (max 1 c.resetBatch)
        { s with phase := .reset 0 0 r } η, ξ) ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
      ‖HeavyTailedSospEstimator.error p c G (iterateSamples (sampleStep p c g H)
        (max 1 c.resetBatch) { s with phase := .reset 0 0 r } η)‖ +
      (6 * ((max 1 c.epoch * max 1 c.transportBatch : ℕ) : ℝ) *
        (((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ ^ α *
          ((ρ * c.h ^ 2) ^ α + 6 * σ ^ α * c.h ^ α))) ^ (1 / α) := by
    let sn := iterateSamples (sampleStep p c g H) (max 1 c.resetBatch)
      { s with phase := .reset 0 0 r } η
    obtain ⟨hv', hb', hz', hnr, hV, hpart⟩ := htail η
    change sn.virtualIndex = s.virtualIndex at hV
    change HeavyTailedSospInvariants.transportPartial p sn.phase = 0 at hpart
    have hal : HeavyTailedSospEpoch.ResetAligned p c sn := fun h => (hnr h).elim
    have hmom := HeavyTailedSospNoise.primitive_endpoint_integral_bound p c ordinal P G hG hD
      hρ hσ hd hh hs hseg hα hα2 hLip g hg H hH hi hm hpi hb n sn hv' hb' hz' hal hnr
      (by simpa only [hV] using halign)
    have hrem : HeavyTailedSospStopped.remaining p c s.virtualIndex (sn, 0) =
        max 1 c.epoch * max 1 c.transportBatch := by
      simp only [HeavyTailedSospStopped.remaining, HeavyTailedSospInvariants.transportProgress,
        hV, hpart, Nat.add_zero, Nat.add_mul, Nat.add_sub_cancel_left]
    simpa only [hV, hrem, F] using hmom
  exact fresh_continuation_root_bound Q (sampleStep p c g H)
    (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) (max 1 c.resetBatch)
    { s with phase := .reset 0 0 r } F hFm (fun _ => norm_nonneg _)
    (HeavyTailedSospEstimator.error p c G) (measurable_estimator_error p c G hG.continuous.measurable)
    hα hreset.1 hreset.2 (fun η => (htailbound η).1) (fun η => (htailbound η).2)

lemma primitive_expected_marked_error_bound (p : Params) (c : Config)
    (P : Measure p.Ω) [IsProbabilityMeasure P] (G : Space p → Space p)
    (hG : Differentiable ℝ G) (hD : Continuous (fderiv ℝ G))
    {ρ σ α : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hd : 0 < p.d)
    (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h) (hα : 1 < α) (hα2 : α ≤ 2)
    (hLip : ∀ x y, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ ρ * ‖x - y‖)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (hi : ∀ y v, Integrable (fun ω => H y ω v) P)
    (hm : ∀ y v, (∫ ω, H y ω v ∂P) = fderiv ℝ G y v)
    (hpi : ∀ y v, Integrable (fun ω => ‖H y ω v - fderiv ℝ G y v‖ ^ α) P)
    (hb : ∀ y v, (∫ ω, ‖H y ω v - fderiv ℝ G y v‖ ^ α ∂P) ≤ σ ^ α * ‖v‖ ^ α)
    (target N : ℕ) {κ : ℝ}
    (hgi : ∀ y, Integrable (fun ω => g y ω - G y) P)
    (hgm : ∀ y, (∫ ω, g y ω - G y ∂P) = 0)
    (hgpi : ∀ y, Integrable (fun ω => ‖g y ω - G y‖ ^ α) P)
    (hgb : ∀ y, (∫ ω, ‖g y ω - G y‖ ^ α ∂P) ≤ κ) :
    let Q := (auxLaw p c).toMeasure.prod P
    Integrable (markedErrorTotal p c G g H target N) (Measure.infinitePi fun _ : ℕ => Q) ∧
      (∫ ξ, markedErrorTotal p c G g H target N ξ ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
        ((6 * κ / ((max 1 c.resetBatch : ℕ) : ℝ) ^ (α - 1)) ^ (1 / α) +
          (6 * ((max 1 c.epoch * max 1 c.transportBatch : ℕ) : ℝ) *
            (((max 1 c.transportBatch : ℕ) : ℝ)⁻¹ ^ α *
              ((ρ * c.h ^ 2) ^ α + 6 * σ ^ α * c.h ^ α))) ^ (1 / α)) *
          ((∫ ξ, ((trajectory (sampleStep p c g H) N (initial p target) ξ).virtualIndex : ℝ)
            ∂Measure.infinitePi (fun _ : ℕ => Q)) + max 1 c.epoch) := by
  intro Q
  have hκ : 0 ≤ κ := (integral_nonneg
    (fun ω => Real.rpow_nonneg (norm_nonneg (g p.x0 ω - G p.x0)) α)).trans (hgb p.x0)
  apply expected_marked_error_bound p c G hG.continuous.measurable g hg H hH Q
    hd hh hs hseg target N _ (by positivity)
  intro j hj s r hv hbound halign
  have hreset := reset_endpoint_integral_bound p c j P G hG hD hρ hσ hd hh hs hseg hα hα2 hLip
    g hg H hH hi hm hpi hb N s r hv hbound halign (hgi s.point) (hgm s.point)
    (hgpi s.point) (hgb s.point)
  simpa only [epochEndpoint_reset_eq] using hreset

end LongTails.Proofs.HeavyTailedSospEpochIntegration
