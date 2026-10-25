import LongTails.Proofs.HeavyTailedSospEstimator
import LongTails.Proofs.HeavyTailedSospMeasurable
import LongTails.Proofs.HeavyTailedSospGeometry

open MeasureTheory
open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open LongTails.Proofs.HeavyTailedSospExecution
open LongTails.Proofs.HeavyTailedSospInvariants
open LongTails.Proofs.HeavyTailedSospEstimator
open LongTails.Proofs.HeavyTailedSospMeasurable

namespace LongTails.Proofs.HeavyTailedSospStopped

abbrev Monitor (p : Params) := State p × ℕ

def active (p : Params) (c : Config) (base ordinal : ℕ) (s : Monitor p) : Bool :=
  decide (s.1.virtualIndex < base + max 1 c.epoch ∧
    ¬ (markCharge p s.1.phase = 1 ∧ ordinal ≤ s.2 + 1))

noncomputable def step (p : Params) (c : Config) (base ordinal : ℕ)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : Monitor p) (z : Aux p c × p.Ω) : Monitor p :=
  if active p c base ordinal s then
    (sampleStep p c g H s.1 z, s.2 + markCharge p s.1.phase)
  else s

noncomputable def stoppedNoise (p : Params) (c : Config) (base ordinal : ℕ)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : Monitor p) (z : Aux p c × p.Ω) : Space p :=
  if active p c base ordinal s then sampleNoise p c G g H s.1 z else 0

def remaining (p : Params) (c : Config) (base : ℕ) (s : Monitor p) : ℕ :=
  (base + max 1 c.epoch) * max 1 c.transportBatch - transportProgress p c s.1

def charge (p : Params) (c : Config) (base ordinal : ℕ) (s : Monitor p) : ℕ :=
  if active p c base ordinal s then transportCharge p s.1.phase else 0

def detectFlag (p : Params) : Resume p → Bool
  | .detect => true
  | _ => false

lemma measurable_detectFlag (p : Params) : Measurable (detectFlag p) := by
  have hh : Measurable (Function.uncurry (fun r (_ : Unit) => detectFlag p r)) := by
    apply measurable_resume_uncurry p
    all_goals exact measurable_const
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))

lemma measurable_markCharge (p : Params) : Measurable (markCharge p) := by
  have hh : Measurable (Function.uncurry (fun ph (_ : Unit) => markCharge p ph)) := by
    apply measurable_phase_uncurry p
    · exact measurable_const
    · have hm : Measurable (fun w : (Space p × ℕ × Space p × Resume p) × Unit =>
          if detectFlag p w.1.2.2.2 = true ∧ w.1.2.1 = 0 then (1 : ℕ) else 0) := by
        apply Measurable.ite
        · exact (measurableSet_eq_fun (measurable_detectFlag p |>.comp
            (by fun_prop)) measurable_const).inter (measurableSet_eq_fun (by fun_prop) measurable_const)
        · exact measurable_const
        · exact measurable_const
      convert hm using 1
      funext w
      cases w.1.2.2.2 <;> simp [markCharge, detectFlag]
    · exact measurable_const
    · exact measurable_const
    · exact measurable_const
    · exact measurable_const
    · exact measurable_const
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))

lemma measurable_active (p : Params) (c : Config) (base ordinal : ℕ) :
    Measurable (active p c base ordinal) := by
  have hm : Measurable (fun s : Monitor p =>
      (s.1.virtualIndex, markCharge p s.1.phase, s.2)) :=
    ((measurable_virtualIndex p).comp measurable_fst).prodMk
      (((measurable_markCharge p).comp ((measurable_phase p).comp measurable_fst)).prodMk measurable_snd)
  exact (measurable_of_countable (fun w : ℕ × ℕ × ℕ =>
    decide (w.1 < base + max 1 c.epoch ∧ ¬ (w.2.1 = 1 ∧ ordinal ≤ w.2.2 + 1)))).comp hm

lemma measurable_step (p : Params) (c : Config) (base ordinal : ℕ)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (step p c base ordinal g H)) := by
  apply Measurable.ite
  · exact measurableSet_eq_fun ((measurable_active p c base ordinal).comp measurable_fst) measurable_const
  · apply Measurable.prodMk
    · exact (measurable_sampleStep p c g H hg hH).comp
        (measurable_fst.fst.prodMk measurable_snd)
    · exact measurable_fst.snd.add
        ((measurable_markCharge p).comp ((measurable_phase p).comp measurable_fst.fst))
  · exact measurable_fst

lemma measurable_noise (p : Params) (c : Config) (G : Space p → Space p)
    (hG : Measurable G) :
    Measurable (fun w : State p × Aux p c × Space p => noise p c G w.1 w.2.1 w.2.2) := by
  have hsign := measurable_signedSegment p c
  have hm : Measurable (Function.uncurry (fun ph (w : State p × Aux p c × Space p) =>
      noise p c G { w.1 with phase := ph } w.2.1 w.2.2)) := by
    apply measurable_phase_uncurry p
    all_goals simp only [noise]
    all_goals fun_prop
  exact hm.comp (((measurable_phase p).comp measurable_fst).prodMk measurable_id)

lemma measurable_sampleNoise (p : Params) (c : Config) (G : Space p → Space p)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hG : Measurable G) (hg : Measurable (Function.uncurry g))
    (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (sampleNoise p c G g H)) := by
  let answer := fun (a : AcceptedCode p) (w : Space p × p.Ω) =>
    match a with
    | .inl v => H w.1 w.2 v
    | .inr _ => g w.1 w.2
  have hm : Measurable (Function.uncurry answer) := by
    apply measurable_sum_uncurry (F := answer)
    · exact isBoundedBilinearMap_apply.continuous.measurable.comp
        ((hH.comp measurable_snd).prodMk measurable_fst)
    · exact hg.comp measurable_snd
  have hq := (measurable_encoded_query p c).comp
    (show Measurable (fun w : State p × (Aux p c × p.Ω) => (w.1, w.2.1)) from by fun_prop)
  have ha := hm.comp (hq.snd.prodMk (hq.fst.prodMk measurable_snd.snd))
  have hn := (measurable_noise p c G hG).comp
    (measurable_fst.prodMk (measurable_snd.fst.prodMk ha))
  convert hn using 1
  funext w
  dsimp only [sampleNoise, Function.comp_def, Function.uncurry, answer]
  cases (query p c w.1 w.2.1).2 <;> rfl

lemma measurable_stoppedNoise (p : Params) (c : Config) (base ordinal : ℕ)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (hG : Measurable G) (hg : Measurable (Function.uncurry g))
    (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (stoppedNoise p c base ordinal G g H)) := by
  apply Measurable.ite
  · exact measurableSet_eq_fun ((measurable_active p c base ordinal).comp measurable_fst) measurable_const
  · exact (measurable_sampleNoise p c G g H hG hg hH).comp
      (measurable_fst.fst.prodMk measurable_snd)
  · exact measurable_const

lemma active_progress_lt (p : Params) (c : Config) (base ordinal : ℕ)
    (s : Monitor p) (hv : PhaseValid p c s.1.phase)
    (ha : active p c base ordinal s = true) :
    transportProgress p c s.1 < (base + max 1 c.epoch) * max 1 c.transportBatch := by
  have hi : s.1.virtualIndex < base + max 1 c.epoch := (of_decide_eq_true ha).1
  have hb : transportPartial p s.1.phase < max 1 c.transportBatch := by
    cases hp : s.1.phase <;> simp only [transportPartial]
    all_goals try omega
    simp only [hp, PhaseValid] at hv
    exact hv.1
  unfold transportProgress
  nlinarith

lemma step_allowance (p : Params) (c : Config) (base ordinal : ℕ)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : Monitor p) (hv : PhaseValid p c s.1.phase) (z : Aux p c × p.Ω) :
    remaining p c base (step p c base ordinal g H s z) + charge p c base ordinal s ≤
      remaining p c base s := by
  unfold step charge
  split_ifs with ha
  · have hi := active_progress_lt p c base ordinal s hv ha
    have hprogress : transportProgress p c (sampleStep p c g H s.1 z) =
        transportProgress p c s.1 + transportCharge p s.1.phase :=
      update_transportProgress p c _ _ _ hv
    change (base + max 1 c.epoch) * max 1 c.transportBatch -
        transportProgress p c (sampleStep p c g H s.1 z) + transportCharge p s.1.phase ≤
      (base + max 1 c.epoch) * max 1 c.transportBatch - transportProgress p c s.1
    rw [hprogress]
    have hc := transportCharge_le_one p s.1.phase
    omega
  · simp

lemma step_valid (p : Params) (c : Config) (base ordinal : ℕ)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : Monitor p) (hv : PhaseValid p c s.1.phase) (z : Aux p c × p.Ω) :
    PhaseValid p c (step p c base ordinal g H s z).1.phase := by
  unfold step
  split_ifs
  · exact update_valid p c _ _ _ hv
  · exact hv

lemma step_bound (p : Params) (c : Config) (base ordinal : ℕ)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : Monitor p) (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    (hv : HeavyTailedSospGeometry.PhaseBound p c.h s.1.phase) (z : Aux p c × p.Ω) :
    HeavyTailedSospGeometry.PhaseBound p c.h (step p c base ordinal g H s z).1.phase := by
  unfold step
  split_ifs
  · exact HeavyTailedSospGeometry.update_bound p c _ _ _ hd hh hs hseg hv
  · exact hv

lemma stopped_moment (p : Params) (c : Config) (base ordinal : ℕ)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (P : Measure (Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (hG : Measurable G) (hg : Measurable (Function.uncurry g))
    (hH : Measurable (Function.uncurry H))
    (hd : 0 < p.d) (hh : 0 ≤ c.h) (hs : 0 ≤ c.s)
    (hseg : c.s / (max 1 c.ncSegments : ℕ) ≤ c.h)
    {α κ : ℝ} (hα : 1 ≤ α) (hα2 : α ≤ 2) (hκ : 0 ≤ κ)
    (hi : ∀ s : State p, PhaseValid p c s.phase → HeavyTailedSospGeometry.PhaseBound p c.h s.phase →
      Integrable (sampleNoise p c G g H s) P)
    (hm : ∀ s : State p, PhaseValid p c s.phase → HeavyTailedSospGeometry.PhaseBound p c.h s.phase →
      (∫ z, sampleNoise p c G g H s z ∂P) = 0)
    (hpi : ∀ s : State p, PhaseValid p c s.phase → HeavyTailedSospGeometry.PhaseBound p c.h s.phase →
      Integrable (fun z => ‖sampleNoise p c G g H s z‖ ^ α) P)
    (hb : ∀ s : State p, PhaseValid p c s.phase → HeavyTailedSospGeometry.PhaseBound p c.h s.phase →
      (∫ z, ‖sampleNoise p c G g H s z‖ ^ α ∂P) ≤ transportCharge p s.phase * κ)
    (n : ℕ) (s : Monitor p) (hv : PhaseValid p c s.1.phase)
    (hbound : HeavyTailedSospGeometry.PhaseBound p c.h s.1.phase) :
    Integrable (fun ξ => ‖HeavyTailedFreshProcess.noiseSum (step p c base ordinal g H)
      (stoppedNoise p c base ordinal G g H) n s 0 ξ‖ ^ α)
      (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, ‖HeavyTailedFreshProcess.noiseSum (step p c base ordinal g H)
        (stoppedNoise p c base ordinal G g H) n s 0 ξ‖ ^ α
          ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 6 * remaining p c base s * κ := by
  have hα0 : α ≠ 0 := by linarith
  have hhresult := HeavyTailedFreshProcess.noiseSum_remaining_moment_on P
    (fun s : Monitor p => PhaseValid p c s.1.phase ∧ HeavyTailedSospGeometry.PhaseBound p c.h s.1.phase)
    (fun s hv z => ⟨step_valid p c base ordinal g H s hv.1 z,
      step_bound p c base ordinal g H s hd hh hs hseg hv.2 z⟩)
    (measurable_step p c base ordinal g H hg hH)
    (measurable_stoppedNoise p c base ordinal G g H hG hg hH)
    (remaining p c base) (charge p c base ordinal)
    (fun s hv z => step_allowance p c base ordinal g H s hv.1 z) hα hα2 hκ
    (fun s hv => ?_) (fun s hv => ?_) (fun s hv => ?_) (fun s hv => ?_) n s ⟨hv, hbound⟩ 0
  · simpa only [norm_zero, Real.zero_rpow hα0, zero_add] using hhresult
  all_goals unfold stoppedNoise
  all_goals split_ifs with ha
  · exact hi _ hv.1 hv.2
  · exact integrable_const _
  · exact hm _ hv.1 hv.2
  · simp
  · exact hpi _ hv.1 hv.2
  · simp [Real.zero_rpow hα0]
  · simpa only [charge, ha, ↓reduceIte] using hb _ hv.1 hv.2
  · simp [charge, ha, Real.zero_rpow hα0]

lemma trajectory_freeze_prefix {S Ω : Type*} (advance : S → Ω → S) (live : S → Bool)
    (n : ℕ) (s : S) (ξ : ℕ → Ω) :
    ∃ k ≤ n, HeavyTailedProductProcess.trajectory (fun s ω => if live s then advance s ω else s) n s ξ =
      HeavyTailedProductProcess.trajectory advance k s ξ ∧
      (k = n ∨ live (HeavyTailedProductProcess.trajectory advance k s ξ) = false) := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl, Or.inl rfl⟩
  | succ n ih =>
    obtain ⟨k, hk, heq, hstop⟩ := ih
    rw [HeavyTailedProductProcess.trajectory_succ_last, heq]
    rcases hstop with rfl | hstop
    · cases ha : live (HeavyTailedProductProcess.trajectory advance k s ξ) with
      | false => exact ⟨k, by omega, by simp, Or.inr ha⟩
      | true => exact ⟨k + 1, le_rfl, by simp [HeavyTailedProductProcess.trajectory_succ_last], Or.inl rfl⟩
    · exact ⟨k, by omega, by simp [hstop], Or.inr hstop⟩


lemma trajectory_freeze_at {S Ω : Type*} (advance : S → Ω → S) (live : S → Bool)
    (k n : ℕ) (s : S) (ξ : ℕ → Ω) (hkn : k ≤ n)
    (hbefore : ∀ i < k, live (HeavyTailedProductProcess.trajectory advance i s ξ) = true)
    (hat : live (HeavyTailedProductProcess.trajectory advance k s ξ) = false) :
    HeavyTailedProductProcess.trajectory (fun s ω => if live s then advance s ω else s) n s ξ =
      HeavyTailedProductProcess.trajectory advance k s ξ := by
  let stopped := fun s ω => if live s then advance s ω else s
  have hpref : ∀ m ≤ k, HeavyTailedProductProcess.trajectory stopped m s ξ =
      HeavyTailedProductProcess.trajectory advance m s ξ := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [HeavyTailedProductProcess.trajectory_succ_last, ih (by omega)]
      simp only [stopped, hbefore m (by omega), ↓reduceIte]
      exact (HeavyTailedProductProcess.trajectory_succ_last advance m s ξ).symm
  have hafter : ∀ m, k ≤ m → HeavyTailedProductProcess.trajectory stopped m s ξ =
      HeavyTailedProductProcess.trajectory advance k s ξ := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hpref k le_rfl
    | succ m hm ih =>
      rw [HeavyTailedProductProcess.trajectory_succ_last, ih]
      simp [stopped, hat]
  exact hafter n hkn

lemma trajectory_noise_pair {S E Ω : Type*} [Add E]
    (advance : S → Ω → S) (increment : S → Ω → E)
    (n : ℕ) (s : S) (z : E) (ξ : ℕ → Ω) :
    HeavyTailedProductProcess.trajectory (fun w ω => (advance w.1 ω, w.2 + increment w.1 ω))
      n (s, z) ξ =
      (HeavyTailedProductProcess.trajectory advance n s ξ,
        HeavyTailedFreshProcess.noiseSum advance increment n s z ξ) := by
  induction n generalizing s z ξ with
  | zero => rfl
  | succ n ih => exact ih _ _ _

lemma stopped_noise_prefix {S E Ω : Type*} [AddZeroClass E]
    (advance : S → Ω → S) (increment : S → Ω → E) (live : S → Bool)
    (n : ℕ) (s : S) (z : E) (ξ : ℕ → Ω) :
    let stopped := fun s ω => if live s then advance s ω else s
    let masked := fun s ω => if live s then increment s ω else 0
    ∃ k ≤ n, HeavyTailedProductProcess.trajectory stopped n s ξ =
      HeavyTailedProductProcess.trajectory advance k s ξ ∧
      HeavyTailedFreshProcess.noiseSum stopped masked n s z ξ =
        HeavyTailedFreshProcess.noiseSum advance increment k s z ξ ∧
      (k = n ∨ live (HeavyTailedProductProcess.trajectory advance k s ξ) = false) := by
  intro stopped masked
  let joint := fun (w : S × E) ω => (advance w.1 ω, w.2 + increment w.1 ω)
  have heq : (fun (w : S × E) ω => if live w.1 then joint w ω else w) =
      (fun w ω => (stopped w.1 ω, w.2 + masked w.1 ω)) := by
    funext w ω
    cases ha : live w.1 <;> simp [joint, stopped, masked, ha]
  obtain ⟨k, hk, hpair, hlast⟩ := trajectory_freeze_prefix joint (fun w => live w.1) n (s, z) ξ
  rw [heq, trajectory_noise_pair, trajectory_noise_pair] at hpair
  refine ⟨k, hk, congrArg Prod.fst hpair, congrArg Prod.snd hpair, ?_⟩
  simpa only [joint, trajectory_noise_pair] using hlast

noncomputable def advance (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : Monitor p) (z : Aux p c × p.Ω) : Monitor p :=
  (sampleStep p c g H s.1 z, s.2 + markCharge p s.1.phase)

lemma advance_trajectory (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (n : ℕ) (s : State p) (m : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    HeavyTailedProductProcess.trajectory (advance p c g H) n (s, m) ξ =
      (HeavyTailedProductProcess.trajectory (sampleStep p c g H) n s ξ,
        m + ∑ k ∈ Finset.range n, markCharge p
          (HeavyTailedProductProcess.trajectory (sampleStep p c g H) k s ξ).phase) := by
  induction n with
  | zero => simp [HeavyTailedProductProcess.trajectory]
  | succ n ih =>
    rw [HeavyTailedProductProcess.trajectory_succ_last, ih]
    simp only [advance]
    rw [HeavyTailedProductProcess.trajectory_succ_last, Finset.sum_range_succ]
    congr 1
    omega

lemma advance_noiseSum (p : Params) (c : Config) (G : Space p → Space p)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (n : ℕ) (s : State p) (m : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    HeavyTailedFreshProcess.noiseSum (advance p c g H)
      (fun s z => sampleNoise p c G g H s.1 z) n (s, m) 0 ξ =
      ∑ k ∈ Finset.range n, sampleNoise p c G g H
        (HeavyTailedProductProcess.trajectory (sampleStep p c g H) k s ξ) (ξ k) := by
  rw [HeavyTailedFreshProcess.noiseSum_eq_sum, zero_add]
  simp only [advance_trajectory]

lemma stopped_actual_prefix (p : Params) (c : Config) (base ordinal : ℕ)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (n : ℕ) (s : State p) (m : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    ∃ k ≤ n,
      HeavyTailedProductProcess.trajectory (step p c base ordinal g H) n (s, m) ξ =
        HeavyTailedProductProcess.trajectory (advance p c g H) k (s, m) ξ ∧
      HeavyTailedFreshProcess.noiseSum (step p c base ordinal g H)
        (stoppedNoise p c base ordinal G g H) n (s, m) 0 ξ =
        ∑ j ∈ Finset.range k, sampleNoise p c G g H
          (HeavyTailedProductProcess.trajectory (sampleStep p c g H) j s ξ) (ξ j) ∧
      (k = n ∨ active p c base ordinal
        (HeavyTailedProductProcess.trajectory (advance p c g H) k (s, m) ξ) = false) := by
  obtain ⟨k, hk, hstate, hnoise, hlast⟩ := stopped_noise_prefix (advance p c g H)
    (fun s z => sampleNoise p c G g H s.1 z) (active p c base ordinal) n (s, m) 0 ξ
  refine ⟨k, hk, hstate, ?_, hlast⟩
  exact hnoise.trans (advance_noiseSum p c G g H k s m ξ)


lemma markCharge_zero_or_one (p : Params) (ph : Phase p) :
    markCharge p ph = 0 ∨ markCharge p ph = 1 := by
  cases ph <;> simp only [markCharge]
  all_goals solve | simp | (split <;> simp; omega)

lemma step_count_lt (p : Params) (c : Config) (base ordinal : ℕ)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : Monitor p) (z : Aux p c × p.Ω) (hs : s.2 < ordinal) :
    (step p c base ordinal g H s z).2 < ordinal := by
  unfold step
  split_ifs with h
  · have ha : ¬ (markCharge p s.1.phase = 1 ∧ ordinal ≤ s.2 + 1) := by
      have hh : s.1.virtualIndex < base + max 1 c.epoch ∧
          ¬ (markCharge p s.1.phase = 1 ∧ ordinal ≤ s.2 + 1) := by
        simpa only [active, decide_eq_true_eq] using h
      exact hh.2
    rcases markCharge_zero_or_one p s.1.phase with hm | hm
    · simpa [hm] using hs
    · dsimp only
      rw [hm]
      omega
  · exact hs

lemma stopped_count_lt (p : Params) (c : Config) (base ordinal : ℕ)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : Monitor p) (hs : s.2 < ordinal) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    (HeavyTailedProductProcess.trajectory (step p c base ordinal g H) n s ξ).2 < ordinal := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [HeavyTailedProductProcess.trajectory_succ_last]
    exact step_count_lt p c base ordinal g H _ _ ih



lemma prefix_mark_strict (f : ℕ → ℕ) {i j : ℕ} (hij : i < j) (hi : f i = 1) :
    (∑ k ∈ Finset.range i, f k) + 1 ≤ ∑ k ∈ Finset.range j, f k := by
  have hm : Monotone (fun n => ∑ k ∈ Finset.range n, f k) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [Finset.sum_range_succ]
    omega
  have hh := hm (show i + 1 ≤ j by omega)
  simpa only [Finset.sum_range_succ, hi] using hh

lemma marked_ordinal_injective (f : ℕ → ℕ) {i j : ℕ} (hi : f i = 1) (hj : f j = 1)
    (heq : (∑ k ∈ Finset.range i, f k) + 1 = (∑ k ∈ Finset.range j, f k) + 1) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hh := prefix_mark_strict f h hi
    omega
  · exact h
  · have hh := prefix_mark_strict f h hj
    omega

lemma stopped_mark_ordinal (p : Params) (c : Config) (base ordinal : ℕ)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (hj : 0 < ordinal) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hend : markCharge p (HeavyTailedProductProcess.trajectory
      (sampleStep p c g H) n s ξ).phase = 0)
    (hmark : markCharge p (HeavyTailedProductProcess.trajectory
      (step p c base ordinal g H) n (s, 0) ξ).1.phase = 1)
    (hwithin : (HeavyTailedProductProcess.trajectory
      (step p c base ordinal g H) n (s, 0) ξ).1.virtualIndex < base + max 1 c.epoch) :
    ∃ k < n, (HeavyTailedProductProcess.trajectory
        (step p c base ordinal g H) n (s, 0) ξ).1 =
        HeavyTailedProductProcess.trajectory (sampleStep p c g H) k s ξ ∧
      (∑ i ∈ Finset.range k, markCharge p
        (HeavyTailedProductProcess.trajectory (sampleStep p c g H) i s ξ).phase) + 1 = ordinal := by
  obtain ⟨k, hk, heq, hstop⟩ := trajectory_freeze_prefix
    (advance p c g H) (active p c base ordinal) n (s, 0) ξ
  change HeavyTailedProductProcess.trajectory (step p c base ordinal g H) n (s, 0) ξ =
    HeavyTailedProductProcess.trajectory (advance p c g H) k (s, 0) ξ at heq
  have hcount := stopped_count_lt p c base ordinal g H (s, 0) hj n ξ
  rw [advance_trajectory] at heq
  have hfirst := congrArg Prod.fst heq
  dsimp only at hfirst
  have hkne : k ≠ n := by
    intro hkn
    rw [hfirst, hkn, hend] at hmark
    omega
  refine ⟨k, by omega, hfirst, ?_⟩
  have hinactive := hstop.resolve_left hkne
  rw [advance_trajectory] at hinactive
  rw [heq] at hcount hmark hwithin
  simp only [Nat.zero_add] at hinactive hcount
  have hbad : ¬ ((HeavyTailedProductProcess.trajectory (sampleStep p c g H) k s ξ).virtualIndex <
      base + max 1 c.epoch ∧ ¬ (markCharge p
      (HeavyTailedProductProcess.trajectory (sampleStep p c g H) k s ξ).phase = 1 ∧
      ordinal ≤ (∑ i ∈ Finset.range k, markCharge p
        (HeavyTailedProductProcess.trajectory (sampleStep p c g H) i s ξ).phase) + 1)) := by
    simpa only [active, decide_eq_false_iff_not] using hinactive
  have hle : ordinal ≤ (∑ i ∈ Finset.range k, markCharge p
      (HeavyTailedProductProcess.trajectory (sampleStep p c g H) i s ξ).phase) + 1 := by
    by_contra hh
    exact hbad ⟨hwithin, fun hh' => hh hh'.2⟩
  omega


lemma stopped_at_mark (p : Params) (c : Config) (base ordinal : ℕ)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (k n : ℕ) (ξ : ℕ → Aux p c × p.Ω) (hkn : k ≤ n)
    (hmark : markCharge p (HeavyTailedProductProcess.trajectory
      (sampleStep p c g H) k s ξ).phase = 1)
    (hwithin : (HeavyTailedProductProcess.trajectory
      (sampleStep p c g H) k s ξ).virtualIndex < base + max 1 c.epoch)
    (hordinal : (∑ i ∈ Finset.range k, markCharge p
      (HeavyTailedProductProcess.trajectory (sampleStep p c g H) i s ξ).phase) + 1 = ordinal) :
    (HeavyTailedProductProcess.trajectory (step p c base ordinal g H) n (s, 0) ξ).1 =
      HeavyTailedProductProcess.trajectory (sampleStep p c g H) k s ξ := by
  have hV : Monotone (fun i => (HeavyTailedProductProcess.trajectory
      (sampleStep p c g H) i s ξ).virtualIndex) := by
    apply monotone_nat_of_le_succ
    intro i
    rw [HeavyTailedProductProcess.trajectory_succ_last]
    exact (update_virtualIndex p c _ _ _).1
  have hbefore (i : ℕ) (hik : i < k) : active p c base ordinal
      (HeavyTailedProductProcess.trajectory (advance p c g H) i (s, 0) ξ) = true := by
    rw [advance_trajectory]
    simp only [active, Nat.zero_add, decide_eq_true_eq]
    refine ⟨lt_of_le_of_lt (hV hik.le) hwithin, ?_⟩
    intro hh
    have hstrict := prefix_mark_strict
      (fun j => markCharge p (HeavyTailedProductProcess.trajectory (sampleStep p c g H) j s ξ).phase)
      hik hh.1
    omega
  have hat : active p c base ordinal
      (HeavyTailedProductProcess.trajectory (advance p c g H) k (s, 0) ξ) = false := by
    rw [advance_trajectory]
    simp only [active, Nat.zero_add, decide_eq_false_iff_not]
    intro hh
    exact hh.2 ⟨hmark, hordinal.ge⟩
  have heq := trajectory_freeze_at (advance p c g H) (active p c base ordinal)
    k n (s, 0) ξ hkn hbefore hat
  change HeavyTailedProductProcess.trajectory (step p c base ordinal g H) n (s, 0) ξ =
    HeavyTailedProductProcess.trajectory (advance p c g H) k (s, 0) ξ at heq
  rw [advance_trajectory] at heq
  exact congrArg Prod.fst heq

lemma stopped_marked_error (p : Params) (c : Config) (ordinal : ℕ)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (hv : PhaseValid p c s.phase)
    (hz : ZeroPartial p s.phase) (ha : HeavyTailedSospEpoch.ResetAligned p c s)
    (hs : ¬ HeavyTailedSospEpoch.IsReset p s.phase)
    (hb : s.virtualIndex % max 1 c.epoch = 0)
    (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    let sn := (HeavyTailedProductProcess.trajectory (step p c s.virtualIndex ordinal g H) n (s, 0) ξ).1
    markCharge p sn.phase = 1 → sn.virtualIndex < s.virtualIndex + max 1 c.epoch →
      sn.estimate - G sn.point = error p c G s +
        HeavyTailedFreshProcess.noiseSum (step p c s.virtualIndex ordinal g H)
          (stoppedNoise p c s.virtualIndex ordinal G g H) n (s, 0) 0 ξ := by
  intro sn hmark hwithin
  obtain ⟨k, hk, hstate, hnoise, hlast⟩ :=
    stopped_actual_prefix p c s.virtualIndex ordinal G g H n s 0 ξ
  rw [advance_trajectory] at hstate
  have hfirst := congrArg Prod.fst hstate
  change sn = HeavyTailedProductProcess.trajectory (sampleStep p c g H) k s ξ at hfirst
  have hmactual : markCharge p
      (HeavyTailedProductProcess.trajectory (sampleStep p c g H) k s ξ).phase = 1 := by
    rw [← hfirst]
    exact hmark
  have hnactual : (HeavyTailedProductProcess.trajectory (sampleStep p c g H) k s ξ).virtualIndex <
      s.virtualIndex + max 1 c.epoch := by
    rw [← hfirst]
    exact hwithin
  have hzero := trajectory_zeroPartial p c g H s hz k ξ
  have herr := epoch_error_sum p c G g H s hv ha hs hb k ξ hnactual
  rw [marked_error p c G _ hzero hmactual] at herr
  rw [hfirst]
  exact herr.trans (congrArg (fun z => error p c G s + z) hnoise.symm)

noncomputable def endpointError (p : Params) (c : Config) (base : ℕ)
    (G : Space p → Space p) (s : State p) : Space p :=
  if markCharge p s.phase = 1 ∧ s.virtualIndex < base + max 1 c.epoch then
    s.estimate - G s.point else 0


lemma epoch_endpoint_sum_bound (p : Params) (c : Config)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    (∑ k ∈ Finset.range n,
      if markCharge p (HeavyTailedProductProcess.trajectory (sampleStep p c g H) k s ξ).phase = 1 ∧
          (HeavyTailedProductProcess.trajectory (sampleStep p c g H) k s ξ).virtualIndex <
            s.virtualIndex + max 1 c.epoch then
        ‖(HeavyTailedProductProcess.trajectory (sampleStep p c g H) k s ξ).estimate -
          G (HeavyTailedProductProcess.trajectory (sampleStep p c g H) k s ξ).point‖ else 0) ≤
      ∑ j ∈ Finset.Icc 1 (max 1 c.epoch), ‖endpointError p c s.virtualIndex G
        (HeavyTailedProductProcess.trajectory (step p c s.virtualIndex j g H) n (s, 0) ξ).1‖ := by
  classical
  let X := fun k => HeavyTailedProductProcess.trajectory (sampleStep p c g H) k s ξ
  let pred := fun k => markCharge p (X k).phase = 1 ∧
    (X k).virtualIndex < s.virtualIndex + max 1 c.epoch
  let K := (Finset.range n).filter pred
  let ord := fun k => (∑ i ∈ Finset.range k, markCharge p (X i).phase) + 1
  let F := fun j => ‖endpointError p c s.virtualIndex G
    (HeavyTailedProductProcess.trajectory (step p c s.virtualIndex j g H) n (s, 0) ξ).1‖
  have hinj : ∀ i ∈ K, ∀ j ∈ K, ord i = ord j → i = j := by
    intro i hi j hj heq
    exact marked_ordinal_injective (fun k => markCharge p (X k).phase)
      (Finset.mem_filter.mp hi).2.1 (Finset.mem_filter.mp hj).2.1 heq
  have hsub : K.image ord ⊆ Finset.Icc 1 (max 1 c.epoch) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    have hp := (Finset.mem_filter.mp hk).2
    exact Finset.mem_Icc.mpr ⟨by dsimp [ord]; omega,
      epoch_mark_ordinal_le p c g H s k (max 1 c.epoch) ξ hp.1 hp.2⟩
  have hvalue (k : ℕ) (hk : k ∈ K) : ‖(X k).estimate - G (X k).point‖ = F (ord k) := by
    obtain ⟨hkn, hp⟩ := Finset.mem_filter.mp hk
    have heq := stopped_at_mark p c s.virtualIndex (ord k) g H s k n ξ
      (Finset.mem_range.mp hkn).le hp.1 hp.2 rfl
    dsimp only [F]
    rw [heq]
    change ‖(X k).estimate - G (X k).point‖ = ‖endpointError p c s.virtualIndex G (X k)‖
    change markCharge p (X k).phase = 1 ∧
      (X k).virtualIndex < s.virtualIndex + max 1 c.epoch at hp
    simp only [endpointError, hp.1, hp.2, and_self, ↓reduceIte]

  calc
    _ = ∑ k ∈ K, ‖(X k).estimate - G (X k).point‖ := by
      simp only [K, Finset.sum_filter]
      rfl
    _ = ∑ k ∈ K, F (ord k) := Finset.sum_congr rfl hvalue
    _ = ∑ j ∈ K.image ord, F j := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => norm_nonneg _)

lemma measurable_endpointError (p : Params) (c : Config) (base : ℕ)
    (G : Space p → Space p) (hG : Measurable G) :
    Measurable (endpointError p c base G) := by
  apply Measurable.ite
  · exact (measurableSet_eq_fun ((measurable_markCharge p).comp (measurable_phase p))
      measurable_const).inter (measurableSet_lt (measurable_virtualIndex p) measurable_const)
  · exact (measurable_estimate p).sub (hG.comp (measurable_point p))
  · exact measurable_const

lemma endpointError_bound (p : Params) (c : Config) (ordinal : ℕ)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (hv : PhaseValid p c s.phase)
    (hz : ZeroPartial p s.phase) (ha : HeavyTailedSospEpoch.ResetAligned p c s)
    (hs : ¬ HeavyTailedSospEpoch.IsReset p s.phase)
    (hb : s.virtualIndex % max 1 c.epoch = 0)
    (n : ℕ) (ξ : ℕ → Aux p c × p.Ω) :
    ‖endpointError p c s.virtualIndex G
      (HeavyTailedProductProcess.trajectory (step p c s.virtualIndex ordinal g H) n (s, 0) ξ).1‖ ≤
      ‖error p c G s‖ + ‖HeavyTailedFreshProcess.noiseSum (step p c s.virtualIndex ordinal g H)
        (stoppedNoise p c s.virtualIndex ordinal G g H) n (s, 0) 0 ξ‖ := by
  unfold endpointError
  split_ifs with hmark
  · rw [stopped_marked_error p c ordinal G g H s hv hz ha hs hb n ξ hmark.1 hmark.2]
    exact norm_add_le _ _
  · simp only [norm_zero]
    positivity

lemma endpoint_integral_bound (p : Params) (c : Config) (ordinal : ℕ)
    (G : Space p → Space p) (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (P : Measure (Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (hG : Measurable G) (hg : Measurable (Function.uncurry g))
    (hH : Measurable (Function.uncurry H))
    (s : State p) (hv : PhaseValid p c s.phase)
    (hz : ZeroPartial p s.phase) (ha : HeavyTailedSospEpoch.ResetAligned p c s)
    (hs : ¬ HeavyTailedSospEpoch.IsReset p s.phase)
    (hb : s.virtualIndex % max 1 c.epoch = 0) (n : ℕ)
    {α M : ℝ} (hα : 1 < α)
    (hpi : Integrable (fun ξ => ‖HeavyTailedFreshProcess.noiseSum
      (step p c s.virtualIndex ordinal g H) (stoppedNoise p c s.virtualIndex ordinal G g H)
      n (s, 0) 0 ξ‖ ^ α) (Measure.infinitePi fun _ : ℕ => P))
    (hm : (∫ ξ, ‖HeavyTailedFreshProcess.noiseSum
      (step p c s.virtualIndex ordinal g H) (stoppedNoise p c s.virtualIndex ordinal G g H)
      n (s, 0) 0 ξ‖ ^ α ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ M) :
    let E := fun ξ => endpointError p c s.virtualIndex G
      (HeavyTailedProductProcess.trajectory (step p c s.virtualIndex ordinal g H) n (s, 0) ξ).1
    Integrable (fun ξ => ‖E ξ‖) (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, ‖E ξ‖ ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ ‖error p c G s‖ + M ^ (1 / α) := by
  intro E
  let Z := fun ξ => HeavyTailedFreshProcess.noiseSum (step p c s.virtualIndex ordinal g H)
    (stoppedNoise p c s.virtualIndex ordinal G g H) n (s, 0) 0 ξ
  have hstep := measurable_step p c s.virtualIndex ordinal g H hg hH
  have hnoise := measurable_stoppedNoise p c s.virtualIndex ordinal G g H hG hg hH
  have hZm : Measurable Z := (HeavyTailedFreshProcess.noiseSum_measurable hstep hnoise n).comp
    ((measurable_const (a := ((s, (0 : ℕ)), (0 : Space p)))).prodMk measurable_id)
  have hEm : Measurable E := (measurable_endpointError p c s.virtualIndex G hG).comp
    (((HeavyTailedProductProcess.trajectory_measurable hstep n).comp
      ((measurable_const (a := (s, (0 : ℕ)))).prodMk measurable_id)).fst)
  have hZi : Integrable (fun ξ => ‖Z ξ‖) (Measure.infinitePi fun _ : ℕ => P) := by
    simpa using integrable_norm_rpow_of_le hZm.aestronglyMeasurable
      (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ α) hα.le hpi
  have hcontrol := (integrable_const ‖error p c G s‖).add hZi
  have hdom (ξ : ℕ → Aux p c × p.Ω) : ‖E ξ‖ ≤ ‖error p c G s‖ + ‖Z ξ‖ :=
    endpointError_bound p c ordinal G g H s hv hz ha hs hb n ξ
  have hEi : Integrable E (Measure.infinitePi fun _ : ℕ => P) :=
    hcontrol.mono' hEm.aestronglyMeasurable (Filter.Eventually.of_forall hdom)
  refine ⟨hEi.norm, ?_⟩
  have hroot := HeavyTailedMomentBounds.integral_norm_le_root_moment hα hZm.aestronglyMeasurable hpi
  have hpower := Real.rpow_le_rpow (integral_nonneg (fun ξ => Real.rpow_nonneg (norm_nonneg (Z ξ)) α))
    hm (by positivity : 0 ≤ 1 / α)
  calc
    _ ≤ ∫ ξ, ‖error p c G s‖ + ‖Z ξ‖ ∂Measure.infinitePi (fun _ : ℕ => P) :=
      integral_mono hEi.norm hcontrol hdom
    _ = ‖error p c G s‖ + ∫ ξ, ‖Z ξ‖ ∂Measure.infinitePi (fun _ : ℕ => P) := by
      rw [integral_add (integrable_const _) hZi, integral_const]
      simp
    _ ≤ _ := add_le_add le_rfl (hroot.trans hpower)

end LongTails.Proofs.HeavyTailedSospStopped
