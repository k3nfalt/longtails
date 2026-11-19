import Mathlib.Tactic
import LongTails.Proofs.LeonEstimator
import LongTails.Proofs.LeonSampling
import LongTails.Proofs.LeonRoundTrace
import LongTails.Proofs.ParameterFreeNsgdmRun
import LongTails.Proofs.LeonCalendar

namespace LongTails.Proofs.LeonDyadicTracking

noncomputable def envelope (M C r : ℝ) : ℝ :=
  if M ≤ r then M else (1 + 2 * C) * M - C * r

lemma envelope_step {M C r R a b : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hR : 2 * r ≤ R) (ha : a ≤ envelope M C R)
    (hmove : b ≤ a + C * r) (hexact : M ≤ r → a ≤ M → b ≤ M) :
    b ≤ envelope M C r := by
  by_cases hc : M ≤ r
  · have hp : M ≤ R := by linarith
    simpa [envelope, hc] using hexact hc (by simpa [envelope, hp] using ha)
  · rw [envelope, ite_eq_right hc]
    by_cases hp : M ≤ R
    · rw [envelope, ite_eq_left hp] at ha
      nlinarith [mul_nonneg hC (sub_nonneg.mpr (le_of_not_ge hc))]
    · rw [envelope, ite_eq_right hp] at ha
      nlinarith [mul_nonneg hC (sub_nonneg.mpr hR)]

lemma envelope_mono {M N C r : ℝ} (h : M ≤ N) (hC : 0 ≤ C) (hN : 0 ≤ N) :
    envelope M C r ≤ envelope N C r := by
  by_cases hn : N ≤ r
  · simp [envelope, hn, h.trans hn, h]
  · rw [envelope, envelope, ite_eq_right hn]
    split_ifs with hm
    · nlinarith [mul_nonneg hC hN, mul_nonneg hC (sub_nonneg.mpr (le_of_not_ge hn))]
    · nlinarith [mul_nonneg hC (sub_nonneg.mpr h)]

lemma envelope_le {M C r : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hr : 0 ≤ r) :
    envelope M C r ≤ (1 + 2 * C) * M := by
  unfold envelope
  split_ifs
  · nlinarith [mul_nonneg hC hM]
  · nlinarith [mul_nonneg hC hr]

lemma self_le_envelope {M C r : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) : M ≤ envelope M C r := by
  unfold envelope
  split_ifs with h
  · exact le_rfl
  · nlinarith [mul_nonneg hC hM, mul_nonneg hC (sub_nonneg.mpr (le_of_not_ge h))]

lemma smaller_estimate_sq {a b x y ex ey : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hex : x ≤ a + ex) (hey : y ≤ b + ey) :
    (if a ≤ b then x else y) ^ 2 ≤ 2 * (a * b + ex ^ 2 + ey ^ 2) := by
  split_ifs with h
  · nlinarith [sq_nonneg (a - ex), sq_nonneg ey, mul_nonneg ha (sub_nonneg.mpr h),
      mul_self_le_mul_self hx hex]
  · nlinarith [sq_nonneg (b - ey), sq_nonneg ex,
      mul_nonneg hb (sub_nonneg.mpr (le_of_not_ge h)), mul_self_le_mul_self hy hey]

end LongTails.Proofs.LeonDyadicTracking

namespace LongTails.Proofs.LeonPathMoments

open MeasureTheory

open LeonDyadicTracking

structure Tracked {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (δ : ℝ)
    (j : ℕ) (err : Ω → ℝ) : Prop where
  witness : ∃ w : Ω → ℝ, Measurable w ∧ (∀ s, 0 ≤ w s) ∧
    Integrable (fun s => w s ^ 2) P ∧ (∫ s, w s ^ 2 ∂P) ≤ 2 * δ ^ 2 / 2 ^ j ∧
    ∀ s, err s ≤ envelope (3 / 2 * (δ + w s)) 11 ((4 : ℝ) ^ j * δ)

lemma root {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ)
    (err noise : Ω → ℝ) (hm : Measurable noise) (hn : ∀ s, 0 ≤ noise s)
    (hi : Integrable (fun s => noise s ^ 2) P) (hv : (∫ s, noise s ^ 2 ∂P) ≤ δ ^ 2 / 2 ^ j)
    (he : ∀ s, err s ≤ 3 / 2 * (δ + noise s)) : Tracked P δ j err := by
  refine ⟨noise, hm, hn, hi, hv.trans ?_, fun s => (he s).trans (self_le_envelope ?_ (by norm_num))⟩
  · gcongr; nlinarith [sq_nonneg δ]
  · have := hn s; positivity

lemma child {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ)
    (old err noise : Ω → ℝ) (hp : Tracked P δ (j+1) old)
    (hm : Measurable noise) (hn : ∀ s, 0 ≤ noise s)
    (hi : Integrable (fun s => noise s ^ 2) P) (hv : (∫ s, noise s ^ 2 ∂P) ≤ δ ^ 2 / 2 ^ j)
    (hmove : ∀ s, err s ≤ old s + 11 * ((4 : ℝ) ^ j * δ))
    (hgood : ∀ s M, δ + noise s ≤ M → M ≤ (4 : ℝ) ^ j * δ → old s ≤ M → err s ≤ M) :
    Tracked P δ j err := by
  obtain ⟨w, hw, hw0, hwi, hwv, hwe⟩ := hp.witness
  let w' := fun s => max (w s) (noise s)
  have hm' : Measurable w' := hw.max hm
  have hn' (s) : 0 ≤ w' s := (hw0 s).trans (le_max_left _ _)
  have hsq (s) : w' s ^ 2 ≤ w s ^ 2 + noise s ^ 2 := by
    by_cases h : w s ≤ noise s
    · simp [w', max_eq_right h, sq_nonneg]
    · simp [w', max_eq_left (le_of_not_ge h), sq_nonneg]
  have hi' : Integrable (fun s => w' s ^ 2) P :=
    (hwi.add hi).mono' (hm'.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s => by simpa [Real.norm_eq_abs] using hsq s))
  refine ⟨w', hm', hn', hi', ?_, ?_⟩
  · have hh := integral_mono hi' (hwi.add hi) hsq
    simp only [Pi.add_apply] at hh
    rw [integral_add hwi hi] at hh
    exact hh.trans ((add_le_add hwv hv).trans_eq (by rw [pow_succ (2 : ℝ) j]; ring))
  · intro s
    let M := 3 / 2 * (δ + w' s)
    have hM : 0 ≤ M := by have := hn' s; dsimp [M]; positivity
    have hle : 3 / 2 * (δ + w s) ≤ M := by dsimp [M, w']; gcongr; exact le_max_left _ _
    have hnoise : δ + noise s ≤ M := by
      dsimp [M, w']
      linarith [le_max_right (w s) (noise s), hn s]
    apply envelope_step (by norm_num : (0 : ℝ) ≤ 11) (by positivity)
      (R := (4 : ℝ) ^ (j+1) * δ) _ ((hwe s).trans (envelope_mono hle (by norm_num) hM))
      (hmove s) (hgood s M hnoise)
    rw [pow_succ]
    nlinarith [show 0 ≤ (4 : ℝ) ^ j * δ by positivity]

lemma leaf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {δ : ℝ} (hδ : 0 ≤ δ) (err : Ω → ℝ) (hm : Measurable err) (hn : ∀ s, 0 ≤ err s)
    (h : Tracked P δ 0 err) : Integrable (fun s => err s ^ 2) P ∧
      (∫ s, err s ^ 2 ∂P) ≤ 7142 * δ ^ 2 := by
  obtain ⟨w, _, hw0, hwi, hwv, he⟩ := h.witness
  have hb (s) : err s ≤ 23 * (3 / 2 * (δ + w s)) := by
    have hpos := hw0 s
    have hb := envelope_le (M := 3 / 2 * (δ + w s)) (C := 11) (r := (4 : ℝ) ^ 0 * δ)
      (by positivity) (by norm_num) (by positivity)
    norm_num at hb
    simpa using (he s).trans (by simpa using hb)
  have hsq (s) : err s ^ 2 ≤ 4761 / 2 * (δ ^ 2 + w s ^ 2) := by
    nlinarith [mul_self_le_mul_self (hn s) (hb s), sq_nonneg (δ - w s)]
  have hI := ((integrable_const (μ := P) (δ ^ 2)).add hwi).const_mul (4761 / 2)
  have hei : Integrable (fun s => err s ^ 2) P := hI.mono' (hm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s => by simpa [Real.norm_eq_abs] using hsq s))
  refine ⟨hei, (integral_mono hei hI hsq).trans ?_⟩
  simp only [Pi.add_apply, integral_const_mul, integral_add (integrable_const _) hwi,
    integral_const, probReal_univ, one_smul]
  simp only [pow_zero, div_one] at hwv
  nlinarith [sq_nonneg δ]

end LongTails.Proofs.LeonPathMoments

namespace LongTails.Proofs.LeonStage

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.LeonAggregate
open LongTails.Algorithms.LeonTrajectory
open LeonRoundTrace

noncomputable def observed (R : Round p) : Point p := decode p.n (width p R.level) (spacing p)
  (radius p R.level) (R.model.anchors (R.level + 1)) (totalCodes p R.model R.level R.values)

noncomputable def raw (R : Round p) : Point p :=
  R.model.anchors (R.level + 1) + displacement p.n (spacing p) (totalCodes p R.model R.level R.values)

lemma stage_step (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (s : Samples p) (ls : List ℕ) (t : ℕ) :
    trajectory p g s ls (t + 1) =
      applyEstimate p (trajectory p g s ls t) (ls[t]?.getD 0) (observed (actualRound p g s ls t)) := rfl

lemma one_move (p : Params) (hε : 0 < p.ε) (hL : 0 < p.L)
    (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (ls : List ℕ) (t : ℕ) :
    ‖(trajectory p g s ls (t+1)).point - (trajectory p g s ls t).point‖ ≤
      if ls[t]?.getD 0 = 0 then resolution p / p.L else 0 := by
  rw [stage_step]
  unfold applyEstimate
  split_ifs with h
  · exact ParameterFreeNsgdmRun.normalized_move_norm _ (div_nonneg
      (LeonBatchTuning.resolution_pos p hε).le hL.le) _ _
  · simp

lemma raw_noise (p : Params) (hε : 0 < p.ε) (f : Functions p)
    (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (ls : List ℕ) (t : ℕ) :
    let R := actualRound p g s ls t
    ‖raw R - gradient (objective p f) R.model.point‖ ≤ resolution p +
      ‖LeonSampling.errorSum p f g R.level R.model.point (LeonAdaptiveSampling.shifted p (spent p (ls.take t)) s)‖ := by
  let R := actualRound p g s ls t
  let m := (p.n : ℝ)⁻¹ • ∑ i, mean p (R.values i)
  have h₁ : ‖raw R - m‖ ≤ resolution p := LeonRounding.raw_error p hε _ _ _
  have h₂ : m - gradient (objective p f) R.model.point = _ :=
    LeonAdaptiveSampling.error_eq p g f hf s (spent p (ls.take t)) R.level R.model.point
  exact (norm_sub_le_norm_sub_add_norm_sub _ m _).trans
    (add_le_add h₁ (by rw [h₂]))

lemma slot_step (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (s : Samples p) (ls : List ℕ) (t j : ℕ) (hne : j ≠ ls[t]?.getD 0) :
    (trajectory p g s ls (t+1)).anchors j = (trajectory p g s ls t).anchors j := by
  rw [stage_step]
  unfold applyEstimate
  split_ifs <;> simp [Function.update_of_ne hne]

lemma slot_set (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (s : Samples p) (ls : List ℕ) (t : ℕ) {j : ℕ} (h : ls[t]?.getD 0 = j + 1) :
    (trajectory p g s ls (t + 1)).anchors (j + 1) = observed (actualRound p g s ls t) ∧
      (trajectory p g s ls (t+1)).point = (trajectory p g s ls t).point := by
  rw [stage_step]
  simp [applyEstimate, h]

end LongTails.Proofs.LeonStage

namespace LongTails.Proofs.LeonChildGeometry

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonCalendar
open LongTails.Algorithms.LeonTrajectory
open LongTails.Algorithms.LeonTuning
open LeonRoundTrace LeonStage LeonBlocks LeonBlockCover

lemma geometry (p : Params) (hε : 0 < p.ε) (hL : 0 < p.L)
    (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (ls : List ℕ)
    (F : Point p → Point p) (hlip : ∀ x y, ‖F x - F y‖ ≤ p.L * ‖x - y‖)
    (t j k : ℕ) (ha : Aligned (fun i : ℕ => ls[i]?.getD 0) t (levels (j+1))) (hk : k < 4) :
    let u := t + 1 + k * (levels j).length
    (trajectory p g s ls u).anchors (j+1) = observed (actualRound p g s ls t) ∧
    ‖F (trajectory p g s ls u).point - F (trajectory p g s ls t).point‖ ≤
      3 * (4 : ℝ) ^ j * resolution p := by
  let level := fun i : ℕ => ls[i]?.getD 0
  let pre := copies (levels j) k
  have hp : Aligned level (t+1) pre := (child_alignment ha hk).1
  have hset := slot_set p g s ls t (children ha).1
  have hne : j+1 ∉ pre := fun h => Nat.not_succ_le_self j
    (level_le j _ (copies_mem _ _ _ h))
  have hanch := slot_constant (fun i => (trajectory p g s ls i).anchors) level
    (slot_step p g s ls) (j+1) pre (t+1) hp hne
  have hmove (i : ℕ) : ‖F (trajectory p g s ls (i+1)).point - F (trajectory p g s ls i).point‖ ≤
      if level i = 0 then resolution p else 0 := by
    apply (hlip _ _).trans
    have hh := mul_le_mul_of_nonneg_left (one_move p hε hL g s ls i) hL.le
    change _ ≤ p.L * (if level i = 0 then _ else 0) at hh
    split_ifs at hh ⊢ <;> simpa [hL.ne', mul_div_cancel₀, mul_comm p.L] using hh
  have hd := leaf_drift (fun i => F (trajectory p g s ls i).point) level hmove pre (t+1) hp
  dsimp only [pre] at hanch hd
  rw [copies_len] at hanch hd
  rw [copies_count, LeonCalendar.leaf_count, hset.2] at hd
  refine ⟨hanch.trans hset.1, hd.trans ?_⟩
  push_cast
  gcongr
  · exact (LeonBatchTuning.resolution_pos p hε).le
  exact_mod_cast (show k ≤ 3 by omega)

end LongTails.Proofs.LeonChildGeometry

namespace LongTails.Proofs.LeonTreeError

open MeasureTheory ProbabilityTheory

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Algorithms.LeonCalendar
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.LeonTrajectory
open LeonRoundTrace LeonStage LeonBlockCover LeonPathMoments

lemma head_level (j : ℕ) : (levels j)[0]?.getD 0 = j := by cases j <;> simp [levels]

lemma aligned_head {level : ℕ → ℕ} {u j : ℕ} (h : LeonBlocks.Aligned level u (levels j)) :
    level u = j := by
  cases j with
  | zero => simpa [levels] using h ⟨0, by simp [levels]⟩
  | succ j => exact (children h).1

set_option maxHeartbeats 800000 in
lemma leaf_error (p : Params) (hh : ∀ i, 0 < p.h i) (hε : 0 < p.ε) (hL : 0 < p.L)
    (P : Measure (Samples p)) [IsProbabilityMeasure P] (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (f : Functions p) (g : Fin p.n → Point p → p.Ω → Point p)
    (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hi : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) P)
    (hg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) p.σ)
    (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (J : ℕ) (hstart : ‖gradient (objective p f) p.x0‖ ≤ 4 ^ J * resolution p)
    (u : ℕ) (hu : u < (levels J).length) (hz : (levels J)[u]?.getD 0 = 0) :
    let R := fun s => actualRound p g s (levels J) u
    let e := fun s => ‖observed (R s) - gradient (objective p f) (R s).model.point‖ ^ 2
    Integrable e P ∧ (∫ s, e s ∂P) ≤ 7142 * resolution p ^ 2 := by
  let ls := levels J
  let level := fun i : ℕ => ls[i]?.getD 0
  let F := gradient (objective p f)
  let R := fun t s => actualRound p g s ls t
  let x := fun t s => (R t s).model.point
  let v := fun t s => observed (R t s)
  let e := fun t s => ‖v t s - F (x t s)‖
  let noise := fun t s => ‖LeonSampling.errorSum p f g (level t) (x t s)
    (LeonAdaptiveSampling.shifted p (spent p (ls.take t)) s)‖
  have hδ := (LeonBatchTuning.resolution_pos p hε).le
  have hstate t (ht : t ≤ ls.length) := LeonMeasurability.measurable_state p g
    (fun i => (hg i).measurable) id ls t ht (fun i j _ => (hi i).measurable j)
  have hnm (t : ℕ) (ht : t ≤ ls.length) : Measurable (noise t) := by
    have hx : Measurable (x t) := (hstate t ht).1
    have hs : Measurable (LeonAdaptiveSampling.shifted p (spent p (ls.take t))) :=
      Measurable.of_eval (fun i => Measurable.of_eval (fun j => (hi i).measurable (spent p (ls.take t) i + j)))
    have hcomp := (LeonFreshError.measurable_noise p μ f g hg (level t)).comp (hx.prodMk hs)
    exact hcomp
  have hmom t (ht : t ≤ ls.length) := LeonFreshError.adaptive_second_moment p hh hε P μ f g
    hw hi hg ls t ht (level t)
  have hr t s : ‖raw (R t s) - F (x t s)‖ ≤ resolution p + noise t s :=
    raw_noise p hε f hf g s ls t
  let G := fun t j => t + (levels j).length ≤ ls.length ∧ Tracked P (resolution p) j (e t)
  have hroot : G 0 J := by
    have h₀ : level 0 = J := head_level J
    have hm := hmom 0 (Nat.zero_le _)
    refine ⟨by simp [ls], root P hδ J _ (noise 0) (hnm 0 (Nat.zero_le _)) (fun _ => norm_nonneg _)
      hm.1 (hm.2.trans_eq (congrArg (fun j : ℕ => resolution p ^ 2 / 2 ^ j) h₀)) ?_⟩
    intro s
    let C := totalCodes p (R 0 s).model (level 0) (R 0 s).values
    have he := LeonEstimator.initial_error p hε (level 0) (F p.x0) C C (fun _ => rfl)
      (by simpa only [h₀] using hstart)
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa [raw, R, actualRound, trajectory, initial, C, level, x] using hr 0 s
  have hc t j k (ha : LeonBlocks.Aligned level t (levels (j+1))) (hk : k < 4)
      (hp : G t (j+1)) : G (t+1+k*(levels j).length) j := by
    let z := t+1+k*(levels j).length
    have hlen : z + (levels j).length ≤ ls.length := by
      have h := hp.1
      have hk' := Nat.mul_le_mul_right (levels j).length (show k ≤ 3 by omega)
      simp only [levels, List.length_cons, List.length_append] at h
      dsimp [z]; omega
    have hzt : z ≤ ls.length := by omega
    have hzj : level z = j := aligned_head (child_alignment ha hk).2
    have hm := hmom z hzt
    refine ⟨hlen, child P hδ j (e t) (e z) (noise z) hp.2 (hnm z hzt) (fun _ => norm_nonneg _)
      hm.1 (hm.2.trans_eq (congrArg (fun j : ℕ => resolution p ^ 2 / 2 ^ j) hzj)) ?_ ?_⟩
    · intro s
      obtain ⟨ha', hd⟩ := LeonChildGeometry.geometry p hε hL g s ls F hlip t j k ha hk
      let C := totalCodes p (R z s).model (level z) (R z s).values
      have hs := LeonAggregate.shifted_error p.n (width p j) (spacing p) (radius p j)
        (show 0 ≤ radius p j by unfold radius; positivity)
        ((R z s).model.anchors (j+1)) (F (x t s)) (F (x z s)) C
      change ‖LongTails.Algorithms.LeonAggregate.decode _ (width p (level z)) _ (radius p (level z))
        ((R z s).model.anchors (level z+1)) C - _‖ ≤ _
      rw [hzj]
      apply hs.trans
      change (R z s).model.anchors (j+1) = v t s at ha'
      rw [ha', norm_sub_rev (F (x t s))]
      change ‖v t s - F (x t s)‖ + radius p j + _ ≤ ‖v t s - F (x t s)‖ + _
      change ‖F (x z s) - F (x t s)‖ ≤ _ at hd
      unfold radius
      linarith
    · intro s M hn hscale hold
      obtain ⟨ha', hd⟩ := LeonChildGeometry.geometry p hε hL g s ls F hlip t j k ha hk
      let C := totalCodes p (R z s).model (level z) (R z s).values
      change ‖LongTails.Algorithms.LeonAggregate.decode _ (width p (level z)) _ (radius p (level z))
        ((R z s).model.anchors (level z+1)) C - _‖ ≤ _
      rw [hzj]
      apply LeonEstimator.exact_from_anchor p hε j _ _ (F (x t s)) C C M (fun _ => rfl) _ _ hd hscale
      · change (R z s).model.anchors (j+1) = v t s at ha'
        rw [ha']; exact hold
      · have h := (hr z s).trans hn
        change ‖(R z s).model.anchors (level z+1) + LongTails.Algorithms.LeonAggregate.displacement p.n (spacing p) C - F (x z s)‖ ≤ M at h
        rw [hzj] at h
        exact h
  have ha : LeonBlocks.Aligned level 0 (levels J) := by
    intro i
    simp [level, ls]
  have htrack := (all_leaves G hc J 0 u ha hroot (Nat.zero_le _) (by simpa using hu) hz).2
  have hLipF : LipschitzWith p.L.toNNReal F := lipschitzWith_iff_norm_sub_le.mpr (by
    simpa only [Real.coe_toNNReal _ hL.le] using hlip)
  have hF := hLipF.continuous
  have hmest : Measurable (v u) := LeonMeasurability.measurable_estimate p g (fun i => (hg i).measurable)
    id _ _ _ (hstate u hu.le).1 (hstate u hu.le).2 (fun i j _ => (hi i).measurable _)
  exact leaf P hδ _ ((hmest.sub (hF.measurable.comp (hstate u hu.le).1)).norm)
    (fun _ => norm_nonneg _) htrack

end LongTails.Proofs.LeonTreeError
