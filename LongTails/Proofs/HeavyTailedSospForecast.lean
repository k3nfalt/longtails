import LongTails.Proofs.HeavyTailedSospInvariants
import LongTails.Proofs.HeavyTailedSospDescent

namespace LongTails.Proofs.HeavyTailedSospForecast

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open HeavyTailedSospInvariants

noncomputable def displacement (p : Params) : Resume p → Space p
  | .ncRest n v => (n : ℝ) • v
  | _ => 0

noncomputable def forecast (p : Params) (s : State p) : Space p :=
  match s.phase with
  | .reset _ _ r => s.point + displacement p r
  | .transport v _ _ r => s.point + v + displacement p r
  | _ => s.point

noncomputable def gradientJump (p : Params) (c : Config) (f : Space p → ℝ) (s : State p) : ℝ :=
  if markCharge p s.phase = 1 then
    f (s.point - c.h • (‖s.estimate‖⁻¹ • s.estimate)) - f s.point else 0

lemma forecast_startCycle (p : Params) (c : Config) (f : Space p → ℝ) (s : State p) :
    f (forecast p (startCycle p c s)) = f s.point + gradientJump p c f (startCycle p c s) := by
  unfold startCycle
  split <;> simp [forecast, displacement, gradientJump, markCharge, sub_eq_add_neg]

lemma forecast_resume (p : Params) (c : Config) (f : Space p → ℝ) (s : State p) (r : Resume p) :
    f (forecast p (resume p c s r)) =
      f (s.point + displacement p r) + gradientJump p c f (resume p c s r) := by
  cases r with
  | startCycle => simpa [resume, displacement] using forecast_startCycle p c f s
  | detect => simp [resume, forecast, displacement, gradientJump, markCharge]
  | ncRest n v =>
    by_cases hn : n = 0
    · subst n
      simpa [resume, displacement] using
        forecast_startCycle p c f { s with cycleIndex := s.cycleIndex + 1 }
    · have hn1 : 1 ≤ n := by omega
      have heq : v + ((n - 1 : ℕ) : ℝ) • v = (n : ℝ) • v := by
        rw [Nat.cast_sub hn1, Nat.cast_one, sub_smul, one_smul]
        abel
      simp only [resume, hn, ↓reduceIte, forecast, displacement, gradientJump, markCharge]
      simp only [add_assoc, heq]
      simp

lemma forecast_completeTransport (p : Params) (c : Config) (f : Space p → ℝ)
    (s : State p) (v z : Space p) (r : Resume p) :
    f (forecast p (completeTransport p c s v z r)) =
      f (s.point + v + displacement p r) + gradientJump p c f (completeTransport p c s v z r) := by
  unfold completeTransport
  dsimp only
  split
  · simp [forecast, gradientJump, markCharge]
  · exact forecast_resume p c f _ r

lemma forecast_transportReply (p : Params) (c : Config) (f : Space p → ℝ)
    (s : State p) (v : Space p) (i : ℕ) (z reply : Space p) (r : Resume p) :
    f (forecast p (transportReply p c s v i z reply r)) =
      f (s.point + v + displacement p r) + gradientJump p c f (transportReply p c s v i z reply r) := by
  unfold transportReply
  split
  · cases r <;> simp [forecast, gradientJump, markCharge]
  · exact forecast_completeTransport p c f s v (z + reply) r

noncomputable def curvatureJump (p : Params) (c : Config) (f : Space p → ℝ)
    (s : State p) (a : Aux p c) : ℝ :=
  match s.phase with
  | .ncInit v => f (s.point + (max 1 c.ncSegments : ℕ) • signedSegment p c a v) - f s.point
  | _ => 0

lemma forecast_probeReply (p : Params) (c : Config) (f : Space p → ℝ)
    (s : State p) (trial : ℕ) (accepted : Option (Space p))
    (probe : LongTails.Algorithms.HeavyTailedEnergyProbe.State p.d) (reply : Space p) :
    f (forecast p (probeReply p c s trial accepted probe reply)) =
      f s.point + gradientJump p c f (probeReply p c s trial accepted probe reply) := by
  unfold probeReply
  dsimp only
  split <;> simp [forecast, gradientJump, markCharge]

lemma forecast_update (p : Params) (c : Config) (f : Space p → ℝ)
    (s : State p) (a : Aux p c) (reply : Space p) :
    f (forecast p (update p c s a reply)) - f (forecast p s) =
      gradientJump p c f (update p c s a reply) + curvatureJump p c f s a := by
  cases hp : s.phase with
  | reset i z r =>
    rw [show forecast p s = s.point + displacement p r by simp [forecast, hp]]
    simp only [update, hp, curvatureJump]
    split
    · simp [forecast, gradientJump, markCharge]
    · rw [forecast_resume p c f]
      simp
  | transport v i z r =>
    rw [show forecast p s = s.point + v + displacement p r by simp [forecast, hp]]
    simp only [update, hp, curvatureJump]
    rw [forecast_transportReply p c f]
    ring
  | probeInit trial accepted =>
    rw [show forecast p s = s.point by simp [forecast, hp]]
    simp only [update, hp, curvatureJump]
    rw [forecast_probeReply p c f]
    ring
  | probe trial accepted probe =>
    rw [show forecast p s = s.point by simp [forecast, hp]]
    simp only [update, hp, curvatureJump]
    rw [forecast_probeReply p c f]
    ring
  | validate trial accepted v values =>
    rw [show forecast p s = s.point by simp [forecast, hp]]
    simp only [update, hp, curvatureJump]
    split
    · simp [forecast, gradientJump, markCharge]
    · split
      · simp [forecast, gradientJump, markCharge]
      · split
        · rw [forecast_startCycle p c f]
          simp
        · simp [forecast, gradientJump, markCharge]
  | ncInit v =>
    rw [show forecast p s = s.point by simp [forecast, hp]]
    simp only [update, hp, curvatureJump]
    rw [forecast_transportReply p c f]
    have hm : 1 ≤ max 1 c.ncSegments := le_max_left _ _
    have heq : signedSegment p c a v +
        displacement p (.ncRest (max 1 c.ncSegments - 1) (signedSegment p c a v)) =
        (max 1 c.ncSegments : ℕ) • signedSegment p c a v := by
      simp only [displacement, Nat.cast_sub hm, Nat.cast_one, sub_smul, one_smul,
        ← Nat.cast_smul_eq_nsmul ℝ]
      abel
    rw [add_assoc, heq]
    ring
  | done => simp [update, hp, forecast, gradientJump, markCharge, curvatureJump]

lemma sum_shift (a : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, a (k + 1)) =
      (∑ k ∈ Finset.range N, a k) + a N - a 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

lemma forecast_trajectory (p : Params) (c : Config) (f : Space p → ℝ)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (ξ : ℕ → Aux p c × p.Ω) (N : ℕ) :
    let X := fun k => HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) k s ξ
    f (forecast p (X N)) - f (forecast p s) =
      (∑ k ∈ Finset.range N, gradientJump p c f (X (k + 1))) +
      ∑ k ∈ Finset.range N, curvatureJump p c f (X k) (ξ k).1 := by
  intro X
  induction N with
  | zero => simp [X, HeavyTailedProductProcess.trajectory]
  | succ N ih =>
    have hstep := forecast_update p c f (X N) (ξ N).1
      (let q := query p c (X N) (ξ N).1
        match q.2 with | none => g q.1 (ξ N).2 | some v => H q.1 (ξ N).2 v)
    have heq : X (N + 1) = update p c (X N) (ξ N).1
        (let q := query p c (X N) (ξ N).1
          match q.2 with | none => g q.1 (ξ N).2 | some v => H q.1 (ξ N).2 v) := by
      simp only [X, HeavyTailedProductProcess.trajectory_succ_last,
        HeavyTailedSospExecution.sampleStep]
      rfl
    rw [← heq] at hstep
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

lemma forecast_completed (p : Params) (c : Config) (f : Space p → ℝ)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target : ℕ) (ξ : ℕ → Aux p c × p.Ω) (N : ℕ)
    (hdone : (HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    let X := fun k => HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) k (initial p target) ξ
    f (X N).point - f p.x0 =
      (∑ k ∈ Finset.range N, gradientJump p c f (X k)) +
      ∑ k ∈ Finset.range N, curvatureJump p c f (X k) (ξ k).1 := by
  intro X
  have ht := forecast_trajectory p c f g H (initial p target) ξ N
  change f (forecast p (X N)) - f (forecast p (initial p target)) = _ at ht
  rw [sum_shift (fun k => gradientJump p c f (X k)) N] at ht
  have hn : gradientJump p c f (X N) = 0 := by
    simp [gradientJump, X, hdone, markCharge]
  have h0 : gradientJump p c f (X 0) = 0 := by
    simp [X, HeavyTailedProductProcess.trajectory, initial, gradientJump, markCharge]
  have hforecast : forecast p (X N) = (X N).point := by simp [forecast, X, hdone]
  rw [hn, h0, hforecast] at ht
  have hi : forecast p (initial p target) = p.x0 := by simp [forecast, initial, displacement]
  rw [hi] at ht
  simpa only [add_zero, sub_zero] using ht

lemma gradientJump_bound (p : Params) (c : Config) (f : Space p → ℝ)
    (G : Space p → Space p) (L : ℝ) (hL : 0 ≤ L) (hh : 0 ≤ c.h)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (s : State p) :
    gradientJump p c f s ≤
      if markCharge p s.phase = 1 then
        -c.h * ‖G s.point‖ + 2 * c.h * ‖s.estimate - G s.point‖ + L * c.h ^ 2 / 2
      else 0 := by
  unfold gradientJump
  split
  · have hb := HeavyTailedSospDescent.normalized_step_descent hL hh hG hLip s.point s.estimate
    rw [norm_sub_rev (G s.point)] at hb
    linarith
  · exact le_rfl

lemma full_signedSegment (p : Params) (c : Config) (a : Aux p c) (v : Space p) :
    (max 1 c.ncSegments : ℕ) • signedSegment p c a v =
      ((if a.2.1 then (1 : ℝ) else -1) * c.s) • v := by
  have hm : ((max 1 c.ncSegments : ℕ) : ℝ) ≠ 0 := by positivity
  rw [← Nat.cast_smul_eq_nsmul ℝ, signedSegment, smul_smul]
  congr 1
  field_simp

lemma curvatureJump_ncInit (p : Params) (c : Config) (f : Space p → ℝ)
    (s : State p) (a : Aux p c) (v : Space p) (hv : s.phase = .ncInit v) :
    curvatureJump p c f s a =
      f (s.point + ((if a.2.1 then (1 : ℝ) else -1) * c.s) • v) - f s.point := by
  simp only [curvatureJump, hv, full_signedSegment]

lemma completed_descent_bound (p : Params) (c : Config) (f : Space p → ℝ)
    (G : Space p → Space p) (L : ℝ) (hL : 0 ≤ L) (hh : 0 ≤ c.h)
    (hG : ∀ x, HasGradientAt f (G x) x)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target : ℕ) (ξ : ℕ → Aux p c × p.Ω) (N : ℕ)
    (hdone : (HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    let X := fun k => HeavyTailedProductProcess.trajectory
      (HeavyTailedSospExecution.sampleStep p c g H) k (initial p target) ξ
    f (X N).point - f p.x0 ≤
      (∑ k ∈ Finset.range N, if markCharge p (X k).phase = 1 then
        -c.h * ‖G (X k).point‖ + 2 * c.h * ‖(X k).estimate - G (X k).point‖ + L * c.h ^ 2 / 2
        else 0) +
      ∑ k ∈ Finset.range N, curvatureJump p c f (X k) (ξ k).1 := by
  intro X
  rw [forecast_completed p c f g H target ξ N hdone]
  exact add_le_add (Finset.sum_le_sum
    (fun k _ => gradientJump_bound p c f G L hL hh hG hLip (X k))) le_rfl

end LongTails.Proofs.HeavyTailedSospForecast
