import LongTails.Proofs.StochasticEqualityModel
import LongTails.Proofs.StochasticEqualityExecution

namespace LongTails.Proofs.StochasticEqualityRestoration

open OracleTemplate
open LongTails.Setups.StochasticRegularEqualities
open LongTails.Algorithms.MatrixPolar
open LongTails.Algorithms.StochasticEquality
open LongTails.Proofs.StochasticEqualityModel
open LongTails.Proofs.StochasticEqualityTuning
open LongTails.Proofs.StochasticEqualityDescent
open LongTails.Proofs.StochasticEqualityExecution

lemma clipped_restoration_error (p : Public) {M t : ℝ} (hL : 0 ≤ p.Lc)
    (hM : 0 ≤ M) (u v : Reply p) (huJ : ‖u.2.2‖ ≤ p.Lc) (huc : ‖u.2.1‖ ≤ M)
    (hc : ‖v.2.1 - u.2.1‖ ≤ t) (hJ : ‖v.2.2 - u.2.2‖ ≤ t) :
    ‖operatorEquiv p.d p.m u.2.2 u.2.1 -
      operatorEquiv p.d p.m (clip p.Lc v.2.2) (clip M v.2.1)‖ ≤ (p.Lc + M) * t := by
  let A := operatorEquiv p.d p.m u.2.2
  let B := operatorEquiv p.d p.m (clip p.Lc v.2.2)
  have hB : ‖B‖ ≤ p.Lc := clipped_jacobian_norm p hL v
  have hAB : ‖A - B‖ ≤ t := by
    dsimp [A, B]
    rw [norm_sub_rev, ← map_sub]
    exact (MomentumSeparationInstance.spectralNorm_le_norm _).trans
      ((norm_clip_sub_le hL huJ _).trans hJ)
  have hcv : ‖u.2.1 - clip M v.2.1‖ ≤ t := by
    rw [norm_sub_rev]
    exact (norm_clip_sub_le hM huc _).trans hc
  have he : A u.2.1 - B (clip M v.2.1) = (A - B) u.2.1 + B (u.2.1 - clip M v.2.1) := by
    simp only [sub_apply, map_sub]
    abel
  change ‖A u.2.1 - B (clip M v.2.1)‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖(A - B) u.2.1‖ + ‖B (u.2.1 - clip M v.2.1)‖ := norm_add_le _ _
    _ ≤ ‖A - B‖ * ‖u.2.1‖ + ‖B‖ * ‖u.2.1 - clip M v.2.1‖ :=
      add_le_add ((A - B).le_opNorm _) (B.le_opNorm _)
    _ ≤ t * M + p.Lc * t := add_le_add
      (mul_le_mul hAB huc (norm_nonneg _) ((norm_nonneg _).trans hAB))
      (mul_le_mul hB hcv (norm_nonneg _) hL)
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
lemma admissible_restore_step (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (x : Point p.d) (v : Reply p.toPublic)
    (hcx : ‖I.c x‖ ≤ (tuning p.toPublic).restoreCap)
    (hvc : ‖v.2.1 - I.c x‖ ≤ (tuning p.toPublic).restoreTolerance)
    (hvJ : ‖v.2.2 - jacobian I x‖ ≤ (tuning p.toPublic).restoreTolerance) :
    let S := scale p.toPublic
    let cfg := tuning p.toPublic
    ‖I.c (restoreUpdate p.toPublic cfg x v)‖ ^ 2 ≤
      (1 - cfg.restoreStep * p.ν ^ 2) * ‖I.c x‖ ^ 2 +
        (cfg.restoreStep * p.ν ^ 2) * ((1 / (10 ^ 6 * S ^ 7)) ^ 2 / 16) := by
  let S := scale p.toPublic
  let cfg := tuning p.toPublic
  let J := fun y => (fderiv ℝ I.c y).adjoint
  let e := J x (I.c x) - operatorEquiv p.d p.m (clip p.Lc v.2.2) (clip cfg.restoreCap v.2.1)
  have hgeo := tuning_restoration_geometry p hp
  rcases hp with ⟨_, _, _, hν, _, hLc, hLJ, _, _, _, hC0, _, _⟩
  have hM : 0 ≤ cfg.restoreCap := by change 0 ≤ p.C0 + 1; linarith only [hC0]
  have herr : ‖e‖ ≤ p.ν * (1 / (10 ^ 6 * S ^ 7)) / 8 := by
    have he := clipped_restoration_error p.toPublic hLc hM (truth I x) v
      (hI.2.2.2.2.2.1 x) hcx hvc hvJ
    rw [truth_operator] at he
    exact he.trans hgeo.2.2.2
  have hJn : ∀ y, ‖J y‖ ≤ p.Lc := by
    intro y
    dsimp only [J]
    rw [← truth_operator I y]
    exact (MomentumSeparationInstance.spectralNorm_le_norm _).trans (hI.2.2.2.2.2.1 y)
  have hJL : ∀ y z, ‖J z - J y‖ ≤ p.LJ * ‖z - y‖ := by
    intro y z
    dsimp only [J]
    rw [← truth_operator I z, ← truth_operator I y, ← map_sub]
    exact (MomentumSeparationInstance.spectralNorm_le_norm _).trans (hI.2.2.2.2.2.2.1 y z)
  have hc : ∀ y, HasFDerivAt I.c (J y).adjoint y := by
    intro y
    simpa only [J, ContinuousLinearMap.adjoint_adjoint] using (hI.2.1 y).hasFDerivAt
  have hy : restoreUpdate p.toPublic cfg x v - x = cfg.restoreStep • (-J x (I.c x) + e) := by
    dsimp [restoreUpdate, e]
    module
  have hh := feasibility_descent hLc hLJ hν hgeo.1.le hc hJn hJL
    (hI.2.2.2.2.2.2.2.1 x) hcx hy hgeo.2.2.1
  have he2 := pow_le_pow_left₀ (norm_nonneg e) herr 2
  have he3 := mul_le_mul_of_nonneg_left he2 (show 0 ≤ 4 * cfg.restoreStep by linarith only [hgeo.1])
  dsimp only
  nlinarith only [hh, he3]

lemma restoration_trace_zero {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (offset : ℕ) :
    restorationTrace p cfg g ξ offset 0 = p.x0 := rfl

lemma restoration_trace_succ {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (offset n : ℕ) :
    restorationTrace p cfg g ξ offset (n + 1) =
      restoreUpdate p cfg (restorationTrace p cfg g ξ offset n)
        (restorationEstimate p cfg g ξ offset n) := by
  simp only [restorationTrace, restorePrefixPlan, restoreUnitCalls]
  rw [sampled_slot_succ_end, QueryPlan.sampledEval_map]
  rfl

lemma restoration_trace_terminal {Ω : Type*} (p : Public) (cfg : Config)
    (g : Point p.d → Ω → Reply p) (ξ : ℕ → Ω) (offset : ℕ) :
    restorationTrace p cfg g ξ offset cfg.restoreSteps =
      QueryPlan.sampledEval g (fun i => ξ (i / 2)) (restorePlan p cfg) (2 * offset) := rfl

set_option maxHeartbeats 1000000 in
lemma admissible_restoration_path (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) {Ω : Type*} (g : Point p.d → Ω → Reply p.toPublic)
    (ξ : ℕ → Ω) (offset : ℕ)
    (herrors : ∀ k : ℕ, k < (tuning p.toPublic).restoreSteps →
      ‖(restorationEstimate p.toPublic (tuning p.toPublic) g ξ offset k).2.1 -
        I.c (restorationTrace p.toPublic (tuning p.toPublic) g ξ offset k)‖ ≤
          (tuning p.toPublic).restoreTolerance ∧
      ‖(restorationEstimate p.toPublic (tuning p.toPublic) g ξ offset k).2.2 -
        jacobian I (restorationTrace p.toPublic (tuning p.toPublic) g ξ offset k)‖ ≤
          (tuning p.toPublic).restoreTolerance) :
    let S := scale p.toPublic
    let cfg := tuning p.toPublic
    let r := 1 / (10 ^ 6 * S ^ 7)
    (∀ k : ℕ, k ≤ cfg.restoreSteps → ‖I.c (restorationTrace p.toPublic cfg g ξ offset k)‖ ≤ cfg.restoreCap) ∧
    ‖I.c (QueryPlan.sampledEval g (fun i => ξ (i / 2)) (restorePlan p.toPublic cfg) (2 * offset))‖ ^ 2 <
      r ^ 2 / 8 := by
  let S := scale p.toPublic
  let cfg := tuning p.toPublic
  let r := 1 / (10 ^ 6 * S ^ 7)
  let a := cfg.restoreStep * p.ν ^ 2
  let v := fun k => ‖I.c (restorationTrace p.toPublic cfg g ξ offset k)‖ ^ 2
  let U := max (p.C0 ^ 2) (r ^ 2 / 16)
  have hgeo := tuning_restoration_geometry p hp
  have hS : 1 ≤ S := by have hh := (scale_bounds p hp).1; dsimp [S]; linarith only [hh]
  have hSpos : 0 < S := by linarith only [hS]
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 10 ^ 6 * S ^ 7)).mpr
    have hh : 1 ≤ S ^ 7 := one_le_pow₀ hS
    norm_num
    linarith only [hh]
  have hC := hp.2.2.2.2.2.2.2.2.2.2.1
  have hM : 0 ≤ cfg.restoreCap := by change 0 ≤ p.C0 + 1; linarith only [hC]
  have ha : 0 ≤ a := mul_nonneg hgeo.1.le (sq_nonneg _)
  have ha1 : a ≤ 1 := hgeo.2.1
  have hF : r ^ 2 / 16 ≤ U := le_max_right _ _
  have hr2 : r ^ 2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hr.le hr1 2
  have hU : U ≤ cfg.restoreCap ^ 2 := by
    change max (p.C0 ^ 2) (r ^ 2 / 16) ≤ (p.C0 + 1) ^ 2
    apply max_le <;> nlinarith only [hC, hr2, sq_nonneg p.C0]
  have hinit : v 0 ≤ p.C0 ^ 2 := by
    change ‖I.c p.x0‖ ^ 2 ≤ p.C0 ^ 2
    exact pow_le_pow_left₀ (norm_nonneg _) hI.2.2.2.1 2
  have hstep (k : ℕ) (hk : k < cfg.restoreSteps) (hvk : v k ≤ U) :
      v (k + 1) ≤ (1 - a) * v k + a * (r ^ 2 / 16) := by
    have hcap : ‖I.c (restorationTrace p.toPublic cfg g ξ offset k)‖ ≤ cfg.restoreCap :=
      (sq_le_sq₀ (norm_nonneg _) hM).mp (hvk.trans hU)
    have hh := admissible_restore_step p hp I O hI
      (restorationTrace p.toPublic cfg g ξ offset k) (restorationEstimate p.toPublic cfg g ξ offset k)
      hcap (herrors k hk).1 (herrors k hk).2
    simpa only [v, restoration_trace_succ] using hh
  have hpath : ∀ k : ℕ, k ≤ cfg.restoreSteps → v k ≤ U := by
    intro k
    induction k with
    | zero => exact fun _ => hinit.trans (le_max_left _ _)
    | succ k ih =>
      intro hk
      have hv := ih (by omega)
      have hs := hstep k (by omega) hv
      have hm := mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr ha1)
      have hf := mul_le_mul_of_nonneg_left hF ha
      nlinarith only [hs, hm, hf]
  refine ⟨fun k hk => (sq_le_sq₀ (norm_nonneg _) hM).mp ((hpath k hk).trans hU), ?_⟩
  have hh := StochasticEqualityStopped.restoration_accuracy v ha1 hr hinit cfg.restoreSteps
    (tuning_restoration_steps p hp) (fun k hk => hstep k hk (hpath k (by omega)))
  exact hh

lemma restoration_distance_budget (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    let cfg := tuning p.toPublic
    (cfg.restoreSteps : ℝ) * (cfg.restoreStep * p.Lc * cfg.restoreCap) ≤
      128 * S ^ 4 * (1 + Real.log S) := by
  let S := scale p.toPublic
  have ⟨hS, _, hcS, hCS, _, _, _, _, _⟩ := scale_bounds p hp
  have hS1 : 1 ≤ S := by dsimp [S]; linarith only [hS]
  have hSpos : 0 < S := by linarith only [hS1]
  have hell : 1 ≤ 1 + Real.log S := by linarith [Real.log_nonneg hS1]
  have hC := hp.2.2.2.2.2.2.2.2.2.2.1
  have hc := hp.2.2.2.2.2.1
  have hnom : 1 ≤ 4096 * S ^ 4 * (1 + Real.log S) := by
    have hs4 : 1 ≤ S ^ 4 := one_le_pow₀ hS1
    nlinarith
  have hN : ((tuning p.toPublic).restoreSteps : ℝ) ≤ 2 * (4096 * S ^ 4 * (1 + Real.log S)) :=
    positiveCeil_le_twice hnom
  have hstep : (tuning p.toPublic).restoreStep * p.Lc * (tuning p.toPublic).restoreCap ≤ 1 / 64 := by
    change (1 / (64 * S ^ 2)) * p.Lc * (p.C0 + 1) ≤ 1 / 64
    have hcS' : p.Lc ≤ S := by dsimp [S]; linarith only [hcS]
    have hCS' : p.C0 + 1 ≤ S := by dsimp [S]; linarith only [hCS]
    have hm := mul_le_mul hcS' hCS' (by linarith only [hC] : 0 ≤ p.C0 + 1) hSpos.le
    have he : (1 / (64 * S ^ 2)) * p.Lc * (p.C0 + 1) = (p.Lc * (p.C0 + 1)) / (64 * S ^ 2) := by ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < 64 * S ^ 2)).mpr
    nlinarith only [hm]
  have hh := mul_le_mul hN hstep
    (show 0 ≤ (tuning p.toPublic).restoreStep * p.Lc * (tuning p.toPublic).restoreCap by
      change 0 ≤ (1 / (64 * S ^ 2)) * p.Lc * (p.C0 + 1)
      positivity)
    (show 0 ≤ 2 * (4096 * S ^ 4 * (1 + Real.log S)) by positivity)
  convert hh using 1
  ring

lemma restoration_gap_polynomial {S : ℝ} (hS : 1 ≤ S) :
    S + 2 * S * (128 * S ^ 4 * (1 + Real.log S)) +
      S * (128 * S ^ 4 * (1 + Real.log S)) ^ 2 ≤ 70000 * S ^ 10 := by
  have hS0 : 0 ≤ S := by linarith only [hS]
  have hlog : 1 + Real.log S ≤ S := by
    linarith only [Real.log_le_sub_one_of_pos (by linarith : 0 < S)]
  have hquad := mul_le_mul_of_nonneg_left (log_factor_square hS)
    (show 0 ≤ 16384 * S ^ 9 by positivity)
  have hcross := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 256 * S ^ 5 by positivity)
  have h1 : S ≤ S ^ 10 := by simpa using pow_le_pow_right₀ hS (show 1 ≤ 10 by omega)
  have h6 : S ^ 6 ≤ S ^ 10 := pow_le_pow_right₀ hS (by norm_num)
  nlinarith only [hquad, hcross, h1, h6, pow_nonneg hS0 10]

set_option maxHeartbeats 1000000 in
lemma admissible_restored_gap (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (fLower : ℝ) (hlow : ∀ x, fLower ≤ I.f x)
    (hgap : I.f p.x0 - fLower ≤ p.Δ) {Ω : Type*} (g : Point p.d → Ω → Reply p.toPublic)
    (ξ : ℕ → Ω) (offset : ℕ) :
    I.f (QueryPlan.sampledEval g (fun i => ξ (i / 2)) (restorePlan p.toPublic (tuning p.toPublic))
      (2 * offset)) - fLower ≤ 70000 * (scale p.toPublic) ^ 10 := by
  let S := scale p.toPublic
  let cfg := tuning p.toPublic
  let y := QueryPlan.sampledEval g (fun i => ξ (i / 2)) (restorePlan p.toPublic cfg) (2 * offset)
  obtain ⟨hS, hfS, _, _, _, _, _, hΔS, _⟩ := scale_bounds p hp
  have hD := restoration_distance_budget p hp
  have hη := (tuning_restoration_geometry p hp).1
  rcases hp with ⟨_, _, _, _, hLf, hLc, _, _, _, _, hC0, _, _⟩
  have hS1 : 1 ≤ S := by dsimp [S]; linarith only [hS]
  have hSpos : 0 < S := by linarith only [hS1]
  have hL : 0 < 1 + p.Lf := by linarith only [hLf]
  have hLip : ∀ x z, ‖gradient I.f x - gradient I.f z‖ ≤ (1 + p.Lf) * ‖x - z‖ := by
    intro x z
    exact (hI.2.2.2.2.1 z x).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hg0 := HeavyTailedPL.gradient_sq_le hL hI.1 hLip hlow p.x0
  have hgap0 : 0 ≤ I.f p.x0 - fLower := sub_nonneg.mpr (hlow p.x0)
  have hg02 : ‖gradient I.f p.x0‖ ^ 2 ≤ 2 * S ^ 2 := by
    have hm := mul_le_mul (show 2 * (1 + p.Lf) ≤ 2 * S by dsimp [S]; linarith only [hfS])
      (hgap.trans hΔS) hgap0 (by positivity : 0 ≤ 2 * S)
    nlinarith only [hg0, hm]
  have hg0norm : ‖gradient I.f p.x0‖ ≤ 2 * S := by
    nlinarith only [hg02, norm_nonneg (gradient I.f p.x0), hSpos, sq_nonneg S]
  have hM : 0 ≤ cfg.restoreCap := by change 0 ≤ p.C0 + 1; linarith only [hC0]
  have hdist : ‖y - p.x0‖ ≤ 128 * S ^ 4 * (1 + Real.log S) :=
    (restoration_path_bound p.toPublic cfg g (fun i => ξ (i / 2)) (2 * offset) hLc hM hη.le).trans hD
  have hbound := StochasticEqualityMerit.objective_upper hLf hI.1 hI.2.2.2.2.1 p.x0 y
  have hinner := real_inner_le_norm (gradient I.f p.x0) (y - p.x0)
  have hlinear := mul_le_mul hg0norm hdist (norm_nonneg _) (by positivity : 0 ≤ 2 * S)
  have hquad := mul_le_mul (show p.Lf ≤ S by dsimp [S]; linarith only [hfS])
    (pow_le_pow_left₀ (norm_nonneg _) hdist 2) (sq_nonneg _) hSpos.le
  have hpoly := restoration_gap_polynomial hS1
  change I.f y - fLower ≤ _
  nlinarith only [hbound, hinner, hlinear, hquad, hgap.trans hΔS, hpoly]

lemma initial_merit_budget {S ν : ℝ} (hS : 1 ≤ S) (hinv : 1 / ν ≤ S) :
    70000 * S ^ 10 + ((4000 * S ^ 6) / ν) * (1 / (10 ^ 6 * S ^ 7)) +
      (10 ^ 10 * S ^ 24) * (1 / (10 ^ 6 * S ^ 7)) ^ 2 / 2 ≤ 10 ^ 6 * S ^ 10 - 1 := by
  have hSpos : 0 < S := by linarith only [hS]
  have hb : (4000 * S ^ 6) / ν ≤ 4000 * S ^ 7 := by
    have hh := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 4000 * S ^ 6 by positivity)
    convert hh using 1 <;> ring
  have hcross := mul_le_mul_of_nonneg_right hb (show 0 ≤ 1 / (10 ^ 6 * S ^ 7) by positivity)
  have he : (4000 * S ^ 7) * (1 / (10 ^ 6 * S ^ 7)) = 1 / 250 := by field_simp; norm_num
  rw [he] at hcross
  have hpen : (10 ^ 10 * S ^ 24) * (1 / (10 ^ 6 * S ^ 7)) ^ 2 / 2 = S ^ 10 / 200 := by
    field_simp
    ring
  rw [hpen]
  have hs10 : 1 ≤ S ^ 10 := one_le_pow₀ hS
  linarith only [hcross, hs10]

set_option maxHeartbeats 1000000 in
lemma restored_initial_bounds (p : Params) (hp : spec.valid p)
    (I : Instance p.toPublic) (O : Oracle (Point p.d) (Reply p.toPublic))
    (hI : spec.admissible p I O) (fLower : ℝ) (hlow : ∀ x, fLower ≤ I.f x)
    (x : Point p.d) (hgap : I.f x - fLower ≤ 70000 * (scale p.toPublic) ^ 10)
    (hc : ‖I.c x‖ ≤ 1 / (10 ^ 6 * (scale p.toPublic) ^ 7)) :
    let S := scale p.toPublic
    let cfg := tuning p.toPublic
    ‖gradient I.f x‖ ≤ cfg.gradientCap ∧ ‖I.c x‖ ≤ cfg.constraintCap ∧
      merit I.f I.c (fun y => (fderiv ℝ I.c y).adjoint) (gradient I.f)
        (10 ^ 10 * S ^ 24) x - fLower ≤ 10 ^ 6 * S ^ 10 - 1 := by
  let S := scale p.toPublic
  obtain ⟨hS, hfS, _, _, _, _, hinv, _, _⟩ := scale_bounds p hp
  have hS1 : 1 ≤ S := by dsimp [S]; linarith only [hS]
  have hSpos : 0 < S := by linarith only [hS1]
  rcases hp with ⟨_, _, _, hν, hLf, _, _, _, _, _, _, _, _⟩
  have hLip : ∀ y z, ‖gradient I.f y - gradient I.f z‖ ≤ (1 + p.Lf) * ‖y - z‖ := by
    intro y z
    exact (hI.2.2.2.2.1 z y).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hg := HeavyTailedPL.gradient_sq_le (show 0 < 1 + p.Lf by linarith only [hLf]) hI.1 hLip hlow x
  have hm := mul_le_mul (show 2 * (1 + p.Lf) ≤ 2 * S by dsimp [S]; linarith only [hfS])
    hgap (sub_nonneg.mpr (hlow x)) (show 0 ≤ 2 * S by positivity)
  have hp11 : S ^ 11 ≤ S ^ 12 := pow_le_pow_right₀ hS1 (by norm_num)
  have hgrad : ‖gradient I.f x‖ ≤ 4000 * S ^ 6 := by
    have hb : ‖gradient I.f x‖ ^ 2 ≤ (4000 * S ^ 6) ^ 2 := by
      nlinarith only [hg, hm, hp11, pow_nonneg hSpos.le 12]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hb
  refine ⟨hgrad, ?_, ?_⟩
  · apply hc.trans
    change 1 / (10 ^ 6 * S ^ 7) ≤ 1 / (10 * S ^ 7)
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [pow_nonneg hSpos.le 7])
  · have hmult := LongTails.Proofs.StochasticEqualityGeometry.norm_multiplier_le hν
      (hI.2.2.2.2.2.2.2.1 x) (gradient I.f x)
    have hmult' : ‖LongTails.Algorithms.StochasticEqualityDirection.multiplier
        ((fderiv ℝ I.c x).adjoint) (gradient I.f x)‖ ≤ (4000 * S ^ 6) / p.ν :=
      hmult.trans (div_le_div_of_nonneg_right hgrad hν.le)
    have hh := field_initial_bound (f := I.f) (c := I.c)
      (J := fun y => (fderiv ℝ I.c y).adjoint) (g := gradient I.f) (x := x)
      (show 0 ≤ 10 ^ 10 * S ^ 24 by positivity) hgap hmult' hc
    exact hh.trans (initial_merit_budget hS1 hinv)

lemma tuning_path_distance (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    let cfg := tuning p.toPublic
    (cfg.restoreSteps : ℝ) * (cfg.restoreStep * p.Lc * cfg.restoreCap) +
      (cfg.steps : ℝ) * (cfg.step * (cfg.gradientCap + p.Lc * cfg.constraintCap)) ≤
      10 ^ 16 * S ^ 18 / p.ε ^ 2 := by
  let S := scale p.toPublic
  let cfg := tuning p.toPublic
  have ⟨hS, _, hcS, _, _, _, _, _, _⟩ := scale_bounds p hp
  have hS1 : 1 ≤ S := by dsimp [S]; linarith only [hS]
  have hS0 : 0 < S := by linarith only [hS1]
  have hcS' : p.Lc ≤ S := by dsimp [S]; linarith only [hcS]
  have hc : 0 ≤ p.Lc := hp.2.2.2.2.2.1
  have hε : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hε1 : p.ε ≤ 1 := hp.2.2.2.2.2.2.2.2.2.2.2.2
  have hε2 : p.ε ^ 2 ≤ 1 := by nlinarith only [hε, hε1]
  have hM : p.Lc * cfg.constraintCap ≤ 1 := by
    change p.Lc * (1 / (10 * S ^ 7)) ≤ 1
    rw [mul_one_div]
    apply (div_le_one (by positivity : 0 < 10 * S ^ 7)).mpr
    have hpow : S ≤ S ^ 7 := by exact le_self_pow₀ hS1 (by norm_num)
    linarith only [hcS', hpow, hS0]
  have hdir : cfg.gradientCap + p.Lc * cfg.constraintCap ≤ 4500 * S ^ 6 := by
    change 4000 * S ^ 6 + p.Lc * cfg.constraintCap ≤ _
    have hpow : 1 ≤ S ^ 6 := one_le_pow₀ hS1
    linarith only [hM, hpow]
  have hT := (tuning_variance_parameters p hp).2.1
  have hstep : 0 ≤ cfg.step := (tuning_geometry p hp).1.le
  have hdir0 : 0 ≤ cfg.gradientCap + p.Lc * cfg.constraintCap := by
    have hgeo := tuning_geometry p hp
    exact add_nonneg hgeo.2.1 (mul_nonneg hc hgeo.2.2.1)
  have ht : (cfg.steps : ℝ) * (cfg.step * (cfg.gradientCap + p.Lc * cfg.constraintCap)) ≤
      9 * 10 ^ 15 * S ^ 18 / p.ε ^ 2 := by
    have hh := mul_le_mul hT (mul_le_mul_of_nonneg_left hdir hstep)
      (mul_nonneg hstep hdir0) (by positivity : 0 ≤ 2 * (10 ^ 24 * S ^ 38 / p.ε ^ 2))
    change (cfg.steps : ℝ) * _ ≤ _ at hh
    apply hh.trans_eq
    change (2 * (10 ^ 24 * S ^ 38 / p.ε ^ 2)) *
      ((1 / (10 ^ 12 * S ^ 26)) * (4500 * S ^ 6)) = _
    field_simp
    ring
  have hr := restoration_distance_budget p hp
  have hr' : (cfg.restoreSteps : ℝ) * (cfg.restoreStep * p.Lc * cfg.restoreCap) ≤
      10 ^ 15 * S ^ 18 / p.ε ^ 2 := by
    have hl : 1 + Real.log S ≤ S := by linarith only [Real.log_le_sub_one_of_pos hS0]
    have hh := hr.trans (mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 128 * S ^ 4))
    have hpow : S ^ 5 ≤ S ^ 18 := pow_le_pow_right₀ hS1 (by norm_num)
    have hnum : 128 * S ^ 5 * p.ε ^ 2 ≤ 10 ^ 15 * S ^ 18 := by
      have hm := mul_le_mul_of_nonneg_left hε2 (show 0 ≤ 128 * S ^ 5 by positivity)
      nlinarith only [hm, hpow, pow_nonneg hS0.le 18]
    apply hh.trans
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    nlinarith only [hnum]
  exact (add_le_add hr' ht).trans_eq (by ring)

end LongTails.Proofs.StochasticEqualityRestoration
