import LongTails.Proofs.CompositeLazyCubicExecution
import LongTails.Proofs.CompositeExtrapolatedObjective
import LongTails.Proofs.CompositeGuardedSearch
import LongTails.Proofs.CompositeLocalCurvature
import LongTails.Proofs.CompositeCubicBridge
import LongTails.Proofs.CompositeCubicAcceleration

namespace LongTails.Proofs.CompositeLazyCubicConvergence

open OracleTemplate OracleTemplate.QueryPlan
open LongTails.Setups.CompositeLipschitzHessian
open LongTails.Algorithms.CompositeLazyCubic
open LongTails.Proofs.CompositeLazyCubicExecution
open LongTails.Proofs.CompositeExtrapolatedObjective
open scoped RealInnerProductSpace

noncomputable def innerObjective {p : Params} (F : Problem p) (center snapshot x : p.E) : ℝ :=
  value p (CompositeLocalObjective.smooth F center) snapshot x + regularizerScale p * F.ψ x

noncomputable def innerShift {p : Params} (F : Problem p) (center w snapshot x : p.E) : ℝ :=
  value p (shifted p (CompositeLocalObjective.smooth F center)
    (localGradient p center w (gradient F.f w)) w) snapshot x +
  regularizerScale p * shiftedRegularizer p F.ψ (localGradient p center w (gradient F.f w)) w x

lemma innerShift_offset {p : Params} (F : Problem p) (center w snapshot x : p.E) :
    innerShift F center w snapshot x = innerObjective F center snapshot x -
      (innerObjective F center snapshot snapshot - innerShift F center w snapshot snapshot) :=
  shifted_value_offset p _ _ _ _ _ _

lemma innerShift_nonneg {p : Params} (F : Problem p) (center w snapshot : p.E)
    (hf : Differentiable ℝ F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hγ : 0 ≤ cubicCoefficient p) (hψ : ConvexOn ℝ F.domain F.ψ) (hw : w ∈ F.domain)
    (hmin : ∀ u ∈ F.domain, CompositeLocalObjective.smooth F center w + F.ψ w ≤
      CompositeLocalObjective.smooth F center u + F.ψ u) {x : p.E} (hx : x ∈ F.domain) :
    0 ≤ innerShift F center w snapshot x := by
  have hfg := CompositeLocalObjective.smooth_hasGradient F center w hf
  have hφ := shifted_nonneg (CompositeLocalObjective.smooth_convex F center hc hγ)
    (fun u => CompositeLocalObjective.smooth_hasGradient F center u hf) w
  have hχ := shiftedRegularizer_nonneg hψ hw hfg hmin hx
  exact add_nonneg (value_nonneg hφ snapshot x)
    (mul_nonneg ((CompositeCurvatureParameters.scale_bounds p).1.trans' zero_le_one) hχ)

lemma innerShift_snapshot {p : Params} (F : Problem p) (center w snapshot : p.E)
    (hf : Differentiable ℝ F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hγ : 0 ≤ cubicCoefficient p) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hgap : CompositeLocalObjective.smooth F center snapshot + F.ψ snapshot -
      (CompositeLocalObjective.smooth F center w + F.ψ w) ≤ Δ) :
    innerShift F center w snapshot snapshot ≤ 2 * Δ := by
  have hφ := shifted_nonneg (CompositeLocalObjective.smooth_convex F center hc hγ)
    (fun u => CompositeLocalObjective.smooth_hasGradient F center u hf) w snapshot
  have hs := snapshot_level hφ (ψ := shiftedRegularizer p F.ψ (localGradient p center w (gradient F.f w)) w)
    (by simpa only [shifted_sum] using hgap)
  have ha := mul_le_mul_of_nonneg_right (CompositeCurvatureParameters.scale_bounds p).2 hΔ
  exact hs.trans ha

lemma eval_extrapolatedGradient {p : Params} (F : Problem p) (center snapshot v : p.E)
    (n i : ℕ) :
    eval (canonicalReply F) (extrapolatedGradient p center snapshot v n i) =
      ∑ j ∈ Finset.range n,
        ((1 / 64 : ℝ) ^ (i + j) * extrapolationFactor p ^ (i + j)) •
          localGradient p center (point p snapshot v (i + j))
            (gradient F.f (point p snapshot v (i + j))) := by
  induction n generalizing i with
  | zero => simp [extrapolatedGradient, eval]
  | succ n ih =>
      simp only [extrapolatedGradient, eval, canonicalReply, ite_true, readVector, eval_map]
      rw [ih, Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp only [show i + 1 + j = i + (j + 1) by omega, point]

lemma eval_extrapolatedGradient_full {p : Params} (F : Problem p) (center snapshot v : p.E) :
    eval (canonicalReply F) (extrapolatedGradient p center snapshot v (depth p + 1) 0) =
      grad p (fun x => localGradient p center x (gradient F.f x)) snapshot v := by
  simpa only [Nat.zero_add, grad] using eval_extrapolatedGradient F center snapshot v (depth p + 1) 0

lemma eval_searchTrial {p : Params} (F : Problem p) (center snapshot y : p.E)
    (B : p.E →L[ℝ] p.E) :
    let g := grad p (fun x => localGradient p center x (gradient F.f x)) snapshot
    let z := modelAnswer F (⟨y, g y, B, 0, regularizerScale p⟩ : Model p)
    eval (canonicalReply F) (searchTrial p center snapshot y B) =
      (⟨y, z, B (y - z), decide (⟪g z - g y, z - y⟫ ≤ ⟪z - y, B (z - y)⟫ / 2)⟩ : SearchTrial p) := by
  classical
  unfold searchTrial trialCalls
  simp only [eval_bind, eval_extrapolatedGradient_full, eval, canonicalReply, readVector, eval_map]

lemma local_shifted_sublevel_curvature {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hf : ContDiff ℝ 2 F.f)
    (hconv : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ) (center w y v : p.E) {Δ : ℝ}
    (hΔ : 0 < Δ) (hw : w ∈ F.domain) (hy : y ∈ F.domain) (hv : v ∈ F.domain)
    (hmin : ∀ u ∈ F.domain, CompositeLocalObjective.smooth F center w + F.ψ w ≤
      CompositeLocalObjective.smooth F center u + F.ψ u)
    (hgap : CompositeLocalObjective.smooth F center y + F.ψ y -
      (CompositeLocalObjective.smooth F center w + F.ψ w) ≤ Δ) :
    let f := CompositeLocalObjective.smooth F center
    let q := localGradient p center w (gradient F.f w)
    let A := fun x => localHessian p center x (fderiv ℝ (gradient F.f) x)
    value p (shifted p f q w) y v + regularizerScale p * shiftedRegularizer p F.ψ q w v ≤ 2 * Δ →
    ∀ d, ⟪d, hessian p A y v d⟫ ≤
      ⟪d, snapshotMetric p center y Δ (fderiv ℝ (gradient F.f) y) d⟫ / 16 := by
  dsimp only
  intro hlevel d
  have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
  have hH0 := CompositeCurvatureParameters.localHessianLip_pos p hH hm
  have hdiff := hf.differentiable (by norm_num)
  let f := CompositeLocalObjective.smooth F center
  let g := fun x => localGradient p center x (gradient F.f x)
  let A := fun x => localHessian p center x (fderiv ℝ (gradient F.f) x)
  let φ := shifted p f (g w) w
  let χ := shiftedRegularizer p F.ψ (g w) w
  let r := (Δ / localHessianLip p) ^ (1 / 3 : ℝ)
  have hr : 0 < r := metric_radius_pos hH0 hΔ
  have hcube : localHessianLip p * r ^ 3 = Δ := metric_radius_cube hH0 hΔ.le
  have hfc : ConvexOn ℝ Set.univ f := CompositeLocalObjective.smooth_convex F center hconv hγ.le
  have hfg : ∀ x, HasGradientAt f (g x) x := fun x => CompositeLocalObjective.smooth_hasGradient F center x hdiff
  have hgA : ∀ x, HasFDerivAt g (A x) x := fun x => CompositeLocalObjective.localGradient_hasFDerivAt F center x hf
  have hAL : ∀ x y, ‖A x - A y‖ ≤ localHessianLip p * ‖x - y‖ :=
    CompositeLocalObjective.localHessian_lipschitz F center hγ.le hLip
  have hφ0 : ∀ x, 0 ≤ φ x := shifted_nonneg hfc hfg w
  have hχ0 : ∀ x ∈ F.domain, 0 ≤ χ x := fun x hx =>
    shiftedRegularizer_nonneg hψ hw (hfg w) hmin hx
  have ht : ∀ x d, |φ (x + d) + φ (x - d) - 2 * φ x - ⟪d, A x d⟫| ≤
      localHessianLip p * ‖d‖ ^ 3 / 3 :=
    shifted_taylor (CubicRegularization.symmetric_taylor (fun x => (hfg x).hasFDerivAt) hgA hAL) (g w) w
  have hgrowth : ∀ x ∈ F.domain, cubicCoefficient p * ‖x - w‖ ^ 3 / 12 ≤ φ x + χ x := by
    intro x hx
    have hb := CompositeLocalObjective.composite_growth_at_minimizer F center hdiff hconv hγ.le hψ hw hx hmin
    change _ ≤ shifted p f (g w) w x + shiftedRegularizer p F.ψ (g w) w x
    rw [shifted_sum]
    have hn : 0 ≤ cubicCoefficient p * ‖x - w‖ ^ 3 := by positivity
    nlinarith only [hb, hn]
  have hb := sublevel_hessian_bound (shifted_convex hfc (g w) w) hφ0 hχ0 ht hAL hγ hH0.le hr hm
    (CompositeCurvatureParameters.local_condition_identity p hm) hgrowth hy hv
    (by simpa only [φ, χ, shifted_sum, hcube] using hgap)
    (by simpa only [hcube] using hlevel)
    (CompositeLocalObjective.localHessian_nonneg F center y hf hconv hγ.le) d
  exact hb

lemma metric_model_inequality {p : Params} (F : Problem p) (B : p.E →L[ℝ] p.E)
    {a : ℝ} {y z g u : p.E} (hz : (⟨y, g, B, 0, a⟩ : Model p).solution F z)
    (hu : u ∈ F.domain) :
    a * F.ψ z ≤ a * F.ψ u + ⟪g + B (z - y), u - z⟫ := by
  have hs := hz.2 u hu
  simp only [Model.derivative, zero_mul, zero_smul, add_zero] at hs
  linarith

lemma metric_model_certificate {p : Params} (F : Problem p) {h : p.E → ℝ} {g : p.E → p.E}
    (hc : ConvexOn ℝ Set.univ h) (hg : ∀ x, HasGradientAt h (g x) x)
    (B : p.E →L[ℝ] p.E) (a : ℝ) {y z u : p.E}
    (hz : (⟨y, g y, B, 0, a⟩ : Model p).solution F z) (hu : u ∈ F.domain)
    (hcert : ⟪g z - g y, z - y⟫ ≤ ⟪z - y, B (z - y)⟫ / 2) :
    h z + a * F.ψ z - (h u + a * F.ψ u) ≤
      ⟪B (y - z), y - u⟫ - ⟪z - y, B (z - y)⟫ / 2 := by
  have hs := hz.2 u hu
  simp only [Model.derivative, zero_mul, zero_smul, add_zero] at hs
  have hmap : B (z - y) = - B (y - z) := by rw [← map_neg]; congr 1; abel
  rw [hmap] at hs
  have hp : a * F.ψ z ≤ a * F.ψ u + ⟪g y - B (y - z), u - z⟫ := by
    simpa only [sub_eq_add_neg] using (show a * F.ψ z ≤ a * F.ψ u + ⟪g y + -B (y - z), u - z⟫ by linarith)
  have he : ⟪B (y - z), y - z⟫ = ⟪z - y, B (z - y)⟫ := by
    rw [hmap]
    have hd : z - y = -(y - z) := by abel
    rw [hd, inner_neg_left, inner_neg_right, neg_neg, real_inner_comm]
  apply CompositeGuardedSearch.residual_certificate (ψ := fun x => a * F.ψ x)
    (gy := g y) (gz := g z) (r := B (y - z)) ?_ ?_ hp he hcert
  · have h := OracleTemplate.Gradient.convex_support hc hg y u
    linarith
  · have h := OracleTemplate.Gradient.convex_support hc hg z y
    linarith

lemma eval_searchRounds_bracket (p : Params) (reply : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot x v : p.E) (B : p.E →L[ℝ] p.E) (n : ℕ) (state : SearchState p) :
    let trial := fun t => eval reply (searchTrial p center snapshot (x + t • (v - x)) B)
    (eval reply (searchRounds p center snapshot x v B n state)).bracket =
      LongTails.Algorithms.CompositeGuardedSearch.runBracket
        (fun t => ((trial t).certified, ⟪(trial t).residual, v - x⟫)) n state.bracket := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [searchRounds, eval_bind, LongTails.Algorithms.CompositeGuardedSearch.runBracket]
      exact ih _

lemma eval_searchRounds_lower (p : Params) (reply : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot x v : p.E) (B : p.E →L[ℝ] p.E) (n : ℕ) (state : SearchState p)
    (hstate : state.lowerTrial = eval reply
      (searchTrial p center snapshot (x + state.bracket.lower • (v - x)) B)) :
    let result := eval reply (searchRounds p center snapshot x v B n state)
    result.lowerTrial = eval reply (searchTrial p center snapshot (x + result.bracket.lower • (v - x)) B) := by
  induction n generalizing state with
  | zero => exact hstate
  | succ n ih =>
      simp only [searchRounds, eval_bind]
      apply ih
      dsimp only [LongTails.Algorithms.CompositeGuardedSearch.advance]
      split
      · rfl
      · exact hstate

lemma metric_model_initial {p : Params} (F : Problem p) {h : p.E → ℝ} {g : p.E → p.E}
    {A : p.E → p.E →L[ℝ] p.E} (hc : ConvexOn ℝ Set.univ h)
    (hψ : ConvexOn ℝ F.domain F.ψ) (hg : ∀ x, HasGradientAt h (g x) x)
    (hgA : ∀ x, HasFDerivAt g (A x) x) (hA : ∀ x d, 0 ≤ ⟪d, A x d⟫)
    (B : p.E →L[ℝ] p.E) {a μ : ℝ} (ha : 0 ≤ a) (hμ : 0 < μ)
    (hB : ∀ d, μ * ‖d‖ ^ 2 ≤ ⟪d, B d⟫) {y z : p.E} (hy : y ∈ F.domain)
    (hz : (⟨y, g y, B, 0, a⟩ : Model p).solution F z)
    (hbound : ∀ u ∈ F.domain, h u + a * F.ψ u ≤ h y + a * F.ψ y →
      ∀ d, ⟪d, A u d⟫ ≤ ⟪d, B d⟫ / 8) :
    h z + a * F.ψ z ≤ h y + a * F.ψ y ∧
      ⟪g z - g y, z - y⟫ ≤ ⟪z - y, B (z - y)⟫ / 8 := by
  by_cases heq : z = y
  · subst z
    simp
  have hd : 0 < ‖z - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
  have he : 0 < ⟪z - y, B (z - y)⟫ :=
    lt_of_lt_of_le (mul_pos hμ (sq_pos_of_pos hd)) (hB _)
  have hp := hz.2 y hy
  simp only [Model.derivative, zero_mul, zero_smul, add_zero] at hp
  have hid : y - z = -(z - y) := by abel
  rw [hid, inner_neg_right, inner_add_left, ← real_inner_comm (B (z - y)) (z - y)] at hp
  apply CompositeLocalCurvature.initial_prox_certificate hc (hψ.smul ha) hy hz.1
    (fun x => (hg x).hasFDerivAt) hgA hA hbound he
  change ⟪g y, z - y⟫ + ⟪z - y, B (z - y)⟫ + a * F.ψ z - a * F.ψ y ≤ 0
  linarith

lemma eval_guardedSearch (p : Params) (reply : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot x v : p.E) (B : p.E →L[ℝ] p.E) :
    let first := eval reply (searchTrial p center snapshot x B)
    let last := eval reply (searchTrial p center snapshot v B)
    let state := eval reply (searchRounds p center snapshot x v B (searchIterations p) ⟨⟨0, 1⟩, first⟩)
    eval reply (guardedSearch p center snapshot x v B) =
      if 0 ≤ ⟪first.residual, v - x⟫ then first
      else if last.certified = true ∧ ⟪last.residual, v - x⟫ ≤ 0 then last else state.lowerTrial := by
  classical
  simp only [guardedSearch, eval_bind, eval_map]

lemma eval_guardedSearch_range (p : Params) (reply : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot x v : p.E) (B : p.E →L[ℝ] p.E) :
    ∃ y, eval reply (guardedSearch p center snapshot x v B) = eval reply (searchTrial p center snapshot y B) := by
  classical
  rw [eval_guardedSearch]
  split_ifs
  · exact ⟨x, rfl⟩
  · exact ⟨v, rfl⟩
  · have h := eval_searchRounds_lower p reply center snapshot x v B (searchIterations p)
      (⟨⟨0, 1⟩, eval reply (searchTrial p center snapshot x B)⟩ : SearchState p)
      (by simp only [zero_smul, add_zero])
    exact ⟨_, h⟩

lemma searchTrial_properties {p : Params} (F : Problem p) (center snapshot y : p.E)
    (B : p.E →L[ℝ] p.E) (hf : Differentiable ℝ F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hγ : 0 ≤ cubicCoefficient p) (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain)
    (hB : ∀ x g, (⟨x, g, B, 0, regularizerScale p⟩ : Model p).valid) :
    let trial := eval (canonicalReply F) (searchTrial p center snapshot y B)
    let h := value p (CompositeLocalObjective.smooth F center) snapshot
    trial.query = y ∧ trial.point ∈ F.domain ∧
      (trial.certified = true → ∀ u ∈ F.domain,
        h trial.point + regularizerScale p * F.ψ trial.point - (h u + regularizerScale p * F.ψ u) ≤
          ⟪trial.residual, trial.query - u⟫ - ⟪trial.point - trial.query, B (trial.point - trial.query)⟫ / 2) := by
  rw [eval_searchTrial]
  dsimp only
  let g := grad p (fun x => localGradient p center x (gradient F.f x)) snapshot
  let q : Model p := ⟨y, g y, B, 0, regularizerScale p⟩
  have hz := modelAnswer_solution F q (hB _ _) hψ hclosed hx0
  refine ⟨rfl, hz.1, ?_⟩
  intro hcert u hu
  have hcert' := of_decide_eq_true hcert
  exact metric_model_certificate F
    (value_convex (CompositeLocalObjective.smooth_convex F center hc hγ) snapshot)
    (fun x => value_hasGradient (fun z => CompositeLocalObjective.smooth_hasGradient F center z hf) snapshot x)
    B (regularizerScale p) hz hu hcert'

lemma guardedSearch_residuals (p : Params) (reply : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot x v : p.E) (B : p.E →L[ℝ] p.E) (τ : p.E → SearchTrial p)
    (heval : ∀ y, eval reply (searchTrial p center snapshot y B) = τ y)
    (hquery : ∀ y, (τ y).query = y) (hfirst : (τ x).certified = true)
    {L ζ : ℝ} (hζ : 0 ≤ ζ)
    (hnear : ∀ l u, 0 ≤ l → l ≤ u → u ≤ 1 →
      (τ (x + l • (v - x))).certified = true → ⟪(τ (x + l • (v - x))).residual, v - x⟫ ≤ 0 →
      u - l ≤ (1 : ℝ) / 2 ^ searchIterations p →
      (τ (x + u • (v - x))).certified = true ∧
        |⟪(τ (x + u • (v - x))).residual, v - x⟫ -
          ⟪(τ (x + l • (v - x))).residual, v - x⟫| ≤ L * (u - l))
    (hsmall : L / 2 ^ searchIterations p ≤ ζ) :
    let result := eval reply (guardedSearch p center snapshot x v B)
    result.certified = true ∧ ⟪result.residual, result.query - x⟫ ≤ 0 ∧
      ⟪result.residual, result.query - v⟫ ≤ ζ := by
  classical
  rw [eval_guardedSearch]
  simp only [heval]
  split_ifs with hx hv
  · refine ⟨hfirst, ?_, ?_⟩
    · rw [hquery]; simp
    · rw [hquery]
      have he : x - v = -(v - x) := by abel
      rw [he, inner_neg_right]
      linarith
  · refine ⟨hv.1, ?_, ?_⟩
    · rw [hquery]; exact hv.2
    · rw [hquery]; simpa using hζ
  · let evaluate : ℝ → Bool × ℝ := fun t =>
      ((τ (x + t • (v - x))).certified, ⟪(τ (x + t • (v - x))).residual, v - x⟫)
    let b := LongTails.Algorithms.CompositeGuardedSearch.runBracket evaluate (searchIterations p) ⟨0, 1⟩
    have hzero : x + (0 : ℝ) • (v - x) = x := by simp
    have hone : x + (1 : ℝ) • (v - x) = v := by simp
    have hl : (evaluate 0).1 = true ∧ (evaluate 0).2 ≤ 0 := by
      dsimp [evaluate]
      rw [hzero]
      exact ⟨hfirst, le_of_lt (lt_of_not_ge hx)⟩
    have hu : 0 ≤ (evaluate 1).2 ∨ (evaluate 1).1 ≠ true := by
      dsimp [evaluate]
      rw [hone]
      by_cases hc : (τ v).certified = true
      · exact Or.inl (le_of_lt (lt_of_not_ge (fun h => hv ⟨hc, h⟩)))
      · exact Or.inr hc
    have hb := CompositeGuardedSearch.runBracket_accuracy evaluate (searchIterations p) hl hu
      (fun l u hl hlu hu hc hq hw => (hnear l u hl hlu hu hc hq hw).1)
      (fun l u hl hlu hu hc hq hw => (hnear l u hl hlu hu hc hq hw).2) le_rfl hsmall
    have hi := CompositeGuardedSearch.runBracket_interval evaluate (searchIterations p)
      (⟨0, 1⟩ : LongTails.Algorithms.CompositeGuardedSearch.Bracket) (by norm_num)
    have hbr : (eval reply (searchRounds p center snapshot x v B (searchIterations p) ⟨⟨0, 1⟩, τ x⟩)).bracket = b := by
      simpa only [heval] using eval_searchRounds_bracket p reply center snapshot x v B
        (searchIterations p) (⟨⟨0, 1⟩, τ x⟩ : SearchState p)
    have hlo := eval_searchRounds_lower p reply center snapshot x v B (searchIterations p)
      (⟨⟨0, 1⟩, τ x⟩ : SearchState p) (by simp only [zero_smul, add_zero, heval])
    dsimp only at hlo
    rw [hbr, heval] at hlo
    rw [hlo]
    refine ⟨hb.1, ?_, ?_⟩
    · rw [hquery]
      simp only [add_sub_cancel_left, inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos hi.1 hb.2.2
    · rw [hquery]
      exact CompositeGuardedSearch.segment_residual hi.1 hb.2.1 hb.2.2

lemma segment_trial_neighbor {p : Params} (F : Problem p) {h : p.E → ℝ} {g z : p.E → p.E}
    {A : p.E → p.E →L[ℝ] p.E} (hc : ConvexOn ℝ Set.univ h)
    (hg : ∀ x, HasGradientAt h (g x) x) (hgA : ∀ x, HasFDerivAt g (A x) x)
    (B : p.E →L[ℝ] p.E) (hB : IsUnit B)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    (hAs : ∀ x u v, ⟪u, A x v⟫ = ⟪A x u, v⟫) (hAp : ∀ x d, 0 ≤ ⟪d, A x d⟫)
    {a Δ offset : ℝ} (hΔ : 0 ≤ Δ)
    (hsol : ∀ y, (⟨y, g y, B, 0, a⟩ : Model p).solution F (z y))
    (hlower : ∀ u ∈ F.domain, offset ≤ h u + a * F.ψ u)
    (hdom : ∀ q ∈ F.domain, h q + a * F.ψ q ≤ offset + 2 * Δ →
      ∀ u, CurvatureMetric.metricNorm B (u - q) ≤ 4 * Real.sqrt Δ →
        ∀ d, ⟪d, A u d⟫ ≤ (1 / 4 : ℝ) * ⟪d, B d⟫)
    {x v : p.E} (hx : x ∈ F.domain) (hxlevel : h x + a * F.ψ x ≤ offset + 2 * Δ)
    {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u)
    (hcert : ⟪g (z (x + l • (v - x))) - g (x + l • (v - x)), z (x + l • (v - x)) - (x + l • (v - x))⟫ ≤
      ⟪z (x + l • (v - x)) - (x + l • (v - x)), B (z (x + l • (v - x)) - (x + l • (v - x)))⟫ / 2)
    (hqlow : ⟪B ((x + l • (v - x)) - z (x + l • (v - x))), v - x⟫ ≤ 0)
    (hnear : CurvatureMetric.metricNorm B ((x + u • (v - x)) - (x + l • (v - x))) ≤ Real.sqrt Δ / 2) :
    let yl := x + l • (v - x)
    let yu := x + u • (v - x)
    ⟪g (z yu) - g yu, z yu - yu⟫ ≤ ⟪z yu - yu, B (z yu - yu)⟫ / 2 ∧
      |⟪B (yu - z yu), v - x⟫ - ⟪B (yl - z yl), v - x⟫| ≤
        (9 / 4 : ℝ) * CurvatureMetric.metricNorm B (v - x) ^ 2 * (u - l) := by
  let yl := x + l • (v - x)
  let yu := x + u • (v - x)
  have hres := metric_model_certificate F hc hg B a (hsol yl) hx hcert
  have he : ⟪z yl - yl, B (z yl - yl)⟫ = CurvatureMetric.metricNorm B (yl - z yl) ^ 2 := by
    rw [CurvatureMetric.metricNorm_sq B hp]
    have hd : z yl - yl = -(yl - z yl) := by abel
    rw [hd, map_neg, inner_neg_left, inner_neg_right, neg_neg]
  rw [he] at hres
  have hd := CompositeLocalCurvature.certified_trial_distance B hl hΔ
    (sub_nonneg.mpr (hlower (z yl) (hsol yl).1))
    (show h x + a * F.ψ x - offset ≤ 2 * Δ by linarith)
    hqlow (show (h (z yl) + a * F.ψ (z yl) - offset) - (h x + a * F.ψ x - offset) ≤
      ⟪B (yl - z yl), yl - x⟫ - CurvatureMetric.metricNorm B (yl - z yl) ^ 2 / 2 by linarith only [hres])
  have hinner : ⟪B (yl - z yl), yl - x⟫ = l * ⟪B (yl - z yl), v - x⟫ := by
    dsimp only [yl]
    simp only [add_sub_cancel_left, inner_smul_right]
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos hl hqlow
  have hzlevel : h (z yl) + a * F.ψ (z yl) ≤ offset + 2 * Δ := by
    rw [hinner] at hres
    nlinarith only [hres, hnonpos, hxlevel, sq_nonneg (CurvatureMetric.metricNorm B (yl - z yl))]
  have hn := CompositeLocalCurvature.certified_neighbor (ψ := fun x => a * F.ψ x)
    (yl := yl) (yu := yu) (zl := z yl) (zu := z yu) B hB hs hp (Real.sqrt_nonneg Δ) hgA hAs hAp
    (hdom (z yl) (hsol yl).1 hzlevel) hd hnear
    (metric_model_inequality F B (hsol yu) (hsol yl).1)
    (metric_model_inequality F B (hsol yl) (hsol yu).1)
  refine ⟨?_, ?_⟩
  · have h := hn.1
    rw [CurvatureMetric.metricNorm_sq B hp] at h
    have hpos := hp (z yu - yu)
    linarith
  · have hr := hn.2
    have hline : yu - yl = (u - l) • (v - x) := by dsimp [yu, yl]; module
    rw [hline] at hr
    exact CurvatureMetric.residual_direction_bound B hB hs hp (sub_nonneg.mpr hlu) hr

lemma guardedSearch_geometry {p : Params} (F : Problem p)
    (reply : Fin 3 × (p.E ⊕ Model p) → Reply p) (center snapshot x v : p.E)
    {h : p.E → ℝ} {g z : p.E → p.E} {A : p.E → p.E →L[ℝ] p.E}
    (hc : ConvexOn ℝ Set.univ h) (hψ : ConvexOn ℝ F.domain F.ψ)
    (hg : ∀ x, HasGradientAt h (g x) x) (hgA : ∀ x, HasFDerivAt g (A x) x)
    (B : p.E →L[ℝ] p.E) {μ Δ offset : ℝ} (hμ : 0 < μ) (hΔ : 0 ≤ Δ)
    (hBl : ∀ d, μ * ‖d‖ ^ 2 ≤ ⟪d, B d⟫)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hAs : ∀ x u v, ⟪u, A x v⟫ = ⟪A x u, v⟫) (hAp : ∀ x d, 0 ≤ ⟪d, A x d⟫)
    (hsol : ∀ y, (⟨y, g y, B, 0, regularizerScale p⟩ : Model p).solution F (z y))
    (hlower : ∀ u ∈ F.domain, offset ≤ h u + regularizerScale p * F.ψ u)
    (hbase : ∀ q ∈ F.domain, h q + regularizerScale p * F.ψ q ≤ offset + 2 * Δ →
      ∀ d, ⟪d, A q d⟫ ≤ ⟪d, B d⟫ / 16)
    (hdom : ∀ q ∈ F.domain, h q + regularizerScale p * F.ψ q ≤ offset + 2 * Δ →
      ∀ u, CurvatureMetric.metricNorm B (u - q) ≤ 4 * Real.sqrt Δ →
        ∀ d, ⟪d, A u d⟫ ≤ (1 / 4 : ℝ) * ⟪d, B d⟫)
    (hx : x ∈ F.domain) (hxlevel : h x + regularizerScale p * F.ψ x ≤ offset + 2 * Δ)
    (hdir : CurvatureMetric.metricNorm B (v - x) ^ 2 ≤
      (2 : ℝ) ^ 40 * ((depth p : ℝ) + 1) ^ 2 * condition p ^ 3 * Δ)
    (heval : ∀ y, eval reply (searchTrial p center snapshot y B) =
      (⟨y, z y, B (y - z y), decide (⟪g (z y) - g y, z y - y⟫ ≤ ⟪z y - y, B (z y - y)⟫ / 2)⟩ : SearchTrial p)) :
    let result := eval reply (guardedSearch p center snapshot x v B)
    result.certified = true ∧ ⟪result.residual, result.query - x⟫ ≤ 0 ∧
      ⟪result.residual, result.query - v⟫ ≤ Δ / 100 := by
  classical
  let τ : p.E → SearchTrial p := fun y =>
    ⟨y, z y, B (y - z y), decide (⟪g (z y) - g y, z y - y⟫ ≤ ⟪z y - y, B (z y - y)⟫ / 2)⟩
  have hp : ∀ d, 0 ≤ ⟪d, B d⟫ := fun d => (mul_nonneg hμ.le (sq_nonneg ‖d‖)).trans (hBl d)
  have hunit := CurvatureMetric.isUnit_of_lower B hμ hBl
  have ha : 0 ≤ regularizerScale p := (CompositeCurvatureParameters.scale_bounds p).1.trans' zero_le_one
  have hinit := metric_model_initial F hc hψ hg hgA hAp B ha hμ hBl hx (hsol x)
    (fun u hu hlevel d => by
      have hh := hbase u hu (hlevel.trans hxlevel) d
      have hpos := hp d
      linarith)
  have hfirst : (τ x).certified = true := by
    dsimp only [τ]
    apply decide_eq_true
    have hh := hinit.2
    have hpos := hp (z x - x)
    linarith
  have hresolution := CompositeCurvatureParameters.search_resolution
    (CurvatureMetric.metricNorm_nonneg B (v - x)) hΔ hdir
  apply guardedSearch_residuals p reply center snapshot x v B τ heval (fun _ => rfl) hfirst
    (by positivity : 0 ≤ Δ / 100) (L := (9 / 4 : ℝ) * CurvatureMetric.metricNorm B (v - x) ^ 2) ?_ hresolution.1
  intro l u hl hlu _hu hcert hq hw
  have hcert' := of_decide_eq_true hcert
  have hnear : CurvatureMetric.metricNorm B ((x + u • (v - x)) - (x + l • (v - x))) ≤ Real.sqrt Δ / 2 := by
    have he : (x + u • (v - x)) - (x + l • (v - x)) = (u - l) • (v - x) := by module
    rw [he, CurvatureMetric.metricNorm_smul B hp, abs_of_nonneg (sub_nonneg.mpr hlu)]
    have hh := mul_le_mul_of_nonneg_right hw (CurvatureMetric.metricNorm_nonneg B (v - x))
    have hh' : (u - l) * CurvatureMetric.metricNorm B (v - x) ≤
        CurvatureMetric.metricNorm B (v - x) / 2 ^ searchIterations p := by simpa only [one_div_mul_eq_div] using hh
    exact hh'.trans hresolution.2
  have hn := segment_trial_neighbor F hc hg hgA B hunit hs hp hAs hAp hΔ hsol hlower hdom
    hx hxlevel hl hlu hcert' hq hnear
  exact ⟨decide_eq_true hn.1, hn.2⟩

lemma canonical_guardedSearch {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hf : ContDiff ℝ 2 F.f)
    (hc : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain) (center w snapshot x v : p.E) {Δ : ℝ}
    (hΔ : 0 < Δ) (hw : w ∈ F.domain) (hy : snapshot ∈ F.domain) (hx : x ∈ F.domain)
    (hmin : ∀ u ∈ F.domain, CompositeLocalObjective.smooth F center w + F.ψ w ≤
      CompositeLocalObjective.smooth F center u + F.ψ u)
    (hgap : CompositeLocalObjective.smooth F center snapshot + F.ψ snapshot -
      (CompositeLocalObjective.smooth F center w + F.ψ w) ≤ Δ)
    (hxlevel : innerShift F center w snapshot x ≤ 2 * Δ)
    (hdir : CurvatureMetric.metricNorm
      (snapshotMetric p center snapshot Δ (fderiv ℝ (gradient F.f) snapshot)) (v - x) ^ 2 ≤
      (2 : ℝ) ^ 40 * ((depth p : ℝ) + 1) ^ 2 * condition p ^ 3 * Δ) :
    let B := snapshotMetric p center snapshot Δ (fderiv ℝ (gradient F.f) snapshot)
    let result := eval (canonicalReply F) (guardedSearch p center snapshot x v B)
    result.certified = true ∧ ⟪result.residual, result.query - x⟫ ≤ 0 ∧
      ⟪result.residual, result.query - v⟫ ≤ Δ / 100 := by
  let B := snapshotMetric p center snapshot Δ (fderiv ℝ (gradient F.f) snapshot)
  let f := CompositeLocalObjective.smooth F center
  let g0 := fun u => localGradient p center u (gradient F.f u)
  let A0 := fun u => localHessian p center u (fderiv ℝ (gradient F.f) u)
  let h := value p f snapshot
  let g := grad p g0 snapshot
  let A := hessian p A0 snapshot
  let z := fun u => modelAnswer F (⟨u, g u, B, 0, regularizerScale p⟩ : Model p)
  let r := (Δ / localHessianLip p) ^ (1 / 3 : ℝ)
  let μ := 4096 * ((depth p : ℝ) + 1) ^ 2 * localHessianLip p * r
  let offset := innerObjective F center snapshot snapshot - innerShift F center w snapshot snapshot
  have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
  have hH0 := CompositeCurvatureParameters.localHessianLip_pos p hH hm
  have hdiff := hf.differentiable (by norm_num)
  have hr : 0 < r := metric_radius_pos hH0 hΔ
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hBl : ∀ d, μ * ‖d‖ ^ 2 ≤ ⟪d, B d⟫ :=
    CompositeLocalObjective.snapshotMetric_lower F center snapshot hf hc hγ.le
  have hs : ∀ u v, ⟪u, B v⟫ = ⟪B u, v⟫ :=
    CompositeLocalObjective.snapshotMetric_symmetric F center snapshot Δ hf
  have hfc : ConvexOn ℝ Set.univ f := CompositeLocalObjective.smooth_convex F center hc hγ.le
  have hfg : ∀ u, HasGradientAt f (g0 u) u := fun u => CompositeLocalObjective.smooth_hasGradient F center u hdiff
  have hgA : ∀ u, HasFDerivAt g0 (A0 u) u := fun u => CompositeLocalObjective.localGradient_hasFDerivAt F center u hf
  have hAL : ∀ u v, ‖A0 u - A0 v‖ ≤ localHessianLip p * ‖u - v‖ :=
    CompositeLocalObjective.localHessian_lipschitz F center hγ.le hLip
  have hsol : ∀ u, (⟨u, g u, B, 0, regularizerScale p⟩ : Model p).solution F (z u) := fun u =>
    modelAnswer_solution F _ (CompositeLocalObjective.snapshot_model_valid F center snapshot u (g u) hf hc hH hm hΔ)
      hψ hclosed hx0
  have hshift (u : p.E) : innerShift F center w snapshot u = h u + regularizerScale p * F.ψ u - offset :=
    innerShift_offset F center w snapshot u
  have hlower : ∀ u ∈ F.domain, offset ≤ h u + regularizerScale p * F.ψ u := by
    intro u hu
    have hn := innerShift_nonneg F center w snapshot hdiff hc hγ.le hψ hw hmin hu
    rw [hshift] at hn
    linarith
  have hbase : ∀ u ∈ F.domain, h u + regularizerScale p * F.ψ u ≤ offset + 2 * Δ →
      ∀ d, ⟪d, A u d⟫ ≤ ⟪d, B d⟫ / 16 := by
    intro u hu hlevel d
    have hlevel' : innerShift F center w snapshot u ≤ 2 * Δ := by rw [hshift]; linarith
    exact local_shifted_sublevel_curvature F hH hm hf hc hLip hψ center w snapshot u hΔ hw hy hu hmin hgap hlevel' d
  have hdom : ∀ q ∈ F.domain, h q + regularizerScale p * F.ψ q ≤ offset + 2 * Δ →
      ∀ u, CurvatureMetric.metricNorm B (u - q) ≤ 4 * Real.sqrt Δ →
        ∀ d, ⟪d, A u d⟫ ≤ (1 / 4 : ℝ) * ⟪d, B d⟫ := by
    intro q hq hlevel u hnear d
    have ht := extrapolated_tube_bound hH0 hr (metric_radius_cube hH0 hΔ.le) hAL B snapshot q u
      hBl (hbase q hq hlevel) hnear d
    linarith
  apply guardedSearch_geometry F (canonicalReply F) center snapshot x v
    (value_convex hfc snapshot) hψ (fun u => value_hasGradient hfg snapshot u)
    (fun u => grad_hasFDerivAt hgA snapshot u) B hμ hΔ.le hBl hs
    (fun u a b => hessian_symmetric (CompositeLocalObjective.localHessian_symmetric F center · hf) snapshot u a b)
    (fun u d => hessian_nonneg (fun q d => CompositeLocalObjective.localHessian_nonneg F center q hf hc hγ.le d) snapshot u d)
    hsol hlower hbase hdom hx (by rw [hshift] at hxlevel; linarith) hdir
  intro u
  exact eval_searchTrial F center snapshot u B

lemma canonical_search_certificate {p : Params} (F : Problem p) (center snapshot x v : p.E)
    (B : p.E →L[ℝ] p.E) (hunit : IsUnit B) (hp : ∀ d, 0 ≤ ⟪d, B d⟫)
    (hf : Differentiable ℝ F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hγ : 0 ≤ cubicCoefficient p) (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain)
    (hB : ∀ y g, (⟨y, g, B, 0, regularizerScale p⟩ : Model p).valid)
    (hcert : (eval (canonicalReply F) (guardedSearch p center snapshot x v B)).certified = true) :
    let result := eval (canonicalReply F) (guardedSearch p center snapshot x v B)
    result.point ∈ F.domain ∧ result.residual = B (result.query - result.point) ∧
      ∀ u ∈ F.domain, innerObjective F center snapshot result.point - innerObjective F center snapshot u ≤
        ⟪result.residual, result.query - u⟫ - CurvatureMetric.metricNorm B (Ring.inverse B result.residual) ^ 2 / 2 := by
  obtain ⟨y, hy⟩ := eval_guardedSearch_range p (canonicalReply F) center snapshot x v B
  rw [hy] at hcert ⊢
  let trial := eval (canonicalReply F) (searchTrial p center snapshot y B)
  have hprops := searchTrial_properties F center snapshot y B hf hc hγ hψ hclosed hx0 hB
  have hr : trial.residual = B (trial.query - trial.point) := by
    dsimp only [trial]
    rw [eval_searchTrial]
  refine ⟨hprops.2.1, hr, ?_⟩
  intro u hu
  have h := hprops.2.2 hcert u hu
  have he : ⟪trial.point - trial.query, B (trial.point - trial.query)⟫ =
      CurvatureMetric.metricNorm B (Ring.inverse B trial.residual) ^ 2 := by
    rw [hr, CurvatureMetric.apply_inverse B hunit, CurvatureMetric.metricNorm_sq B hp]
    have hd : trial.point - trial.query = -(trial.query - trial.point) := by abel
    rw [hd, map_neg, inner_neg_left, inner_neg_right, neg_neg]
  change innerObjective F center snapshot trial.point - innerObjective F center snapshot u ≤ _
  rw [← he]
  exact h

lemma advance_potential {p : Params} (B : p.E →L[ℝ] p.E) (hB : IsUnit B)
    (hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫) (hp : ∀ x, 0 ≤ ⟪x, B x⟫)
    (F : p.E → ℝ) (k : ℕ) (state : LongTails.Algorithms.CompositeGuardedSearch.AccelerationState p.E)
    (trial : SearchTrial p) (u : p.E) {ζ : ℝ}
    (hcx : F trial.point - F state.point ≤ ⟪trial.residual, trial.query - state.point⟫ -
      CurvatureMetric.metricNorm B (Ring.inverse B trial.residual) ^ 2 / 2)
    (hcu : F trial.point - F u ≤ ⟪trial.residual, trial.query - u⟫ -
      CurvatureMetric.metricNorm B (Ring.inverse B trial.residual) ^ 2 / 2)
    (hrx : ⟪trial.residual, trial.query - state.point⟫ ≤ 0)
    (hrv : ⟪trial.residual, trial.query - state.momentum⟫ ≤ ζ) :
    let next := LongTails.Algorithms.CompositeGuardedSearch.acceleratedAdvance B k state trial.point trial.residual
    F next.point ≤ F state.point ∧
      (((k : ℝ) + 1) * ((k : ℝ) + 2) / 4) * (F next.point - F u) +
        CurvatureMetric.metricNorm B (next.momentum - u) ^ 2 / 2 ≤
      ((k : ℝ) * ((k : ℝ) + 1) / 4) * (F state.point - F u) +
        CurvatureMetric.metricNorm B (state.momentum - u) ^ 2 / 2 + ((k : ℝ) + 1) / 2 * ζ := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have h := CompositeGuardedSearch.accelerated_potential B hB hs hp
    (A := (k : ℝ) * ((k : ℝ) + 1) / 4) (a := ((k : ℝ) + 1) / 2)
    (by positivity) (by positivity) (by nlinarith only [hk]) hcx hcu hrx hrv
  have he : (k : ℝ) * ((k : ℝ) + 1) / 4 + ((k : ℝ) + 1) / 2 =
      ((k : ℝ) + 1) * ((k : ℝ) + 2) / 4 := by ring
  rw [he] at h
  refine ⟨?_, h⟩
  change F trial.point ≤ F state.point
  nlinarith only [hcx, hrx, sq_nonneg (CurvatureMetric.metricNorm B (Ring.inverse B trial.residual))]

lemma acceleratedRounds_invariant (p : Params) (reply : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (center snapshot : p.E) (B : p.E →L[ℝ] p.E)
    (P : ℕ → LongTails.Algorithms.CompositeGuardedSearch.AccelerationState p.E → Prop) (N : ℕ)
    (hstep : ∀ k < N, ∀ state, P k state →
      let trial := eval reply (guardedSearch p center snapshot state.point state.momentum B)
      P (k + 1) (LongTails.Algorithms.CompositeGuardedSearch.acceleratedAdvance B k state trial.point trial.residual))
    (n k : ℕ) (state : LongTails.Algorithms.CompositeGuardedSearch.AccelerationState p.E)
    (hkn : k + n ≤ N) (hstate : P k state) :
    P (k + n) (eval reply (acceleratedRounds p center snapshot B n k state)) := by
  induction n generalizing k state with
  | zero => simpa only [Nat.add_zero, acceleratedRounds, eval] using hstate
  | succ n ih =>
      simp only [acceleratedRounds, eval_bind]
      have h := ih (k + 1) _ (by omega) (hstep k (by omega) state hstate)
      simpa only [Nat.add_assoc, Nat.add_comm 1 n] using h

lemma epoch_comparator {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hf : ContDiff ℝ 2 F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ) (center w snapshot : p.E) {Δ : ℝ}
    (hΔ : 0 < Δ) (hw : w ∈ F.domain) (hy : snapshot ∈ F.domain)
    (hmin : ∀ u ∈ F.domain, CompositeLocalObjective.smooth F center w + F.ψ w ≤
      CompositeLocalObjective.smooth F center u + F.ψ u)
    (hgap : CompositeLocalObjective.smooth F center snapshot + F.ψ snapshot -
      (CompositeLocalObjective.smooth F center w + F.ψ w) ≤ Δ) :
    let u := snapshot + (extrapolationFactor p ^ depth p)⁻¹ • (w - snapshot)
    let B := snapshotMetric p center snapshot Δ (fderiv ℝ (gradient F.f) snapshot)
    u ∈ F.domain ∧ innerShift F center w snapshot u ≤ 2 * Δ ∧
      CurvatureMetric.metricNorm B (u - snapshot) ^ 2 ≤
        131072 * (p.m : ℝ) ^ 2 * ((depth p : ℝ) + 1) ^ 2 * Δ := by
  let f := CompositeLocalObjective.smooth F center
  let g := fun x => localGradient p center x (gradient F.f x)
  let A := fun x => localHessian p center x (fderiv ℝ (gradient F.f) x)
  let φ := shifted p f (g w) w
  let χ := shiftedRegularizer p F.ψ (g w) w
  let r := (Δ / localHessianLip p) ^ (1 / 3 : ℝ)
  let B := snapshotMetric p center snapshot Δ (fderiv ℝ (gradient F.f) snapshot)
  have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
  have hH0 := CompositeCurvatureParameters.localHessianLip_pos p hH hm
  have hdiff := hf.differentiable (by norm_num)
  have hfc : ConvexOn ℝ Set.univ f := CompositeLocalObjective.smooth_convex F center hc hγ.le
  have hfg : ∀ x, HasGradientAt f (g x) x := fun x => CompositeLocalObjective.smooth_hasGradient F center x hdiff
  have hgA : ∀ x, HasFDerivAt g (A x) x := fun x => CompositeLocalObjective.localGradient_hasFDerivAt F center x hf
  have hAL : ∀ x y, ‖A x - A y‖ ≤ localHessianLip p * ‖x - y‖ :=
    CompositeLocalObjective.localHessian_lipschitz F center hγ.le hLip
  have hφ0 : ∀ x, 0 ≤ φ x := shifted_nonneg hfc hfg w
  have hχy : 0 ≤ χ snapshot := shiftedRegularizer_nonneg hψ hw (hfg w) hmin hy
  have hφχ : φ snapshot + χ snapshot ≤ Δ := by simpa only [φ, χ, shifted_sum] using hgap
  have hφy : φ snapshot ≤ Δ := by linarith
  have hzero : φ w = 0 ∧ χ w = 0 := shifted_at_base p f F.ψ (g w) w
  have hcomp := comparator_level_bound (shifted_convex hfc (g w) w)
    (shiftedRegularizer_convex hψ (g w) w) hy hw hzero.1 hzero.2 hΔ.le (hφ0 snapshot) hφχ
  refine ⟨comparator_mem hψ.1 hy hw, hcomp, ?_⟩
  have hr : 0 < r := metric_radius_pos hH0 hΔ
  have hcube : localHessianLip p * r ^ 3 = Δ := metric_radius_cube hH0 hΔ.le
  have ht := shifted_taylor (CubicRegularization.symmetric_taylor (fun x => (hfg x).hasFDerivAt) hgA hAL) (g w) w
  have hgrowth := CompositeLocalObjective.composite_growth_at_minimizer F center hdiff hc hγ.le hψ hw hy hmin
  have hgy : cubicCoefficient p * ‖snapshot - w‖ ^ 3 / 12 ≤ Δ := by
    have hn : 0 ≤ cubicCoefficient p * ‖snapshot - w‖ ^ 3 := by positivity
    linarith
  have hdist := snapshot_distance_bound (shifted_convex hfc (g w) w) hφ0 ht hAL hH0 hr.le hΔ.le hm
    (CompositeCurvatureParameters.local_condition_identity p hm) hcube hzero.1 hφy hgy
  have hBpos : ∀ d, 0 ≤ ⟪d, B d⟫ := by
    intro d
    have hl := CompositeLocalObjective.snapshotMetric_lower F center snapshot (Δ := Δ) hf hc hγ.le d
    have hn : 0 ≤ 4096 * ((depth p : ℝ) + 1) ^ 2 * localHessianLip p * r * ‖d‖ ^ 2 := by positivity
    exact hn.trans hl
  have h := comparator_metric_bound B hBpos hdist
  convert h using 1
  ring

lemma epoch_point_distance {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hf : ContDiff ℝ 2 F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ) (center w snapshot x : p.E) {Δ : ℝ}
    (hΔ : 0 < Δ) (hw : w ∈ F.domain) (hy : snapshot ∈ F.domain) (hx : x ∈ F.domain)
    (hmin : ∀ u ∈ F.domain, CompositeLocalObjective.smooth F center w + F.ψ w ≤
      CompositeLocalObjective.smooth F center u + F.ψ u)
    (hgap : CompositeLocalObjective.smooth F center snapshot + F.ψ snapshot -
      (CompositeLocalObjective.smooth F center w + F.ψ w) ≤ Δ)
    (hxlevel : innerShift F center w snapshot x ≤ 2 * Δ) :
    CurvatureMetric.metricNorm (snapshotMetric p center snapshot Δ (fderiv ℝ (gradient F.f) snapshot)) (x - snapshot) ^ 2 ≤
      153000 * ((depth p : ℝ) + 1) ^ 2 * condition p ^ 3 * Δ := by
  let f := CompositeLocalObjective.smooth F center
  let g := fun u => localGradient p center u (gradient F.f u)
  let A := fun u => localHessian p center u (fderiv ℝ (gradient F.f) u)
  let φ := shifted p f (g w) w
  let χ := shiftedRegularizer p F.ψ (g w) w
  let r := (Δ / localHessianLip p) ^ (1 / 3 : ℝ)
  have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
  have hH0 := CompositeCurvatureParameters.localHessianLip_pos p hH hm
  have hdiff := hf.differentiable (by norm_num)
  have hfc : ConvexOn ℝ Set.univ f := CompositeLocalObjective.smooth_convex F center hc hγ.le
  have hfg : ∀ u, HasGradientAt f (g u) u := fun u => CompositeLocalObjective.smooth_hasGradient F center u hdiff
  have hgA : ∀ u, HasFDerivAt g (A u) u := fun u => CompositeLocalObjective.localGradient_hasFDerivAt F center u hf
  have hAL : ∀ u v, ‖A u - A v‖ ≤ localHessianLip p * ‖u - v‖ :=
    CompositeLocalObjective.localHessian_lipschitz F center hγ.le hLip
  have hφ0 : ∀ u, 0 ≤ φ u := shifted_nonneg hfc hfg w
  have hχ0 : ∀ u ∈ F.domain, 0 ≤ χ u := fun u hu => shiftedRegularizer_nonneg hψ hw (hfg w) hmin hu
  have hφχ : φ snapshot + χ snapshot ≤ Δ := by simpa only [φ, χ, shifted_sum] using hgap
  have hφy : φ snapshot ≤ Δ := by linarith [hχ0 snapshot hy]
  have hxgap : φ x + χ x ≤ 3 * Δ :=
    original_gap_of_level (shifted_convex hfc (g w) w) (hφ0 snapshot) hφy hxlevel
  have hφx : φ x ≤ 3 * Δ := by linarith [hχ0 x hx]
  have hygrowth := CompositeLocalObjective.composite_growth_at_minimizer F center hdiff hc hγ.le hψ hw hy hmin
  have hxgrowth := CompositeLocalObjective.composite_growth_at_minimizer F center hdiff hc hγ.le hψ hw hx hmin
  have hgrowth_y : cubicCoefficient p * ‖snapshot - w‖ ^ 3 / 12 ≤ Δ := by
    have hn : 0 ≤ cubicCoefficient p * ‖snapshot - w‖ ^ 3 := by positivity
    linarith
  have hgrowth_x : cubicCoefficient p * ‖x - w‖ ^ 3 / 12 ≤ 3 * Δ := by
    rw [show φ x + χ x = f x + F.ψ x - (f w + F.ψ w) from shifted_sum p f F.ψ (g w) w x] at hxgap
    have hn : 0 ≤ cubicCoefficient p * ‖x - w‖ ^ 3 := by positivity
    nlinarith only [hxgrowth, hxgap, hn]
  have hr : 0 < r := metric_radius_pos hH0 hΔ
  have hb := sublevel_metric_bound hfg hgA hAL
    (CompositeLocalObjective.localHessian_nonneg F center w hf hc hγ.le)
    hγ hr.le hΔ.le (CompositeCurvatureParameters.local_condition_identity p hm)
    (metric_radius_cube hH0 hΔ.le) hφy hφx hgrowth_y hgrowth_x
  have hvalid := CompositeLocalObjective.snapshot_model_valid F center snapshot snapshot 0 hf hc hH hm hΔ
  rw [CurvatureMetric.metricNorm_sq _ hvalid.2.2.2.1]
  exact hb

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
lemma accelerated_epoch_accuracy {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hf : ContDiff ℝ 2 F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain) (center w snapshot : p.E) {Δ : ℝ}
    (hΔ : 0 < Δ) (hw : w ∈ F.domain) (hy : snapshot ∈ F.domain)
    (hmin : ∀ u ∈ F.domain, CompositeLocalObjective.smooth F center w + F.ψ w ≤
      CompositeLocalObjective.smooth F center u + F.ψ u)
    (hgap : CompositeLocalObjective.smooth F center snapshot + F.ψ snapshot -
      (CompositeLocalObjective.smooth F center w + F.ψ w) ≤ Δ) :
    let B := snapshotMetric p center snapshot Δ (fderiv ℝ (gradient F.f) snapshot)
    let u := snapshot + (extrapolationFactor p ^ depth p)⁻¹ • (w - snapshot)
    let result := eval (canonicalReply F) (acceleratedRounds p center snapshot B (innerIterations p) 0 ⟨snapshot, snapshot⟩)
    result.point ∈ F.domain ∧ innerObjective F center snapshot result.point - innerObjective F center snapshot u ≤ Δ / 12 := by
  let B := snapshotMetric p center snapshot Δ (fderiv ℝ (gradient F.f) snapshot)
  let u := snapshot + (extrapolationFactor p ^ depth p)⁻¹ • (w - snapshot)
  let N := innerIterations p
  let R2 := 131072 * (p.m : ℝ) ^ 2 * ((depth p : ℝ) + 1) ^ 2 * Δ
  let obj := innerObjective F center snapshot
  let offset := obj snapshot - innerShift F center w snapshot snapshot
  let P : ℕ → LongTails.Algorithms.CompositeGuardedSearch.AccelerationState p.E → Prop := fun k state =>
    state.point ∈ F.domain ∧ obj state.point ≤ obj snapshot ∧
      ((k : ℝ) * ((k : ℝ) + 1) / 4) * (obj state.point - obj u) +
        CurvatureMetric.metricNorm B (state.momentum - u) ^ 2 / 2 ≤
      R2 / 2 + ((k : ℝ) * ((k : ℝ) + 1) / 4) * (Δ / 100)
  have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
  have hH0 := CompositeCurvatureParameters.localHessianLip_pos p hH hm
  have hdiff := hf.differentiable (by norm_num)
  have hvalid : ∀ y g, (⟨y, g, B, 0, regularizerScale p⟩ : Model p).valid :=
    fun y g => CompositeLocalObjective.snapshot_model_valid F center snapshot y g hf hc hH hm hΔ
  have hp : ∀ d, 0 ≤ ⟪d, B d⟫ := (hvalid snapshot 0).2.2.2.1
  have hs : ∀ x y, ⟪x, B y⟫ = ⟪B x, y⟫ := (hvalid snapshot 0).2.2.1
  have hunit : IsUnit B := by
    obtain hzero | ⟨μ, hμ, hl⟩ := (hvalid snapshot 0).2.2.2.2
    · norm_num at hzero
    · exact CurvatureMetric.isUnit_of_lower B hμ hl
  have hcomp := epoch_comparator F hH hm hf hc hLip hψ center w snapshot hΔ hw hy hmin hgap
  have hu : u ∈ F.domain := hcomp.1
  have hR : CurvatureMetric.metricNorm B (u - snapshot) ^ 2 ≤ R2 := hcomp.2.2
  have hshift (x : p.E) : innerShift F center w snapshot x = obj x - offset := innerShift_offset F center w snapshot x
  have hlower : ∀ x ∈ F.domain, offset ≤ obj x := by
    intro x hx
    have hn := innerShift_nonneg F center w snapshot hdiff hc hγ.le hψ hw hmin hx
    rw [hshift] at hn
    linarith
  have huGap : obj u - offset ≤ 2 * Δ := by simpa only [hshift] using hcomp.2.1
  have hyLevel := innerShift_snapshot F center w snapshot hdiff hc hγ.le hΔ.le hgap
  have hstart : P 0 ⟨snapshot, snapshot⟩ := by
    refine ⟨hy, le_rfl, ?_⟩
    have he : snapshot - u = -(u - snapshot) := by abel
    have hr : CurvatureMetric.metricNorm B (snapshot - u) ^ 2 ≤ R2 := by
      rw [he, CurvatureMetric.metricNorm_neg B hp]
      exact hR
    dsimp only
    norm_num
    linarith only [hr]
  have hstep : ∀ k < N, ∀ state, P k state →
      let trial := eval (canonicalReply F) (guardedSearch p center snapshot state.point state.momentum B)
      P (k + 1) (LongTails.Algorithms.CompositeGuardedSearch.acceleratedAdvance B k state trial.point trial.residual) := by
    intro k hk state hstate
    obtain ⟨hx, hobj, hpot⟩ := hstate
    have hxlevel : innerShift F center w snapshot state.point ≤ 2 * Δ := by
      rw [hshift] at hyLevel ⊢
      linarith
    have hX := epoch_point_distance F hH hm hf hc hLip hψ center w snapshot state.point hΔ hw hy hx hmin hgap hxlevel
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast (le_of_lt hk)
    have hk1 : (k : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hk
    have hprod := mul_le_mul hkN hk1 (by positivity : 0 ≤ (k : ℝ) + 1) hN0
    have hAN : (k : ℝ) * ((k : ℝ) + 1) / 4 ≤ (innerIterations p : ℝ) ^ 2 := by
      change _ ≤ (N : ℝ) ^ 2
      nlinarith only [hprod, sq_nonneg (N : ℝ)]
    have hdir := CompositeCurvatureParameters.inner_direction_scalar hm hΔ.le
      (by positivity : 0 ≤ (k : ℝ) * ((k : ℝ) + 1) / 4) hAN (hlower state.point hx) huGap hpot hX hR
      (CurvatureMetric.metricNorm_sub_three_sq B hp state.momentum state.point u snapshot)
    have hsearch := canonical_guardedSearch F hH hm hf hc hLip hψ hclosed hx0 center w snapshot
      state.point state.momentum hΔ hw hy hx hmin hgap hxlevel hdir
    have hcert := canonical_search_certificate F center snapshot state.point state.momentum B hunit hp hdiff hc hγ.le
      hψ hclosed hx0 hvalid hsearch.1
    have hadv := advance_potential B hunit hs hp obj k state
      (eval (canonicalReply F) (guardedSearch p center snapshot state.point state.momentum B)) u
      (hcert.2.2 state.point hx) (hcert.2.2 u hu) hsearch.2.1 hsearch.2.2
    dsimp only [P, LongTails.Algorithms.CompositeGuardedSearch.acceleratedAdvance]
    refine ⟨hcert.1, hadv.1.trans hobj, ?_⟩
    have he := hadv.2
    dsimp only [LongTails.Algorithms.CompositeGuardedSearch.acceleratedAdvance] at he
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith only [he, hpot]
  have hfinal := acceleratedRounds_invariant p (canonicalReply F) center snapshot B P N hstep N 0
    (⟨snapshot, snapshot⟩ : LongTails.Algorithms.CompositeGuardedSearch.AccelerationState p.E) (by omega) hstart
  simp only [Nat.zero_add] at hfinal
  have hacc := CompositeCurvatureParameters.inner_accuracy hm hΔ.le
    (by positivity : 0 ≤ CurvatureMetric.metricNorm B
      ((eval (canonicalReply F) (acceleratedRounds p center snapshot B N 0 ⟨snapshot, snapshot⟩)).momentum - u) ^ 2 / 2)
    hfinal.2.2
  exact ⟨hfinal.1, hacc⟩

lemma gapEpoch_contraction {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hf : ContDiff ℝ 2 F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain) (center w snapshot : p.E) {Δ : ℝ}
    (hΔ : 0 < Δ) (hw : w ∈ F.domain) (hy : snapshot ∈ F.domain)
    (hmin : ∀ u ∈ F.domain, CompositeLocalObjective.smooth F center w + F.ψ w ≤
      CompositeLocalObjective.smooth F center u + F.ψ u)
    (hgap : CompositeLocalObjective.smooth F center snapshot + F.ψ snapshot -
      (CompositeLocalObjective.smooth F center w + F.ψ w) ≤ Δ) :
    let z := eval (canonicalReply F) (gapEpoch p center snapshot Δ)
    z ∈ F.domain ∧ CompositeLocalObjective.smooth F center z + F.ψ z -
      (CompositeLocalObjective.smooth F center w + F.ψ w) ≤ 3 * Δ / 4 := by
  have ha := accelerated_epoch_accuracy F hH hm hf hc hLip hψ hclosed hx0 center w snapshot hΔ hw hy hmin hgap
  simp only [gapEpoch, eval, canonicalReply, show (1 : Fin 3) ≠ 0 by decide, ite_false,
    readHessian, eval_map]
  refine ⟨ha.1, ?_⟩
  apply contraction_of_accuracy (q := (0 : p.E))
    (CompositeLocalObjective.smooth_convex F center hc
      (CompositeCurvatureParameters.cubicCoefficient_pos p hH hm).le) hψ hy hw hΔ.le hgap
  have hs := mul_le_mul_of_nonneg_right (CompositeCurvatureParameters.scale_bounds p).1 hΔ.le
  change innerObjective F center snapshot _ - innerObjective F center snapshot _ ≤ _
  linarith [ha.2]

lemma gapRounds_contraction {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hf : ContDiff ℝ 2 F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain) (center w : p.E) (hw : w ∈ F.domain)
    (hmin : ∀ u ∈ F.domain, CompositeLocalObjective.smooth F center w + F.ψ w ≤
      CompositeLocalObjective.smooth F center u + F.ψ u)
    (n : ℕ) (snapshot : p.E) {Δ : ℝ} (hΔ : 0 < Δ) (hy : snapshot ∈ F.domain)
    (hgap : CompositeLocalObjective.smooth F center snapshot + F.ψ snapshot -
      (CompositeLocalObjective.smooth F center w + F.ψ w) ≤ Δ) :
    let z := eval (canonicalReply F) (gapRounds p center n snapshot Δ)
    z ∈ F.domain ∧ CompositeLocalObjective.smooth F center z + F.ψ z -
      (CompositeLocalObjective.smooth F center w + F.ψ w) ≤ (3 / 4 : ℝ) ^ n * Δ := by
  induction n generalizing snapshot Δ with
  | zero => simpa only [gapRounds, eval, pow_zero, one_mul] using And.intro hy hgap
  | succ n ih =>
    have he := gapEpoch_contraction F hH hm hf hc hLip hψ hclosed hx0 center w snapshot hΔ hw hy hmin hgap
    have hn := ih _ (by positivity : 0 < 3 * Δ / 4) he.1 he.2
    simp only [gapRounds, eval_bind]
    refine ⟨hn.1, ?_⟩
    convert hn.2 using 1
    ring

lemma cubicStep_properties {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hf : ContDiff ℝ 2 F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain) (center x : p.E) :
    let z := eval (canonicalReply F) (cubicStep p center x)
    let G := fun u => CompositeLocalObjective.smooth F center u + F.ψ u
    z.point ∈ F.domain ∧
      (∀ u ∈ F.domain, G z.point + ⟪z.residual, u - z.point⟫ +
        cubicCoefficient p * ‖u - z.point‖ ^ 3 / 6 ≤ G u) ∧
      ‖z.residual‖ ≤ 3 * localHessianLip p * ‖z.point - x‖ ^ 2 / 2 ∧
      (x ∈ F.domain → 5 * localHessianLip p * ‖z.point - x‖ ^ 3 / 6 ≤ G x - G z.point) ∧
      (∀ w ∈ F.domain, G z.point - G w ≤ localHessianLip p * ‖w - x‖ ^ 3 / 2) := by
  let f := CompositeLocalObjective.smooth F center
  let g := fun u => localGradient p center u (gradient F.f u)
  let A := fun u => localHessian p center u (fderiv ℝ (gradient F.f) u)
  let q : Model p := ⟨x, g x, A x, localHessianLip p, 1⟩
  let z := modelAnswer F q
  let r := g z - g x - A x (z - x) - (localHessianLip p * ‖z - x‖) • (z - x)
  have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
  have hL := CompositeCurvatureParameters.localHessianLip_pos p hH hm
  have hd := hf.differentiable (by norm_num)
  have hg : ∀ u, HasFDerivAt g (A u) u := fun u => CompositeLocalObjective.localGradient_hasFDerivAt F center u hf
  have hfg : ∀ u, HasFDerivAt f (innerSL ℝ (g u)) u :=
    fun u => (CompositeLocalObjective.smooth_hasGradient F center u hd).hasFDerivAt
  have hAL : ∀ u v, ‖A u - A v‖ ≤ localHessianLip p * ‖u - v‖ :=
    CompositeLocalObjective.localHessian_lipschitz F center hγ.le hLip
  have hvalid : q.valid := ⟨by norm_num, hL.le,
    CompositeLocalObjective.localHessian_symmetric F center x hf,
    CompositeLocalObjective.localHessian_nonneg F center x hf hc hγ.le, Or.inl hL⟩
  have hsol : q.solution F z := modelAnswer_solution F q hvalid hψ hclosed hx0
  have he : eval (canonicalReply F) (cubicStep p center x) = ⟨z, r⟩ := by
    simp [cubicStep, eval, canonicalReply, readVector, readHessian, z, r, q, g, A]
  rw [he]
  have ht (u : p.E) := CubicRegularization.objective_taylor hfg hg hAL x (u - x)
  simp only [add_sub_cancel] at ht
  have htupper (u : p.E) : f u ≤ f x + ⟪g x, u - x⟫ + ⟪u - x, A x (u - x)⟫ / 2 +
      localHessianLip p * ‖u - x‖ ^ 3 / 6 := by have h := (abs_le.mp (ht u)).2; linarith
  refine ⟨hsol.1, ?_, ?_, ?_, ?_⟩
  · intro u hu
    have hv := hsol.2 u hu
    have hb := CompositeLocalObjective.smooth_bregman_lower F center z u hd hc hγ.le
    simp only [Model.derivative, q, one_mul, inner_add_left] at hv
    change f z + F.ψ z + ⟪r, u - z⟫ + cubicCoefficient p * ‖u - z‖ ^ 3 / 6 ≤ f u + F.ψ u
    dsimp only [r]
    simp only [inner_sub_left]
    change f z + ⟪g z, u - z⟫ + cubicCoefficient p * ‖u - z‖ ^ 3 / 6 ≤ f u at hb
    linarith
  · have hgt := CubicRegularization.gradient_taylor hg hAL x (z - x)
    simp only [add_sub_cancel] at hgt
    exact CompositeCubicBridge.residual_norm hL.le hgt
  · intro hx
    have hd := CompositeCubicBridge.cubic_descent F hx hsol (htupper z)
    have hp := hvalid.2.2.2.1 (z - x)
    change 0 ≤ ⟪z - x, A x (z - x)⟫ at hp
    change 5 * localHessianLip p * ‖z - x‖ ^ 3 / 6 ≤ f x + F.ψ x - (f z + F.ψ z)
    linarith
  · intro w hw
    apply CompositeCubicBridge.first_model_gap F hvalid hsol hw (htupper z)
    have h := (abs_le.mp (ht w)).1
    linarith

lemma eval_padding (p : Params) {U : Type} (reply : Fin 3 × (p.E ⊕ Model p) → Reply p)
    (value : U) (n : ℕ) : eval reply (padGradients p value n) = value := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [padGradients, eval] using ih

open scoped Classical in
lemma eval_cubicSolve {p : Params} (F : Problem p) (center : p.E) :
    let first := eval (canonicalReply F) (cubicStep p center center)
    let second := eval (canonicalReply F) (cubicStep p center first.point)
    eval (canonicalReply F) (cubicSolve p center) =
      if second.residual = 0 then second else
        let Δ := 2 * ‖second.residual‖ * Real.sqrt (‖second.residual‖ / cubicCoefficient p)
        eval (canonicalReply F) (cubicStep p center
          (eval (canonicalReply F) (gapRounds p center (gapIterations p) second.point Δ))) := by
  classical
  unfold cubicSolve cubicSolveCalls
  rw [eval_bind, eval_bind]
  split_ifs with h <;> simp only [h, ite_true, ite_false, eval_padding, eval_bind]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
lemma cubicSolve_certificate {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hf : ContDiff ℝ 2 F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain) (center w : p.E) (hw : w ∈ F.domain)
    (hmin : ∀ u ∈ F.domain, CompositeLocalObjective.smooth F center w + F.ψ w ≤
      CompositeLocalObjective.smooth F center u + F.ψ u) :
    let z := eval (canonicalReply F) (cubicSolve p center)
    let G := fun u => CompositeLocalObjective.smooth F center u + F.ψ u
    z.point ∈ F.domain ∧
      (∀ u ∈ F.domain, G z.point + ⟪z.residual, u - z.point⟫ +
        cubicCoefficient p * ‖u - z.point‖ ^ 3 / 6 ≤ G u) ∧
      ‖z.residual‖ ≤ cubicCoefficient p * ‖z.point - center‖ ^ 2 / 32 := by
  classical
  let first := eval (canonicalReply F) (cubicStep p center center)
  let second := eval (canonicalReply F) (cubicStep p center first.point)
  let G := fun u => CompositeLocalObjective.smooth F center u + F.ψ u
  have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
  have hL := CompositeCurvatureParameters.localHessianLip_pos p hH hm
  have hfirst := cubicStep_properties F hH hm hf hc hLip hψ hclosed hx0 center center
  have hsecond := cubicStep_properties F hH hm hf hc hLip hψ hclosed hx0 center first.point
  rw [eval_cubicSolve]
  change (if second.residual = 0 then second else _).point ∈ F.domain ∧ _
  split_ifs with hz
  · refine ⟨hsecond.1, hsecond.2.1, ?_⟩
    rw [hz, norm_zero]
    positivity
  · let Δ := 2 * ‖second.residual‖ * Real.sqrt (‖second.residual‖ / cubicCoefficient p)
    let a := (3 / 4 : ℝ) ^ gapIterations p
    let point := eval (canonicalReply F) (gapRounds p center (gapIterations p) second.point Δ)
    let z := eval (canonicalReply F) (cubicStep p center point)
    have hb : 0 < ‖second.residual‖ := norm_pos_iff.mpr hz
    have hΔ : 0 < Δ := by dsimp [Δ]; positivity
    have hgap : G second.point - G w ≤ Δ :=
      CompositeCubicBridge.gap_from_strong_subgradient hγ (hsecond.2.1 w hw)
    have hrounds := gapRounds_contraction F hH hm hf hc hLip hψ hclosed hx0 center w hw hmin
      (gapIterations p) second.point hΔ hsecond.1 hgap
    have hzprop := cubicStep_properties F hH hm hf hc hLip hψ hclosed hx0 center point
    change z.point ∈ F.domain ∧ _
    refine ⟨hzprop.1, hzprop.2.1, ?_⟩
    have hdes2 : 5 * localHessianLip p * ‖second.point - first.point‖ ^ 3 / 6 ≤
        localHessianLip p * ‖w - center‖ ^ 3 / 2 := by
      have hd := hsecond.2.2.2.1 hfirst.1
      have hinit := hfirst.2.2.2.2 w hw
      have hlow := hmin second.point hsecond.1
      linarith
    have hb3 : ‖second.residual‖ ^ 3 ≤ (9 : ℝ) / 4 * localHessianLip p ^ 3 * ‖w - center‖ ^ 6 := by
      have hb3 := CompositeCubicBridge.residual_gap_cube (norm_nonneg second.residual) hL.le
        (norm_nonneg (second.point - first.point)) hsecond.2.2.1 hdes2
      convert hb3 using 1
      ring
    have hΔ2 := CompositeCubicBridge.initial_gap_square (norm_nonneg second.residual) hγ hb3
    have hdesz : 5 * localHessianLip p * ‖z.point - point‖ ^ 3 / 6 ≤ a * Δ := by
      have hd := hzprop.2.2.2.1 hrounds.1
      have hlow := hmin z.point hzprop.1
      have hgapz := hrounds.2
      change G point - G w ≤ a * Δ at hgapz
      change 5 * localHessianLip p * ‖z.point - point‖ ^ 3 / 6 ≤ G point - G z.point at hd
      change G w ≤ G z.point at hlow
      linarith
    have hbz := CompositeCubicBridge.residual_gap_cube (norm_nonneg z.residual) hL.le
      (norm_nonneg (z.point - point)) hzprop.2.2.1 hdesz
    have hbz' : ‖z.residual‖ ^ 3 ≤ 9 * localHessianLip p * a ^ 2 * Δ ^ 2 := by
      convert hbz using 1
      ring
    have hsmall := CompositeCubicBridge.bridge_small_residual (norm_nonneg z.residual) hγ
      (le_trans (by norm_num) (CompositeCurvatureParameters.condition_bounds p hm).1) (by positivity : 0 ≤ a)
      (norm_nonneg (w - center)) (CompositeCurvatureParameters.local_condition_identity p hm)
      (by norm_num [a] at ⊢; have h := CompositeCurvatureParameters.gap_contraction_bound p hm; norm_num at h; exact h) hΔ2 hbz'
    have hgrowth := CompositeCubicBridge.distance_from_strong_subgradient (G := G) (x := z.point) (w := w) (r := z.residual) hγ.le
      (hmin z.point hzprop.1) (hzprop.2.1 w hw)
    apply CompositeCubicBridge.relative_residual_transfer (norm_nonneg z.residual) hγ
      (norm_nonneg (z.point - center)) (norm_nonneg (w - center)) (norm_nonneg (z.point - w)) hsmall hgrowth
    calc
      ‖w - center‖ ≤ ‖w - z.point‖ + ‖z.point - center‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖z.point - center‖ + ‖z.point - w‖ := by rw [norm_sub_rev w z.point]; ring

set_option maxRecDepth 4000 in
lemma cubicSolve_oracle {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hf : ContDiff ℝ 2 F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain) (center : p.E) :
    let z := eval (canonicalReply F) (cubicSolve p center)
    let s := z.residual - (cubicCoefficient p * ‖z.point - center‖) • (z.point - center)
    z.point ∈ F.domain ∧
      (∀ u ∈ F.domain, F.f z.point + F.ψ z.point + ⟪s, u - z.point⟫ ≤ F.f u + F.ψ u) ∧
      ‖z.residual‖ ≤ cubicCoefficient p * ‖z.point - center‖ ^ 2 / 32 := by
  have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
  obtain ⟨w, hw, hmin⟩ := CompositeCubicBridge.regularized_minimizer_exists F center hγ hc hf.continuous hψ hclosed hx0
  have hm' : ∀ u ∈ F.domain, CompositeLocalObjective.smooth F center w + F.ψ w ≤
      CompositeLocalObjective.smooth F center u + F.ψ u := by
    intro u hu
    have h := hmin u hu
    dsimp only [CompositeLocalObjective.smooth]
    linarith
  have hz := cubicSolve_certificate F hH hm hf hc hLip hψ hclosed hx0 center w hw hm'
  refine ⟨hz.1, ?_, hz.2.2⟩
  apply CompositeLocalObjective.original_subgradient F center _ _ (hf.differentiable (by norm_num)) hc hψ hz.1
  intro u hu
  have h := hz.2.1 u hu
  have hn : 0 ≤ cubicCoefficient p * ‖u - (eval (canonicalReply F) (cubicSolve p center)).point‖ ^ 3 := by positivity
  linarith

lemma cubicSolve_zero_optimal {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hf : ContDiff ℝ 2 F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain) (center : p.E)
    (he : (eval (canonicalReply F) (cubicSolve p center)).point = center) :
    center ∈ F.domain ∧ ∀ u ∈ F.domain, F.f center + F.ψ center ≤ F.f u + F.ψ u := by
  have hz := cubicSolve_oracle F hH hm hf hc hLip hψ hclosed hx0 center
  have hr := hz.2.2
  rw [he, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_div] at hr
  have hr0 : (eval (canonicalReply F) (cubicSolve p center)).residual = 0 := norm_eq_zero.mp (le_antisymm hr (norm_nonneg _))
  refine ⟨he ▸ hz.1, ?_⟩
  intro u hu
  simpa only [he, hr0, sub_self, norm_zero, mul_zero, zero_smul, inner_zero_left, add_zero] using hz.2.1 u hu

noncomputable def outerReply {p : Params} (F : Problem p)
    (state : LongTails.Algorithms.CompositeCubicAcceleration.State p.E) : CubicPoint p :=
  eval (canonicalReply F) (cubicSolve p (LongTails.Algorithms.CompositeCubicAcceleration.center p.E (outerCoefficient p) state))

noncomputable def outerStep {p : Params} (F : Problem p)
    (state : LongTails.Algorithms.CompositeCubicAcceleration.State p.E) :
    LongTails.Algorithms.CompositeCubicAcceleration.State p.E :=
  let z := outerReply F state
  let d := z.point - LongTails.Algorithms.CompositeCubicAcceleration.center p.E (outerCoefficient p) state
  LongTails.Algorithms.CompositeCubicAcceleration.advance p.E (outerCoefficient p) (cubicCoefficient p) state z.point
    (z.residual - (cubicCoefficient p * ‖d‖) • d)

noncomputable def outerState {p : Params} (F : Problem p) : ℕ →
    LongTails.Algorithms.CompositeCubicAcceleration.State p.E
  | 0 => ⟨0, p.x0, p.x0⟩
  | n + 1 => outerStep F (outerState F n)

lemma outerState_weight {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hR : 0 < p.R) (hε : 0 < p.ε) :
    (∀ k, 0 ≤ (outerState F k).weight) ∧ Monotone (fun k => (outerState F k).weight) := by
  have hμ := CompositeCurvatureParameters.outerCoefficient_pos p hH hm hR hε
  have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
  have hpos : ∀ k, 0 ≤ (outerState F k).weight := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      exact ih.trans (CompositeCubicAcceleration.advance_weight_mono (outerState F k) _ _ hμ hγ.le ih)
  refine ⟨hpos, monotone_nat_of_le_succ (fun k => ?_)⟩
  exact CompositeCubicAcceleration.advance_weight_mono (outerState F k) _ _ hμ hγ.le (hpos k)

lemma outerStep_certificate {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hf : ContDiff ℝ 2 F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain) (hstar : F.xstar ∈ F.domain)
    (state : LongTails.Algorithms.CompositeCubicAcceleration.State p.E)
    (hA : 0 ≤ state.weight) (hx : state.point ∈ F.domain)
    (hne : (outerReply F state).point ≠ LongTails.Algorithms.CompositeCubicAcceleration.center p.E (outerCoefficient p) state) :
    let G := fun u => F.f u + F.ψ u
    let r := ‖(outerReply F state).point - LongTails.Algorithms.CompositeCubicAcceleration.center p.E (outerCoefficient p) state‖
    let next := outerStep F state
    next.point ∈ F.domain ∧ state.weight < next.weight ∧
      next.weight * (G next.point - G F.xstar) + ‖next.momentum - F.xstar‖ ^ 2 / 2 +
        (1 - (1 / 32 : ℝ) ^ 2) * (state.weight + LongTails.Algorithms.CompositeCubicAcceleration.trialWeight (outerCoefficient p) state.weight) *
          min (outerCoefficient p) (cubicCoefficient p * r) * r ^ 2 / 2 ≤
      state.weight * (G state.point - G F.xstar) + ‖state.momentum - F.xstar‖ ^ 2 / 2 := by
  have hμ := CompositeCurvatureParameters.outerCoefficient_pos p hH hm hR hε
  have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
  have hz := cubicSolve_oracle F hH hm hf hc hLip hψ hclosed hx0
    (LongTails.Algorithms.CompositeCubicAcceleration.center p.E (outerCoefficient p) state)
  apply CompositeCubicAcceleration.advance_certificate
    ((hc.subset (Set.subset_univ _) hψ.1).add hψ) state hμ hγ hA hx hz.1 hstar hne hz.2.1
  simpa only [sub_add_cancel] using hz.2.2

noncomputable def outerEnergy {p : Params} (F : Problem p) (k : ℕ) : ℝ :=
  (outerState F k).weight * (F.f (outerState F k).point + F.ψ (outerState F k).point -
    (F.f F.xstar + F.ψ F.xstar)) + ‖(outerState F k).momentum - F.xstar‖ ^ 2 / 2

noncomputable def outerDissipation {p : Params} (F : Problem p) (k : ℕ) : ℝ :=
  let state := outerState F k
  let r := ‖(outerReply F state).point - LongTails.Algorithms.CompositeCubicAcceleration.center p.E (outerCoefficient p) state‖
  (state.weight + LongTails.Algorithms.CompositeCubicAcceleration.trialWeight (outerCoefficient p) state.weight) *
    min (outerCoefficient p) (cubicCoefficient p * r) * r ^ 2

lemma outerState_potential {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hf : ContDiff ℝ 2 F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain) (hstar : F.xstar ∈ F.domain) (n : ℕ)
    (hsteps : ∀ k < n, (outerReply F (outerState F k)).point ≠
      LongTails.Algorithms.CompositeCubicAcceleration.center p.E (outerCoefficient p) (outerState F k)) :
    (outerState F n).point ∈ F.domain ∧
      outerEnergy F n + (1 - (1 / 32 : ℝ) ^ 2) / 2 * (∑ k ∈ Finset.range n, outerDissipation F k) ≤
        ‖p.x0 - F.xstar‖ ^ 2 / 2 := by
  induction n with
  | zero => simpa only [outerState, outerEnergy, zero_mul, zero_add, Finset.sum_range_zero, mul_zero, add_zero] using And.intro hx0 (le_refl (‖p.x0 - F.xstar‖ ^ 2 / 2))
  | succ n ih =>
    have hi := ih (fun k hk => hsteps k (Nat.lt_succ_of_lt hk))
    have hweight := (outerState_weight F hH hm hR hε).1 n
    have hn := outerStep_certificate F hH hm hR hε hf hc hLip hψ hclosed hx0 hstar
      (outerState F n) hweight hi.1 (hsteps n (Nat.lt_succ_self n))
    refine ⟨hn.1, ?_⟩
    have hstep : outerEnergy F (n + 1) + (1 - (1 / 32 : ℝ) ^ 2) / 2 * outerDissipation F n ≤ outerEnergy F n := by
      convert hn.2.2 using 1
      all_goals dsimp only [outerEnergy, outerDissipation, outerState]
      all_goals ring
    rw [Finset.sum_range_succ]
    nlinarith only [hstep, hi.2]

set_option maxRecDepth 4000 in
lemma eval_outerRounds_cases {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hf : ContDiff ℝ 2 F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain) (n k : ℕ) :
    let output := eval (canonicalReply F) (outerRounds p n (outerState F k))
    (output ∈ F.domain ∧ ∀ u ∈ F.domain, F.f output + F.ψ output ≤ F.f u + F.ψ u) ∨
      ((∀ i < n, (outerReply F (outerState F (k + i))).point ≠
        LongTails.Algorithms.CompositeCubicAcceleration.center p.E (outerCoefficient p) (outerState F (k + i))) ∧
        output = (outerState F (k + n)).point) := by
  classical
  induction n generalizing k with
  | zero =>
    right
    exact ⟨fun i hi => by omega, by simp only [outerRounds, eval, Nat.add_zero]⟩
  | succ n ih =>
    simp only [outerRounds, eval_bind]
    split_ifs with he
    · left
      have hpad := eval_padding p (canonicalReply F)
        (LongTails.Algorithms.CompositeCubicAcceleration.center p.E (outerCoefficient p) (outerState F k)) (cubicSolveCalls p * n)
      have hz := cubicSolve_zero_optimal F hH hm hf hc hLip hψ hclosed hx0 _ he
      simpa only [hpad, he] using hz
    · have hn := ih (k + 1)
      rcases hn with hopt | ⟨hsteps, hout⟩
      · left
        exact hopt
      · right
        refine ⟨?_, ?_⟩
        · intro i hi
          cases i with
          | zero => simpa only [Nat.add_zero, outerReply] using he
          | succ i =>
            have h := hsteps i (by omega)
            simpa only [Nat.add_assoc, Nat.add_comm 1 i] using h
        · convert hout using 1
          all_goals congr 2
          all_goals omega

lemma outerDissipation_nonneg {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hR : 0 < p.R) (hε : 0 < p.ε) (k : ℕ) :
    0 ≤ outerDissipation F k := by
  have hμ := CompositeCurvatureParameters.outerCoefficient_pos p hH hm hR hε
  have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
  have hA := (outerState_weight F hH hm hR hε).1 k
  have ha := CompositeCubicAcceleration.trialWeight_pos hμ hA
  dsimp only [outerDissipation]
  exact mul_nonneg (mul_nonneg (add_nonneg hA ha.le)
    (le_min hμ.le (mul_nonneg hγ.le (norm_nonneg _)))) (sq_nonneg _)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
lemma canonical_accuracy {p : Params} (F : Problem p)
    (hH : 0 < p.H) (hm : 1 ≤ p.m) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hf : ContDiff ℝ 2 F.f) (hc : ConvexOn ℝ Set.univ F.f)
    (hLip : ∀ x y, ‖fderiv ℝ (gradient F.f) x - fderiv ℝ (gradient F.f) y‖ ≤ p.H * ‖x - y‖)
    (hψ : ConvexOn ℝ F.domain F.ψ)
    (hclosed : IsClosed {z : p.E × ℝ | z.1 ∈ F.domain ∧ F.ψ z.1 ≤ z.2})
    (hx0 : p.x0 ∈ F.domain) (hstar : F.xstar ∈ F.domain) (hR0 : ‖p.x0 - F.xstar‖ ≤ p.R)
    (hmin : ∀ x ∈ F.domain, F.f F.xstar + F.ψ F.xstar ≤ F.f x + F.ψ x) :
    let output := eval (canonicalReply F) (plan p)
    output ∈ F.domain ∧ F.f output + F.ψ output - (F.f F.xstar + F.ψ F.xstar) ≤ p.ε := by
  let N := outerIterations p
  let A := fun k => (outerState F k).weight
  let r := fun k => ‖(outerReply F (outerState F k)).point -
    LongTails.Algorithms.CompositeCubicAcceleration.center p.E (outerCoefficient p) (outerState F k)‖
  let v := scaledGap p ^ (2 / 7 : ℝ)
  let L := Nat.log2 (2 + ⌈scaledGap p ^ (4 / 7 : ℝ)⌉₊)
  have hμ := CompositeCurvatureParameters.outerCoefficient_pos p hH hm hR hε
  have hγ := CompositeCurvatureParameters.cubicCoefficient_pos p hH hm
  have hq := CompositeCurvatureParameters.scaledGap_pos p hH hm hR hε
  have hv : 0 ≤ v := Real.rpow_nonneg hq.le _
  have hw := outerState_weight F hH hm hR hε
  have hcases := eval_outerRounds_cases F hH hm hf hc hLip hψ hclosed hx0 N 0
  rcases hcases with hopt | ⟨hsteps, hout⟩
  · refine ⟨hopt.1, ?_⟩
    have h := hopt.2 F.xstar hstar
    change F.f (eval (canonicalReply F) (plan p)) + F.ψ (eval (canonicalReply F) (plan p)) ≤
      F.f F.xstar + F.ψ F.xstar at h
    linarith
  · simp only [Nat.zero_add] at hsteps hout
    have heval : eval (canonicalReply F) (plan p) = (outerState F N).point := hout
    change eval (canonicalReply F) (plan p) ∈ F.domain ∧ _
    rw [heval]
    have hp := outerState_potential F hH hm hR hε hf hc hLip hψ hclosed hx0 hstar N hsteps
    have hgap := hmin _ hp.1
    have hE0 : 0 ≤ outerEnergy F N := by
      exact add_nonneg (mul_nonneg (hw.1 N) (sub_nonneg.mpr hgap)) (div_nonneg (sq_nonneg _) (by norm_num))
    have hD0 : 0 ≤ ∑ k ∈ Finset.range N, outerDissipation F k :=
      Finset.sum_nonneg (fun k _ => outerDissipation_nonneg F hH hm hR hε k)
    have hR2 := pow_le_pow_left₀ (norm_nonneg (p.x0 - F.xstar)) hR0 2
    have hEb : outerEnergy F N ≤ p.R ^ 2 / 2 := by nlinarith only [hp.2, hD0, hR2]
    have hDb : (∑ k ∈ Finset.range N, outerDissipation F k) ≤ 2 * p.R ^ 2 := by
      nlinarith only [hp.2, hE0, hR2, sq_nonneg p.R]
    have hA : p.R ^ 2 / p.ε ≤ A N := by
      by_contra hh
      have hAN : A N < p.R ^ 2 / p.ε := lt_of_not_ge hh
      have hr : ∀ k < N, 0 < r k := fun k hk => norm_pos_iff.mpr (sub_ne_zero.mpr (hsteps k hk))
      have hrec : ∀ k < N, A (k + 1) = A k + min 1 (outerCoefficient p / (cubicCoefficient p * r k)) *
          LongTails.Algorithms.CompositeCubicAcceleration.trialWeight (outerCoefficient p) (A k) := fun _ _ => rfl
      have hscale := CompositeCurvatureParameters.outer_tuning_cube p hH hm hR hε
      have hXscale : outerCoefficient p * (p.R ^ 2 / p.ε) = v ^ 2 := by
        rw [← mul_div_assoc, CompositeCurvatureParameters.outer_tuning_identity p hH hm hR hε]
        exact (CompositeCurvatureParameters.outer_rate_square p hq.le).symm
      have hcount := CompositeCubicAcceleration.outer_count A r N L hμ hγ hv hw.2 (by exact le_rfl) hAN hr hrec hDb
        hscale hXscale (CompositeCurvatureParameters.outer_dyadic_cover p hH hm hR hε)
      have hlt := CompositeCurvatureParameters.outer_horizon_exceeds p hq.le
      change (2 + 4 * ((L : ℝ) + 2)) * v < (N : ℝ) at hlt
      linarith
    refine ⟨hp.1, ?_⟩
    have hANpos : 0 < A N := lt_of_lt_of_le (div_pos (sq_pos_of_pos hR) hε) hA
    have hAε : p.R ^ 2 ≤ A N * p.ε := (div_le_iff₀ hε).mp hA
    have hbound : A N * (F.f (outerState F N).point + F.ψ (outerState F N).point -
        (F.f F.xstar + F.ψ F.xstar)) ≤ p.R ^ 2 / 2 := by
      have hn := sq_nonneg ((‖(outerState F N).momentum - F.xstar‖ : ℝ))
      dsimp only [outerEnergy] at hEb
      dsimp only [A]
      nlinarith only [hEb, hn]
    by_contra hbad
    have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge hbad) hANpos
    nlinarith only [hlt, hbound, hAε, sq_nonneg p.R]

lemma execution_accuracy (p : Params) (hp : spec.valid p) (F : Problem p)
    (O : Oracle (p.E ⊕ Model p) (Reply p) 3) (hF : spec.admissible p F O)
    (budget : Fin 3 → ℕ)
    (hHess : (gapIterations p + 3) * outerIterations p ≤ budget 1)
    (hOther : ∀ i, i ≠ 1 → cubicSolveCalls p * outerIterations p ≤ budget i)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm p) budget seed ξ ∈ F.domain ∧
      F.f (execute O (algorithm p) budget seed ξ) + F.ψ (execute O (algorithm p) budget seed ξ) -
        (F.f F.xstar + F.ψ F.xstar) ≤ p.ε := by
  rw [execute_eq_canonical p hp F O hF budget hHess hOther seed ξ]
  obtain ⟨hf, hc, hLip, hψ, hclosed, hx0, hstar, hR0, hmin, _⟩ := hF
  exact canonical_accuracy F hp.1 hp.2.2.2 hp.2.1 hp.2.2.1 hf hc hLip hψ hclosed hx0 hstar hR0 hmin

end LongTails.Proofs.CompositeLazyCubicConvergence
