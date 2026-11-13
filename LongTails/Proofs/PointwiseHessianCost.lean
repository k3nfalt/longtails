import LongTails.Proofs.PointwiseHessianComplexity

open scoped Classical

namespace LongTails.Proofs.PointwiseHessianCost

open LongTails.Setups.PointwiseHessianConvex
open LongTails.Algorithms.PointwiseHessianAccelerated
open LongTails.Proofs.PointwiseHessianComplexity
open LongTails.Proofs.PointwiseHessianExecution
open LongTails.Proofs.PointwiseHessianEpisodes
open LongTails.Proofs.PointwiseHessianLedger

lemma path_cost_bound (p : Params) (hv : spec.valid p) {f : p.E → ℝ}
    (s : ℕ → State p.toPublic) (xs : p.E) (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (hmin : IsMinOn f Set.univ xs)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.M₀ + p.M₁ * ‖gradient f x‖)
    (hH0 : ‖fderiv ℝ (gradient f) p.x0‖ ≤ p.H₀)
    (hx : ‖p.x0 - xs‖ ≤ p.R) (hgap : f p.x0 - f xs ≤ p.Δ)
    (reply : ℕ → p.E ⊕ (p.E →L[ℝ] p.E)) {N : ℕ} (hN : 0 < N)
    (hi : ∀ k ≤ N, StateInvariant f xs (s k))
    (hs : ∀ k < N, s (k + 1) = update (s k) (reply k))
    (hcert : ∀ k ≤ N, CertificateInvariant f (s k))
    (hrad : ∀ k < N, RadiusInvariant f (s k))
    (hg : ∀ k < N, (s k).phase = .newtonGradient → reply k = .inl (gradient f (s k).x))
    (hH : ∀ k < N, (s k).phase = .newtonHessian → reply k = .inr (fderiv ℝ (gradient f) (s k).x))
    (hloss : (∑ k ∈ Finset.range N, loss (s k) (reply k)) ≤ p.R ^ 2)
    (h0 : s 0 = initial p.toPublic) (hn : ∀ k ≤ N, (s k).phase ≠ .finished)
    (hA : ∀ k ≤ N, (s k).A < targetWeight p.toPublic)
    (hb : ∀ k ≤ N, PointwiseHessianBounds.BoundedScales (s k)) :
    (N : ℝ) ≤ 17592186044416 *
      (1 + (p.M₀ * p.R ^ 3 / p.ε) ^ (2 / 7 : ℝ) + (Real.sqrt p.M₁ * p.R) ^ 3) *
        (1 + Real.log (dataScale p)) ^ 4 := by
  obtain ⟨hZ,hΔZ,hBZ,hUZ,hKZ⟩ := dataScale_bounds p hv
  have hvalid := hv
  obtain ⟨hM₀,hM₁,hR,hΔ,hH₀,hε⟩ := hvalid
  let ell := 1 + Real.log (dataScale p)
  let W := 1 + (p.M₀ * p.R ^ 3 / p.ε) ^ (2 / 7 : ℝ)
  let P := fun k => RadiusStart (s k) (s (k + 1))
  let r := fun k => (s (k + 1)).r
  let d := fun k => ‖(s (k + 1)).center - (s (k + 1)).w‖
  have hell : 1 ≤ ell := by dsimp [ell]; linarith [Real.log_nonneg (show 1 ≤ dataScale p by linarith)]
  have hW : 1 ≤ W := by dsimp [W]; linarith [Real.rpow_nonneg (show 0 ≤ p.M₀ * p.R ^ 3 / p.ε by positivity) (2 / 7 : ℝ)]
  have h0c : (s 0).phase = .centerGradient := by
    have hh := hn 0 (Nat.zero_le N)
    rw [h0] at hh ⊢
    by_cases he : p.Δ ≤ p.ε
    · simp [initial, he] at hh
    · simp [initial, he]
  have hcap : (s N).A ≤ 3 * targetWeight p.toPublic := by
    have ht : 0 < targetWeight p.toPublic := by unfold targetWeight; positivity
    linarith [hA N le_rfl]
  have hAc := quantitative_outer_count p hv s xs hf hc hmin reply N hi hs
    (fun k hk => hcert k hk.le) hg hloss h0 hcap
  have hAc' : (∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then (1 : ℝ) else 0) ≤ 1024 * W * ell := by
    simpa only [PointwiseHessianEvents.acceptedIndices, Finset.card_filter, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, W, ell] using hAc
  have htb := PointwiseHessianTrialCount.path_trialBounds s reply N hM₀ hR hε hZ hΔZ hBZ h0c hi hA hb hs
  have hcount := PointwiseHessianTrialCount.path_radius_start_count s reply N
    (show 0 < p.ε / p.R ^ 2 by positivity) (show 0 < p.R / (1048576 * dataScale p) by positivity)
    hZ h0c hs hn htb
  have hP : (∑ k ∈ Finset.range N, if P k then (1 : ℝ) else 0) ≤ 2097152 * W * ell ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hAc' (show 0 ≤ 1024 * ell ^ 2 by positivity)
    have hh : 1 ≤ W * ell := one_le_mul_of_one_le_of_one_le hW hell
    change (∑ k ∈ Finset.range N, if P k then (1 : ℝ) else 0) ≤ 1024 * ell ^ 2 *
      ((∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then (1 : ℝ) else 0) + 1) at hcount
    nlinarith [mul_nonneg (sq_nonneg ell) (sub_nonneg.mpr hh)]
  have hS := path_radius_square_sum s xs hf hc hM₀ hR hmin reply N hi hcert hrad hs
    (fun k hk hp => by rw [hg k hk hp]; rfl) hloss
  have hd : ∀ k ∈ Finset.range N, P k → d k ≤ 6 * p.R := by
    intro k hk _
    exact center_displacement_bound (s (k + 1)) hR hmin (hi (k + 1) (by have := Finset.mem_range.mp hk; omega)).outer
  have hV := finite_radius_cross_sum (Finset.range N) P r d hR.le hd hS
  have hlog : Real.log (s N).A - Real.log (s 0).A ≤ 6 * ell := by
    rw [h0]
    change Real.log (s N).A - Real.log (initialWeight p.toPublic) ≤ _
    apply (PointwiseHessianBounds.weight_log_bound p.toPublic hR hΔ hε (hi N le_rfl).outer.A_pos hcap).trans
    simpa only [mul_div_assoc, ell] using log_six_bound hZ (div_pos hΔ hε) hΔZ
  have hcenter := path_center_displacement_sum s xs hR (fun x => hmin (Set.mem_univ x)) reply N hi hs
  have hcenter' : (∑ k ∈ Finset.range N, if Accepted (s k) (reply k) then ‖(s k).center - (s k).w‖ else 0) +
      ‖(s N).center - (s N).w‖ ≤ 180 * p.R * ell := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hR.le, mul_nonneg hR.le (sub_nonneg.mpr hell)]
  have hweighted := PointwiseHessianTrialCount.path_weighted_radius_start_count s reply N
    (show 0 < p.ε / p.R ^ 2 by positivity) (show 0 < p.R / (1048576 * dataScale p) by positivity)
    hZ h0c hs hn htb
  have hTsum : (∑ k ∈ Finset.range N, if P k then d k else 0) ≤ 262144 * p.R * ell ^ 3 := by
    have hh := mul_le_mul_of_nonneg_left hcenter' (show 0 ≤ 1024 * ell ^ 2 by positivity)
    change (∑ k ∈ Finset.range N, if P k then d k else 0) ≤ 1024 * ell ^ 2 * _ at hweighted
    nlinarith [mul_nonneg hR.le (pow_nonneg (show 0 ≤ ell by linarith) 3)]
  have hGstart (k : ℕ) (hk : k ∈ Finset.range N) (hp : P k) :
      PointwiseHessianEpisodePartition.gradientAllowance (s (k + 1)) ≤
        1048576 * (1 + p.M₁ * r k ^ 2) * (ell + Real.sqrt p.M₁ * d k) := by
    have hk' := Finset.mem_range.mp hk
    have hkn : k + 1 ≤ N := by omega
    have hinner := (hi (k + 1) hkn).phase
    simp only [PhaseInvariant, hp.2] at hinner
    have hbstart := started_regularization (s k) (reply k) (by rw [← hs k hk']; exact hp)
    rw [← hs k hk'] at hbstart
    have hbounds := htb (k + 1) hkn (Or.inl hp.2)
    apply started_allowance_bound p hv (s (k + 1)) hinner.1 hbstart hbounds.1 _ hbounds.2.1
      (center_gradient_budget p hv hf hc hmin hT hH0 hx hgap (s (k + 1)) (hi (k + 1) hkn).outer)
    simpa only [div_div_eq_mul_div] using hbounds.2.2.1
  have hGsum := finite_allowance_sum (Finset.range N) P r d
    (fun k => PointwiseHessianEpisodePartition.gradientAllowance (s (k + 1))) hGstart
  have hG := PointwiseHessianEpisodePartition.gradient_prefix_allowance_bound s hf hc hM₀ hM₁ hR hε hT reply
    hN h0c hs hn (fun k hk => (hi k hk).phase) hH hg
  have hQ := PointwiseHessianEpisodePartition.active_calls_le_radius_counts s reply N hs
  have hQeq : (∑ k ∈ Finset.range N, if (s k).phase ≠ .finished then (1 : ℝ) else 0) = N := by
    calc
      _ = ∑ _k ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact ite_eq_left (hn k (Finset.mem_range.mp hk).le)
      _ = N := by simp
  rw [hQeq] at hQ
  exact aggregate_physical_cost hW hM₁ hR hell hP hS hTsum hV (hG.trans hGsum) hAc' hQ

open OracleTemplate

lemma trace_finished (p : Params) (hv : spec.valid p) (f : p.E → ℝ)
    (O : Oracle p.E (p.E ⊕ (p.E →L[ℝ] p.E)) 2) (had : spec.admissible p f O)
    (seed : (algorithm p.toPublic).Seed) (ξ : (k : ℕ) → O.Seed k) (K : ℕ)
    (hK : 35184372088832 * (1 + (p.M₀ * p.R ^ 3 / p.ε) ^ (2 / 7 : ℝ) + (Real.sqrt p.M₁ * p.R) ^ 3) *
      (1 + Real.log (dataScale p)) ^ 4 ≤ (K : ℝ)) :
    (executeIndexedState O (algorithm p.toPublic) seed ξ K).1.phase = .finished := by
  obtain ⟨hf,hc,hT,hH0,⟨xs,hmin,hx,hgap⟩,hgrad,hHess⟩ := had
  have hvalid := hv
  obtain ⟨hM₀,hM₁,hR,hΔ,hH₀,hε⟩ := hvalid
  have hZ := (dataScale_bounds p hv).1
  have hlog : 0 ≤ Real.log (dataScale p) := Real.log_nonneg (by linarith)
  let F := (1 + (p.M₀ * p.R ^ 3 / p.ε) ^ (2 / 7 : ℝ) + (Real.sqrt p.M₁ * p.R) ^ 3) *
    (1 + Real.log (dataScale p)) ^ 4
  have hF : 0 < F := by dsimp [F]; positivity
  rw [mul_assoc] at hK
  change 35184372088832 * F ≤ (K : ℝ) at hK
  have hKr : 0 < (K : ℝ) := by
    have hh : 0 < 35184372088832 * F := by positivity
    exact hh.trans_le hK
  have hKn : 0 < K := by exact_mod_cast hKr
  by_contra hn
  let s := fun k => (executeIndexedState O (algorithm p.toPublic) seed ξ k).1
  let reply := fun k => executeAnswerAt O (algorithm p.toPublic) seed ξ k (query (s k))
  have hall (k : ℕ) (hk : k ≤ K) : (s k).phase ≠ .finished := by
    intro hfin
    have he := trace_finished_stable O seed ξ hfin (K - k)
    rw [Nat.add_sub_of_le hk] at he
    exact hn ((congrArg State.phase he).trans hfin)
  have hi (k : ℕ) : StateInvariant f xs (s k) := trace_invariant xs hf hc hM₀ hM₁ hR hΔ hε hT
    (fun x => hmin (Set.mem_univ x)) hx hgap O hgrad hHess seed ξ k
  have hcert (k : ℕ) : CertificateInvariant f (s k) := trace_certificateInvariant p.toPublic xs hf hc
    hM₀ hM₁ hR hΔ hε hT hmin hx hgap O hgrad hHess seed ξ k
  have hrad (k : ℕ) : RadiusInvariant f (s k) := trace_radiusInvariant p.toPublic xs hf hc
    hM₀ hM₁ hR hΔ hε hT hmin hx hgap O hgrad hHess seed ξ k
  have hg (k : ℕ) (_ : k < K) (hp : (s k).phase = .newtonGradient) : reply k = .inl (gradient f (s k).x) := by
    dsimp [reply, executeAnswerAt]
    rw [show query (s k) = (0, (s k).x) by simp [query, hp]]
    exact hgrad _ _ _
  have hH (k : ℕ) (_ : k < K) (hp : (s k).phase = .newtonHessian) : reply k = .inr (fderiv ℝ (gradient f) (s k).x) := by
    dsimp [reply, executeAnswerAt]
    rw [show query (s k) = (1, (s k).x) by simp [query, hp]]
    exact hHess _ _ _
  have hloss := trace_loss_bound p.toPublic xs hf hc hM₀ hM₁ hR hΔ hε hT hmin hx hgap O hgrad hHess seed ξ K
  have hcost := path_cost_bound p hv s xs hf hc hmin hT hH0 hx hgap reply hKn
    (fun k _ => hi k) (fun _ _ => rfl) (fun k _ => hcert k) (fun k _ => hrad k) hg hH hloss rfl hall
    (fun k hk => PointwiseHessianBounds.trace_live_weight p.toPublic hR hε O seed ξ k (hall k hk))
    (fun k _ => PointwiseHessianBounds.trace_boundedScales p.toPublic xs hf hc hM₀ hM₁ hR hΔ hε
      hT hmin hx hgap O hgrad hHess seed ξ k)
  rw [mul_assoc] at hcost
  change (K : ℝ) ≤ 17592186044416 * F at hcost
  nlinarith

end LongTails.Proofs.PointwiseHessianCost
