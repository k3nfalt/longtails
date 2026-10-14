import LongTails.Proofs.MomentumLastIterateGap

open MeasureTheory Set InnerProductSpace ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.MomentumConvex

open LongTails.Setups.MomentumLipschitzConvex

open OracleTemplate.SampledConvex (integral_prefix extend measurable_extend extend_agree)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]
  {p : Measure Ξ} [IsProbabilityMeasure p] {f : E → ℝ} {Gr : Ξ → E → E} {G : ℝ} {xstar : E}

lemma Hyp.descent_step (h : Hyp p f Gr G xstar) {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ : 0 < γ) (N : ℕ) (x0 : E) {k : ℕ} (hk : k ≤ N) :
    ∫ ξ, ‖zed Gr β γ N x0 ξ (k + 1) - refp Gr β γ N x0 xstar ξ (k + 1)‖ ^ 2 ∂(prodLaw p) ≤
      ∫ ξ, ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ (k + 1)‖ ^ 2 ∂(prodLaw p) -
        2 * (γ * tau N k) *
          ((1 + β / (1 - β) * tau N k / (tau N k + 1 + β / (1 - β))) *
              ∫ ξ, (f (traj Gr β γ N x0 ξ k).1 - f xstar) ∂(prodLaw p) -
            β / (1 - β) * tau N k / (tau N k + 1 + β / (1 - β)) *
              ∫ ξ, (f (traj Gr β γ N x0 ξ (k - 1)).1 - f xstar) ∂(prodLaw p) -
            ∫ ξ, (f (refp Gr β γ N x0 xstar ξ (k + 1)) - f xstar) ∂(prodLaw p)) +
        (γ * tau N k) ^ 2 * G ^ 2 := by
  have hκ : 0 ≤ β / (1 - β) := div_nonneg hβ0 (by linarith)
  have hτ1 : 1 ≤ tau N k := tau_ge_one hk
  have hs : 0 ≤ γ * tau N k := by positivity
  have hc : 0 ≤ β / (1 - β) * γ * tau N k := by positivity
  have he : 0 < γ * (tau N k + 1 + β / (1 - β)) := by positivity
  have hq : β / (1 - β) * γ * tau N k / (γ * (tau N k + 1 + β / (1 - β))) =
      β / (1 - β) * tau N k / (tau N k + 1 + β / (1 - β)) := by
    have h1 : tau N k + 1 + β / (1 - β) ≠ 0 := by positivity
    field_simp
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  let X : (Fin k → Ξ) → (E × E) × E := fun u =>
    (traj Gr β γ N x0 (extend ω0 u) k, refp Gr β γ N x0 xstar (extend ω0 u) (k + 1))
  have hX : Measurable X :=
    ((((measurable_traj h.meas β γ N x0 k).1).prodMk ((measurable_traj h.meas β γ N x0 k).2)).comp
        (measurable_extend ω0)).prodMk
      ((measurable_refp h.meas β γ N x0 xstar (k + 1)).comp (measurable_extend ω0))
  have hXeq : ∀ ξ : ℕ → Ξ, X (fun i : Fin k => ξ i) =
      (traj Gr β γ N x0 ξ k, refp Gr β γ N x0 xstar ξ (k + 1)) := fun ξ => by
    simp only [X]
    rw [traj_congr Gr β γ N x0 k (extend_agree ω0 ξ),
      (refp_congr Gr β γ N x0 xstar k (extend_agree ω0 ξ)).1]
  let Φ : (E × E) × E → Ξ → ℝ := fun y ω =>
    ‖y.1.1 - (β / (1 - β) * γ * tau N k) • y.1.2 - (γ * tau N k) • Gr ω y.1.1 - y.2‖ ^ 2
  have hΦ : Measurable (Function.uncurry Φ) := by
    have hg : Measurable (fun r : ((E × E) × E) × Ξ => Gr r.2 r.1.1.1) :=
      h.meas.comp (measurable_snd.prodMk (measurable_fst.comp (measurable_fst.comp measurable_fst)))
    have h1 : Measurable (fun r : ((E × E) × E) × Ξ => r.1.1.1) :=
      measurable_fst.comp (measurable_fst.comp measurable_fst)
    have h2 : Measurable (fun r : ((E × E) × E) × Ξ => r.1.1.2) :=
      measurable_snd.comp (measurable_fst.comp measurable_fst)
    have h3 : Measurable (fun r : ((E × E) × E) × Ξ => r.1.2) :=
      measurable_snd.comp measurable_fst
    exact (((h1.sub (h2.const_smul _)).sub (hg.const_smul _)).sub h3).norm.pow_const 2
  have hfun : (fun ξ : ℕ → Ξ => Φ (X (fun i : Fin k => ξ i)) (ξ k)) =
      fun ξ : ℕ → Ξ => ‖zed Gr β γ N x0 ξ (k + 1) - refp Gr β γ N x0 xstar ξ (k + 1)‖ ^ 2 := by
    funext ξ
    simp only [Φ]
    rw [hXeq, zed_succ Gr hβ1 γ N x0 ξ k]
    rfl
  have hi : Integrable (fun ξ : ℕ → Ξ => Φ (X (fun i : Fin k => ξ i)) (ξ k)) (prodLaw p) := by
    rw [hfun]
    exact integrable_sq_sub (h.memLp_zed β γ N x0 (k + 1)) (h.memLp_refp β γ N x0 (k + 1))
  obtain ⟨hin, heq⟩ := integral_prefix p k X hX Φ hΦ hi
  rw [hfun] at heq
  rw [heq]
  have hA := integrable_sq_sub (h.memLp_zed β γ N x0 k)
    (h.memLp_refp β γ N x0 (xstar := xstar) (k + 1))
  have hB := h.integrable_gap (h.memLp_traj β γ N x0 k).1
  have hC := h.integrable_gap (h.memLp_traj β γ N x0 (k - 1)).1
  have hD := h.integrable_gap (h.memLp_refp β γ N x0 (xstar := xstar) (k + 1))
  set q := β / (1 - β) * tau N k / (tau N k + 1 + β / (1 - β)) with hqdef
  obtain ⟨hcI, hcE⟩ := integral_combo hA hB hC hD (-(2 * (γ * tau N k) * (1 + q)))
    (2 * (γ * tau N k) * q) (2 * (γ * tau N k)) ((γ * tau N k) ^ 2 * G ^ 2)
  have hpt : ∀ ξ : ℕ → Ξ, (∫ ω, Φ (X (fun i : Fin k => ξ i)) ω ∂p) ≤
      ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ (k + 1)‖ ^ 2 +
        -(2 * (γ * tau N k) * (1 + q)) * (f (traj Gr β γ N x0 ξ k).1 - f xstar) +
        2 * (γ * tau N k) * q * (f (traj Gr β γ N x0 ξ (k - 1)).1 - f xstar) +
        2 * (γ * tau N k) * (f (refp Gr β γ N x0 xstar ξ (k + 1)) - f xstar) +
        (γ * tau N k) ^ 2 * G ^ 2 := by
    intro ξ
    have h1 := (h.one_sample (traj Gr β γ N x0 ξ k).1 (traj Gr β γ N x0 ξ k).2
      (refp Gr β γ N x0 xstar ξ (k + 1)) hs hc he).2
    rw [hq, traj_prev Gr β γ N x0 ξ k] at h1
    have hz : ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ (k + 1)‖ ^ 2 =
        ‖(traj Gr β γ N x0 ξ k).1 - (β / (1 - β) * γ * tau N k) • (traj Gr β γ N x0 ξ k).2 -
          refp Gr β γ N x0 xstar ξ (k + 1)‖ ^ 2 := rfl
    simp only [Φ]
    rw [hXeq, hz]
    linarith
  have hmono := integral_mono hin hcI hpt
  rw [hcE] at hmono
  linarith

theorem Hyp.expected_gap (h : Hyp p f Gr G xstar) {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ : 0 < γ) (N : ℕ) (x0 : E) :
    Integrable (fun ξ : ℕ → Ξ => f (traj Gr β γ N x0 ξ N).1 - f xstar) (prodLaw p) ∧
    2 * uu (β / (1 - β)) 1 * ∫ ξ, (f (traj Gr β γ N x0 ξ N).1 - f xstar) ∂(prodLaw p) ≤
      wt γ (β / (1 - β)) ((N : ℝ) + 2) * ‖x0 - xstar‖ ^ 2 +
        2 * nu (β / (1 - β)) ((N : ℝ) + 1) * (f x0 - f xstar) +
        (2 * γ * ((N : ℝ) + 1) + 4 * (β / (1 - β)) ^ 2 * γ * Real.log ((N : ℝ) + 2)) * G ^ 2 := by
  have hκ : 0 ≤ β / (1 - β) := div_nonneg hβ0 (by linarith)
  refine ⟨h.integrable_gap (h.memLp_traj β γ N x0 N).1, ?_⟩
  let a : ℕ → ℝ := fun k => ∫ ξ, (f (traj Gr β γ N x0 ξ k).1 - f xstar) ∂(prodLaw p)
  let D : ℕ → ℝ := fun k =>
    ∫ ξ, ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ k‖ ^ 2 ∂(prodLaw p)
  let B : ℕ → ℝ := fun k =>
    ∫ ξ, ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ (k + 1)‖ ^ 2 ∂(prodLaw p)
  let F : ℕ → ℝ := fun k => ∫ ξ, (f (refp Gr β γ N x0 xstar ξ k) - f xstar) ∂(prodLaw p)
  have ha : ∀ t, 0 ≤ a t := fun t => integral_nonneg (fun ξ => (h.gap_bounds _).1)
  have hD : ∀ t, 0 ≤ D t := fun t => integral_nonneg (fun ξ => sq_nonneg _)
  have hF0 : F 0 = 0 := by simp [F, refp]
  have hcast : ∀ t : ℕ, ((N + 1 : ℕ) : ℝ) - t = tau N t := fun t => by unfold tau; push_cast; ring
  have hle : ∀ t, t < N + 1 → t ≤ N := fun t ht => Nat.lt_succ_iff.mp ht
  have hpb := potential_bound (G := G) hγ hκ (Nat.succ_le_succ (Nat.zero_le N)) a D B F ha hD hF0
    (fun t ht => by
      rw [hcast t]
      exact h.descent_step hβ0 hβ1 hγ N x0 (hle t ht))
    (fun t ht => by
      rw [hcast t]
      exact h.jensen_step hβ0 hβ1 hγ N x0 (hle t ht))
    (fun t ht => by
      rw [hcast t]
      exact h.ref_gap_step hβ0 hβ1 hγ N x0 (hle t ht))
  have hsum := error_sum_le (κ := β / (1 - β)) (G := G) hγ.le (N + 1)
  have hD0 : D 0 = ‖x0 - xstar‖ ^ 2 := by simp [D, zed, traj, refp]
  have ha0 : a 0 = f x0 - f xstar := by simp [a, traj]
  have haN : a (N + 1 - 1) = ∫ ξ, (f (traj Gr β γ N x0 ξ N).1 - f xstar) ∂(prodLaw p) := by
    simp [a]
  rw [haN, hD0, ha0] at hpb
  have e1 : ((N + 1 : ℕ) : ℝ) + 1 = (N : ℝ) + 2 := by push_cast; ring
  have e2 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  rw [e1] at hpb hsum
  rw [e2] at hpb hsum
  linarith

end OracleTemplate.MomentumConvex
