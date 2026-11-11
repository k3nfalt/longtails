import LongTails.Proofs.EmpiricalProximalSampling
import LongTails.Proofs.EmpiricalProximalCertificate
import LongTails.Proofs.EmpiricalProximalOuter

open Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.EmpiricalProximalConvergence

open OracleTemplate
open LongTails.Setups.FiniteSumStrongGrowthConvex
open LongTails.Algorithms.EmpiricalProximalAcceleration
open EmpiricalProximalModel EmpiricalProximalInner EmpiricalProximalSampling

noncomputable def potential (p : Params) (f : Fin p.n → p.E → ℝ) (u : p.E) (s : State p) : ℝ :=
  s.1 * (objective f s.2.1 - objective f u) + ‖s.2.2 - u‖ ^ 2 / 2

lemma step_energy (p : Params) (hL : 0 < p.L) (hρ : 1 ≤ p.ρ)
    (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ p.L * ‖x - y‖)
    (hsg : ∀ x, (𝔼 i, ‖g (i, x)‖ ^ 2) ≤ p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2)
    {u : p.E} (hu : ∀ i x, f i u ≤ f i x) (s : State p) (hA : 0 ≤ s.1) :
    (𝔼 σ : BatchIndices p × InnerSeeds p, potential p f u (step p g s σ)) ≤ potential p f u s := by
  let μ := regularization p
  let v := predictor p s
  let y := RecursiveEnvelopeGeometry.prox (FiniteSum.fullGradient g) μ v
  let φ := fun σ : BatchIndices p × InnerSeeds p =>
    LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun j => f (indices p σ.1 j))
  let q := fun σ : BatchIndices p × InnerSeeds p =>
    FiniteSum.fullGradient (fun r => g (indices p σ.1 r.1, r.2))
  let z := fun σ : BatchIndices p × InnerSeeds p => batchPoint g μ v (indices p σ.1)
  let w := fun σ : BatchIndices p × InnerSeeds p => innerOutput p g v (indices p σ.1) σ.2
  have hμ : 0 < μ := regularization_pos p hL
  have hφc : ∀ σ, ConvexOn ℝ univ (φ σ) := fun σ =>
    FiniteSum.objective_convex (fun j => hc (indices p σ.1 j))
  have hφg : ∀ σ x, HasGradientAt (φ σ) (q σ x) x := fun σ x =>
    FiniteSum.objective_gradient (fun j x => hg (indices p σ.1 j) x) x
  have hφl : ∀ σ x t, ‖q σ x - q σ t‖ ≤ p.L * ‖x - t‖ := fun σ =>
    FiniteSum.fullGradient_lipschitz (fun j x t => hlip (indices p σ.1 j) x t)
  have hy : FiniteSum.fullGradient g y = μ • (v - y) :=
    batch_point_field hg hμ hu v (fun i : Fin p.n => i)
  have hz : ∀ σ, q σ (z σ) = μ • (v - z σ) := fun σ =>
    batch_point_field hg hμ hu v (indices p σ.1)
  have ep (F : BatchIndices p × InnerSeeds p → ℝ) :
      (𝔼 σ, F σ) = 𝔼 β, 𝔼 ξ, F (β, ξ) := Finset.expect_product _ _ F
  have hv : (𝔼 σ, ‖z σ - y‖ ^ 2) ≤ ‖v - y‖ ^ 2 / 1024 := by
    rw [ep]
    simp only [z, Fintype.expect_const]
    exact sampled_variance p hL hρ f g hc hg hsg hu v
  have hgen : (𝔼 σ, (objective f (z σ) - φ σ (z σ))) ≤ μ * ‖v - y‖ ^ 2 / 64 := by
    rw [ep]
    simp only [z, φ, Fintype.expect_const]
    exact sampled_generalization p hL hρ f g hc hg hlip hsg hu v
  have hi : (p.L + μ) ^ 2 * (𝔼 σ, ‖w σ - z σ‖ ^ 2) ≤ μ ^ 2 * ‖v - y‖ ^ 2 / 2 ^ 20 := by
    rw [ep]
    exact inner_population_distance p hL (by linarith) f g hc hg hlip hu v (indices p)
      (sampled_raw_moment p hρ g hsg v)
  have hcert := EmpiricalProximalCertificate.approximate_certificate hL.le hμ
    (FiniteSum.objective_gradient hg) hφg hφc (FiniteSum.fullGradient_lipschitz hlip) hφl
    v y z w hy hz hv hgen hi
  have hmean (x : p.E) : (𝔼 σ, φ σ x) = objective f x := by
    rw [ep]
    simp only [φ, Fintype.expect_const]
    exact sampled_objective_mean p f x
  have he := EmpiricalProximalOuter.expected_energy_step hφc hφg (objective f)
    (inv_pos.mpr hμ) hA s.2.1 s.2.2 u w hmean hcert.1 hcert.2
  exact he

lemma run_energy (p : Params) (hL : 0 < p.L) (hρ : 1 ≤ p.ρ)
    (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ p.L * ‖x - y‖)
    (hsg : ∀ x, (𝔼 i, ‖g (i, x)‖ ^ 2) ≤ p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2)
    {u : p.E} (hu : ∀ i x, f i u ≤ f i x) (T : ℕ) (s : State p) (hA : 0 ≤ s.1) :
    (𝔼 ξ : Seeds p T, potential p f u (run p g T s ξ)) ≤ potential p f u s := by
  induction T generalizing s with
  | zero => simp [run]
  | succ T ih =>
    change (𝔼 ξ : Fin (T + 1) → BatchIndices p × InnerSeeds p,
      potential p f u (run p g (T + 1) s ξ)) ≤ _
    rw [VarianceReducedWeakMinty.expect_fin_succ]
    simp only [run, Fin.cons_zero, Fin.cons_succ]
    have hn (σ : BatchIndices p × InnerSeeds p) : 0 ≤ (step p g s σ).1 := by
      change 0 ≤ s.1 + ProximalStorm.aNext (regularization p)⁻¹ s.1
      exact add_nonneg hA (ProximalStorm.aNext_pos (inv_pos.mpr (regularization_pos p hL)) hA).le
    have he := Finset.expect_le_expect (s := Finset.univ) (fun σ _ => ih (step p g s σ) (hn σ))
    exact he.trans (step_energy p hL hρ f g hc hg hlip hsg hu s hA)

lemma run_weight (p : Params) (g : Fin p.n × p.E → p.E) (T k : ℕ) (s : State p)
    (hs : s.1 = ProximalStorm.accA (regularization p)⁻¹ k) (ξ : Seeds p T) :
    (run p g T s ξ).1 = ProximalStorm.accA (regularization p)⁻¹ (k + T) := by
  induction T generalizing k s with
  | zero => simpa only [run, Nat.add_zero] using hs
  | succ T ih =>
    have hn : (step p g s (ξ 0)).1 = ProximalStorm.accA (regularization p)⁻¹ (k + 1) := by
      change s.1 + ProximalStorm.aNext (regularization p)⁻¹ s.1 = _
      rw [hs, ProximalStorm.accA]
    have he := ih (k + 1) (step p g s (ξ 0)) hn (fun i => ξ i.succ)
    simpa only [run, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he

lemma output_gap_bound (p : Params) (hL : 0 < p.L) (hρ : 1 ≤ p.ρ)
    (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ p.L * ‖x - y‖)
    (hsg : ∀ x, (𝔼 i, ‖g (i, x)‖ ^ 2) ≤ p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2)
    {u : p.E} (hu : ∀ i x, f i u ≤ f i x) (T : ℕ) (hT : 0 < T) :
    (𝔼 ξ : Seeds p T, (objective f (output p g T ξ) - objective f u)) ≤
      2 * regularization p * ‖p.x0 - u‖ ^ 2 / (T : ℝ) ^ 2 := by
  let lam := (regularization p)⁻¹
  have hl : 0 < lam := inv_pos.mpr (regularization_pos p hL)
  have hw (ξ : Seeds p T) : (run p g T (0, p.x0, p.x0) ξ).1 = ProximalStorm.accA lam T := by
    simpa only [Nat.zero_add] using run_weight p g T 0 (0, p.x0, p.x0) rfl ξ
  have he := run_energy p hL hρ f g hc hg hlip hsg hu T (0, p.x0, p.x0) le_rfl
  have hp (ξ : Seeds p T) : ProximalStorm.accA lam T *
      (objective f (output p g T ξ) - objective f u) ≤
        potential p f u (run p g T (0, p.x0, p.x0) ξ) := by
    unfold potential output
    rw [hw]
    exact le_add_of_nonneg_right (by positivity)
  have hmean := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ => hp ξ)
  rw [← Finset.mul_expect] at hmean
  have hmin (x : p.E) : objective f u ≤ objective f x := by
    simp only [objective, FiniteSum.objective_eq_expect]
    exact Finset.expect_le_expect (s := Finset.univ) (fun i _ => hu i x)
  have hgap : 0 ≤ (𝔼 ξ : Seeds p T, (objective f (output p g T ξ) - objective f u)) :=
    Finset.expect_nonneg (fun ξ _ => sub_nonneg.mpr (hmin _))
  have hweight := mul_le_mul_of_nonneg_right (ProximalStorm.accA_ge hl T) hgap
  have hpot : potential p f u (0, p.x0, p.x0) = ‖p.x0 - u‖ ^ 2 / 2 := by simp [potential]
  rw [hpot] at he
  have hlow : lam * (T : ℝ) ^ 2 / 4 *
      (𝔼 ξ : Seeds p T, (objective f (output p g T ξ) - objective f u)) ≤ ‖p.x0 - u‖ ^ 2 / 2 :=
    hweight.trans (hmean.trans he)
  have hm := mul_le_mul_of_nonneg_left hlow (regularization_pos p hL).le
  have hid : regularization p * lam = 1 := mul_inv_cancel₀ (regularization_pos p hL).ne'
  have ht : 0 < (T : ℝ) ^ 2 := sq_pos_of_pos (by exact_mod_cast hT)
  apply (le_div_iff₀ ht).mpr
  have heq : regularization p * (lam * (T : ℝ) ^ 2 / 4 *
      (𝔼 ξ : Seeds p T, (objective f (output p g T ξ) - objective f u))) =
      (T : ℝ) ^ 2 / 4 * (𝔼 ξ : Seeds p T, (objective f (output p g T ξ) - objective f u)) := by
    rw [show regularization p * (lam * (T : ℝ) ^ 2 / 4 *
      (𝔼 ξ : Seeds p T, (objective f (output p g T ξ) - objective f u))) =
      (regularization p * lam) * ((T : ℝ) ^ 2 / 4 *
        (𝔼 ξ : Seeds p T, (objective f (output p g T ξ) - objective f u))) by ring, hid, one_mul]
  rw [heq] at hm
  nlinarith only [hm]

end LongTails.Proofs.EmpiricalProximalConvergence
