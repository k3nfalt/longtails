import LongTails.Setups.InexactGradientStronglyConvex
import LongTails.Proofs.InexactAcceleratedStep
import LongTails.Proofs.SgdExecution
import LongTails.Proofs.GdPL
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.InexactGradient

open LongTails.Setups.InexactGradientStronglyConvex

lemma momentum_bounds {L μ α : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < momentum L μ α ∧ momentum L μ α ≤ 1 ∧
      16 * L * momentum L μ α ^ 2 ≤ μ * (1 - α) ∧
      16 * α ^ 2 * L * momentum L μ α ≤ μ * (1 - α) ∧
      μ * (1 - α) ≤ 20 * L * momentum L μ α ∧
      2 / momentum L μ α = 8 * Real.sqrt (L / (μ * (1 - α))) +
        32 * α ^ 2 * L / (μ * (1 - α)) := by
  have hm : 0 < μ * (1 - α) := mul_pos hμ (by linarith)
  have hmμ : μ * (1 - α) ≤ μ := by nlinarith
  obtain ⟨k, hk⟩ : ∃ k, k = L / (μ * (1 - α)) := ⟨_, rfl⟩
  have hk1 : 1 ≤ k := by
    rw [hk, le_div_iff₀ hm]
    linarith
  have hLk : L = k * (μ * (1 - α)) := by
    rw [hk, div_mul_cancel₀ _ hm.ne']
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt k := ⟨_, rfl⟩
  have hss : s * s = k := by
    rw [hs]
    exact Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ s := by
    rw [hs]
    exact Real.one_le_sqrt.mpr hk1
  have hsk : s ≤ k := by nlinarith
  have hα2 : α ^ 2 ≤ 1 := by nlinarith
  have hαk : 0 ≤ α ^ 2 * k := by positivity
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = momentum L μ α := ⟨_, rfl⟩
  have hθD : θ = 1 / (4 * s + 16 * (α ^ 2 * k)) := by
    rw [hθ, hs, hk, momentum]
    congr 2
    ring
  have hD : 0 < 4 * s + 16 * (α ^ 2 * k) := by linarith
  have hθ0 : 0 < θ := by
    rw [hθD]
    positivity
  have hθ1 : θ * (4 * s + 16 * (α ^ 2 * k)) = 1 := by
    rw [hθD]
    field_simp
  have hsθ : 0 ≤ s * θ := by positivity
  have hakθ : 0 ≤ α ^ 2 * k * θ := by positivity
  have h4s : 4 * (s * θ) ≤ 1 := by nlinarith
  have hkθ2 : 16 * (k * θ ^ 2) ≤ 1 := by
    have : (4 * (s * θ)) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hkθ : 1 ≤ 20 * (k * θ) := by nlinarith
  rw [← hθ]
  refine ⟨hθ0, by nlinarith, ?_, ?_, ?_, ?_⟩
  · rw [hLk]
    nlinarith
  · rw [hLk]
    nlinarith
  · rw [hLk]
    nlinarith
  · rw [hθD, hs, hk, one_div, div_inv_eq_mul]
    ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma advance_potential {f : E → ℝ} {grad : E → E} {L μ α δ θ : ℝ} {xs : E}
    (hL : 0 < L) (hμ : 0 < μ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hθL : 16 * L * θ ^ 2 ≤ μ * (1 - α)) (hθα : 16 * α ^ 2 * L * θ ≤ μ * (1 - α))
    (hup : ∀ x y, f y ≤ f x + ⟪grad x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hsc : ∀ x y, f x + ⟪grad x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : ∀ x, f xs ≤ f x) (answer : ℕ → E → E)
    (herr : ∀ k x, ‖answer k x - grad x‖ ≤ α * ‖grad x‖ + δ)
    (K call : ℕ) (s : E × E) :
    potential f μ xs (StochasticGradient.advance
        (fun k s => step L μ θ s (answer k (query θ s))) K call s) -
        2 / θ * (2 / (1 - α) * (3 / (4 * L) + 2 * θ / μ) * δ ^ 2) ≤
      (1 - θ / 2) ^ K * (potential f μ xs s -
        2 / θ * (2 / (1 - α) * (3 / (4 * L) + 2 * θ / μ) * δ ^ 2)) := by
  induction K generalizing call s with
  | zero => simp [StochasticGradient.advance]
  | succ K ih =>
    rw [StochasticGradient.advance]
    have h1 := ih (call + 1) (step L μ θ s (answer call (query θ s)))
    have h2 := step_potential hL hμ hα0 hα1 hθ0 hθ1 hθL hθα hup hsc hmin s
      (answer call (query θ s)) (herr call (query θ s))
    have hq : 0 ≤ (1 - θ / 2) ^ K := pow_nonneg (by linarith) K
    have hB : θ / 2 * (2 / θ * (2 / (1 - α) * (3 / (4 * L) + 2 * θ / μ) * δ ^ 2)) =
        2 / (1 - α) * (3 / (4 * L) + 2 * θ / μ) * δ ^ 2 := by
      field_simp
    have h3 := mul_le_mul_of_nonneg_left
      (show potential f μ xs (step L μ θ s (answer call (query θ s))) -
          2 / θ * (2 / (1 - α) * (3 / (4 * L) + 2 * θ / μ) * δ ^ 2) ≤
        (1 - θ / 2) * (potential f μ xs s -
          2 / θ * (2 / (1 - α) * (3 / (4 * L) + 2 * θ / μ) * δ ^ 2)) by linarith) hq
    refine h1.trans (h3.trans (le_of_eq ?_))
    rw [pow_succ]
    ring

lemma floor_le {L μ α δ θ ε : ℝ} (hL : 0 < L) (hμ : 0 < μ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθ : μ * (1 - α) ≤ 20 * L * θ)
    (hδ : 136 * δ ^ 2 ≤ μ * (1 - α) ^ 2 * ε) :
    2 / θ * (2 / (1 - α) * (3 / (4 * L) + 2 * θ / μ) * δ ^ 2) ≤ ε / 2 := by
  have hm : 0 < 1 - α := by linarith
  have h1 : 3 / (4 * L * θ) ≤ 15 / (μ * (1 - α)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have h2 : 2 / μ ≤ 2 / (μ * (1 - α)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  have he : 2 / θ * (2 / (1 - α) * (3 / (4 * L) + 2 * θ / μ) * δ ^ 2) =
      4 / (1 - α) * (3 / (4 * L * θ) + 2 / μ) * δ ^ 2 := by
    field_simp
    ring
  have h3 : 4 / (1 - α) * (3 / (4 * L * θ) + 2 / μ) * δ ^ 2 ≤
      4 / (1 - α) * (17 / (μ * (1 - α))) * δ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg δ)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have : (17 : ℝ) / (μ * (1 - α)) = 15 / (μ * (1 - α)) + 2 / (μ * (1 - α)) := by ring
    linarith
  have h4 : 4 / (1 - α) * (17 / (μ * (1 - α))) * δ ^ 2 ≤ ε / 2 := by
    have : 4 / (1 - α) * (17 / (μ * (1 - α))) * δ ^ 2 =
        68 * δ ^ 2 / (μ * (1 - α) ^ 2) := by
      field_simp
      ring
    rw [this, div_le_iff₀ (by positivity)]
    linarith
  linarith

lemma execute_accuracy [CompleteSpace E] {f : E → ℝ} {L μ α δ R ε : ℝ} {x0 xstar : E}
    (hμ : 0 < μ) (hμL : μ ≤ L) (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε)
    (hδ : 136 * δ ^ 2 ≤ μ * (1 - α) ^ 2 * ε)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hup : ∀ x y, f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : IsMinOn f Set.univ xstar) (hdist : ‖x0 - xstar‖ ≤ R)
    (O : Oracle E E)
    (herr : ∀ k x seed, ‖O.answer k (0, x) seed - gradient f x‖ ≤ α * ‖gradient f x‖ + δ)
    (seed : (inexactAccelerated L μ α x0).Seed) (ξ : (k : ℕ) → O.Seed k) (K : ℕ)
    (hbudget : ⌈(8 * Real.sqrt (L / (μ * (1 - α))) + 32 * α ^ 2 * L / (μ * (1 - α))) *
      Real.log (1 + 2 * L * R ^ 2 / ε)⌉₊ ≤ K) :
    f (execute O (inexactAccelerated L μ α x0) (fun _ => K) seed ξ) - f xstar ≤ ε := by
  have hL : 0 < L := hμ.trans_le hμL
  obtain ⟨hθ0, hθ1, hθL, hθα, hθlow, hθeq⟩ := momentum_bounds hμ hμL hα0 hα1
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = momentum L μ α := ⟨_, rfl⟩
  rw [← hθ] at hθ0 hθ1 hθL hθα hθlow hθeq
  have hminx : ∀ x, f xstar ≤ f x := fun x => hmin (Set.mem_univ x)
  have hzero : gradient f xstar = 0 := by
    apply (toDual ℝ E).injective
    simpa using (hmin.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero (hg xstar).hasFDerivAt
  have hstart : potential f μ xstar (x0, x0) ≤ L * R ^ 2 := by
    have h := hup xstar x0
    rw [hzero, inner_zero_left, add_zero] at h
    have hsq : ‖x0 - xstar‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
    have hn : 0 ≤ ‖x0 - xstar‖ ^ 2 := sq_nonneg _
    show f x0 - f xstar + μ / 4 * ‖x0 - xstar‖ ^ 2 ≤ L * R ^ 2
    nlinarith
  rw [StochasticGradient.execute_advance]
  have hadv := advance_potential hL hμ hα0 hα1 hθ0 hθ1 hθL hθα hup hsc hminx
    (fun k x => O.answer k (0, x) (ξ k)) (fun k x => herr k x (ξ k)) K 0 (x0, x0)
  have hfloor := floor_le hL hμ hα0 hα1 hθ0 hθlow hδ
  have hfloor0 : 0 ≤ 2 / θ * (2 / (1 - α) * (3 / (4 * L) + 2 * θ / μ) * δ ^ 2) := by
    have : 0 < 1 - α := by linarith
    positivity
  have hgeo := PLGradient.geometric_budget 2 θ (L * R ^ 2) (ε / 2) hθ0 (by linarith)
    (by positivity) (by positivity) K (by
      convert hbudget using 1
      rw [hθeq]
      congr 3
      field_simp)
  have hq : 0 ≤ (1 - θ / 2) ^ K := pow_nonneg (by linarith) K
  have h1 := mul_le_mul_of_nonneg_left hstart hq
  have h2 := mul_nonneg hq hfloor0
  have hpot : f (StochasticGradient.advance
      (fun k s => step L μ θ s (O.answer k (0, (query θ s)) (ξ k))) K 0 (x0, x0)).1 - f xstar ≤
      potential f μ xstar (StochasticGradient.advance
        (fun k s => step L μ θ s (O.answer k (0, (query θ s)) (ξ k))) K 0 (x0, x0)) := by
    have : 0 ≤ μ / 4 * ‖(StochasticGradient.advance
        (fun k s => step L μ θ s (O.answer k (0, (query θ s)) (ξ k))) K 0 (x0, x0)).2 - xstar‖ ^ 2 := by
      positivity
    unfold potential
    linarith
  rw [hθ] at hpot hadv
  show f (StochasticGradient.advance
      (fun k s => step L μ (momentum L μ α) s (O.answer k (0, (query (momentum L μ α) s)) (ξ k)))
      K 0 (x0, x0)).1 - f xstar ≤ ε
  rw [hθ] at h1 h2 hfloor hgeo
  nlinarith

end OracleTemplate.InexactGradient
