import LongTails.Proofs.SilverTrace

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SilverNonexpansive

open LongTails.Algorithms.SilverSchedule
open LongTails.Proofs.SilverCertificate
open LongTails.Proofs.SilverTrace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma certificate (φ : E → ℝ) (g : E → E)
    (hdef : ∀ u v, 0 ≤ defect (φ u) (φ v) u v (g u) (g v))
    (k : ℕ) (x z : E) (hz : g z = 0) :
    ‖run g (steps k) x - z‖ ^ 2 +
        (steps k).sum * ((steps k).sum + 1) * ‖g (run g (steps k) x)‖ ^ 2 +
        2 * (steps k).sum * (φ (run g (steps k) x) - φ z) ≤ ‖x - z‖ ^ 2 := by
  have h := endpoint_bound φ g (fun _ => True) 0 le_rfl
    (fun u v _ _ => by simpa using hdef u v) k x z hz trivial (fun _ _ => trivial)
  simpa using h

lemma join_nonexpansive (φ : E → ℝ) (g : E → E)
    (hdef : ∀ u v, 0 ≤ defect (φ u) (φ v) u v (g u) (g v))
    (k : ℕ) (x z : E) (hz : g z = 0) :
    ‖run g (steps k) x - (1 + ratio ^ k / ratio) • g (run g (steps k) x) - z‖ ≤ ‖x - z‖ := by
  set y := run g (steps k) x
  set μ := 1 + ratio ^ k / ratio
  set S := (steps k).sum
  have hc := certificate φ g hdef k x z hz
  have h1 := hdef z y
  have h2 := hdef y z
  rw [hz] at h1 h2
  simp only [defect, zero_sub, norm_neg, inner_zero_left, mul_zero, sub_zero] at h1 h2
  have hS : S = ratio ^ k - 1 := steps_sum k
  have hr1 : 1 ≤ ratio ^ k := one_le_pow₀ (by linarith [ratio_gt_two])
  have hμ1 : μ - 1 = ratio ^ k / ratio := by simp [μ]
  have hdiv : ratio ^ k / ratio ≤ ratio ^ k := by
    rw [div_le_iff₀ ratio_pos]
    nlinarith [ratio_gt_two]
  have hdiv0 : 0 ≤ ratio ^ k / ratio := div_nonneg (by positivity) ratio_pos.le
  have hμ : 0 ≤ μ := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hsq : (μ - 1) ^ 2 ≤ (S + 1) ^ 2 := by
    rw [hμ1, hS]
    nlinarith
  have hexp : ‖y - μ • g y - z‖ ^ 2 =
      ‖y - z‖ ^ 2 - 2 * μ * ⟪g y, y - z⟫ + μ ^ 2 * ‖g y‖ ^ 2 := by
    have he : y - μ • g y - z = (y - z) - μ • g y := by module
    rw [he, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg hμ,
      real_inner_comm]
    ring
  have hin : ⟪g y, z - y⟫ = -⟪g y, y - z⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [hin] at h1
  have ha := sq_nonneg ‖g y‖
  have hm1 := mul_le_mul_of_nonneg_left
    (show (φ y - φ z) + ‖g y‖ ^ 2 / 2 ≤ ⟪g y, y - z⟫ by linarith) hμ
  have hm2 := mul_le_mul_of_nonneg_left
    (show ‖g y‖ ^ 2 / 2 ≤ φ y - φ z by linarith) (show 0 ≤ 2 * S + 2 * μ by linarith)
  have hm3 := mul_le_mul_of_nonneg_right hsq ha
  have hfinal : ‖y - μ • g y - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
    rw [hexp]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hfinal

lemma nonexpansive (φ : E → ℝ) (g : E → E)
    (hdef : ∀ u v, 0 ≤ defect (φ u) (φ v) u v (g u) (g v))
    (k : ℕ) (x z : E) (hz : g z = 0) :
    ∀ u ∈ nodes g (steps k) x, ‖u - z‖ ≤ ‖x - z‖ := by
  induction k generalizing x with
  | zero =>
    intro u hu
    have he : u = x := by simpa only [steps, nodes, List.mem_singleton] using hu
    rw [he]
  | succ k ih =>
    let μ := 1 + ratio ^ k / ratio
    let y := run g (steps k) x
    let p := y - μ • g y
    have hp : ‖p - z‖ ≤ ‖x - z‖ := join_nonexpansive φ g hdef k x z hz
    intro u hu
    change u ∈ nodes g (steps k ++ [μ] ++ steps k) x at hu
    rcases (nodes_append g (steps k ++ [μ]) (steps k) x u).1 hu with hu | hu
    · rcases (nodes_append g (steps k) [μ] x u).1 hu with hu | hu
      · exact ih x u hu
      · change u ∈ nodes g [μ] y at hu
        simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact ih x _ (run_mem_nodes g (steps k) x)
        · exact hp
    · have hu' : u ∈ nodes g (steps k) p := by
        simpa only [run_append, run, y, p] using hu
      exact (ih p u hu').trans hp

end LongTails.Proofs.SilverNonexpansive
