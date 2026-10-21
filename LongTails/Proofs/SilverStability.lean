import LongTails.Proofs.SilverTrace

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SilverStability

open LongTails.Algorithms.SilverSchedule
open LongTails.Proofs.SilverCertificate
open LongTails.Proofs.SilverTrace

lemma join_coefficient (k : ℕ) :
    (1 + ratio ^ (k + 1) / ratio) ^ 2 ≤
      4 * (steps (k + 1)).sum * ((steps (k + 1)).sum + 1) := by
  rw [steps_sum, pow_succ ratio k, mul_div_cancel_right₀ _ (ne_of_gt ratio_pos)]
  have hq : 1 ≤ ratio ^ k := one_le_pow₀ (by linarith [ratio_gt_two])
  have hr := mul_le_mul_of_nonneg_left ratio_gt_two.le (show 0 ≤ ratio ^ k by positivity)
  have hs : 0 ≤ ratio ^ k * ratio - 1 := by nlinarith
  have hμ : 1 + ratio ^ k ≤ 2 * (ratio ^ k * ratio - 1) := by nlinarith
  have hp := pow_le_pow_left₀ (show 0 ≤ 1 + ratio ^ k by positivity) hμ 2
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma join_radius {S μ a D : ℝ} (y v z : E)
    (ha : 0 ≤ a) (hD : 0 ≤ D) (hμ : 0 ≤ μ) (hS : 0 ≤ S * (S + 1))
    (hc : μ ^ 2 ≤ 4 * S * (S + 1))
    (hp : ‖y - z‖ ^ 2 + S * (S + 1) * ‖v‖ ^ 2 ≤ a ^ 2 + D ^ 2) :
    ‖y - μ • v - z‖ ≤ 3 * a + 3 * D := by
  have hnon := mul_nonneg hS (sq_nonneg ‖v‖)
  have hy : ‖y - z‖ ≤ a + D := by
    nlinarith [norm_nonneg (y - z), mul_nonneg ha hD]
  have hscaled := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖v‖)
  have hv : μ * ‖v‖ ≤ 2 * (a + D) := by
    nlinarith [sq_nonneg ‖y - z‖, mul_nonneg hμ (norm_nonneg v), mul_nonneg ha hD]
  calc
    ‖y - μ • v - z‖ = ‖y - z - μ • v‖ := by congr 1; module
    _ ≤ ‖y - z‖ + ‖μ • v‖ := norm_sub_le _ _
    _ = ‖y - z‖ + μ * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg hμ]
    _ ≤ 3 * a + 3 * D := by linarith

lemma empty_join_radius (g : E → E) (x z : E) {a : ℝ}
    (hx : ‖x - z‖ ≤ a) (hg : ‖g x‖ ≤ ‖x - z‖) :
    ‖x - (1 + ratio ^ 0 / ratio) • g x - z‖ ≤ 3 * a := by
  have hμ : 0 ≤ 1 + ratio ^ 0 / ratio := by
    have := ratio_pos
    positivity
  have hμ₂ : 1 + ratio ^ 0 / ratio ≤ 2 := by
    rw [pow_zero, ratio_inverse]
    linarith [ratio_lt_three]
  have hscaled := mul_le_mul_of_nonneg_right hμ₂ (norm_nonneg (g x))
  calc
    ‖x - (1 + ratio ^ 0 / ratio) • g x - z‖ =
        ‖x - z - (1 + ratio ^ 0 / ratio) • g x‖ := by congr 1; module
    _ ≤ ‖x - z‖ + ‖(1 + ratio ^ 0 / ratio) • g x‖ := norm_sub_le _ _
    _ = ‖x - z‖ + (1 + ratio ^ 0 / ratio) * ‖g x‖ := by
      rw [norm_smul, Real.norm_of_nonneg hμ]
    _ ≤ 3 * a := by linarith

lemma prefix_localization (f : E → ℝ) (g : E → E) (z : E) {R D δ : ℝ}
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hz : g z = 0)
    (hmin : ∀ u, ‖u - z‖ ≤ R → 0 ≤ f u - f z)
    (hgrad : ∀ u, ‖u - z‖ ≤ R → ‖g u‖ ≤ ‖u - z‖)
    (hq : ∀ u v, ‖u - z‖ ≤ R → ‖v - z‖ ≤ R →
      -δ ≤ defect (f u) (f v) u v (g u) (g v))
    (k : ℕ) (a : ℝ) (x : E) (ha : 0 ≤ a) (hx : ‖x - z‖ ≤ a)
    (herror : ∀ j ≤ k, 3 * (2 + 2 * ratio) ^ j * δ ≤ D ^ 2)
    (hsize : (3 : ℝ) ^ k * (2 * a + 3 * D) ≤ 2 * R + 3 * D) :
    ∀ u ∈ nodes g (steps k) x, ‖u - z‖ ≤ R := by
  induction k generalizing a x with
  | zero =>
    intro u hu
    have he : u = x := by simpa only [steps, nodes, List.mem_singleton] using hu
    subst u
    have har : a ≤ R := by
      simp only [pow_zero, one_mul] at hsize
      linarith
    exact hx.trans har
  | succ k ih =>
    let μ := 1 + ratio ^ k / ratio
    let y := run g (steps k) x
    let p := y - μ • g y
    have herr : ∀ j ≤ k, 3 * (2 + 2 * ratio) ^ j * δ ≤ D ^ 2 :=
      fun j hj => herror j (Nat.le_trans hj (Nat.le_succ k))
    have hsmall : (3 : ℝ) ^ k * (2 * a + 3 * D) ≤ 2 * R + 3 * D := by
      rw [pow_succ] at hsize
      have hp : 0 ≤ (3 : ℝ) ^ k * (2 * a + 3 * D) := by positivity
      nlinarith
    have hleft := ih a x ha hx herr hsmall
    have hy : ‖y - z‖ ≤ R := hleft y (run_mem_nodes g (steps k) x)
    have hpot := endpoint_bound f g (fun u => ‖u - z‖ ≤ R) δ hδ hq k x z hz
      (by simpa only [sub_self, norm_zero] using hR) hleft
    change ‖y - z‖ ^ 2 + (steps k).sum * ((steps k).sum + 1) * ‖g y‖ ^ 2 +
      2 * (steps k).sum * (f y - f z) ≤
        ‖x - z‖ ^ 2 + 3 * (2 + 2 * ratio) ^ k * δ at hpot
    have hS : 0 ≤ (steps k).sum := by
      rw [steps_sum]
      exact sub_nonneg.mpr (one_le_pow₀ (by linarith [ratio_gt_two]))
    have hgap := mul_nonneg (show 0 ≤ 2 * (steps k).sum by positivity) (hmin y hy)
    have hxx := pow_le_pow_left₀ (norm_nonneg (x - z)) hx 2
    have henergy : ‖y - z‖ ^ 2 + (steps k).sum * ((steps k).sum + 1) * ‖g y‖ ^ 2 ≤
        a ^ 2 + D ^ 2 := by linarith [herr k le_rfl]
    have hp : ‖p - z‖ ≤ 3 * a + 3 * D := by
      cases k with
      | zero =>
        have hxR : ‖x - z‖ ≤ R := hleft x (start_mem_nodes g (steps 0) x)
        have he := empty_join_radius g x z hx (hgrad x hxR)
        have hb : ‖x - (1 + ratio ^ 0 / ratio) • g x - z‖ ≤ 3 * a + 3 * D := by
          linarith
        simpa only [p, y, μ, steps, run] using hb
      | succ j =>
        have hμ : 0 ≤ μ := by
          dsimp [μ]
          have := ratio_pos
          positivity
        exact join_radius y (g y) z ha hD hμ
          (mul_nonneg hS (by linarith)) (join_coefficient j) henergy
    have hrightsize : (3 : ℝ) ^ k * (2 * (3 * a + 3 * D) + 3 * D) ≤
        2 * R + 3 * D := by
      rw [pow_succ] at hsize
      nlinarith only [hsize]
    have hright := ih (3 * a + 3 * D) p (by positivity) hp herr hrightsize
    intro u hu
    change u ∈ nodes g (steps k ++ [μ] ++ steps k) x at hu
    rcases (nodes_append g (steps k ++ [μ]) (steps k) x u).1 hu with hu | hu
    · rcases (nodes_append g (steps k) [μ] x u).1 hu with hu | hu
      · exact hleft u hu
      · change u ∈ nodes g [μ] y at hu
        simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact hy
        · exact hright p (start_mem_nodes g (steps k) p)
    · apply hright u
      simpa only [run_append, run, y, p] using hu

lemma local_block (f : E → ℝ) (g : E → E) (x z : E) {R D ν : ℝ}
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hν : 0 ≤ ν) (hz : g z = 0)
    (hx : ‖x - z‖ ≤ D)
    (hmin : ∀ u, ‖u - z‖ ≤ R → 0 ≤ f u - f z)
    (hgrad : ∀ u, ‖u - z‖ ≤ R → ‖g u‖ ≤ ‖u - z‖)
    (hq : ∀ u v, ‖u - z‖ ≤ R → ‖v - z‖ ≤ R →
      -ν * ‖u - v‖ ^ 2 ≤ defect (f u) (f v) u v (g u) (g v))
    (k : ℕ) (hsize : (3 : ℝ) ^ k * (5 * D) ≤ 2 * R + 3 * D)
    (herror : 12 * ν * (2 + 2 * ratio) ^ k * R ^ 2 ≤ D ^ 2) :
    (∀ u ∈ nodes g (steps k) x, ‖u - z‖ ≤ R) ∧
      ‖run g (steps k) x - z‖ ^ 2 +
          (steps k).sum * ((steps k).sum + 1) * ‖g (run g (steps k) x)‖ ^ 2 +
          2 * (steps k).sum * (f (run g (steps k) x) - f z) ≤ 2 * D ^ 2 := by
  let δ := 4 * ν * R ^ 2
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hflat : ∀ u v, ‖u - z‖ ≤ R → ‖v - z‖ ≤ R →
      -δ ≤ defect (f u) (f v) u v (g u) (g v) := by
    intro u v hu hv
    have hnorm : ‖u - v‖ ≤ 2 * R := by
      have he : u - v = (u - z) - (v - z) := by module
      rw [he]
      exact (norm_sub_le _ _).trans (by linarith)
    have hs := pow_le_pow_left₀ (norm_nonneg (u - v)) hnorm 2
    have hm := mul_le_mul_of_nonneg_left hs hν
    have hd := hq u v hu hv
    dsimp [δ]
    nlinarith
  have hcap : ∀ j ≤ k, 3 * (2 + 2 * ratio) ^ j * δ ≤ D ^ 2 := by
    intro j hj
    have hp := pow_le_pow_right₀ (show 1 ≤ 2 + 2 * ratio by linarith [ratio_pos]) hj
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 3 by norm_num)) hδ
    have he : 3 * (2 + 2 * ratio) ^ k * δ ≤ D ^ 2 := by
      dsimp [δ]
      nlinarith only [herror]
    exact hm.trans he
  have hbudget : (3 : ℝ) ^ k * (2 * D + 3 * D) ≤ 2 * R + 3 * D := by
    nlinarith only [hsize]
  have hn := prefix_localization f g z hR hD hδ hz hmin hgrad hflat k D x hD hx hcap hbudget
  refine ⟨hn, ?_⟩
  have he := endpoint_bound f g (fun u => ‖u - z‖ ≤ R) δ hδ hflat k x z hz
    (by simpa only [sub_self, norm_zero] using hR) hn
  have hs := pow_le_pow_left₀ (norm_nonneg (x - z)) hx 2
  linarith [hcap k le_rfl]

end LongTails.Proofs.SilverStability
