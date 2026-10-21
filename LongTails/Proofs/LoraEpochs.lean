import LongTails.Proofs.LoraModel
import LongTails.Proofs.LoraSilverLocal

namespace LongTails.Proofs.LoraEpochs

open LongTails.Algorithms.LoraGd LongTails.Setups.LocalSmoothStronglyConvexLora
open LongTails.Proofs.LoraModel LongTails.Proofs.SilverCertificate
open LongTails.Algorithms.SilverSchedule LongTails.Proofs.SilverTrace

variable {p : Params} {f : MatrixSpace p.m p.n → ℝ} {c : Factors p.m p.n p.r}

lemma step (H : Model p f c) (k : ℕ) {D₀ D : ℝ} (hD₀ : 0 ≤ D₀) (hD : 0 ≤ D) (hDD : D ≤ D₀)
    (hsmall : ((4 : ℝ) * 3 ^ k + 4) * D₀ ≤ p.s / 256)
    (herror : 12 * (2 + 2 * ratio) ^ k * ((4 : ℝ) * 3 ^ k) ^ 3 * D₀ ≤ p.R)
    (hS : 8 * condition p ≤ (steps k).sum)
    (x z : Factors p.m p.n p.r) (hz : product z = product c)
    (hcenter : ‖z - c‖ ≤ 41 * p.s / 256 + 4 * D₀ - 4 * D)
    (hx : ‖x - z‖ ≤ D) :
    let g := fun u => (1 / smoothness p) • pullback u (gradient f (product u))
    let y := run g (steps k) x
    ∃ z' : Factors p.m p.n p.r, product z' = product c ∧
      ‖y - z'‖ ≤ D / 2 ∧ ‖z' - c‖ ≤ 41 * p.s / 256 + 4 * D₀ - 2 * D ∧
      (steps k).sum * (f (product y) - f (product c)) ≤ smoothness p * D ^ 2 := by
  intro g y
  let A : ℝ := 4 * 3 ^ k
  let a := A * D
  have hA : 0 < A := by dsimp [A]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hR := H.R_pos
  have hs := H.s_pos
  have hL := H.smoothness_pos
  have hα := H.growth_pos
  have hκ : 0 < condition p := by rw [H.condition_eq]; positivity
  have hSpos : 0 < (steps k).sum := by nlinarith
  have hacap : a + 4 * D₀ ≤ p.s / 256 := by
    have hh := mul_le_mul_of_nonneg_left hDD (le_of_lt hA)
    change (A + 4) * D₀ ≤ p.s / 256 at hsmall
    dsimp [a]
    nlinarith
  have haR : a ≤ p.R := by linarith [H.s_le]
  have hcenter' : ‖z - c‖ + a ≤ p.s / 2 := by linarith
  have hsize : (3 : ℝ) ^ k * (5 * D) ≤ 2 * a + 3 * D := by
    dsimp [a, A]
    have hh : 0 ≤ (3 : ℝ) ^ k * D := by positivity
    nlinarith
  have herror' : 12 * (a / p.R) * (2 + 2 * ratio) ^ k * a ^ 2 ≤ D ^ 2 := by
    have hbase : 12 * (2 + 2 * ratio) ^ k * A ^ 3 * D ≤ p.R :=
      (mul_le_mul_of_nonneg_left hDD (by have := ratio_pos; positivity)).trans herror
    have hh := mul_le_mul_of_nonneg_right hbase (sq_nonneg D)
    apply (mul_le_mul_iff_of_pos_left hR).mp
    dsimp [a]
    field_simp
    ring_nf at hh ⊢
    exact hh
  obtain ⟨hnodes, hpot⟩ := LongTails.Proofs.LoraSilverLocal.block x z c
    H.rho_pos H.R_pos (le_of_lt H.s_pos) H.s_le ha haR hD H.convex H.grad H.lip H.reference
    H.gradient_zero (fun X => H.min (Set.mem_univ X)) hz hcenter' hx k hsize herror'
  change ‖y - z‖ ^ 2 + 2 * (steps k).sum *
    (f (product y) / smoothness p - f (product z) / smoothness p) ≤ 2 * D ^ 2 at hpot
  rw [hz, ← sub_div] at hpot
  have he := H.gap_nonneg y
  have hnterm : 0 ≤ 2 * (steps k).sum * ((f (product y) - f (product c)) / smoothness p) := by positivity
  have hold : ‖y - z‖ ≤ 3 * D / 2 := by nlinarith [norm_nonneg (y - z)]
  have hgap : (steps k).sum * (f (product y) - f (product c)) ≤ smoothness p * D ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hpot (le_of_lt hL)
    have heq : smoothness p *
        (2 * (steps k).sum * ((f (product y) - f (product c)) / smoothness p)) =
        2 * (steps k).sum * (f (product y) - f (product c)) := by
      have := ne_of_gt hL
      field_simp
    rw [mul_add, heq] at hh
    nlinarith [mul_nonneg (le_of_lt hL) (sq_nonneg ‖y - z‖)]
  have hy : ‖y - c‖ ≤ p.s / 2 := by
    have hyr := hnodes y (run_mem_nodes g (steps k) x)
    have hh : ‖y - c‖ ≤ ‖y - z‖ + ‖z - c‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (y - z) (z - c)
    linarith
  obtain ⟨z', hz', hrepair⟩ := H.repair y hy
  have hSα : 8 * smoothness p ≤ growth p * (steps k).sum := by
    have hh := mul_le_mul_of_nonneg_left hS (le_of_lt hα)
    rw [H.condition_eq] at hh
    have heq : growth p * (8 * (smoothness p / growth p)) = 8 * smoothness p := by
      have := ne_of_gt hα
      field_simp
    rwa [heq] at hh
  have hnew : ‖y - z'‖ ≤ D / 2 := by
    have hh := mul_le_mul_of_nonneg_left hrepair (le_of_lt hSpos)
    have hb := mul_le_mul_of_nonneg_right hSα (sq_nonneg ‖y - z'‖)
    have hsq : ‖y - z'‖ ^ 2 ≤ D ^ 2 / 4 := by
      apply (mul_le_mul_iff_of_pos_left hL).mp
      nlinarith only [hh, hb, hgap]
    nlinarith [norm_nonneg (y - z')]
  refine ⟨z', hz', hnew, ?_, hgap⟩
  have hmove : ‖z' - z‖ ≤ 2 * D := by
    have hh := norm_add_le (z' - y) (y - z)
    rw [sub_add_sub_cancel, norm_sub_rev z' y] at hh
    linarith
  have hh := norm_add_le (z' - z) (z - c)
  rw [sub_add_sub_cancel] at hh
  linarith

lemma trajectory (H : Model p f c) (k : ℕ) {D₀ : ℝ} (hD₀ : 0 ≤ D₀)
    (hsmall : ((4 : ℝ) * 3 ^ k + 4) * D₀ ≤ p.s / 256)
    (herror : 12 * (2 + 2 * ratio) ^ k * ((4 : ℝ) * 3 ^ k) ^ 3 * D₀ ≤ p.R)
    (hS : 8 * condition p ≤ (steps k).sum)
    (x : ℕ → Factors p.m p.n p.r) (z₀ : Factors p.m p.n p.r)
    (hz₀ : product z₀ = product c) (hcenter : ‖z₀ - c‖ ≤ 41 * p.s / 256)
    (hx : ‖x 0 - z₀‖ ≤ D₀)
    (hgap₀ : f (product (x 0)) - f (product c) ≤ 4 * smoothness p * p.R ^ 2)
    (hupdate : ∀ j, x (j + 1) = run (fun u => (1 / smoothness p) • pullback u (gradient f (product u))) (steps k) (x j)) :
    ∀ j, (∃ z : Factors p.m p.n p.r, product z = product c ∧
      ‖x j - z‖ ≤ D₀ / (2 : ℝ) ^ j ∧
      ‖z - c‖ ≤ 41 * p.s / 256 + 4 * D₀ - 4 * (D₀ / (2 : ℝ) ^ j)) ∧
      f (product (x j)) - f (product c) ≤ 4 * smoothness p * p.R ^ 2 / (4 : ℝ) ^ j := by
  have hL := H.smoothness_pos
  have hα := H.growth_pos
  have hR := H.R_pos
  have hκ : 1 ≤ condition p := by
    rw [H.condition_eq]
    exact (le_div_iff₀ hα).mpr (by simpa using H.growth_le)
  have hS1 : 1 ≤ (steps k).sum := by linarith
  have hD₀R : D₀ ≤ p.R := by
    have hh : 0 ≤ (4 : ℝ) * 3 ^ k * D₀ := by positivity
    nlinarith [H.s_pos, H.s_le]
  intro j
  induction j with
  | zero =>
    refine ⟨⟨z₀, hz₀, ?_, ?_⟩, ?_⟩
    · simpa using hx
    · simpa using hcenter
    · simpa using hgap₀
  | succ j ih =>
    obtain ⟨z, hz, hdist, hcen⟩ := ih.1
    have hD : 0 ≤ D₀ / (2 : ℝ) ^ j := by positivity
    have hDD : D₀ / (2 : ℝ) ^ j ≤ D₀ := div_le_self hD₀ (one_le_pow₀ (by norm_num))
    obtain ⟨z', hz', hdist', hcen', hgap'⟩ := step H k hD₀ hD hDD hsmall herror hS
      (x j) z hz hcen hdist
    rw [← hupdate j] at hdist' hgap'
    have hhalf : D₀ / (2 : ℝ) ^ (j + 1) = (D₀ / (2 : ℝ) ^ j) / 2 := by rw [pow_succ]; ring
    refine ⟨⟨z', hz', ?_, ?_⟩, ?_⟩
    · rw [hhalf]
      exact hdist'
    · rw [hhalf]
      nlinarith only [hcen']
    · have hgap0 := H.gap_nonneg (x (j + 1))
      have hh := mul_le_mul_of_nonneg_right hS1 hgap0
      have hgap : f (product (x (j + 1))) - f (product c) ≤
          smoothness p * (D₀ / (2 : ℝ) ^ j) ^ 2 := by nlinarith only [hh, hgap']
      have hsquare : D₀ ^ 2 ≤ p.R ^ 2 := pow_le_pow_left₀ hD₀ hD₀R 2
      have heq : smoothness p * (D₀ / (2 : ℝ) ^ j) ^ 2 = smoothness p * D₀ ^ 2 / (4 : ℝ) ^ j := by
        rw [div_pow, ← pow_mul, Nat.mul_comm j 2, pow_mul]
        norm_num
        ring
      rw [heq] at hgap
      have hbound : smoothness p * D₀ ^ 2 / (4 : ℝ) ^ j ≤
          smoothness p * p.R ^ 2 / (4 : ℝ) ^ j :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare (le_of_lt hL)) (by positivity)
      have heq' : 4 * smoothness p * p.R ^ 2 / (4 : ℝ) ^ (j + 1) =
          smoothness p * p.R ^ 2 / (4 : ℝ) ^ j := by rw [pow_succ]; ring
      rw [heq']
      exact hgap.trans hbound

end LongTails.Proofs.LoraEpochs
