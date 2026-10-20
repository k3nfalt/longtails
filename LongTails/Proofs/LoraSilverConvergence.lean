import LongTails.Proofs.LoraSilverTuning
import LongTails.Proofs.LoraEpochs
import LongTails.Proofs.LoraExecution

namespace LongTails.Proofs.LoraSilverConvergence

open LongTails.Algorithms.LoraGd LongTails.Setups.LocalSmoothStronglyConvexLora
open LongTails.Proofs.LoraModel LongTails.Proofs.LoraSilverTuning
open LongTails.Algorithms.SilverSchedule LongTails.Algorithms.LoraSilver
open LongTails.Proofs.SilverCertificate LongTails.Proofs.SilverTrace LongTails.Proofs.LoraExecution

variable {p : Params} {f : MatrixSpace p.m p.n → ℝ} {c : Factors p.m p.n p.r}

lemma cap_coarse (H : Model p f c) : growth p ^ 2 / (256 * p.ρ) ≤ 4 * smoothness p * p.R ^ 2 := by
  have hρ := H.rho_pos
  have hsq := pow_le_pow_left₀ (le_of_lt H.growth_pos) H.growth_le 2
  apply (div_le_iff₀ (show 0 < 256 * p.ρ by positivity)).mpr
  unfold smoothness at hsq ⊢
  nlinarith [sq_nonneg (p.ρ * p.R ^ 2)]

lemma warmup_entry (H : Model p f c)
    (hinit : ‖p.x₀ - c‖ ≤ p.μ * p.s ^ 2 / (256 * p.ρ * p.R)) :
    let g := fun u : Factors p.m p.n p.r => (1 / smoothness p) • pullback u (gradient f (product u))
    let x := run g (List.replicate (warmup p) 1) p.x₀
    ∃ z : Factors p.m p.n p.r, product z = product c ∧
      ‖x - z‖ ≤ tiny p ∧ ‖z - c‖ ≤ 41 * p.s / 256 ∧
      f (product x) - f (product c) ≤ 4 * smoothness p * p.R ^ 2 := by
  intro g x
  let w := fun n => run g (List.replicate n 1) p.x₀
  have hw0 : w 0 = p.x₀ := rfl
  have hwstep : ∀ n, w (n + 1) = w n - (1 / smoothness p) • pullback (w n) (gradient f (product (w n))) := by
    intro n
    dsimp only [w]
    rw [run_replicate, run_replicate, Function.iterate_succ_apply']
    simp only [one_smul]
    rfl
  have ht := LongTails.Proofs.LoraWarmup.trajectory H w (by simpa only [hw0] using hinit) hwstep (warmup p)
  change 0 ≤ f (product x) - f (product c) ∧
    f (product x) - f (product c) ≤ (f (product p.x₀) - f (product c)) *
      (1 - growth p / (4 * smoothness p)) ^ warmup p ∧ ‖x - c‖ ≤ 33 * p.s / 256 at ht
  have hq : 0 ≤ 1 - growth p / (4 * smoothness p) := by
    have hh : growth p / (4 * smoothness p) ≤ 1 :=
      (div_le_one (by have := H.smoothness_pos; positivity)).mpr
        (by have := H.growth_le; have := H.smoothness_pos; linarith)
    linarith
  have hcap := LongTails.Proofs.LoraWarmup.initial_gap H p.x₀ hinit
  have he : f (product x) - f (product c) ≤
      (growth p ^ 2 / (256 * p.ρ)) / (2 : ℝ) ^ (32 * (depth p + 1)) := by
    have hh := mul_le_mul hcap (warmup_decay H) (pow_nonneg hq _)
      (show 0 ≤ growth p ^ 2 / (256 * p.ρ) by have := H.rho_pos; positivity)
    exact ht.2.1.trans (by simpa only [mul_one_div] using hh)
  have hecap : f (product x) - f (product c) ≤ growth p ^ 2 / (256 * p.ρ) :=
    he.trans (div_le_self (by have := H.rho_pos; positivity) (one_le_pow₀ (by norm_num)))
  obtain ⟨z, hz, hd, hcenter⟩ := LongTails.Proofs.LoraWarmup.repair_center H x ht.2.2 hecap
  exact ⟨z, hz, warmup_repair_accuracy H (norm_nonneg _) hd he, hcenter, hecap.trans (cap_coarse H)⟩

lemma schedule_accuracy (H : Model p f c) (hε : 0 < p.ε)
    (hinit : ‖p.x₀ - c‖ ≤ p.μ * p.s ^ 2 / (256 * p.ρ * p.R)) :
    f (product (run (fun u => (1 / smoothness p) • pullback u (gradient f (product u)))
      (schedule p) p.x₀)) - f (product c) ≤ p.ε := by
  let g := fun u : Factors p.m p.n p.r => (1 / smoothness p) • pullback u (gradient f (product u))
  let w := run g (List.replicate (warmup p) 1) p.x₀
  obtain ⟨z, hz, hd, hc, he⟩ := warmup_entry H hinit
  let x := fun j => (run g (steps (depth p)))^[j] w
  have hx0 : x 0 = w := rfl
  have hxstep : ∀ j, x (j + 1) = run g (steps (depth p)) (x j) :=
    fun j => Function.iterate_succ_apply' _ _ _
  have hS : 8 * condition p ≤ (steps (depth p)).sum := by
    rw [steps_sum]
    linarith [depth_mass H]
  have ht := LongTails.Proofs.LoraEpochs.trajectory H (depth p) (le_of_lt (tiny_pos H))
    (tiny_tube H) (tiny_certificate H) hS x z hz hc hd he hxstep (epochs p)
  have hout : run g (schedule p) p.x₀ = x (epochs p) := by
    rw [schedule, run_append, run_blocks]
  change f (product (run g (schedule p) p.x₀)) - f (product c) ≤ p.ε
  rw [hout]
  exact ht.2.trans (epochs_accuracy H hε)

end LongTails.Proofs.LoraSilverConvergence
