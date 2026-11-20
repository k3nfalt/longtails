import LongTails.Proofs.MultirateService
import LongTails.Proofs.MultirateTrajectory
import LongTails.Proofs.LeonAccuracy

namespace LongTails.Proofs.MultirateStaleness

open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex (objective)
open LongTails.Algorithms.MultirateSchedule
open MultirateTrajectory

variable {p : Params}

lemma gradient_average {f : Functions p} (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (z : Point p) : gradient (objective (network p) f) z = (p.n : ℝ)⁻¹ • ∑ i, gradient (f i) z :=
  (OracleTemplate.FiniteSum.objective_gradient (f := f)
    (oracle := fun ix : Fin p.n × Point p => gradient (f ix.1) ix.2) hf z).gradient

lemma gradient_lipschitz {f : Functions p} (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hl : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x-y‖) (z w : Point p) :
    ‖gradient (objective (network p) f) z - gradient (objective (network p) f) w‖ ≤
      smoothness p * ‖z - w‖ := by
  rw [gradient_average hf, gradient_average hf, ← smul_sub, ← Finset.sum_sub_distrib, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (p.n : ℝ)⁻¹ * (∑ i, p.L i * ‖z - w‖) := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hl i z w))
    _ = _ := by rw [← Finset.sum_mul]; unfold smoothness; ring

variable (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)

lemma travel (hε : 0 < p.ε) (hL : 0 < smoothness p) (j k : ℕ) (hj : j ≤ k) :
    ‖x g s k - x g s j‖ ≤ (k-j : ℕ) * (δ p / smoothness p) := by
  have hd := LeonBatchTuning.resolution_pos (network p) hε
  have hη := div_nonneg hd.le hL.le
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hj
  induction r with
  | zero => simp
  | succ r ih =>
    have hs := ParameterFreeNsgdmRun.normalized_move_norm (δ p / smoothness p) hη
      (x g s (j+r)) (v g s (j+r))
    rw [← x_step] at hs
    have he := (norm_sub_le_norm_sub_add_norm_sub (x g s ((j+r)+1)) (x g s (j+r)) (x g s j)).trans
      (add_le_add hs (ih (Nat.le_add_right _ _)))
    simpa [Nat.add_assoc, add_mul, add_comm] using he

noncomputable def stale (f : Functions p) (k : ℕ) : Point p :=
  (p.n : ℝ)⁻¹ • ∑ i, gradient (f i) (x g s (anchor p i (block p i k)))

lemma stale_error (hh : ∀ i, 0 < p.h i) (hε : 0 < p.ε) (hL : 0 < smoothness p)
    (hcomp : ∀ i, 0 ≤ p.L i) {f : Functions p} (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hl : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x-y‖) (k : ℕ) :
    ‖stale g s f k - gradient (objective (network p) f) (x g s k)‖ ≤ 4 * δ p := by
  let η := δ p / smoothness p
  have hη : 0 ≤ η := div_nonneg (LeonBatchTuning.resolution_pos (network p) hε).le hL.le
  have htime := MultirateService.tick_pos hh hcomp hL
  have hcost := MultirateService.weighted_periods hcomp htime hL
  have hle (i : Fin p.n) :
      ‖gradient (f i) (x g s (anchor p i (block p i k))) - gradient (f i) (x g s k)‖ ≤
        (p.L i * (period p i : ℝ)) * (2*η) := by
    apply (hl i _ _).trans
    rw [norm_sub_rev]
    have h := travel g s hε hL _ _ (anchor_bounds (p := p) i k).1
    have hc : ((k - anchor p i (block p i k) : ℕ) : ℝ) ≤ 2 * (period p i : ℝ) := by
      exact_mod_cast source_age (p := p) i k
    calc
      _ ≤ p.L i * ((2 * (period p i : ℝ)) * η) :=
        mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right hc hη)) (hcomp i)
      _ = _ := by ring
  rw [stale,gradient_average hf,← smul_sub, ← Finset.sum_sub_distrib,norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  calc
    _ ≤ (p.n : ℝ)⁻¹ * (∑ i, (p.L i * (period p i : ℝ)) * (2*η)) := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hle i))
    _ ≤ (p.n : ℝ)⁻¹ * ((2 * ∑ i, p.L i) * (2*η)) := by
      rw [← Finset.sum_mul]; gcongr
    _ = 4 * (smoothness p * η) := by unfold smoothness; ring
    _ = _ := by dsimp [η]; field_simp

end LongTails.Proofs.MultirateStaleness
