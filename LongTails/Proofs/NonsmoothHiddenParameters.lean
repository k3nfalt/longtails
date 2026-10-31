import LongTails.Algorithms.NonsmoothHiddenAveraging
import LongTails.Proofs.NonsmoothHiddenTuning

namespace OracleTemplate.NonsmoothHidden

open LongTails.Setups.NonsmoothHiddenConvex

lemma parameter_geometry (p : Params) (hp : spec.valid p) :
    1 ≤ conditioning p ∧ 1 ≤ shape p ∧ 0 < radius p ∧ radius p ≤ p.R ∧
    64 * p.LJ * radius p ≤ p.μ ∧ 0 < epochFraction p ∧ epochFraction p ≤ 1 ∧
    2 * epochFraction p * p.Lc * p.R / p.μ = radius p := by
  rcases hp with ⟨hμ, hLc, hLJ, hG, hR, hε⟩
  have hκ : 1 ≤ conditioning p := (one_le_div hμ).2 hLc
  have hS : 1 ≤ shape p := by
    unfold shape
    have hh : 0 ≤ 64 * p.LJ * p.R / p.μ := by positivity
    linarith
  have hSp : 0 < shape p := by linarith
  have hκp : 0 < conditioning p := by linarith
  have hr : 0 < radius p := div_pos hR hSp
  have hrR : radius p ≤ p.R := div_le_self hR.le hS
  have hreg : 64 * p.LJ * radius p ≤ p.μ := by
    change 64 * p.LJ * (p.R / shape p) ≤ p.μ
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hSp).2
    unfold shape
    have he : p.μ * (1 + 64 * p.LJ * p.R / p.μ) = p.μ + 64 * p.LJ * p.R := by
      field_simp
    rw [he]
    linarith
  have ht : 0 < epochFraction p := by unfold epochFraction; positivity
  have ht1 : epochFraction p ≤ 1 := by
    unfold epochFraction
    apply (div_le_one (by positivity)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hκ) (sub_nonneg.mpr hS)]
  refine ⟨hκ, hS, hr, hrR, hreg, ht, ht1, ?_⟩
  have hLcpos : 0 < p.Lc := lt_of_lt_of_le hμ hLc
  unfold epochFraction conditioning radius
  field_simp

lemma parameter_counts (p : Params) (hp : spec.valid p) :
    1 ≤ localIterations p ∧ 0 < dualScale p ∧
    16 * p.G * radius p * (1 + Real.log ((localIterations p : ℝ) + 1)) /
      Real.sqrt (localIterations p : ℝ) ≤ epochFraction p * p.ε / 2 := by
  have hg := parameter_geometry p hp
  rcases hp with ⟨hμ, hLc, hLJ, hG, hR, hε⟩
  have hLcpos : 0 < p.Lc := lt_of_lt_of_le hμ hLc
  have hv : 0 ≤ signal p := by unfold signal; positivity
  have hc := local_accuracy_tuning hv (localIterations p) (Nat.le_ceil _)
    (Nat.ceil_lt_add_one (by positivity)).le
  have hN : (1 : ℝ) ≤ localIterations p := by exact_mod_cast hc.1
  have hs : 0 < Real.sqrt (localIterations p : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hD : 0 < dualScale p := by unfold dualScale; exact div_pos (mul_pos hG hs) hg.2.2.1
  refine ⟨hc.1, hD, ?_⟩
  have ht : 0 < epochFraction p := hg.2.2.2.2.2.1
  have hshape : 0 < shape p := by linarith [hg.2.1]
  have he : signal p * (epochFraction p * p.ε) = p.G * radius p := by
    unfold signal epochFraction conditioning radius
    field_simp
  have hh := mul_le_mul_of_nonneg_right hc.2 (mul_nonneg ht.le hε.le)
  calc
    _ = (16 * signal p * (1 + Real.log ((localIterations p : ℝ) + 1)) /
        Real.sqrt (localIterations p : ℝ)) * (epochFraction p * p.ε) := by
      calc
        _ = 16 * (p.G * radius p) * (1 + Real.log ((localIterations p : ℝ) + 1)) /
            Real.sqrt (localIterations p : ℝ) := by ring
        _ = _ := by rw [← he]; ring
    _ ≤ (1 / 2 : ℝ) * (epochFraction p * p.ε) := hh
    _ = _ := by ring

noncomputable def workSize (p : Params) : ℝ :=
  shape p * (conditioning p + p.G ^ 2 * p.Lc ^ 3 * p.R ^ 2 / (p.μ ^ 3 * p.ε ^ 2))

lemma parameter_outer_accuracy (p : Params) (hp : spec.valid p) :
    (1 - epochFraction p) ^ outerIterations p * initialBound p ≤ p.ε / 2 := by
  have hg := parameter_geometry p hp
  rcases hp with ⟨hμ, hLc, hLJ, hG, hR, hε⟩
  have hA : 1 ≤ conditioning p * shape p := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hg.1) (sub_nonneg.mpr hg.2.1)]
  have hd : 0 ≤ initialBound p / p.ε := by unfold initialBound; positivity
  have hK : 2 * (conditioning p * shape p) * Real.log (2 + 2 * (initialBound p / p.ε)) ≤
      (outerIterations p : ℝ) := by
    unfold outerIterations
    have he : 2 * (conditioning p * shape p) * Real.log (2 + 2 * (initialBound p / p.ε)) =
        2 * conditioning p * shape p * Real.log (2 + 2 * initialBound p / p.ε) := by
      congr 1 <;> ring
    rw [he]
    exact Nat.le_ceil _
  have hh := epoch_accuracy_tuning hA hd (outerIterations p) hK
  have ht : 1 / (2 * (conditioning p * shape p)) = epochFraction p := by unfold epochFraction; ring
  rw [ht] at hh
  have he : (1 - epochFraction p) ^ outerIterations p * (initialBound p / p.ε) =
      ((1 - epochFraction p) ^ outerIterations p * initialBound p) / p.ε := by ring
  rw [he] at hh
  have h := (div_le_iff₀ hε).mp hh
  linarith

lemma parameter_work (p : Params) (hp : spec.valid p) :
    (outerIterations p : ℝ) * localIterations p ≤ 10000000000 * workSize p *
      (Real.log (10000000000 * (2 + workSize p))) ^ 3 := by
  have hg := parameter_geometry p hp
  rcases hp with ⟨hμ, hLc, hLJ, hG, hR, hε⟩
  let κ := conditioning p
  let θ := p.LJ * p.R / p.μ
  let w := p.G * p.R / p.ε
  let A := κ * (1 + 64 * θ)
  let B := w ^ 2 * κ ^ 3 * (1 + 64 * θ)
  have hκ : 1 ≤ κ := hg.1
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hS : 1 ≤ 1 + 64 * θ := by linarith
  have hA : 1 ≤ A := by
    dsimp [A]
    nlinarith [mul_nonneg (sub_nonneg.mpr hκ) (sub_nonneg.mpr hS)]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hv : 0 ≤ signal p := by unfold signal; have : 0 < p.Lc := lt_of_lt_of_le hμ hLc; positivity
  have hd : 0 ≤ initialBound p / p.ε := by unfold initialBound; positivity
  have hsignal : signal p = 2 * w * κ := by dsimp [signal, w, κ, conditioning]; ring
  have hdval : initialBound p / p.ε = w * (1 + θ) := by dsimp [initialBound, w, θ]; ring
  have hAv : A * signal p ^ 2 = 4 * B := by rw [hsignal]; dsimp [A, B]; ring
  have hκ2 : 1 ≤ κ ^ 2 := by nlinarith
  have hθS : 1 + θ ≤ 1 + 64 * θ := by linarith
  have hcomp : 1 + θ ≤ κ ^ 2 * (1 + 64 * θ) := by
    have hh := mul_le_mul_of_nonneg_right hκ2 (by linarith : 0 ≤ 1 + 64 * θ)
    linarith
  have hdAv : 2 * (initialBound p / p.ε) ≤ A * signal p := by
    rw [hdval, hsignal]
    have hh := mul_le_mul_of_nonneg_left hcomp hw
    dsimp [A]
    nlinarith
  have hAB : 2 * (initialBound p / p.ε) ≤ A + B := by
    have hh := mul_nonneg (by linarith : 0 ≤ A) (sq_nonneg (signal p - 2))
    nlinarith [hAv]
  have hN : (localIterations p : ℝ) ≤
      4194304 * (1 + signal p) ^ 2 * (Real.log (16 * (1 + signal p))) ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hAeq : A = conditioning p * shape p := by dsimp [A, κ, θ, shape]; ring
  have hK : (outerIterations p : ℝ) ≤ 2 * A * Real.log (2 + 2 * (initialBound p / p.ε)) + 1 := by
    have hh := (Nat.ceil_lt_add_one (show 0 ≤ 2 * conditioning p * shape p *
      Real.log (2 + 2 * initialBound p / p.ε) from by
        have hl : 0 ≤ Real.log (2 + 2 * initialBound p / p.ε) := Real.log_nonneg (by
          have hi : 0 ≤ initialBound p := by unfold initialBound; positivity
          have hh : 0 ≤ 2 * initialBound p / p.ε := by positivity
          linarith)
        have hk : 0 ≤ conditioning p := by linarith [hg.1]
        have hs : 0 ≤ shape p := by linarith [hg.2.1]
        positivity)).le
    change (outerIterations p : ℝ) ≤ _ at hh
    convert hh using 1
    rw [hAeq]
    ring
  have hab : A + B = workSize p := by
    dsimp [A, B, κ, θ, w, workSize, shape, conditioning]
    ring
  have hh := total_count_bound hA hB hv hd hAv.le hAB (localIterations p) (outerIterations p) hN hK
  simpa only [add_assoc, hab] using hh

end OracleTemplate.NonsmoothHidden
