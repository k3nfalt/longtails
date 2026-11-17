import LongTails.Proofs.HolderNoiseHardLower
import LongTails.Proofs.HolderNoiseHardScales
import LongTails.Proofs.HolderNoiseInitializationLower
import LongTails.Proofs.HolderNoisePhase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace LongTails.Proofs.HolderNoiseChainFailure

open OracleTemplate LongTails.Setups.HolderNoiseNonconvexLower
open HolderNoiseHardScaling HolderNoiseHardScales HolderNoiseHardLength HolderNoiseHardDimension
open HolderNoiseHardOracle HolderNoiseHardAdmissible HolderNoiseHardExecution HolderNoiseHardLower

lemma failure (q : LowerParams) (hq : spec.valid q) (A : Alg q) (N : ℕ) {ℓ v : ℝ}
    (hℓ : 0 < ℓ) (hℓL : ℓ ≤ q.L) (hD : (2 : ℝ) ^ 22 ≤ q.Δ * ℓ / q.ε ^ 2)
    (hv : (2 : ℝ) ^ 24 ≤ v) (hN : (N : ℝ) ≤ (q.Δ * ℓ / q.ε ^ 2) * v / (2 : ℝ) ^ 60)
    (hNdim : (N : ℝ) ≤ (q.L * q.Δ / q.ε ^ 2) * (1 + q.σ ^ 2 / q.ε ^ 2))
    (hσ : v = (2 : ℝ) ^ 24 ∨ q.ε ^ 2 * v ≤ q.σ ^ 2)
    (hM : v = (2 : ℝ) ^ 24 ∨ q.ε ^ 2 * v ≤ q.M * (q.ε / ℓ) ^ (2 * q.ν)) :
    ∃ (f : spec.Instance q) (O : Oracle (spec.Query q) (spec.Reply q)),
      spec.admissible q f O ∧
        ¬ spec.successful q f
          (fun z : A.Seed × ((t : ℕ) → O.Seed t) => execute O A (fun _ => N) z.1 z.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  rcases hq with ⟨hq, _, hdim⟩
  change 0 < q.L ∧ 0 ≤ q.M ∧ 0 < q.ν ∧ q.ν ≤ 1 ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε at hq
  rcases hq with ⟨hL, hM0, hν, hν1, _, hΔ, hε⟩
  let p := (2 : ℝ) ^ 24 / v
  let k := ⌈8 * N * p⌉₊
  let a := valueScale ℓ q.ε
  let b := spaceScale ℓ q.ε
  have hp := probability_bounds hv
  change 0 < p ∧ p ≤ 1 at hp
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv
  have ha : 0 ≤ a := (valueScale_pos hℓ hε).le
  have hb : 0 < b := spaceScale_pos hℓ hε
  have hk : (k : ℝ) + 1 ≤ q.L * q.Δ / q.ε ^ 2 := by
    have h := length_le hD hv N hN
    have hle : q.Δ * ℓ / q.ε ^ 2 ≤ q.L * q.Δ / q.ε ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith
    exact h.trans hle
  have hd : (2 : ℝ) ^ 30 * (1 + q.L * q.Δ / q.ε ^ 2) ^ 3 * (1 + q.σ ^ 2 / q.ε ^ 2) ≤ q.d :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hdim)
  have hmargin := dimension_margin (d := q.d) (k := k) (N := N)
    (by positivity : 0 ≤ q.L * q.Δ / q.ε ^ 2) (by positivity : 0 ≤ q.σ ^ 2 / q.ε ^ 2)
    hd (by exact_mod_cast hk) hNdim
  let D := (q.d : ℝ) - (k + 1)
  have hDs : D + (k + 1 : ℕ) ≤ q.d := by dsimp [D]; push_cast; linarith
  have hacc : q.ε < (a / b) * (3 / 8 : ℝ) * (1 - N * p / (k + 1)) := accuracy_margin hℓ hε hp.1.le N
  have hσ' : p = 1 ∨ (66 * a / b) ^ 2 / p ≤ q.σ ^ 2 := by
    rcases hσ with he | hσ
    · left
      dsimp [p]
      rw [he]
      norm_num
    · exact Or.inr (scale_variance hℓ hε hv0 hσ)
  have hM' : p = 1 ∨ ((2 * (66 * a / b)) ^ (2 - 2 * q.ν) * (10242 * a / b ^ 2) ^ (2 * q.ν) / p) ≤ q.M := by
    rcases hM with he | hM
    · left
      dsimp [p]
      rw [he]
      norm_num
    · exact Or.inr (scale_holder hℓ hε hv0 hν.le hM)
  obtain ⟨π, hπ⟩ := exists_failure q A ha hb hp.1 hp.2 N D hmargin.1 hDs hmargin.2 hacc
  refine ⟨objective π a b q.x0,
    pairOracle q hp.1.le hp.2 (oracleValue p (field π a b q.x0) (noise π a b q.x0)), ?_, hπ⟩
  apply HolderNoiseHardAdmissible.admissible q π ha hb hp.1 hp.2 hν.le hν1 hM0
  · exact (scale_smoothness hℓ hε).le.trans hℓL
  · exact objective_gap_scale hℓ hε hD hv N hN
  · exact hσ'
  · exact hM'

end LongTails.Proofs.HolderNoiseChainFailure

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace LongTails.Proofs.HolderNoiseDeterministicFailure

open OracleTemplate LongTails.Setups.HolderNoiseNonconvexLower HolderNoiseHardExecution

lemma failure (q : LowerParams) (hq : spec.valid q) (A : Alg q) (N : ℕ)
    (hN : (N : ℝ) ≤ (q.L * q.Δ / q.ε ^ 2) / (2 : ℝ) ^ 40) :
    ∃ (f : spec.Instance q) (O : Oracle (spec.Query q) (spec.Reply q)),
      spec.admissible q f O ∧
        ¬ spec.successful q f
          (fun z : A.Seed × ((t : ℕ) → O.Seed t) => execute O A (fun _ => N) z.1 z.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hv := hq.1
  change 0 < q.L ∧ 0 ≤ q.M ∧ 0 < q.ν ∧ q.ν ≤ 1 ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε at hv
  rcases hv with ⟨hL, _, _, _, _, hΔ, hε⟩
  by_cases hzero : N = 0
  · subst N
    apply HolderNoiseInitializationFailure.failure q hq A 0
    norm_num only [Nat.cast_zero]
    positivity
  · have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hD : (2 : ℝ) ^ 22 ≤ q.Δ * q.L / q.ε ^ 2 := by
      have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 40)).mp hN
      rw [mul_comm q.Δ q.L]
      norm_num at h ⊢
      nlinarith
    have hn : (N : ℝ) ≤ (q.Δ * q.L / q.ε ^ 2) * (2 : ℝ) ^ 24 / (2 : ℝ) ^ 60 := by
      rw [mul_comm q.Δ q.L]
      have hd : 0 ≤ q.L * q.Δ / q.ε ^ 2 := by positivity
      norm_num at hN ⊢
      nlinarith
    have hnDim : (N : ℝ) ≤ (q.L * q.Δ / q.ε ^ 2) * (1 + q.σ ^ 2 / q.ε ^ 2) := by
      have hd : 0 ≤ q.L * q.Δ / q.ε ^ 2 := by positivity
      have hnD : (N : ℝ) ≤ q.L * q.Δ / q.ε ^ 2 := by norm_num at hN; nlinarith
      have hσ : 0 ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
      nlinarith
    exact HolderNoiseChainFailure.failure q hq A N hL le_rfl hD le_rfl hn hnDim (Or.inl rfl) (Or.inl rfl)

end LongTails.Proofs.HolderNoiseDeterministicFailure

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace LongTails.Proofs.HolderNoiseLowerBound

open OracleTemplate LongTails.Setups.HolderNoiseNonconvexLower HolderNoiseHardExecution
open HolderNoisePhase HolderNoiseLowerReduction

lemma failure_at (q : LowerParams) (hq : spec.valid q) (A : Alg q) (N : ℕ)
    (hN : (N : ℝ) ≤ ((q.L * q.Δ + q.σ ^ 2) / q.ε ^ 2 +
      min (q.Δ * q.L * q.σ ^ 2 / q.ε ^ 4)
        (q.Δ / q.ε ^ 3 * max (q.M * (q.L / q.ε) ^ (1 - 2 * q.ν))
          (q.M ^ (1 / (2 * q.ν)) * q.σ ^ (2 - 1 / q.ν)))) / (2 : ℝ) ^ 80) :
    ∃ (f : spec.Instance q) (O : Oracle (spec.Query q) (spec.Reply q)),
      spec.admissible q f O ∧
        ¬ spec.successful q f
          (fun z : A.Seed × ((t : ℕ) → O.Seed t) => execute O A (fun _ => N) z.1 z.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hv := hq.1
  change 0 < q.L ∧ 0 ≤ q.M ∧ 0 < q.ν ∧ q.ν ≤ 1 ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε at hv
  rcases hv with ⟨hL, hM, hν, _, hσ, hΔ, hε⟩
  let D := q.L * q.Δ / q.ε ^ 2
  let V := q.σ ^ 2 / q.ε ^ 2
  let U := q.M * (q.ε / q.L) ^ (2 * q.ν) / q.ε ^ 2
  have hD : 0 < D := by
    have hgap := hq.2.1
    have hd : 64 ≤ D := by
      dsimp [D]
      rw [le_div_iff₀ (sq_pos_of_pos hε)]
      exact hgap
    linarith
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hphase := normalized_phase hL hM hν hσ hΔ hε
  have hbudget : (N : ℝ) ≤ (D + V + D * min V
      (max U (U ^ (1 / (2 * q.ν)) * V ^ (1 - 1 / (2 * q.ν))))) / (2 : ℝ) ^ 80 := by
    dsimp [D, V, U]
    rw [hphase, ← add_div]
    exact hN
  by_cases hdet : (N : ℝ) ≤ D / (2 : ℝ) ^ 40
  · exact HolderNoiseDeterministicFailure.failure q hq A N hdet
  · by_cases hinit : (N : ℝ) ≤ V / 64
    · apply HolderNoiseInitializationFailure.failure q hq A N
      simpa only [V, div_div, mul_comm] using hinit
    · obtain ⟨τ, v, hτ0, hτ1, hDt, hv, hvV, hvU, hNv, hNdim⟩ :=
        select_noise_regime hD hV hU hν N hbudget hdet hinit
      have hℓ : 0 < q.L * τ := mul_pos hL hτ0
      have hℓL : q.L * τ ≤ q.L := by nlinarith
      have he : q.Δ * (q.L * τ) / q.ε ^ 2 = D * τ := by dsimp [D]; ring
      have hvar : q.ε ^ 2 * v ≤ q.σ ^ 2 := by
        have h := (le_div_iff₀ (sq_pos_of_pos hε)).mp hvV
        nlinarith
      have hholder : q.ε ^ 2 * v ≤ q.M * (q.ε / (q.L * τ)) ^ (2 * q.ν) := by
        have hr : (q.ε / (q.L * τ)) ^ (2 * q.ν) =
            (q.ε / q.L) ^ (2 * q.ν) * τ ^ (-2 * q.ν) := by
          rw [show q.ε / (q.L * τ) = (q.ε / q.L) * τ⁻¹ by field_simp,
            Real.mul_rpow (div_nonneg hε.le hL.le) (inv_nonneg.mpr hτ0.le),
            Real.inv_rpow hτ0.le, ← Real.rpow_neg hτ0.le]
          congr 2
          ring
        calc
          _ ≤ q.ε ^ 2 * (U * τ ^ (-2 * q.ν)) := mul_le_mul_of_nonneg_left hvU (sq_nonneg _)
          _ = _ := by dsimp [U]; rw [hr]; field_simp
      apply HolderNoiseChainFailure.failure q hq A N hℓ hℓL
        (by simpa only [he] using hDt) hv (by simpa only [he] using hNv) hNdim (Or.inr hvar) (Or.inr hholder)

end LongTails.Proofs.HolderNoiseLowerBound
