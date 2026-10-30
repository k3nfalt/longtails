import LongTails.Proofs.ScheduledMomentumWitness

namespace LongTails.Proofs.ScheduledMomentumSgd

open MeasureTheory ProbabilityTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar
open LongTails.Setups.ScheduledMomentumComparison
open LongTails.Proofs.DiagonalSpectral LongTails.Proofs.SeparationInstance
open LongTails.Proofs.SeparationModel LongTails.Proofs.GaussianBlocks
open LongTails.Proofs.GaussianLinear LongTails.Proofs.ScheduledMomentumExecution
open LongTails.Proofs.ScheduledMomentumWitness

noncomputable def coef (ℓ s β : ℝ) (η : ℕ → ℝ) (B : ℕ) : ℕ → ℕ → ℝ × ℝ
  | 0, _ => (0, 0)
  | t + 1, k =>
      if k < B * t then
        ((coef ℓ s β η B t k).1 - η t * (β * (coef ℓ s β η B t k).2 +
            (1 - β) * ℓ * (coef ℓ s β η B t k).1),
          β * (coef ℓ s β η B t k).2 + (1 - β) * ℓ * (coef ℓ s β η B t k).1)
      else (-(η t * ((1 - β) * s / B)), (1 - β) * s / B)

variable (r : ℕ) (ℓ c s β : ℝ) (η : ℕ → ℝ) (φ : FlatShape) (B : ℕ)

lemma sgd_linear (ξ : ℕ → ℝ) (t : ℕ) :
    (scalarState r false ℓ c s β η φ B ξ t).1.1 =
        ∑ k ∈ Finset.range (B * t), (coef ℓ s β η B t k).1 * ξ k ∧
      (scalarState r false ℓ c s β η φ B ξ t).2.1 =
        ∑ k ∈ Finset.range (B * t), (coef ℓ s β η B t k).2 * ξ k := by
  induction t with
  | zero => simp [scalarState]
  | succ t ih =>
      obtain ⟨hx, ha⟩ := ih
      have hnot : ∀ j, ¬ (B * t + j < B * t) := fun j => by omega
      have h1 : (∑ k ∈ Finset.range (B * t), (coef ℓ s β η B (t + 1) k).2 * ξ k) =
          β * (∑ k ∈ Finset.range (B * t), (coef ℓ s β η B t k).2 * ξ k) +
            (1 - β) * ℓ * ∑ k ∈ Finset.range (B * t), (coef ℓ s β η B t k).1 * ξ k := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [coef, Finset.mem_range.mp hk, ↓reduceIte]
        ring
      have h3 : (∑ k ∈ Finset.range (B * t), (coef ℓ s β η B (t + 1) k).1 * ξ k) =
          (∑ k ∈ Finset.range (B * t), (coef ℓ s β η B t k).1 * ξ k) -
            η t * ∑ k ∈ Finset.range (B * t), (coef ℓ s β η B (t + 1) k).2 * ξ k := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [coef, Finset.mem_range.mp hk, ↓reduceIte]
        ring
      have h2 : (∑ j ∈ Finset.range B, (coef ℓ s β η B (t + 1) (B * t + j)).2 * ξ (B * t + j)) =
          (1 - β) * s * blockMean B t ξ := by
        simp only [coef, hnot, ↓reduceIte, blockMean, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have h4 : (∑ j ∈ Finset.range B, (coef ℓ s β η B (t + 1) (B * t + j)).1 * ξ (B * t + j)) =
          -(η t * ((1 - β) * s * blockMean B t ξ)) := by
        simp only [coef, hnot, ↓reduceIte, blockMean, Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      simp only [scalarState, scalarDirection, Bool.false_eq_true, ↓reduceIte]
      rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_add, h3, h1, h2, h4, ← hx, ← ha]
      constructor <;> ring

lemma sgd_flat_indep (ξ ξ' : ℕ → ℝ) (t : ℕ) :
    (scalarState r false ℓ c s β η φ B ξ t).1.2 = (scalarState r false ℓ c s β η φ B ξ' t).1.2 ∧
      (scalarState r false ℓ c s β η φ B ξ t).2.2 =
        (scalarState r false ℓ c s β η φ B ξ' t).2.2 := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [scalarState, scalarDirection, Bool.false_eq_true, ↓reduceIte, h1, h2, and_self]

lemma sgd_flat_step (ξ : ℕ → ℝ) (u : ℕ) :
    (scalarState r false ℓ c s β η φ B ξ (u + 1)).1.2 -
        (scalarState r false ℓ c s β η φ B ξ u).1.2 =
      -(η u * (scalarState r false ℓ c s β η φ B ξ (u + 1)).2.2) := by
  simp only [scalarState, scalarDirection, Bool.false_eq_true, ↓reduceIte]
  ring

lemma coef_sq_lower {B : ℕ} (hB : 0 < B) (t : ℕ) :
    η t ^ 2 * ((1 - β) * s) ^ 2 / B ≤
      ∑ k ∈ Finset.range (B * (t + 1)), (coef ℓ s β η B (t + 1) k).1 ^ 2 := by
  have hnot : ∀ j, ¬ (B * t + j < B * t) := fun j => by omega
  rw [Nat.mul_succ, Finset.sum_range_add]
  have h2 : (∑ j ∈ Finset.range B, (coef ℓ s β η B (t + 1) (B * t + j)).1 ^ 2) =
      η t ^ 2 * ((1 - β) * s) ^ 2 / B := by
    simp only [coef, hnot, ↓reduceIte, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    field_simp
  rw [h2]
  have h1 : 0 ≤ ∑ k ∈ Finset.range (B * t), (coef ℓ s β η B (t + 1) k).1 ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  linarith

lemma stiff_abs_integral (t : ℕ) :
    Integrable (fun ξ => |(scalarState r false ℓ c s β η φ B ξ t).1.1|) stdStream ∧
    (4 / 9) * Real.sqrt (∑ k ∈ Finset.range (B * t), (coef ℓ s β η B t k).1 ^ 2) ≤
      ∫ ξ, |(scalarState r false ℓ c s β η φ B ξ t).1.1| ∂stdStream := by
  have hlaw := linear_law (fun k => (coef ℓ s β η B t k).1) (B * t)
  have he : (fun ξ => |(scalarState r false ℓ c s β η φ B ξ t).1.1|) =
      fun ξ : ℕ → ℝ => |∑ k ∈ Finset.range (B * t), (coef ℓ s β η B t k).1 * ξ k| := by
    funext ξ
    rw [(sgd_linear r ℓ c s β η φ B ξ t).1]
  have hV : 0 ≤ ∑ k ∈ Finset.range (B * t), (coef ℓ s β η B t k).1 ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmeas : Measurable (fun ξ : ℕ → ℝ =>
      ∑ k ∈ Finset.range (B * t), (coef ℓ s β η B t k).1 * ξ k) := by fun_prop
  rw [he]
  constructor
  · apply (integrable_map_measure (g := fun x : ℝ => |x|) (by fun_prop) hmeas.aemeasurable).mp
    rw [hlaw]
    exact ((memLp_id_gaussianReal 1).integrable le_rfl).abs
  · rw [← integral_map (f := fun x : ℝ => |x|) hmeas.aemeasurable (by fun_prop), hlaw]
    exact gaussian_abs_lower _ hV

lemma stiff_step_lower {B : ℕ} (hB : 0 < B) (u : ℕ) :
    4 / 9 * (|η u| * ((1 - β) * s) / Real.sqrt B) ≤
      ∫ ξ, |(scalarState r false ℓ c s β η φ B ξ (u + 1)).1.1| ∂stdStream := by
  refine le_trans ?_ (stiff_abs_integral r ℓ c s β η φ B (u + 1)).2
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.le_sqrt_of_sq_le
  have hB' : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  rw [div_pow, Real.sq_sqrt hB', mul_pow, sq_abs]
  exact coef_sq_lower ℓ s β η hB u

set_option maxHeartbeats 1000000 in
theorem sgd_momentum_lower (p : LongTails.Setups.BatchedSpectralSmooth.Public)
    (hp : LongTails.Setups.ScheduledMomentumComparison.spec.valid p) : SgdMomentumLower p := by
  obtain ⟨hr, hL, hΔ, hs, hε, hLΔ⟩ := hp
  intro β hβ0 hβ1 η B T hB A hA
  have hr0 : 0 < min p.m p.n := by omega
  set R : ℝ := ((min p.m p.n - 1 : ℕ) : ℝ) with hRdef
  have hR1 : 1 ≤ R := by
    rw [hRdef]
    exact_mod_cast (show 1 ≤ min p.m p.n - 1 by omega)
  have hR0 : 0 < R := by linarith
  set c := 3 * p.ε / R with hcdef
  have hc : 0 < c := by positivity
  have hRc : R * c = 3 * p.ε := by rw [hcdef]; field_simp
  set w := 6 * p.ε / p.L with hwdef
  have hw : 0 < w := by positivity
  set D := p.Δ / (3 * p.ε) with hDdef
  set ℓ := p.L / 2 with hℓdef
  have hℓ : 0 < ℓ := by positivity
  set φ := valleyShape hw D with hφ
  have hDw4 : p.Δ / (4 * p.ε) ≤ D - w := by
    rw [hDdef, hwdef]
    have h1 : p.Δ / (3 * p.ε) - p.Δ / (4 * p.ε) = p.Δ / (12 * p.ε) := by field_simp; ring
    have h2 : 6 * p.ε / p.L ≤ p.Δ / (12 * p.ε) := by
      rw [div_le_div_iff₀ hL (by positivity)]
      nlinarith
    linarith
  have hΔpos : 0 < p.Δ := by
    by_contra h
    push Not at h
    nlinarith [sq_pos_of_pos hε, mul_nonneg hL.le (show 0 ≤ -p.Δ by linarith)]
  have hDw : 0 < D - w := lt_of_lt_of_le (by positivity) hDw4
  refine ⟨objective ℓ c φ p.x0,
    LongTails.Proofs.SeparationSuccess.gaussianOracle (sample ℓ c p.s φ p.x0),
    witness_admissible p hr hL hΔ hs hε hRdef rfl hw rfl rfl, ?_⟩
  intro hsucc
  have hA' : FollowsScheduledMomentum (matrixDirection false) β η B T p.x0 A := hA
  have hdir : Measurable (matrixDirection false : Space p.m p.n → Space p.m p.n) := measurable_id
  have hflat_int : ∀ t, Integrable (fun ξ => R * |c * valleySlope w D (scalarState (min p.m p.n) false ℓ c p.s β η φ B ξ t).1.2|) stdStream := by
    intro t
    have he : (fun ξ => R * |c * valleySlope w D (scalarState (min p.m p.n) false ℓ c p.s β η φ B ξ t).1.2|) =
        fun _ => R * |c * valleySlope w D (scalarState (min p.m p.n) false ℓ c p.s β η φ B 0 t).1.2| := by
      funext ξ
      rw [(sgd_flat_indep _ ℓ c p.s β η φ B ξ 0 t).1]
    rw [he]
    exact integrable_const _
  have hstiff_int : ∀ t, Integrable (fun ξ => |ℓ * (scalarState (min p.m p.n) false ℓ c p.s β η φ B ξ t).1.1|) stdStream := by
    intro t
    have he : (fun ξ => |ℓ * (scalarState (min p.m p.n) false ℓ c p.s β η φ B ξ t).1.1|) = fun ξ => ℓ * |(scalarState (min p.m p.n) false ℓ c p.s β η φ B ξ t).1.1| := by
      funext ξ
      rw [abs_mul, abs_of_pos hℓ]
    rw [he]
    exact (stiff_abs_integral _ ℓ c p.s β η φ B t).1.const_mul ℓ
  have hi : ∀ t, Integrable (fun ξ => nuclearNorm (gradient (objective ℓ c φ p.x0)
      (sampledMomentum (matrixDirection false) β η B p.x0 (sample ℓ c p.s φ p.x0) ξ t).1))
      stdStream := by
    intro t
    have he := funext fun ξ => nuclear_momentum hr0 false ℓ c p.s β η φ p.x0 hB ξ t
    rw [he]
    exact (hstiff_int t).add (hflat_int t)
  have hsum := success_sum_momentum (measurable_sample ℓ c p.s φ p.x0) hdir hA' hi hsucc
  simp_rw [nuclear_momentum hr0 false ℓ c p.s β η φ p.x0 hB] at hsum
  set V0 := ∑ u ∈ Finset.range T, |(scalarState (min p.m p.n) false ℓ c p.s β η φ B 0 (u + 1)).1.2 - (scalarState (min p.m p.n) false ℓ c p.s β η φ B 0 u).1.2| with hV0
  have hVconst : (fun ξ => ∑ u ∈ Finset.range T, |(scalarState (min p.m p.n) false ℓ c p.s β η φ B ξ (u + 1)).1.2 - (scalarState (min p.m p.n) false ℓ c p.s β η φ B ξ u).1.2|) =
      fun _ => V0 := by
    funext ξ
    apply Finset.sum_congr rfl
    intro u _
    rw [(sgd_flat_indep _ ℓ c p.s β η φ B ξ 0 (u + 1)).1, (sgd_flat_indep _ ℓ c p.s β η φ B ξ 0 u).1]
  have hmain := travel_bound hRc hc.le hR0.le hw hDw hε.le (fun ξ t => (scalarState (min p.m p.n) false ℓ c p.s β η φ B ξ t).1.1)
    (fun ξ t => (scalarState (min p.m p.n) false ℓ c p.s β η φ B ξ t).1.2) (fun ξ => rfl) hstiff_int hflat_int
    (by rw [hVconst]; exact integrable_const _) hsum
  rw [hVconst, integral_const, probReal_univ, one_smul] at hmain
  set H := ∑ u ∈ Finset.range T, |η u| with hH
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hVle : V0 ≤ c * H := by
    rw [hV0, hH, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u _
    rw [sgd_flat_step, abs_neg, abs_mul, mul_comm c]
    exact mul_le_mul_of_nonneg_left
      (flat_momentum_le _ false η φ B 0 hc.le hβ0 hβ1.le (u + 1)) (abs_nonneg _)
  set K := ℓ * (4 / 9 * ((1 - β) * p.s / Real.sqrt B)) with hK
  have hsqB : 0 < Real.sqrt B := Real.sqrt_pos.mpr (by exact_mod_cast hB)
  have hK0 : 0 ≤ K := by
    have : 0 ≤ 1 - β := by linarith
    positivity
  have hstiff : K * H ≤ ∑ t ∈ Finset.range (T + 1), ∫ ξ, |ℓ * (scalarState (min p.m p.n) false ℓ c p.s β η φ B ξ t).1.1| ∂stdStream := by
    rw [Finset.sum_range_succ', hH, Finset.mul_sum]
    have h0 : 0 ≤ ∫ ξ, |ℓ * (scalarState (min p.m p.n) false ℓ c p.s β η φ B ξ 0).1.1| ∂stdStream := integral_nonneg fun _ => abs_nonneg _
    have hle : ∑ u ∈ Finset.range T, K * |η u| ≤
        ∑ u ∈ Finset.range T, ∫ ξ, |ℓ * (scalarState (min p.m p.n) false ℓ c p.s β η φ B ξ (u + 1)).1.1| ∂stdStream := by
      apply Finset.sum_le_sum
      intro u _
      have he : (fun ξ => |ℓ * (scalarState (min p.m p.n) false ℓ c p.s β η φ B ξ (u + 1)).1.1|) = fun ξ => ℓ * |(scalarState (min p.m p.n) false ℓ c p.s β η φ B ξ (u + 1)).1.1| := by
        funext ξ
        rw [abs_mul, abs_of_pos hℓ]
      rw [he, integral_const_mul, hK]
      have h := stiff_step_lower (min p.m p.n) ℓ c p.s β η φ hB u
      have e : 4 / 9 * (|η u| * ((1 - β) * p.s) / Real.sqrt B) =
          4 / 9 * ((1 - β) * p.s / Real.sqrt B) * |η u| := by ring
      rw [e] at h
      calc ℓ * (4 / 9 * ((1 - β) * p.s / Real.sqrt B)) * |η u| =
          ℓ * (4 / 9 * ((1 - β) * p.s / Real.sqrt B) * |η u|) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h hℓ.le
    linarith
  set Q := 3 * p.ε / 2 * (T + 1) * c / (D - w) with hQ
  have hQH : 3 * p.ε / 2 * (T + 1) * V0 / (D - w) ≤ Q * H := by
    rw [hQ]
    have e : 3 * p.ε / 2 * (T + 1) * c / (D - w) * H =
        3 * p.ε / 2 * (T + 1) * (c * H) / (D - w) := by ring
    rw [e]
    apply div_le_div_of_nonneg_right _ hDw.le
    exact mul_le_mul_of_nonneg_left hVle (by positivity)
  have hpos : 0 < ((T : ℝ) + 1) * p.ε / 2 := by positivity
  have hKQ : K ≤ Q := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul_of_nonneg_right h.le hH0]
  have h1 : K * (D - w) ≤ 3 * p.ε / 2 * (T + 1) * c := by
    rw [hQ, le_div_iff₀ hDw] at hKQ
    exact hKQ
  have h2 : K * (p.Δ / (4 * p.ε)) ≤ 3 * p.ε / 2 * (T + 1) * c :=
    (mul_le_mul_of_nonneg_left hDw4 hK0).trans h1
  have hsB : Real.sqrt B ≤ B := by
    have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
    calc Real.sqrt B ≤ Real.sqrt ((B : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = B := Real.sqrt_sq (by linarith)
  have hsqB' : Real.sqrt B ≠ 0 := hsqB.ne'
  have e1 : (1 - β) * R * p.L * p.Δ * p.s =
      18 * p.ε * R * (K * (p.Δ / (4 * p.ε))) * Real.sqrt B := by
    rw [hK, hℓdef]
    field_simp
    ring
  have e2 : 18 * p.ε * R * (3 * p.ε / 2 * (T + 1) * c) = 81 * p.ε ^ 3 * (T + 1) := by
    rw [show 18 * p.ε * R * (3 * p.ε / 2 * (T + 1) * c) = 27 * p.ε ^ 2 * (T + 1) * (R * c) by ring,
      hRc]
    ring
  have h3 : 18 * p.ε * R * (K * (p.Δ / (4 * p.ε))) ≤ 81 * p.ε ^ 3 * (T + 1) := by
    rw [← e2]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [e1]
  have h4 : 0 ≤ 18 * p.ε * R * (K * (p.Δ / (4 * p.ε))) := by positivity
  calc 18 * p.ε * R * (K * (p.Δ / (4 * p.ε))) * Real.sqrt B ≤
      81 * p.ε ^ 3 * (T + 1) * Real.sqrt B := mul_le_mul_of_nonneg_right h3 hsqB.le
    _ ≤ 81 * p.ε ^ 3 * (T + 1) * B := mul_le_mul_of_nonneg_left hsB (by positivity)
    _ = 81 * p.ε ^ 3 * (B * (T + 1)) := by ring

end LongTails.Proofs.ScheduledMomentumSgd
