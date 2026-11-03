import LongTails.Proofs.MomentumDirectionExecution
import LongTails.Proofs.BatchedMuonRate

namespace LongTails.Proofs.MomentumMuonRate

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace
open LongTails.Algorithms.MatrixPolar LongTails.Proofs.MomentumDirectionExecution
open LongTails.Proofs.MuonProcess

lemma nuclearNorm_smul_le {m n : ℕ} {κ : ℝ} (hκ : 0 ≤ κ) (X : Space m n) :
    nuclearNorm (κ • X) ≤ κ * nuclearNorm X := by
  unfold nuclearNorm
  rw [map_smul, ContinuousLinearMap.smul_comp]
  have h := ContinuousLinearMap.opNorm_smul_le κ
    ((innerSL ℝ X).comp (operatorEquiv m n).symm.toContinuousLinearMap)
  rwa [Real.norm_of_nonneg hκ] at h

lemma polar_scaled_alignment {m n : ℕ} (G M : Space m n) {κ : ℝ} (hκ : 0 ≤ κ) :
    nuclearNorm G - ⟪G, polar M⟫ ≤ 2 * nuclearNorm (κ • M - G) := by
  have hpair : ⟪κ • M, polar M⟫ = κ * nuclearNorm M := by
    rw [inner_smul_left, polar_pairing_eq_nuclear]
    simp
  have hab : |⟪κ • M - G, polar M⟫| ≤ nuclearNorm (κ • M - G) :=
    (inner_le_nuclear_mul_spectral _ (polar M)).trans
      (by simpa using mul_le_mul_of_nonneg_left (polar_mem M) (nuclearNorm_nonneg (κ • M - G)))
  have hsplit : ⟪G, polar M⟫ = ⟪κ • M, polar M⟫ - ⟪κ • M - G, polar M⟫ := by
    rw [inner_sub_left]; ring
  have ht := nuclearNorm_add_le (κ • M) (G - κ • M)
  rw [add_sub_cancel] at ht
  have hs := nuclearNorm_smul_le hκ M
  have he : nuclearNorm (G - κ • M) = nuclearNorm (κ • M - G) := by
    rw [← neg_sub (κ • M) G, nuclearNorm_neg]
  rw [he] at ht
  rw [hsplit, hpair]
  linarith [(abs_le.mp hab).1, (abs_le.mp hab).2]

lemma scaled_step_bound {m n : ℕ} {f : Space m n → ℝ} {L η : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (x M : Space m n) {κ : ℝ} (hκ : 0 ≤ κ) :
    η * nuclearNorm (gradient f x) ≤
      f x - f (x - η • polar M) + 2 * η * nuclearNorm (κ • M - gradient f x) + L / 2 * η ^ 2 := by
  have hd := MatrixSmooth.polar_descent hgrad hlip hL hη x M
  have ha := polar_scaled_alignment (gradient f x) M hκ
  nlinarith

lemma lag_closed (β : ℝ) (t : ℕ) :
    (1 - β) ^ 2 * ∑ j ∈ Finset.range (t + 1), (j : ℝ) * β ^ j =
      β - (t + 1) * β ^ (t + 1) + t * β ^ (t + 2) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

lemma lag_bound {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (t : ℕ) :
    (1 - β) ^ 2 * ∑ j ∈ Finset.range (t + 1), (j : ℝ) * β ^ j ≤ β * (1 - β ^ (t + 1)) := by
  rw [lag_closed]
  have hp : 0 ≤ β ^ (t + 1) := pow_nonneg hβ0 _
  have h : (t + 1 : ℝ) * β ^ (t + 2) ≤ (t + 1) * β ^ (t + 1) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [pow_succ]
    nlinarith
  have he : β ^ (t + 2) = β * β ^ (t + 1) := by ring
  nlinarith

lemma weight_sum (β : ℝ) (t : ℕ) :
    ∑ j ∈ Finset.range (t + 1), (1 - β) * β ^ j = 1 - β ^ (t + 1) := by
  rw [← Finset.mul_sum, mul_comm, geom_sum_mul_neg]

lemma weight_square_sum {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (t : ℕ) :
    ∑ j ∈ Finset.range (t + 1), ((1 - β) * β ^ j) ^ 2 ≤ (1 - β) * (1 - β ^ (t + 1)) := by
  rw [← weight_sum β t, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hp : 0 ≤ β ^ j := pow_nonneg hβ0 j
  have hp1 : β ^ j ≤ 1 := pow_le_one₀ hβ0 hβ1
  have h1 : 0 ≤ 1 - β := by linarith
  nlinarith [mul_nonneg h1 hp, mul_le_mul_of_nonneg_left hp1 (mul_nonneg h1 hp)]

lemma pow_le_inv_one_add {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (k : ℕ) :
    β ^ k * (1 + k * (1 - β)) ≤ 1 := by
  have hb : (1 + k * (1 - β)) ≤ (1 + (1 - β)) ^ k :=
    one_add_mul_le_pow (by linarith) k
  have hq : β * (1 + (1 - β)) ≤ 1 := by nlinarith [sq_nonneg (1 - β)]
  have hq0 : 0 ≤ β * (1 + (1 - β)) := by nlinarith
  calc β ^ k * (1 + k * (1 - β)) ≤ β ^ k * (1 + (1 - β)) ^ k :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg hβ0 k)
    _ = (β * (1 + (1 - β))) ^ k := by rw [mul_pow]
    _ ≤ 1 := pow_le_one₀ hq0 hq

lemma ratio_bound {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (t : ℕ) :
    (1 - β) / (1 - β ^ (t + 1)) ≤ (1 - β) + 1 / (t + 1) := by
  have hδ : 0 < 1 - β := by linarith
  have hk := pow_le_inv_one_add hβ0 hβ1.le (t + 1)
  have hpos : 0 < 1 - β ^ (t + 1) := by
    have : β ^ (t + 1) < 1 := pow_lt_one₀ hβ0 hβ1 (Nat.succ_ne_zero t)
    linarith
  rw [div_le_iff₀ hpos]
  push_cast at hk
  have ht : (0 : ℝ) < t + 1 := by positivity
  have hkey : (1 - β) * (t + 1) ≤ ((1 - β) * (t + 1) + 1) * (1 - β ^ (t + 1)) := by
    nlinarith
  calc 1 - β = (1 - β) * (t + 1) / (t + 1) := by field_simp
    _ ≤ ((1 - β) * (t + 1) + 1) * (1 - β ^ (t + 1)) / (t + 1) :=
        div_le_div_of_nonneg_right hkey ht.le
    _ = ((1 - β) + 1 / (t + 1)) * (1 - β ^ (t + 1)) := by field_simp

lemma inv_sqrt_sum (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), 1 / Real.sqrt (t + 1) ≤ 2 * Real.sqrt (T + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ]
      push_cast
      have ha : 0 < Real.sqrt ((T : ℝ) + 1 + 1) := Real.sqrt_pos.mpr (by positivity)
      have hb : Real.sqrt ((T : ℝ) + 1) ≤ Real.sqrt ((T : ℝ) + 1 + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      have hs : Real.sqrt ((T : ℝ) + 1 + 1) ^ 2 = (T : ℝ) + 1 + 1 := Real.sq_sqrt (by positivity)
      have hs' : Real.sqrt ((T : ℝ) + 1) ^ 2 = (T : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have hkey : 1 / Real.sqrt ((T : ℝ) + 1 + 1) ≤
          2 * Real.sqrt ((T : ℝ) + 1 + 1) - 2 * Real.sqrt ((T : ℝ) + 1) := by
        rw [div_le_iff₀ ha]
        nlinarith [Real.sqrt_nonneg ((T : ℝ) + 1)]
      linarith

noncomputable def batchAt {m n : ℕ} {Ω : Type*} (direction : Space m n → Space m n) (β η : ℝ)
    (B : ℕ) (x0 : Space m n) (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω) (u : ℕ) : Space m n :=
  (1 / (B : ℝ)) • ∑ j ∈ Finset.range B,
    g (sampledMomentum direction β η B x0 g ξ u).1 (ξ (B * u + j))

lemma momentum_closed {m n : ℕ} {Ω : Type*} (direction : Space m n → Space m n) (β η : ℝ)
    (B : ℕ) (x0 : Space m n) (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω) (t : ℕ) :
    (sampledMomentum direction β η B x0 g ξ (t + 1)).2 =
      ∑ u ∈ Finset.range (t + 1),
        ((1 - β) * β ^ (t - u)) • batchAt direction β η B x0 g ξ u := by
  induction t with
  | zero => simp [sampledMomentum, batchAt]
  | succ t ih =>
      change β • (sampledMomentum direction β η B x0 g ξ (t + 1)).2 +
        (1 - β) • batchAt direction β η B x0 g ξ (t + 1) = _
      rw [ih, Finset.smul_sum, Finset.sum_range_succ (fun u =>
        ((1 - β) * β ^ (t + 1 - u)) • batchAt direction β η B x0 g ξ u) (t + 1)]
      congr 1
      · apply Finset.sum_congr rfl
        intro u hu
        have hu' : u ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
        rw [smul_smul, show t + 1 - u = (t - u) + 1 by omega, pow_succ]
        ring_nf
      · simp

lemma point_succ {m n : ℕ} {Ω : Type*} (direction : Space m n → Space m n) (β η : ℝ)
    (B : ℕ) (x0 : Space m n) (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω) (t : ℕ) :
    (sampledMomentum direction β η B x0 g ξ (t + 1)).1 =
      (sampledMomentum direction β η B x0 g ξ t).1 -
        η • direction (sampledMomentum direction β η B x0 g ξ (t + 1)).2 := rfl

lemma point_distance {m n : ℕ} {Ω : Type*} {β η : ℝ} (hη : 0 ≤ η)
    (B : ℕ) (x0 : Space m n) (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω) (u k : ℕ) :
    spectralNorm ((sampledMomentum polar β η B x0 g ξ u).1 -
      (sampledMomentum polar β η B x0 g ξ (u + k)).1) ≤ η * k := by
  induction k with
  | zero => simp [spectralNorm]
  | succ k ih =>
      rw [show u + (k + 1) = (u + k) + 1 by omega, point_succ]
      set P := (sampledMomentum polar β η B x0 g ξ (u + k + 1)).2
      have hp : spectralNorm (η • polar P) ≤ η := by
        rw [MatrixSmooth.spectralNorm_smul, abs_of_nonneg hη]
        have := polar_mem P
        simp only [spectralBall, Set.mem_ofPred_eq] at this
        nlinarith
      have he : (sampledMomentum polar β η B x0 g ξ u).1 -
          ((sampledMomentum polar β η B x0 g ξ (u + k)).1 - η • polar P) =
          ((sampledMomentum polar β η B x0 g ξ u).1 -
            (sampledMomentum polar β η B x0 g ξ (u + k)).1) + η • polar P := by abel
      rw [he]
      have htri : spectralNorm (((sampledMomentum polar β η B x0 g ξ u).1 -
            (sampledMomentum polar β η B x0 g ξ (u + k)).1) + η • polar P) ≤
          spectralNorm ((sampledMomentum polar β η B x0 g ξ u).1 -
            (sampledMomentum polar β η B x0 g ξ (u + k)).1) + spectralNorm (η • polar P) := by
        unfold spectralNorm
        rw [map_add]
        exact norm_add_le _ _
      push_cast
      linarith

lemma adapted_sampledMomentum {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {direction : Space m n → Space m n} (hdir : Measurable direction) (β η : ℝ) (B : ℕ)
    (x0 : Space m n) {g : Space m n → Ω → Space m n} (hg : Measurable (Function.uncurry g))
    (t : ℕ) :
    Measurable[past (B * t)] (fun ξ => sampledMomentum direction β η B x0 g ξ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hle : B * t ≤ B * (t + 1) := Nat.mul_le_mul_left B (Nat.le_succ t)
      have ih' := ih.mono (past_mono hle) le_rfl
      have hsum : Measurable[past (B * (t + 1))] (fun ξ : ℕ → Ω =>
          ∑ j ∈ Finset.range B, g (sampledMomentum direction β η B x0 g ξ t).1
            (ξ (B * t + j))) := by
        apply Finset.measurable_sum
        intro j hj
        have hj' : B * t + j < B * (t + 1) := by
          have := Finset.mem_range.mp hj
          rw [Nat.mul_succ]
          omega
        exact hg.comp (ih'.fst.prodMk (measurable_eval_past hj'))
      have hM : Measurable[past (B * (t + 1))] (fun ξ : ℕ → Ω =>
          β • (sampledMomentum direction β η B x0 g ξ t).2 + (1 - β) • ((1 / (B : ℝ)) •
            ∑ j ∈ Finset.range B, g (sampledMomentum direction β η B x0 g ξ t).1
              (ξ (B * t + j)))) :=
        (ih'.snd.const_smul β).add ((hsum.const_smul (1 / (B : ℝ))).const_smul (1 - β))
      exact (ih'.fst.sub ((hdir.comp hM).const_smul η)).prodMk hM

lemma sum_range_mul {E : Type*} [AddCommMonoid E] (F : ℕ → E) (B t : ℕ) :
    ∑ k ∈ Finset.range (B * t), F k =
      ∑ u ∈ Finset.range t, ∑ j ∈ Finset.range B, F (B * u + j) := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma nuclearNorm_sum_le {m n : ℕ} {ι : Type*} (S : Finset ι) (F : ι → Space m n) :
    nuclearNorm (∑ i ∈ S, F i) ≤ ∑ i ∈ S, nuclearNorm (F i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      have h := nuclearNorm_smul_le (le_refl (0 : ℝ)) (0 : Space m n)
      rwa [zero_smul, zero_mul] at h
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (nuclearNorm_add_le _ _).trans (by linarith)

lemma weighted_noise_bound {m n : ℕ} {f : Space m n → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    (β η : ℝ) {B : ℕ} (hB : 0 < B) (x0 : Space m n) (t : ℕ) (w : ℕ → ℝ) :
    Integrable (fun ξ => nuclearNorm (∑ u ∈ Finset.range (t + 1), w u •
      (batchAt polar β η B x0 model.sample ξ u -
        gradient f (sampledMomentum polar β η B x0 model.sample ξ u).1))) P ∧
    (∫ ξ, nuclearNorm (∑ u ∈ Finset.range (t + 1), w u •
      (batchAt polar β η B x0 model.sample ξ u -
        gradient f (sampledMomentum polar β η B x0 model.sample ξ u).1)) ∂P) ≤
      Real.sqrt ((∑ u ∈ Finset.range (t + 1), w u ^ 2) / B) * s := by
  let X := fun u (ξ : ℕ → model.Ω) => (sampledMomentum polar β η B x0 model.sample ξ u).1
  have hXa (u : ℕ) : Measurable[past (B * u)] (X u) :=
    (adapted_sampledMomentum (measurable_polar m n) β η B x0 model.jointly_measurable u).fst
  let Q := fun k (ξ : ℕ → model.Ω) => X (k / B) ξ
  have hQ (k : ℕ) : Measurable[past k] (Q k) :=
    (hXa (k / B)).mono (past_mono (Nat.mul_div_le k B)) le_rfl
  have hh := model_weighted_noise_bounds model h hQ 0 (B * (t + 1)) (fun k => w (k / B) / B)
  have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hdiv (u j : ℕ) (hj : j < B) : (B * u + j) / B = u := by
    rw [Nat.mul_add_div hB, Nat.div_eq_of_lt hj, Nat.add_zero]
  have hV : ∀ ξ, (∑ k ∈ Finset.range (B * (t + 1)), (w (k / B) / B) •
      (model.sample (Q (0 + k) ξ) (ξ (0 + k)) - gradient f (Q (0 + k) ξ))) =
      ∑ u ∈ Finset.range (t + 1), w u •
        (batchAt polar β η B x0 model.sample ξ u - gradient f (X u ξ)) := by
    intro ξ
    rw [sum_range_mul]
    apply Finset.sum_congr rfl
    intro u _
    have hin : ∀ j ∈ Finset.range B, (w ((B * u + j) / B) / B) •
        (model.sample (Q (0 + (B * u + j)) ξ) (ξ (0 + (B * u + j))) -
          gradient f (Q (0 + (B * u + j)) ξ)) =
        (w u / B) • (model.sample (X u ξ) (ξ (B * u + j)) - gradient f (X u ξ)) := by
      intro j hj
      have hd := hdiv u j (Finset.mem_range.mp hj)
      simp only [Q, Nat.zero_add, hd]
    rw [Finset.sum_congr rfl hin, ← Finset.smul_sum, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, batchAt]
    have e1 : (w u / B) • (B • gradient f (X u ξ)) = w u • gradient f (X u ξ) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1
      field_simp
    rw [smul_sub, smul_sub, e1, smul_smul]
    congr 2
    ring
  have hW : (∑ k ∈ Finset.range (B * (t + 1)), (w (k / B) / B) ^ 2) =
      (∑ u ∈ Finset.range (t + 1), w u ^ 2) / B := by
    rw [sum_range_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    have hin : ∀ j ∈ Finset.range B, (w ((B * u + j) / B) / B) ^ 2 = (w u / B) ^ 2 := by
      intro j hj
      rw [hdiv u j (Finset.mem_range.mp hj)]
    rw [Finset.sum_congr rfl hin, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  simp only [hV, hW] at hh
  obtain ⟨hmem, hsq, _, _⟩ := hh
  let V := fun ξ => nuclearNorm (∑ u ∈ Finset.range (t + 1), w u •
    (batchAt polar β η B x0 model.sample ξ u - gradient f (X u ξ)))
  have hXm (u : ℕ) : Measurable (X u) := (hXa u).mono (past_le _) le_rfl
  have hbm (u : ℕ) : Measurable (fun ξ => batchAt polar β η B x0 model.sample ξ u) := by
    unfold batchAt
    exact (Finset.measurable_sum (Finset.range B) (fun j _ => model.jointly_measurable.comp
      ((hXm u).prodMk (measurable_pi_apply (B * u + j))))).const_smul (1 / (B : ℝ))
  have hVm : Measurable V :=
    (MatrixCovariance.continuous_nuclearNorm m n).measurable.comp
      (Finset.measurable_sum _ (fun u _ => ((hbm u).sub
        ((measurable_gradient f).comp (hXm u))).const_smul (w u)))
  obtain ⟨hVi, hJ⟩ := LongTails.Proofs.BatchedMuonRate.integral_square_le P hVm
    (fun _ => nuclearNorm_nonneg _) hmem.integrable_sq
  refine ⟨hVi, ?_⟩
  have hW0 : 0 ≤ (∑ u ∈ Finset.range (t + 1), w u ^ 2) / B :=
    div_nonneg (Finset.sum_nonneg (fun u _ => sq_nonneg _)) (Nat.cast_nonneg _)
  have hI0 : 0 ≤ ∫ ξ, V ξ ∂P := integral_nonneg fun _ => nuclearNorm_nonneg _
  have hfin : (∫ ξ, V ξ ∂P) ^ 2 ≤ (Real.sqrt ((∑ u ∈ Finset.range (t + 1), w u ^ 2) / B) * s) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hW0]
    exact hJ.trans hsq
  exact (pow_le_pow_iff_left₀ hI0 (mul_nonneg (Real.sqrt_nonneg _) hs) two_ne_zero).mp hfin

lemma reflect_weight_sum (β : ℝ) (t : ℕ) :
    ∑ u ∈ Finset.range (t + 1), (1 - β) * β ^ (t - u) = 1 - β ^ (t + 1) := by
  rw [← weight_sum β t]
  have h := Finset.sum_range_reflect (fun j => (1 - β) * β ^ j) (t + 1)
  simpa only [Nat.add_sub_cancel] using h

lemma reflect_lag_sum (β : ℝ) (t : ℕ) :
    ∑ u ∈ Finset.range (t + 1), (1 - β) * β ^ (t - u) * ((t - u : ℕ) : ℝ) =
      (1 - β) * ∑ j ∈ Finset.range (t + 1), (j : ℝ) * β ^ j := by
  rw [Finset.mul_sum]
  have h := Finset.sum_range_reflect (fun j => (1 - β) * ((j : ℝ) * β ^ j)) (t + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro u _
  ring

lemma reflect_square_sum {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (t : ℕ) :
    ∑ u ∈ Finset.range (t + 1), ((1 - β) * β ^ (t - u)) ^ 2 ≤ (1 - β) * (1 - β ^ (t + 1)) := by
  have h := Finset.sum_range_reflect (fun j => ((1 - β) * β ^ j) ^ 2) (t + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [h]
  exact weight_square_sum hβ0 hβ1 t

lemma momentum_step {m n : ℕ} {Ω : Type*} {f : Space m n → ℝ} {L η β : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (B : ℕ) (x0 : Space m n) (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω) (t : ℕ) :
    η * nuclearNorm (gradient f (sampledMomentum polar β η B x0 g ξ t).1) ≤
      f (sampledMomentum polar β η B x0 g ξ t).1 - f (sampledMomentum polar β η B x0 g ξ (t + 1)).1 +
        2 * η * (nuclearNorm (∑ u ∈ Finset.range (t + 1),
            ((1 - β) * β ^ (t - u) / (1 - β ^ (t + 1))) •
              (batchAt polar β η B x0 g ξ u - gradient f (sampledMomentum polar β η B x0 g ξ u).1)) +
          L * η * (β / (1 - β))) + L / 2 * η ^ 2 := by
  set X := fun u => (sampledMomentum polar β η B x0 g ξ u).1 with hX
  set D := 1 - β ^ (t + 1) with hD
  have hDpos : 0 < D := by
    have : β ^ (t + 1) < 1 := pow_lt_one₀ hβ0 hβ1 (Nat.succ_ne_zero t)
    rw [hD]; linarith
  set κ := 1 / D with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set w := fun u => (1 - β) * β ^ (t - u) / D with hw
  have hw0 (u : ℕ) : 0 ≤ w u := by
    have : 0 ≤ 1 - β := by linarith
    positivity
  have hws : ∑ u ∈ Finset.range (t + 1), w u = 1 := by
    rw [hw]
    simp only
    rw [← Finset.sum_div, reflect_weight_sum, ← hD, div_self hDpos.ne']
  have hstep := scaled_step_bound hL hη hgrad hlip (X t)
    (sampledMomentum polar β η B x0 g ξ (t + 1)).2 hκ0
  have hX1 : X t - η • polar (sampledMomentum polar β η B x0 g ξ (t + 1)).2 = X (t + 1) := by
    rw [hX]; exact (point_succ polar β η B x0 g ξ t).symm
  rw [hX1] at hstep
  have hκM : κ • (sampledMomentum polar β η B x0 g ξ (t + 1)).2 =
      ∑ u ∈ Finset.range (t + 1), w u • batchAt polar β η B x0 g ξ u := by
    rw [momentum_closed, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [smul_smul, hw, hκ]
    congr 1
    ring
  have hdecomp : κ • (sampledMomentum polar β η B x0 g ξ (t + 1)).2 - gradient f (X t) =
      (∑ u ∈ Finset.range (t + 1), w u • (batchAt polar β η B x0 g ξ u - gradient f (X u))) +
        ∑ u ∈ Finset.range (t + 1), w u • (gradient f (X u) - gradient f (X t)) := by
    rw [hκM, ← Finset.sum_add_distrib]
    have hg : gradient f (X t) = ∑ u ∈ Finset.range (t + 1), w u • gradient f (X t) := by
      rw [← Finset.sum_smul, hws, one_smul]
    conv_lhs => rw [hg]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [← smul_add, ← smul_sub]
    congr 1
    abel
  have hdrift : nuclearNorm (∑ u ∈ Finset.range (t + 1), w u • (gradient f (X u) - gradient f (X t))) ≤
      L * η * (β / (1 - β)) := by
    refine (nuclearNorm_sum_le _ _).trans ?_
    have hterm : ∀ u ∈ Finset.range (t + 1),
        nuclearNorm (w u • (gradient f (X u) - gradient f (X t))) ≤
          L * η * ((1 - β) * β ^ (t - u) * ((t - u : ℕ) : ℝ) / D) := by
      intro u hu
      have hut : u ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)
      refine (nuclearNorm_smul_le (hw0 u) _).trans ?_
      have hdist := point_distance (β := β) hη B x0 g ξ u (t - u)
      rw [show u + (t - u) = t by omega] at hdist
      have hl := hlip (X u) (X t)
      have h1 : nuclearNorm (gradient f (X u) - gradient f (X t)) ≤ L * (η * ((t - u : ℕ) : ℝ)) :=
        hl.trans (mul_le_mul_of_nonneg_left hdist hL)
      calc w u * nuclearNorm (gradient f (X u) - gradient f (X t)) ≤
            w u * (L * (η * ((t - u : ℕ) : ℝ))) := mul_le_mul_of_nonneg_left h1 (hw0 u)
        _ = _ := by rw [hw]; ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, ← Finset.sum_div, reflect_lag_sum]
    have hlb := lag_bound hβ0 hβ1.le t
    have hδ : 0 < 1 - β := by linarith
    have hLη : 0 ≤ L * η := mul_nonneg hL hη
    apply mul_le_mul_of_nonneg_left _ hLη
    rw [div_le_div_iff₀ hDpos hδ]
    nlinarith
  have hsplit := nuclearNorm_add_le
    (∑ u ∈ Finset.range (t + 1), w u • (batchAt polar β η B x0 g ξ u - gradient f (X u)))
    (∑ u ∈ Finset.range (t + 1), w u • (gradient f (X u) - gradient f (X t)))
  rw [← hdecomp] at hsplit
  have hη2 : 0 ≤ 2 * η := by linarith
  nlinarith [mul_le_mul_of_nonneg_left (hsplit.trans (add_le_add_right hdrift _)) hη2]

lemma noise_weight_root {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {B : ℕ} (hB : 0 < B) (t : ℕ) :
    Real.sqrt ((∑ u ∈ Finset.range (t + 1), ((1 - β) * β ^ (t - u) / (1 - β ^ (t + 1))) ^ 2) / B) ≤
      (Real.sqrt (1 - β) + 1 / Real.sqrt (t + 1)) / Real.sqrt B := by
  have hDpos : 0 < 1 - β ^ (t + 1) := by
    have : β ^ (t + 1) < 1 := pow_lt_one₀ hβ0 hβ1 (Nat.succ_ne_zero t)
    linarith
  have hsq : (∑ u ∈ Finset.range (t + 1), ((1 - β) * β ^ (t - u) / (1 - β ^ (t + 1))) ^ 2) ≤
      (1 - β) + 1 / (t + 1) := by
    have he : (∑ u ∈ Finset.range (t + 1), ((1 - β) * β ^ (t - u) / (1 - β ^ (t + 1))) ^ 2) =
        (∑ u ∈ Finset.range (t + 1), ((1 - β) * β ^ (t - u)) ^ 2) / (1 - β ^ (t + 1)) ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u _
      rw [div_pow]
    rw [he]
    have h1 := reflect_square_sum hβ0 hβ1.le t
    have h2 := ratio_bound hβ0 hβ1 t
    calc _ ≤ ((1 - β) * (1 - β ^ (t + 1))) / (1 - β ^ (t + 1)) ^ 2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = (1 - β) / (1 - β ^ (t + 1)) := by field_simp
      _ ≤ _ := h2
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  rw [Real.sqrt_div' _ hBpos.le]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have ht : (0 : ℝ) < t + 1 := by positivity
  calc _ ≤ Real.sqrt ((1 - β) + 1 / (t + 1)) := Real.sqrt_le_sqrt hsq
    _ ≤ Real.sqrt (1 - β) + Real.sqrt (1 / (t + 1)) := by
        have ha := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - β by linarith)
        have hb := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / (t + 1) by positivity)
        have hm := mul_nonneg (Real.sqrt_nonneg (1 - β)) (Real.sqrt_nonneg (1 / (t + 1)))
        have hle : (1 - β) + 1 / (t + 1) ≤
            (Real.sqrt (1 - β) + Real.sqrt (1 / (t + 1))) ^ 2 := by nlinarith
        calc Real.sqrt ((1 - β) + 1 / (t + 1)) ≤
              Real.sqrt ((Real.sqrt (1 - β) + Real.sqrt (1 / (t + 1))) ^ 2) :=
            Real.sqrt_le_sqrt hle
          _ = _ := Real.sqrt_sq (by positivity)
    _ = _ := by rw [Real.sqrt_div' _ ht.le, Real.sqrt_one]

lemma momentum_average_bound {m n : ℕ} {f : Space m n → ℝ} {L Δ s η β fmin : ℝ}
    (hL : 0 ≤ L) (hs : 0 ≤ s) (hη : 0 < η) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, nuclearNorm (gradient f x - gradient f y) ≤ L * spectralNorm (x - y))
    (hmin : ∀ x, fmin ≤ f x) (x0 : Space m n) (hgap : f x0 - fmin ≤ Δ)
    (model : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s)
    {P : Measure (ℕ → model.Ω)} [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → model.Ω) => ξ k) (model.law : Measure _) P)
    {B : ℕ} (hB : 0 < B) (T : ℕ) :
    (∀ t, Integrable (fun ξ =>
      nuclearNorm (gradient f (sampledMomentum polar β η B x0 model.sample ξ t).1)) P) ∧
    (∑ t ∈ Finset.range (T + 1), ∫ ξ,
      nuclearNorm (gradient f (sampledMomentum polar β η B x0 model.sample ξ t).1) ∂P) ≤
      Δ / η + 2 * s * ((T + 1) * Real.sqrt (1 - β) + 2 * Real.sqrt (T + 1)) / Real.sqrt B +
        (T + 1) * (2 * L * η * (β / (1 - β)) + L / 2 * η) := by
  let X := fun t (ξ : ℕ → model.Ω) => (sampledMomentum polar β η B x0 model.sample ξ t).1
  have hXm (t : ℕ) : Measurable (X t) :=
    ((adapted_sampledMomentum (measurable_polar m n) β η B x0 model.jointly_measurable t).fst).mono
      (past_le _) le_rfl
  let G := fun t ξ => nuclearNorm (gradient f (X t ξ))
  have hGm (t : ℕ) : Measurable (G t) :=
    (MatrixCovariance.continuous_nuclearNorm m n).measurable.comp
      ((measurable_gradient f).comp (hXm t))
  have hGi (t : ℕ) : Integrable (G t) P := by
    apply Integrable.of_bound (hGm t).aestronglyMeasurable
      (nuclearNorm (gradient f x0) + L * (η * t))
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (nuclearNorm_nonneg _)]
      have hd := point_distance (β := β) hη.le B x0 model.sample ξ 0 t
      rw [Nat.zero_add] at hd
      have hl := hlip (X t ξ) x0
      have hsym : spectralNorm (X t ξ - x0) = spectralNorm (x0 - X t ξ) := by
        unfold spectralNorm
        rw [← norm_neg, ← map_neg, neg_sub]
      have htri := nuclearNorm_add_le (gradient f (X t ξ) - gradient f x0) (gradient f x0)
      rw [sub_add_cancel] at htri
      have hx0 : (sampledMomentum polar β η B x0 model.sample ξ 0).1 = x0 := rfl
      rw [hx0] at hd
      change G t ξ ≤ _
      have : spectralNorm (X t ξ - x0) ≤ η * t := by rw [hsym]; exact hd
      nlinarith [mul_le_mul_of_nonneg_left this hL]
  let w := fun t u => (1 - β) * β ^ (t - u) / (1 - β ^ (t + 1))
  let V := fun t (ξ : ℕ → model.Ω) => nuclearNorm (∑ u ∈ Finset.range (t + 1), w t u •
    (batchAt polar β η B x0 model.sample ξ u - gradient f (X u ξ)))
  have hV (t : ℕ) := weighted_noise_bound hs model h β η hB x0 t (w t)
  refine ⟨hGi, ?_⟩
  have hpoint (ξ : ℕ → model.Ω) :
      η * ∑ t ∈ Finset.range (T + 1), G t ξ ≤
        Δ + 2 * η * ∑ t ∈ Finset.range (T + 1), V t ξ +
          (T + 1) * (2 * η * (L * η * (β / (1 - β))) + L / 2 * η ^ 2) := by
    have hstep (t : ℕ) : η * G t ξ ≤ f (X t ξ) - f (X (t + 1) ξ) + 2 * η * V t ξ +
        (2 * η * (L * η * (β / (1 - β))) + L / 2 * η ^ 2) := by
      have hs' := momentum_step hL hη.le hβ0 hβ1 hgrad hlip B x0 model.sample ξ t
      change η * G t ξ ≤ _ at hs'
      simp only [V, w, X] at hs' ⊢
      linarith
    have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range (T + 1)) => hstep t)
    rw [← Finset.mul_sum] at hsum
    have htel : (∑ t ∈ Finset.range (T + 1), (f (X t ξ) - f (X (t + 1) ξ) + 2 * η * V t ξ +
        (2 * η * (L * η * (β / (1 - β))) + L / 2 * η ^ 2))) = f (X 0 ξ) - f (X (T + 1) ξ) +
          2 * η * ∑ t ∈ Finset.range (T + 1), V t ξ +
            (T + 1) * (2 * η * (L * η * (β / (1 - β))) + L / 2 * η ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_range_sub' (fun t => f (X t ξ)), ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [htel] at hsum
    have h0 : X 0 ξ = x0 := rfl
    rw [h0] at hsum
    linarith [hmin (X (T + 1) ξ)]
  have hVi : Integrable (fun ξ => ∑ t ∈ Finset.range (T + 1), V t ξ) P :=
    integrable_finsetSum _ (fun t _ => (hV t).1)
  have hGs : Integrable (fun ξ => ∑ t ∈ Finset.range (T + 1), G t ξ) P :=
    integrable_finsetSum _ (fun t _ => hGi t)
  have hL1 : Integrable (fun ξ => η * ∑ t ∈ Finset.range (T + 1), G t ξ) P := hGs.const_mul η
  have hR1 : Integrable (fun ξ => Δ + 2 * η * ∑ t ∈ Finset.range (T + 1), V t ξ) P :=
    (integrable_const Δ).add (hVi.const_mul (2 * η))
  have hR2 : Integrable (fun ξ => 2 * η * ∑ t ∈ Finset.range (T + 1), V t ξ) P :=
    hVi.const_mul (2 * η)
  have hR : Integrable (fun ξ => Δ + 2 * η * ∑ t ∈ Finset.range (T + 1), V t ξ +
      (T + 1) * (2 * η * (L * η * (β / (1 - β))) + L / 2 * η ^ 2)) P :=
    hR1.add (integrable_const _)
  have hint := integral_mono hL1 hR hpoint
  rw [integral_const_mul, integral_finsetSum _ (fun t _ => hGi t), integral_add hR1
    (integrable_const _), integral_add (integrable_const Δ) hR2, integral_const_mul,
    integral_finsetSum _ (fun t _ => (hV t).1)] at hint
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hint
  have hVsum : (∑ t ∈ Finset.range (T + 1), ∫ ξ, V t ξ ∂P) ≤
      s * ((T + 1) * Real.sqrt (1 - β) + 2 * Real.sqrt (T + 1)) / Real.sqrt B := by
    have hBpos : (0 : ℝ) < Real.sqrt B := Real.sqrt_pos.mpr (by exact_mod_cast hB)
    calc _ ≤ ∑ t ∈ Finset.range (T + 1),
          s * ((Real.sqrt (1 - β) + 1 / Real.sqrt (t + 1)) / Real.sqrt B) := by
          apply Finset.sum_le_sum
          intro t _
          refine (hV t).2.trans ?_
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (noise_weight_root hβ0 hβ1 hB t) hs
      _ = s * ((T + 1) * Real.sqrt (1 - β) +
            ∑ t ∈ Finset.range (T + 1), 1 / Real.sqrt (t + 1)) / Real.sqrt B := by
          rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ hBpos.le
          apply mul_le_mul_of_nonneg_left _ hs
          linarith [inv_sqrt_sum T]
  have hfin : η * ∑ t ∈ Finset.range (T + 1), ∫ ξ, G t ξ ∂P ≤
      η * (Δ / η + 2 * s * ((T + 1) * Real.sqrt (1 - β) + 2 * Real.sqrt (T + 1)) / Real.sqrt B +
        (T + 1) * (2 * L * η * (β / (1 - β)) + L / 2 * η)) := by
    have h2 := mul_le_mul_of_nonneg_left hVsum (by positivity : (0 : ℝ) ≤ 2 * η)
    have he : η * (Δ / η + 2 * s * ((T + 1) * Real.sqrt (1 - β) + 2 * Real.sqrt (T + 1)) /
        Real.sqrt B + (T + 1) * (2 * L * η * (β / (1 - β)) + L / 2 * η)) =
        Δ + 2 * η * (s * ((T + 1) * Real.sqrt (1 - β) + 2 * Real.sqrt (T + 1)) / Real.sqrt B) +
          (T + 1) * (2 * η * (L * η * (β / (1 - β))) + L / 2 * η ^ 2) := by
      field_simp
    rw [he]
    linarith
  exact le_of_mul_le_mul_left hfin hη

lemma momentum_uniform_output {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Space m n → Ω → Space m n)
    (hg : Measurable (Function.uncurry g))
    {direction : Space m n → Space m n} (hdir : Measurable direction) {β η : ℝ} {B T : ℕ}
    {x0 : Space m n} {A : Algorithm (Space m n) (Space m n) (Space m n)}
    (hA : LongTails.Setups.MomentumSpectralSmooth.FollowsMomentum direction β η B T x0 A)
    (F : Space m n → ℝ) (hF : Measurable F)
    (hi : ∀ t, Integrable (fun ξ => F (sampledMomentum direction β η B x0 g ξ t).1)
      (P : Measure _)) :
    let O : Oracle (Space m n) (Space m n) :=
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
    let out := fun z : A.Seed × (ℕ → Ω) => execute O A (fun _ => B * (T + 1)) z.1 z.2
    Measurable out ∧ Integrable (fun z => F (out z)) ((A.law : Measure _).prod (P : Measure _)) ∧
      (∫ z, F (out z) ∂((A.law : Measure _).prod (P : Measure _))) =
        (∑ t ∈ Finset.range (T + 1),
          ∫ ξ, F (sampledMomentum direction β η B x0 g ξ t).1 ∂(P : Measure _)) / (T + 1) := by
  intro O out
  obtain ⟨draw, hdraw, hlaw, hA'⟩ := hA
  have hout : out = fun z => (sampledMomentum direction β η B x0 g z.2 (draw z.1)).1 := by
    funext z
    exact execute_eq_sampledMomentum P g draw hA' z.1 z.2
  have hX (t : ℕ) : Measurable (fun ξ : ℕ → Ω => (sampledMomentum direction β η B x0 g ξ t).1) :=
    ((adapted_sampledMomentum hdir β η B x0 hg t).fst).mono (past_le _) le_rfl
  have hjoint : Measurable (fun z : Fin (T + 1) × (ℕ → Ω) =>
      (sampledMomentum direction β η B x0 g z.2 z.1).1) :=
    measurable_from_prod_countable_right fun k => hX k
  have hm : Measurable out := by
    rw [hout]
    exact hjoint.comp ((hdraw.comp measurable_fst).prodMk measurable_snd)
  let G := fun k : Fin (T + 1) =>
    ∫ ξ, F (sampledMomentum direction β η B x0 g ξ k).1 ∂(P : Measure _)
  have hFm : Measurable (fun z : A.Seed × (ℕ → Ω) => F (out z)) := hF.comp hm
  have hbound : ∀ k : Fin (T + 1),
      ∫ ξ, ‖F (sampledMomentum direction β η B x0 g ξ k).1‖ ∂(P : Measure _) ≤
        ∑ t : Fin (T + 1), ∫ ξ, ‖F (sampledMomentum direction β η B x0 g ξ t).1‖ ∂(P : Measure _) := by
    intro k
    exact Finset.single_le_sum (f := fun t : Fin (T + 1) =>
      ∫ ξ, ‖F (sampledMomentum direction β η B x0 g ξ t).1‖ ∂(P : Measure _))
      (fun t _ => integral_nonneg fun _ => norm_nonneg _) (Finset.mem_univ k)
  have hint : Integrable (fun z => F (out z)) ((A.law : Measure _).prod (P : Measure _)) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    constructor
    · exact Filter.Eventually.of_forall fun seed => by
        simpa only [hout] using hi (draw seed)
    · apply Integrable.of_bound (C := ∑ t : Fin (T + 1),
        ∫ ξ, ‖F (sampledMomentum direction β η B x0 g ξ t).1‖ ∂(P : Measure _))
      · exact (hFm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun seed => by
          rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
          simpa only [hout] using hbound (draw seed)
  refine ⟨hm, hint, ?_⟩
  rw [integral_prod _ hint]
  have hinner : (fun seed => ∫ ξ, F (out (seed, ξ)) ∂(P : Measure _)) =
      fun seed => G (draw seed) := by
    funext seed
    simp only [hout, G]
  rw [hinner, ← integral_map hdraw.aemeasurable (measurable_of_countable G).aestronglyMeasurable,
    hlaw, OracleTemplate.MixedNoise.integral_uniform_finite, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun t => ∫ ξ, F (sampledMomentum direction β η B x0 g ξ t).1
    ∂(P : Measure _)) (T + 1)]
  push_cast
  ring

lemma tuned_budget_bound {L Δ s ε β : ℝ} (hL : 0 < L) (hΔ : 0 ≤ Δ) (hs : 0 ≤ s) (hε : 0 < ε)
    (hβ1 : β < 1) {B T : ℕ} (hB : 0 < B)
    (hBge : 128 * (1 - β) * s ^ 2 / ε ^ 2 ≤ B)
    (hTge : (32 * L * Δ / ε ^ 2 + 16) / (1 - β) ≤ T) :
    Δ / ((1 - β) * ε / (8 * L)) +
      2 * s * ((T + 1) * Real.sqrt (1 - β) + 2 * Real.sqrt (T + 1)) / Real.sqrt B +
        (T + 1) * (2 * L * ((1 - β) * ε / (8 * L)) * (β / (1 - β)) +
          L / 2 * ((1 - β) * ε / (8 * L))) ≤ (T + 1) * ε := by
  have hδ : 0 < 1 - β := by linarith
  have hT1 : (0 : ℝ) < T + 1 := by positivity
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hTδ : 32 * L * Δ / ε ^ 2 + 16 ≤ (T + 1) * (1 - β) := by
    rw [div_le_iff₀ hδ] at hTge
    nlinarith
  have h32 : 32 * L * Δ ≤ (T + 1) * (1 - β) * ε ^ 2 := by
    have hq : 32 * L * Δ / ε ^ 2 ≤ (T + 1) * (1 - β) := by linarith
    rw [div_le_iff₀ (by positivity)] at hq
    linarith
  have h8 : 16 ≤ (T + 1) * (1 - β) := by
    have : 0 ≤ 32 * L * Δ / ε ^ 2 := by positivity
    linarith
  set a := Real.sqrt B with ha
  have hapos : 0 < a := Real.sqrt_pos.mpr hBpos
  have ha2 : a ^ 2 = B := Real.sq_sqrt hBpos.le
  set d := Real.sqrt (1 - β) with hd
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d ^ 2 = 1 - β := Real.sq_sqrt hδ.le
  set q := Real.sqrt (T + 1) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr hT1
  have hq2 : q ^ 2 = T + 1 := Real.sq_sqrt hT1.le
  have hkey : 128 * (d * s) ^ 2 ≤ (ε * a) ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hBge
    rw [mul_pow, mul_pow, hd2, ha2]
    linarith
  have hkey' : 11 * (d * s) ≤ ε * a := by
    have h0 : 0 ≤ d * s := mul_nonneg hd0 hs
    nlinarith [sq_nonneg (11 * (d * s) - ε * a), mul_pos hε hapos]
  have hqd : 4 ≤ q * d := by
    have hsq : 16 ≤ (q * d) ^ 2 := by rw [mul_pow, hq2, hd2]; exact h8
    nlinarith [mul_nonneg hq0.le hd0]
  have hn1 : 2 * s * ((T + 1) * d) / a ≤ (T + 1) * (ε / 4) := by
    rw [div_le_iff₀ hapos]
    nlinarith [mul_le_mul_of_nonneg_left hkey' hT1.le, mul_nonneg hT1.le (mul_nonneg hd0 hs)]
  have hn2 : 2 * s * (2 * q) / a ≤ (T + 1) * (ε / 8) := by
    rw [div_le_iff₀ hapos, ← hq2]
    have h1 := mul_le_mul_of_nonneg_left hkey' (sq_nonneg q)
    have h2 := mul_le_mul_of_nonneg_left hqd (mul_nonneg hq0.le hs)
    nlinarith
  have hgapterm : Δ / ((1 - β) * ε / (8 * L)) ≤ (T + 1) * (ε / 4) := by
    rw [div_le_iff₀ (by positivity)]
    rw [show (T + 1 : ℝ) * (ε / 4) * ((1 - β) * ε / (8 * L)) =
      ((T + 1) * (1 - β) * ε ^ 2) / (32 * L) by field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hdrift : 2 * L * ((1 - β) * ε / (8 * L)) * (β / (1 - β)) +
      L / 2 * ((1 - β) * ε / (8 * L)) ≤ ε / 4 + ε / 16 := by
    have he : 2 * L * ((1 - β) * ε / (8 * L)) * (β / (1 - β)) +
        L / 2 * ((1 - β) * ε / (8 * L)) = ε * β / 4 + (1 - β) * ε / 16 := by
      field_simp
      ring
    rw [he]
    nlinarith
  have hsplit : 2 * s * ((T + 1) * d + 2 * q) / a =
      2 * s * ((T + 1) * d) / a + 2 * s * (2 * q) / a := by ring
  rw [hsplit]
  have h3 := mul_le_mul_of_nonneg_left hdrift hT1.le
  have h4 := mul_pos hT1 hε
  linarith

set_option maxHeartbeats 1000000 in
lemma muon_momentum_accuracy (p : LongTails.Setups.MomentumSpectralSmooth.Public)
    (hp : LongTails.Setups.MomentumSpectralSmooth.spec.valid p) (f : Space p.m p.n → ℝ)
    (O : Oracle (Space p.m p.n) (Space p.m p.n))
    (hadm : LongTails.Setups.BatchedSpectralSmooth.spec.admissible p.toBase f O) :
    let η := (1 - p.β) * p.ε / (8 * p.L)
    let B := ⌈128 * (1 - p.β) * p.s ^ 2 / p.ε ^ 2⌉₊ + 1
    let T := ⌈(32 * p.L * p.Δ / p.ε ^ 2 + 16) / (1 - p.β)⌉₊
    let A := LongTails.Algorithms.MomentumDirection.muonMomentum p.β η B T p.x0
    LongTails.Setups.BatchedSpectralSmooth.spec.successful p.toBase f
      (fun z : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => B * (T + 1)) z.1 z.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hL, hΔ, hs, hε, hβ0, hβ1⟩ := hp
  obtain ⟨hgrad, hlip, ⟨fmin, hmin, hgap⟩, model, P, hIID, rfl⟩ := hadm
  dsimp only [LongTails.Setups.MomentumSpectralSmooth.Public.toBase] at hgrad hlip hmin hgap model
  dsimp only
  set η := (1 - p.β) * p.ε / (8 * p.L) with hηdef
  set B := ⌈128 * (1 - p.β) * p.s ^ 2 / p.ε ^ 2⌉₊ + 1 with hBdef
  set T := ⌈(32 * p.L * p.Δ / p.ε ^ 2 + 16) / (1 - p.β)⌉₊ with hTdef
  have hδ : 0 < 1 - p.β := by linarith
  have hη : 0 < η := by positivity
  have hB : 0 < B := Nat.succ_pos _
  have hfol := momentum_follows polar p.β η hB T p.x0
  have hbound := momentum_average_bound hL.le hs hη hβ0 hβ1 hgrad hlip hmin p.x0 hgap model
    hIID hB T
  have hout := momentum_uniform_output P model.sample model.jointly_measurable
    (measurable_polar _ _) hfol (fun X => nuclearNorm (gradient f X))
    ((LongTails.Proofs.MatrixCovariance.continuous_nuclearNorm _ _).measurable.comp
      (LongTails.Proofs.MuonProcess.measurable_gradient f)) hbound.1
  refine ⟨hout.1, hout.2.1, hout.2.2.trans_le ?_⟩
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < T + 1)]
  refine hbound.2.trans ?_
  have hBge : 128 * (1 - p.β) * p.s ^ 2 / p.ε ^ 2 ≤ (B : ℝ) := by
    have := Nat.le_ceil (128 * (1 - p.β) * p.s ^ 2 / p.ε ^ 2)
    rw [hBdef]
    push_cast
    linarith
  have hTge : (32 * p.L * p.Δ / p.ε ^ 2 + 16) / (1 - p.β) ≤ T := Nat.le_ceil _
  have hfinal := tuned_budget_bound hL hΔ hs hε hβ1 hB hBge hTge
  rw [← hηdef] at hfinal
  dsimp only [LongTails.Setups.MomentumSpectralSmooth.Public.toBase]
  linarith

end LongTails.Proofs.MomentumMuonRate
