import LongTails.Proofs.ReshuffledMoments
import LongTails.Proofs.LinearDecaySgdWeights

open Finset
open scoped RealInnerProductSpace

namespace OracleTemplate.ReshuffledConvex

open LongTails.Setups.ReshuffledSmoothConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {n : ℕ}
  [NeZero n]

noncomputable def iterate (g : Fin n → E → E) (ord : ℕ → Equiv.Perm (Fin n)) (η : ℕ → ℝ)
    (x0 : E) : ℕ → E
  | 0 => x0
  | t + 1 => iterate g ord η x0 t -
      η (t / n) • g (ord (t / n) ⟨t % n, Nat.mod_lt t (NeZero.pos n)⟩) (iterate g ord η x0 t)

omit [CompleteSpace E] in
lemma iterate_inner (g : Fin n → E → E) (ord : ℕ → Equiv.Perm (Fin n)) (η : ℕ → ℝ) (x0 : E)
    (k j : ℕ) (hj : j < n) :
    iterate g ord η x0 (n * k + (j + 1)) = iterate g ord η x0 (n * k + j) -
      η k • g (ord k ⟨j, hj⟩) (iterate g ord η x0 (n * k + j)) := by
  have hd : (n * k + j) / n = k := by
    rw [Nat.mul_add_div (NeZero.pos n), Nat.div_eq_of_lt hj, add_zero]
  have hm : (n * k + j) % n = j := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  have hf : (⟨(n * k + j) % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) = ⟨j, hj⟩ := Fin.ext hm
  show iterate g ord η x0 (n * k + j) - η ((n * k + j) / n) •
      g (ord ((n * k + j) / n) ⟨(n * k + j) % n, Nat.mod_lt _ (NeZero.pos n)⟩)
        (iterate g ord η x0 (n * k + j)) = _
  rw [hf, hd]

noncomputable def anchor (w : ℕ → ℝ) (X : ℕ → E) (xstar : E) : ℕ → E
  | 0 => xstar
  | k + 1 => (w k / w (k + 1)) • anchor w X xstar k + (1 - w k / w (k + 1)) • X (k + 1)

variable {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ} {Lavg Lmax σ : ℝ} {xstar : E}

lemma anchor_objective (h : Hyp f g ℓ Lavg Lmax σ xstar) (w : ℕ → ℝ) (X : ℕ → E) (k : ℕ)
    (hw : 0 < w k) (hww : w k ≤ w (k + 1)) :
    w (k + 1) * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (anchor w X xstar (k + 1)) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) ≤
      w k * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (anchor w X xstar k) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) +
        (w (k + 1) - w k) * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X (k + 1)) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) := by
  have hw1 : 0 < w (k + 1) := lt_of_lt_of_le hw hww
  have hθ0 : 0 ≤ w k / w (k + 1) := div_nonneg hw.le hw1.le
  have hθ1 : w k / w (k + 1) ≤ 1 := (div_le_one hw1).mpr hww
  have hθw : w k / w (k + 1) * w (k + 1) = w k := div_mul_cancel₀ _ hw1.ne'
  have hc := h.obj_convex (anchor w X xstar k) (X (k + 1)) hθ0 hθ1
  have hc' : LongTails.Setups.FiniteSumSmoothAndConvex.objective f (anchor w X xstar (k + 1)) ≤
      w k / w (k + 1) * LongTails.Setups.FiniteSumSmoothAndConvex.objective f (anchor w X xstar k) +
        (1 - w k / w (k + 1)) * LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X (k + 1)) := hc
  have hm := mul_le_mul_of_nonneg_left hc' hw1.le
  have he : w (k + 1) * (w k / w (k + 1) * LongTails.Setups.FiniteSumSmoothAndConvex.objective f (anchor w X xstar k) +
      (1 - w k / w (k + 1)) * LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X (k + 1))) =
      w k * LongTails.Setups.FiniteSumSmoothAndConvex.objective f (anchor w X xstar k) +
        (w (k + 1) - w k) * LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X (k + 1)) := by
    have e1 : w (k + 1) * (w k / w (k + 1) * LongTails.Setups.FiniteSumSmoothAndConvex.objective f (anchor w X xstar k) +
        (1 - w k / w (k + 1)) * LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X (k + 1))) =
        (w k / w (k + 1) * w (k + 1)) * LongTails.Setups.FiniteSumSmoothAndConvex.objective f (anchor w X xstar k) +
        (w (k + 1) - w k / w (k + 1) * w (k + 1)) * LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X (k + 1)) := by ring
    rw [e1, hθw]
  rw [he] at hm
  linarith

omit [CompleteSpace E] in
lemma anchor_distance (w : ℕ → ℝ) (X : ℕ → E) (xstar : E) (k : ℕ)
    (hw : 0 < w k) (hww : w k ≤ w (k + 1)) :
    w (k + 1) * ‖X (k + 1) - anchor w X xstar (k + 1)‖ ^ 2 ≤
      w k * ‖X (k + 1) - anchor w X xstar k‖ ^ 2 := by
  have hw1 : 0 < w (k + 1) := lt_of_lt_of_le hw hww
  have hθ0 : 0 ≤ w k / w (k + 1) := div_nonneg hw.le hw1.le
  have hθ1 : w k / w (k + 1) ≤ 1 := (div_le_one hw1).mpr hww
  have hθw : w k / w (k + 1) * w (k + 1) = w k := div_mul_cancel₀ _ hw1.ne'
  have he : X (k + 1) - anchor w X xstar (k + 1) =
      (w k / w (k + 1)) • (X (k + 1) - anchor w X xstar k) := by
    show X (k + 1) - ((w k / w (k + 1)) • anchor w X xstar k +
      (1 - w k / w (k + 1)) • X (k + 1)) = _
    module
  rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hN : 0 ≤ ‖X (k + 1) - anchor w X xstar k‖ ^ 2 := sq_nonneg _
  have e1 : w (k + 1) * ((w k / w (k + 1)) ^ 2 * ‖X (k + 1) - anchor w X xstar k‖ ^ 2) =
      (w k / w (k + 1) * w (k + 1)) * (w k / w (k + 1)) *
        ‖X (k + 1) - anchor w X xstar k‖ ^ 2 := by ring
  rw [e1, hθw]
  have h2 : w k * (w k / w (k + 1)) ≤ w k := by
    have := mul_le_mul_of_nonneg_left hθ1 hw.le
    linarith
  exact mul_le_mul_of_nonneg_right h2 hN

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [NeZero n] in
lemma sum_linear {ι : Type*} [Fintype ι] (T u v a sc : ι → ℝ) (c c3 c4 : ℝ) :
    ∑ s, (T s - c * (u s - v s) + c3 * a s + c4 * sc s) =
      ∑ s, T s - c * (∑ s, u s - ∑ s, v s) + c3 * ∑ s, a s + c4 * ∑ s, sc s := by
  simp only [sum_add_distrib, sum_sub_distrib, mul_sum, mul_sub]

set_option maxHeartbeats 1600000 in
theorem sum_gap (h : Hyp f g ℓ Lavg Lmax σ xstar) {ι : Type*} [Fintype ι] [Nonempty ι]
    (ord : ι → ℕ → Equiv.Perm (Fin n)) {γ B R : ℝ} {K : ℕ} (hK : 0 < K) (hγ : 0 < γ)
    (hΛ : 8 * Real.sqrt (Lavg * Lmax) * γ ≤ 1 / 8) (hB0 : 0 ≤ B)
    (hB : ∀ k, k < K → ∑ s, scatter g ℓ xstar (ord s k) ≤ Fintype.card ι * B)
    (x0 : E) (hR : ‖x0 - xstar‖ ≤ R) :
    ∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f
        (iterate g (ord s) (fun k => SampledConvex.step γ K k / n) x0 (n * K)) -
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) ≤
      Fintype.card ι * (3 * R ^ 2 / (γ * K) + 12 * γ ^ 2 * B / (n : ℝ) ^ 3) := by
  classical
  have hn := card_pos' n
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Fintype.card ι := ⟨_, rfl⟩
  have hMpos : 0 < M := by rw [hM]; exact_mod_cast Fintype.card_pos
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = Real.sqrt (Lavg * Lmax) := ⟨_, rfl⟩
  rw [← hΛdef] at hΛ
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; exact Real.sqrt_nonneg _
  have hΛsq : Λ ^ 2 = Lavg * Lmax := by
    rw [hΛdef]; exact Real.sq_sqrt (mul_nonneg h.pos.le h.lmax_pos.le)
  have hLavgΛ : Lavg ≤ Λ := by
    rw [hΛdef]
    calc Lavg = Real.sqrt (Lavg ^ 2) := (Real.sqrt_sq h.pos.le).symm
      _ ≤ Real.sqrt (Lavg * Lmax) := Real.sqrt_le_sqrt (by nlinarith [h.pos, h.le])
  have hL'0 : (0 : ℝ) ≤ 8 * Λ := by positivity
  obtain ⟨η, hη⟩ : ∃ η : ℕ → ℝ, η = fun k => SampledConvex.step γ K k / n := ⟨_, rfl⟩
  rw [← hη]
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, w = SampledConvex.weight (8 * Λ) γ K := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ι → ℕ → E, X = fun s k => iterate g (ord s) η x0 (n * k) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ι → ℕ → E, Z = fun s => anchor w (X s) xstar := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ, ∀ k, A k =
    ∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s k) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) := ⟨_, fun _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → ℝ, ∀ k, Φ k =
    ∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (Z s k) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) := ⟨_, fun _ => rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℝ, ∀ k, d k = ∑ s, ‖X s k - Z s k‖ ^ 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, ∀ k, e k = ∑ s, ‖X s (k + 1) - Z s k‖ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨σP, hσP⟩ : ∃ σP : ℝ, σP = Real.sqrt (M * (2 * γ * B / (n : ℝ) ^ 3)) := ⟨_, rfl⟩
  have hσP2 : σP ^ 2 = M * (2 * γ * B / (n : ℝ) ^ 3) := by
    rw [hσP]
    exact Real.sq_sqrt (mul_nonneg hMpos.le (div_nonneg (by positivity) hn3.le))
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = Real.sqrt M * R := ⟨_, rfl⟩
  have hD2 : D ^ 2 = M * R ^ 2 := by rw [hD, mul_pow, Real.sq_sqrt hMpos.le]
  have hwpos : ∀ k, k < K → 0 < w k := fun k hk => by
    rw [hw]; exact (SampledConvex.weight_bounds hL'0 hγ hΛ k hk).1
  have hwmono : ∀ k, k + 1 < K → w k ≤ w (k + 1) := fun k hk => by
    rw [hw]; exact SampledConvex.weight_mono hL'0 hγ hΛ hk
  have hA0 : ∀ k, 0 ≤ A k := fun k => by
    rw [hA k]; exact sum_nonneg (fun s _ => h.gap_nonneg _)
  have hXZ0 : ∀ s, Z s 0 = xstar := fun s => by rw [hZ]; rfl
  have hX0 : ∀ s, X s 0 = x0 := fun s => by rw [hX]; rfl
  have hH : ∀ k, k < K → SampledConvex.step γ K k * SampledConvex.weight (8 * Λ) γ K k *
      (A (k + 1) - Φ k) ≤
      SampledConvex.weight (8 * Λ) γ K k / 2 * (d k - e k) +
        SampledConvex.weight (8 * Λ) γ K k * SampledConvex.charge (8 * Λ) γ K k * A k +
        SampledConvex.step γ K k ^ 2 * SampledConvex.weight (8 * Λ) γ K k *
          (1 + 8 * Λ * SampledConvex.step γ K k) * σP ^ 2 := by
    intro k hk
    have hsp := SampledConvex.step_pos hγ hk
    have hsl := SampledConvex.step_le hγ.le hk
    obtain ⟨γk, hγk⟩ : ∃ γk : ℝ, γk = SampledConvex.step γ K k := ⟨_, rfl⟩
    rw [← hγk] at hsp hsl
    have hwk : 0 < w k := hwpos k hk
    rw [← hw, ← hγk]
    have hγkΛ : γk * Λ ≤ 1 / 64 := by
      have := mul_le_mul_of_nonneg_right hsl hΛ0
      linarith
    have hγkLavg : γk * Lavg ≤ 1 / 64 := (mul_le_mul_of_nonneg_left hLavgΛ hsp.le).trans hγkΛ
    have hηk : η k = γk / n := by rw [hη, hγk]
    have hηk0 : 0 ≤ η k := by rw [hηk]; exact div_nonneg hsp.le hn.le
    have hn' : (n : ℝ) ≠ 0 := hn.ne'
    have hnη : (n : ℝ) * η k = γk := by rw [hηk]; field_simp
    have hpath : ∀ s, ‖X s (k + 1) - Z s k‖ ^ 2 ≤ ‖X s k - Z s k‖ ^ 2 -
        2 * γk * ((LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s (k + 1)) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) -
          (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (Z s k) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)) +
        32 * γk ^ 3 * Lavg * Lmax * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s k) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) +
        2 * η k ^ 3 * (1 + 8 * γk ^ 2 * Lavg ^ 2) * scatter g ℓ xstar (ord s k) := by
      intro s
      have hy : ∀ j (hj : j < n), iterate g (ord s) η x0 (n * k + (j + 1)) =
          iterate g (ord s) η x0 (n * k + j) -
            η k • g (ord s k ⟨j, hj⟩) (iterate g (ord s) η x0 (n * k + j)) :=
        fun j hj => iterate_inner g (ord s) η x0 k j hj
      have hep := h.epoch_inequality (ord s k) hηk0 (by rw [hnη]; linarith)
        (fun j => iterate g (ord s) η x0 (n * k + j)) hy (Z s k)
      have e1 : iterate g (ord s) η x0 (n * k + n) = X s (k + 1) := by
        rw [hX]; rfl
      have e0 : iterate g (ord s) η x0 (n * k + 0) = X s k := by rw [hX]; rfl
      simp only [e1, e0, hnη] at hep
      linarith
    have hsum := sum_le_sum (fun s (_ : s ∈ univ) => hpath s)
    have hsumR : ∑ s, (‖X s k - Z s k‖ ^ 2 -
        2 * γk * ((LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s (k + 1)) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) -
          (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (Z s k) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)) +
        32 * γk ^ 3 * Lavg * Lmax * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s k) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) +
        2 * η k ^ 3 * (1 + 8 * γk ^ 2 * Lavg ^ 2) * scatter g ℓ xstar (ord s k)) =
        d k - 2 * γk * (A (k + 1) - Φ k) + 32 * γk ^ 3 * Lavg * Lmax * A k +
          2 * η k ^ 3 * (1 + 8 * γk ^ 2 * Lavg ^ 2) * ∑ s, scatter g ℓ xstar (ord s k) := by
      rw [hd k, hA (k + 1), hA k, hΦ k]
      exact sum_linear (fun s => ‖X s k - Z s k‖ ^ 2)
        (fun s => LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s (k + 1)) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)
        (fun s => LongTails.Setups.FiniteSumSmoothAndConvex.objective f (Z s k) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)
        (fun s => LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s k) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)
        (fun s => scatter g ℓ xstar (ord s k)) (2 * γk) (32 * γk ^ 3 * Lavg * Lmax)
        (2 * η k ^ 3 * (1 + 8 * γk ^ 2 * Lavg ^ 2))
    have hsumL : ∑ s, ‖X s (k + 1) - Z s k‖ ^ 2 = e k := (he k).symm
    rw [hsumR, hsumL] at hsum
    have hscat0 : 0 ≤ ∑ s, scatter g ℓ xstar (ord s k) :=
      sum_nonneg (fun s _ => scatter_nonneg g h.nonneg xstar _)
    have hBk := hB k hk
    rw [← hM] at hBk
    have hcharge : 16 * γk ^ 3 * (Lavg * Lmax) ≤ SampledConvex.charge (8 * Λ) γ K k := by
      unfold SampledConvex.charge
      rw [← hγk, ← hΛsq]
      have hpos : 0 ≤ 16 * Λ * γk ^ 2 * (1 + 7 * Λ * γk) := by
        have := hsp.le
        positivity
      have e1 : 2 * (8 * Λ) * γk ^ 2 * (1 + 8 * Λ * γk) - 16 * γk ^ 3 * Λ ^ 2 =
          16 * Λ * γk ^ 2 * (1 + 7 * Λ * γk) := by ring
      linarith
    have hc2 : 1 + 8 * γk ^ 2 * Lavg ^ 2 ≤ 2 := by
      have h0 : 0 ≤ γk * Lavg := mul_nonneg hsp.le h.pos.le
      have h1 : (γk * Lavg) ^ 2 ≤ (1 / 64) ^ 2 := pow_le_pow_left₀ h0 hγkLavg 2
      have e1 : 8 * γk ^ 2 * Lavg ^ 2 = 8 * (γk * Lavg) ^ 2 := by ring
      rw [e1]
      nlinarith [h1]
    have hη3 : η k ^ 3 = γk ^ 3 / (n : ℝ) ^ 3 := by rw [hηk, div_pow]
    have hη30 : 0 ≤ η k ^ 3 := pow_nonneg hηk0 3
    have hnoise : w k * (η k ^ 3 * (1 + 8 * γk ^ 2 * Lavg ^ 2) *
        ∑ s, scatter g ℓ xstar (ord s k)) ≤
        γk ^ 2 * w k * (1 + 8 * Λ * γk) * σP ^ 2 := by
      have hc20 : 0 ≤ 1 + 8 * γk ^ 2 * Lavg ^ 2 := by positivity
      have s1 : (1 + 8 * γk ^ 2 * Lavg ^ 2) * ∑ s, scatter g ℓ xstar (ord s k) ≤ 2 * (M * B) :=
        mul_le_mul hc2 hBk hscat0 (by norm_num)
      have s2 : η k ^ 3 * ((1 + 8 * γk ^ 2 * Lavg ^ 2) * ∑ s, scatter g ℓ xstar (ord s k)) ≤
          η k ^ 3 * (2 * (M * B)) := mul_le_mul_of_nonneg_left s1 hη30
      have s3 := mul_le_mul_of_nonneg_left s2 hwk.le
      have hfac : γk ≤ (1 + 8 * Λ * γk) * γ := by
        have := mul_nonneg (mul_nonneg hL'0 hsp.le) hγ.le
        nlinarith
      have hTq : 0 ≤ w k * γk ^ 2 * (2 * M * B / (n : ℝ) ^ 3) :=
        mul_nonneg (mul_nonneg hwk.le (sq_nonneg _))
          (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hMpos.le) hB0) hn3.le)
      have s4 := mul_le_mul_of_nonneg_left hfac hTq
      rw [hσP2]
      calc w k * (η k ^ 3 * (1 + 8 * γk ^ 2 * Lavg ^ 2) * ∑ s, scatter g ℓ xstar (ord s k))
          = w k * (η k ^ 3 * ((1 + 8 * γk ^ 2 * Lavg ^ 2) *
              ∑ s, scatter g ℓ xstar (ord s k))) := by ring
        _ ≤ w k * (η k ^ 3 * (2 * (M * B))) := s3
        _ = w k * γk ^ 2 * (2 * M * B / (n : ℝ) ^ 3) * γk := by rw [hη3]; ring
        _ ≤ w k * γk ^ 2 * (2 * M * B / (n : ℝ) ^ 3) * ((1 + 8 * Λ * γk) * γ) := s4
        _ = γk ^ 2 * w k * (1 + 8 * Λ * γk) * (M * (2 * γ * B / (n : ℝ) ^ 3)) := by ring
    have h1 := mul_le_mul_of_nonneg_left hsum (by linarith : (0 : ℝ) ≤ w k / 2)
    have h2 : w k * (16 * γk ^ 3 * (Lavg * Lmax)) * A k ≤
        w k * SampledConvex.charge (8 * Λ) γ K k * A k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcharge hwk.le) (hA0 k)
    linarith
  have hJ : ∀ k, k + 1 < K → SampledConvex.weight (8 * Λ) γ K (k + 1) * Φ (k + 1) ≤
      SampledConvex.weight (8 * Λ) γ K k * Φ k +
        (SampledConvex.weight (8 * Λ) γ K (k + 1) - SampledConvex.weight (8 * Λ) γ K k) *
          A (k + 1) := by
    intro k hk
    rw [← hw]
    have hwk := hwpos k (Nat.lt_of_succ_lt hk)
    have hww := hwmono k hk
    have hs := sum_le_sum (fun s (_ : s ∈ univ) =>
      anchor_objective h w (X s) k hwk hww)
    rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum] at hs
    rw [hΦ (k + 1), hΦ k, hA (k + 1)]
    have hZs : ∀ s j, Z s j = anchor w (X s) xstar j := fun s j => by rw [hZ]
    simp only [hZs]
    exact hs
  have hDd : ∀ k, k + 1 < K → SampledConvex.weight (8 * Λ) γ K (k + 1) * d (k + 1) ≤
      SampledConvex.weight (8 * Λ) γ K k * e k := by
    intro k hk
    rw [← hw]
    have hwk := hwpos k (Nat.lt_of_succ_lt hk)
    have hww := hwmono k hk
    have hs := sum_le_sum (fun s (_ : s ∈ univ) =>
      anchor_distance w (X s) xstar k hwk hww)
    rw [← mul_sum, ← mul_sum] at hs
    rw [hd (k + 1), he k]
    have hZs : ∀ s j, Z s j = anchor w (X s) xstar j := fun s j => by rw [hZ]
    simp only [hZs]
    exact hs
  have he0 : ∀ k, k < K → 0 ≤ e k := fun k _ => by
    rw [he k]; exact sum_nonneg (fun s _ => sq_nonneg _)
  have hΦ0 : Φ 0 = 0 := by
    rw [hΦ 0]
    simp only [hXZ0, sub_self, sum_const_zero]
  have hRsq : ‖x0 - xstar‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR 2
  have hd0 : d 0 ≤ D ^ 2 := by
    rw [hd 0, hD2]
    simp only [hXZ0, hX0, sum_const, card_univ, nsmul_eq_mul]
    rw [← hM]
    exact mul_le_mul_of_nonneg_left hRsq hMpos.le
  have hA00 : A 0 ≤ 8 * Λ * D ^ 2 / 2 := by
    rw [hA 0, hD2]
    simp only [hX0, sum_const, card_univ, nsmul_eq_mul]
    rw [← hM]
    have h1 := h.init_gap x0
    have h2 : Lavg / 2 * ‖x0 - xstar‖ ^ 2 ≤ 8 * Λ / 2 * R ^ 2 := by
      have h3 : Lavg / 2 ≤ 8 * Λ / 2 := by linarith
      exact mul_le_mul h3 hRsq (sq_nonneg _) (by positivity)
    have h4 := mul_le_mul_of_nonneg_left (h1.trans h2) hMpos.le
    calc M * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f x0 - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) ≤
          M * (8 * Λ / 2 * R ^ 2) := h4
      _ = 8 * Λ * (M * R ^ 2) / 2 := by ring
  have hfinal := SampledConvex.potential_bound hL'0 hγ hΛ hK A Φ d e hH hJ hDd he0 hΦ0 hd0 hA00
  rw [hD2, hσP2] at hfinal
  have hAK : A K = ∑ s, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (iterate g (ord s) η x0 (n * K)) -
      LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) := by rw [hA K, hX]
  rw [← hAK, ← hM]
  calc A K ≤ 3 * (M * R ^ 2) / (γ * K) + 6 * γ * (M * (2 * γ * B / (n : ℝ) ^ 3)) := hfinal
    _ = M * (3 * R ^ 2 / (γ * K) + 12 * γ ^ 2 * B / (n : ℝ) ^ 3) := by ring

end OracleTemplate.ReshuffledConvex
