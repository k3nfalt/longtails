import LongTails.Proofs.MomentumSeparationBridge

namespace LongTails.Proofs.MomentumSeparationLower

open MeasureTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar
open LongTails.Proofs.DiagonalSpectral
open LongTails.Proofs.MomentumSeparationInstance LongTails.Proofs.MomentumSeparationModel
open LongTails.Proofs.MomentumSeparationCore LongTails.Proofs.MomentumDirectionExecution
open LongTails.Proofs.MomentumSeparationBridge

variable {m n : ℕ}

lemma flat_sum_le {hr : 0 < min m n} {ℓ c s β η : ℝ} {B : ℕ} {x0 : Space m n}
    {direction : Space m n → Space m n} {κ : Space m n → ℝ} (hB : 0 < B)
    (hdir : ∀ M, direction M = κ M • M) {w D : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (ξ : ℕ → Col m n × Bool) (t : ℕ) :
    ((min m n - 1 : ℕ) : ℝ) * c * |SeparationInstance.valleySlope w D
      (flat β c w D (gain hr ℓ c s β η (SeparationInstance.valleyShape hw D) B x0 direction κ ξ)
        t).1| ≤
      nuclearNorm (gradient (MomentumSeparationInstance.objective ℓ c
        (SeparationInstance.valleyShape hw D) x0)
        (iter hr ℓ c s β η (SeparationInstance.valleyShape hw D) B x0 direction ξ t).1) := by
  refine le_trans (le_of_eq ?_) (nuclear_ge_flat ℓ c _ x0 _)
  have hterm : ∀ k : Fin (min m n), |SeparationInstance.coefficients 0 c
      (SeparationInstance.valleyShape hw D) (SeparationInstance.offset x0
        (iter hr ℓ c s β η (SeparationInstance.valleyShape hw D) B x0 direction ξ t).1) k| =
      if SeparationInstance.stiff k then 0 else c * |SeparationInstance.valleySlope w D
        (flat β c w D (gain hr ℓ c s β η (SeparationInstance.valleyShape hw D) B x0 direction κ ξ)
          t).1| := by
    intro k
    by_cases hk : SeparationInstance.stiff k
    · simp [SeparationInstance.coefficients, hk]
    · have hk' : k.val ≠ 0 := hk
      rw [ite_eq_right hk]
      simp only [SeparationInstance.coefficients, hk, ↓reduceIte, SeparationInstance.offset]
      rw [(flat_entries (κ := κ) hB hdir hw rfl ξ hk' t).1, abs_mul, abs_of_nonneg hc]
      rfl
  rw [Finset.sum_congr rfl (fun k _ => hterm k), sum_stiff_split' hr]
  ring

lemma witness_params {L Δ ε : ℝ} {r : ℕ} (hL : 0 < L) (hε : 0 < ε) (hr : 1 ≤ (r : ℝ))
    (hLΔ : 1024 * ε ^ 2 ≤ L * Δ) :
    let c := 8 * ε / r
    let w := 16 * ε / L
    let D := Δ / (8 * ε)
    (r : ℝ) * c = 8 * ε ∧ 0 < c ∧ 0 < w ∧ Δ / (16 * ε) ≤ D - w ∧
      2 * c ≤ 3 * (L / 2) * (D - w) ∧ L / 2 + r * (c * (1 / w)) = L := by
  intro c w D
  have hr0 : (0 : ℝ) < r := by linarith
  have hΔ : 0 ≤ Δ := by nlinarith
  have hDw : Δ / (16 * ε) ≤ D - w := by
    simp only [D, w]
    have h1 : 16 * ε / L ≤ Δ / (16 * ε) := by
      rw [div_le_div_iff₀ hL (by positivity)]
      nlinarith
    have h2 : Δ / (8 * ε) = Δ / (16 * ε) + Δ / (16 * ε) := by field_simp; ring
    linarith
  refine ⟨by simp only [c]; field_simp, by positivity, by positivity, hDw, ?_, ?_⟩
  · have hc : 2 * c ≤ 16 * ε := by
      simp only [c]
      rw [show 2 * (8 * ε / r) = 16 * ε / r by ring, div_le_iff₀ hr0]
      nlinarith
    have h96 : 16 * ε ≤ 3 * (L / 2) * (Δ / (16 * ε)) := by
      rw [show 3 * (L / 2) * (Δ / (16 * ε)) = 3 * (L * Δ) / (32 * ε) by field_simp; ring,
        le_div_iff₀ (by positivity)]
      nlinarith
    have h3 := mul_le_mul_of_nonneg_left hDw (by positivity : (0 : ℝ) ≤ 3 * (L / 2))
    linarith
  · simp only [c, w]
    field_simp
    ring

lemma final_scaling {L Δ ε s β D w c ℓ : ℝ} {r B T : ℕ} (hL : 0 < L) (hε : 0 < ε)
    (hr : 1 ≤ (r : ℝ)) (hB : 0 < B) (hc : (r : ℝ) * c = 8 * ε) (hℓ : ℓ = L / 2)
    (hDw : Δ / (16 * ε) ≤ D - w) (hβ1 : β < 1)
    (hcore : (D - w) * ℓ * (1 - β) ^ 3 * (s / Real.sqrt B) ^ 2 ≤ 6912 * c * ε ^ 2 * (T + 1)) :
    (r : ℝ) * L * Δ * s ^ 2 * (1 - β) ^ 3 ≤ 2 ^ 21 * ε ^ 4 * (B * (T + 1)) := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hν : (s / Real.sqrt B) ^ 2 = s ^ 2 / B := by rw [div_pow, Real.sq_sqrt hB'.le]
  rw [hν, hℓ] at hcore
  have hδ : 0 ≤ (1 - β) ^ 3 := by have : 0 ≤ 1 - β := by linarith
                                  positivity
  have h1 : Δ / (16 * ε) * (L / 2) * (1 - β) ^ 3 * (s ^ 2 / B) ≤
      (D - w) * (L / 2) * (1 - β) ^ 3 * (s ^ 2 / B) := by
    have h0 : 0 ≤ (L / 2) * (1 - β) ^ 3 * (s ^ 2 / B) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hDw h0]
  have h2 := h1.trans hcore
  have h3 : (r : ℝ) * L * Δ * s ^ 2 * (1 - β) ^ 3 =
      (Δ / (16 * ε) * (L / 2) * (1 - β) ^ 3 * (s ^ 2 / B)) * (32 * ε * r * B) := by
    field_simp
    ring
  have h4 : 6912 * c * ε ^ 2 * (T + 1) * (32 * ε * r * B) = 1769472 * ε ^ 4 * (B * (T + 1)) := by
    have : c * r = 8 * ε := by linarith [mul_comm c (r : ℝ)]
    calc 6912 * c * ε ^ 2 * (T + 1) * (32 * ε * r * B) =
          6912 * 32 * (c * r) * ε ^ 3 * (B * (T + 1)) := by ring
      _ = _ := by rw [this]; ring
  have h5 : (r : ℝ) * L * Δ * s ^ 2 * (1 - β) ^ 3 ≤ 1769472 * ε ^ 4 * (B * (T + 1)) := by
    rw [h3, ← h4]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have h6 : (0 : ℝ) ≤ ε ^ 4 * (B * (T + 1)) := by positivity
  nlinarith

section Paths

variable {L Δ ε s β η : ℝ} {B T : ℕ} {x0 : Space m n}

theorem path_bound {direction : Space m n → Space m n} {κ : Space m n → ℝ}
    (hdir : ∀ M, direction M = κ M • M)
    (hr2 : 2 ≤ min m n) (hL : 0 < L) (hε : 0 < ε) (hs : 0 < s) (hβ1 : β < 1)
    (hB : 0 < B) (hLΔ : 1024 * ε ^ 2 ≤ L * Δ)
    (hcoreapp : ∀ {c w D : ℝ} (hw : 0 < w), 0 < c → ((min m n - 1 : ℕ) : ℝ) * c = 8 * ε →
      0 ≤ D - w → 2 * c ≤ 3 * (L / 2) * (D - w) →
      ∀ ξ : ℕ → Col m n × Bool,
      (∑ t ∈ Finset.range (T + 1), L / 2 * (s / Real.sqrt B * Real.sqrt (∑ u ∈ Finset.range T,
        ((impulse β (L / 2) (gain (lt_of_lt_of_le (by norm_num) hr2) (L / 2) c s β η
          (SeparationInstance.valleyShape hw D) B x0 direction κ ξ) u t).1) ^ 2)) ≤
          3 * (T + 1) * ε) →
      (∑ t ∈ Finset.range (T + 1), ((min m n - 1 : ℕ) : ℝ) * c *
        |SeparationInstance.valleySlope w D (flat β c w D (gain (lt_of_lt_of_le (by norm_num) hr2)
          (L / 2) c s β η (SeparationInstance.valleyShape hw D) B x0 direction κ ξ) t).1| ≤
          3 * (T + 1) * ε) →
      Distinct B T ξ →
      (D - w) * (L / 2) * (1 - β) ^ 3 * (s / Real.sqrt B) ^ 2 ≤ 6912 * c * ε ^ 2 * (T + 1))
    {ξ : ℕ → Col m n × Bool} (hd : Distinct B T ξ) (hw : 0 < 16 * ε / L)
    (hS : ∑ t ∈ Finset.range (T + 1), nuclearNorm (gradient
      (MomentumSeparationInstance.objective (L / 2) (8 * ε / ((min m n - 1 : ℕ) : ℝ))
        (SeparationInstance.valleyShape hw (Δ / (8 * ε))) x0)
      (iter (lt_of_lt_of_le (by norm_num) hr2) (L / 2) (8 * ε / ((min m n - 1 : ℕ) : ℝ)) s β η
        (SeparationInstance.valleyShape hw (Δ / (8 * ε))) B x0 direction ξ t).1) ≤
        3 * (T + 1) * ε) :
    ((min m n - 1 : ℕ) : ℝ) * L * Δ * s ^ 2 * (1 - β) ^ 3 ≤ 2 ^ 21 * ε ^ 4 * (B * (T + 1)) := by
  have hr1 : (1 : ℝ) ≤ ((min m n - 1 : ℕ) : ℝ) := by
    have : 1 ≤ min m n - 1 := by omega
    exact_mod_cast this
  obtain ⟨hrc, hc, _, hDw, hDl, _⟩ := witness_params (r := min m n - 1) hL hε hr1 hLΔ
  have hΔ : 0 ≤ Δ := by nlinarith
  have hDw0 : 0 ≤ Δ / (8 * ε) - 16 * ε / L := le_trans (by positivity) hDw
  set hr : 0 < min m n := lt_of_lt_of_le (by norm_num) hr2
  have hstiff : ∑ t ∈ Finset.range (T + 1), L / 2 * (s / Real.sqrt B * Real.sqrt
      (∑ u ∈ Finset.range T, ((impulse β (L / 2) (gain hr (L / 2) (8 * ε / ((min m n - 1 : ℕ) : ℝ))
        s β η (SeparationInstance.valleyShape hw (Δ / (8 * ε))) B x0 direction κ ξ) u t).1) ^ 2)) ≤
      3 * (T + 1) * ε := by
    refine le_trans (Finset.sum_le_sum fun t ht => ?_) hS
    rw [← stiff_norm_good (κ := κ) hB hdir hs.le hd
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))]
    exact nuclear_ge_stiff (L / 2) _ _ x0 _
  have hflat : ∑ t ∈ Finset.range (T + 1), ((min m n - 1 : ℕ) : ℝ) *
      (8 * ε / ((min m n - 1 : ℕ) : ℝ)) * |SeparationInstance.valleySlope (16 * ε / L) (Δ / (8 * ε))
        (flat β (8 * ε / ((min m n - 1 : ℕ) : ℝ)) (16 * ε / L) (Δ / (8 * ε))
          (gain hr (L / 2) (8 * ε / ((min m n - 1 : ℕ) : ℝ)) s β η
            (SeparationInstance.valleyShape hw (Δ / (8 * ε))) B x0 direction κ ξ) t).1| ≤
      3 * (T + 1) * ε :=
    le_trans (Finset.sum_le_sum fun t _ => flat_sum_le (κ := κ) hB hdir hw hc.le ξ t) hS
  have hcore := hcoreapp hw hc hrc hDw0 hDl ξ hstiff hflat hd
  exact final_scaling hL hε hr1 hB hrc rfl hDw hβ1 hcore


theorem core_app_nsgd (hr2 : 2 ≤ min m n) (hs : 0 < s) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hε : 0 < ε) (hL : 0 < L) (hη : 0 < η) (hB : 0 < B) {c w D : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hrc : ((min m n - 1 : ℕ) : ℝ) * c = 8 * ε) (hDw0 : 0 ≤ D - w)
    (hDl : 2 * c ≤ 3 * (L / 2) * (D - w)) (ξ : ℕ → Col m n × Bool)
    (hstiff : ∑ t ∈ Finset.range (T + 1), L / 2 * (s / Real.sqrt B * Real.sqrt (∑ u ∈ Finset.range T,
        ((impulse β (L / 2) (gain (lt_of_lt_of_le (by norm_num) hr2) (L / 2) c s β η
          (SeparationInstance.valleyShape hw D) B x0
            LongTails.Setups.MomentumSpectralSmooth.frobeniusNormalize (fun M => ‖M‖⁻¹) ξ)
              u t).1) ^ 2)) ≤ 3 * (T + 1) * ε)
    (hflat : ∑ t ∈ Finset.range (T + 1), ((min m n - 1 : ℕ) : ℝ) * c *
        |SeparationInstance.valleySlope w D (flat β c w D (gain (lt_of_lt_of_le (by norm_num) hr2)
          (L / 2) c s β η (SeparationInstance.valleyShape hw D) B x0
            LongTails.Setups.MomentumSpectralSmooth.frobeniusNormalize (fun M => ‖M‖⁻¹) ξ) t).1| ≤
          3 * (T + 1) * ε)
    (hd : Distinct B T ξ) :
    (D - w) * (L / 2) * (1 - β) ^ 3 * (s / Real.sqrt B) ^ 2 ≤ 6912 * c * ε ^ 2 * (T + 1) := by
  set hr : 0 < min m n := lt_of_lt_of_le (by norm_num) hr2
  have hr1 : (1 : ℝ) ≤ ((min m n - 1 : ℕ) : ℝ) := by
    have : 1 ≤ min m n - 1 := by omega
    exact_mod_cast this
  have hdir : ∀ M : Space m n, LongTails.Setups.MomentumSpectralSmooth.frobeniusNormalize M =
      (fun M : Space m n => ‖M‖⁻¹) M • M := fun M => rfl
  set α := gain hr (L / 2) c s β η (SeparationInstance.valleyShape hw D) B x0
    LongTails.Setups.MomentumSpectralSmooth.frobeniusNormalize (fun M => ‖M‖⁻¹) ξ with hαdef
  have hα : ∀ i, 0 ≤ α i := fun i => mul_nonneg hη.le (inv_nonneg.mpr (norm_nonneg _))
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hν : (s / Real.sqrt B) ^ 2 = s ^ 2 / B := by rw [div_pow, Real.sq_sqrt hB'.le]
  have hnorm : ∀ t < T, α t * Real.sqrt ((s / Real.sqrt B) ^ 2 * ∑ u ∈ Finset.range T,
      ((impulse β (L / 2) α u (t + 1)).2) ^ 2 + ((min m n - 1 : ℕ) : ℝ) *
        ((flat β c w D α (t + 1)).2) ^ 2) = η := by
    intro t ht
    have hM := momentum_norm_good (κ := fun M : Space m n => ‖M‖⁻¹) (hr := hr) (ℓ := L / 2)
      (c := c) (s := s) (β := β) (η := η) (x0 := x0) (D := D)
      (φ := SeparationInstance.valleyShape hw D) hB hdir hw rfl hd ht
    rw [hν, ← hM, Real.sqrt_sq (norm_nonneg _)]
    have hpos : 0 < ‖(iter hr (L / 2) c s β η (SeparationInstance.valleyShape hw D) B x0
        LongTails.Setups.MomentumSpectralSmooth.frobeniusNormalize ξ (t + 1)).2‖ := by
      apply lt_of_le_of_ne (norm_nonneg _)
      intro h0
      have hz := hM
      rw [← h0] at hz
      have hW := impulse_fresh_momentum β (L / 2) α t
      have hle : (1 - β) ^ 2 ≤ ∑ u ∈ Finset.range T, ((impulse β (L / 2) α u (t + 1)).2) ^ 2 := by
        rw [← hW]
        exact Finset.single_le_sum (f := fun u => ((impulse β (L / 2) α u (t + 1)).2) ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_range.mpr ht)
      have h1 : 0 < s ^ 2 / B * (1 - β) ^ 2 := by
        have : 0 < 1 - β := by linarith
        positivity
      have h2 : 0 ≤ ((min m n - 1 : ℕ) : ℝ) * ((flat β c w D α (t + 1)).2) ^ 2 := by positivity
      have h3 := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ s ^ 2 / B)
      have : (0 : ℝ) ^ 2 = 0 := by ring
      linarith
    change η * ‖_‖⁻¹ * _ = η
    rw [mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
  exact core_nsgd hβ0 hβ1 (by positivity : (0 : ℝ) < L / 2) hc hw hε (by positivity) hη hrc hr1
    hDw0 hDl hα hnorm hstiff hflat

theorem core_app_sgd (hr2 : 2 ≤ min m n) (hs : 0 < s) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hε : 0 < ε) (hL : 0 < L) (hη : 0 < η) (hB : 0 < B) {c w D : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hrc : ((min m n - 1 : ℕ) : ℝ) * c = 8 * ε) (hDw0 : 0 ≤ D - w)
    (hDl : 2 * c ≤ 3 * (L / 2) * (D - w)) (ξ : ℕ → Col m n × Bool)
    (hstiff : ∑ t ∈ Finset.range (T + 1), L / 2 * (s / Real.sqrt B * Real.sqrt (∑ u ∈ Finset.range T,
        ((impulse β (L / 2) (gain (lt_of_lt_of_le (by norm_num) hr2) (L / 2) c s β η
          (SeparationInstance.valleyShape hw D) B x0 id (fun _ => 1) ξ) u t).1) ^ 2)) ≤
          3 * (T + 1) * ε)
    (hflat : ∑ t ∈ Finset.range (T + 1), ((min m n - 1 : ℕ) : ℝ) * c *
        |SeparationInstance.valleySlope w D (flat β c w D (gain (lt_of_lt_of_le (by norm_num) hr2)
          (L / 2) c s β η (SeparationInstance.valleyShape hw D) B x0 id (fun _ => 1) ξ) t).1| ≤
          3 * (T + 1) * ε)
    (_hd : Distinct B T ξ) :
    (D - w) * (L / 2) * (1 - β) ^ 3 * (s / Real.sqrt B) ^ 2 ≤ 6912 * c * ε ^ 2 * (T + 1) := by
  have hg : gain (lt_of_lt_of_le (by norm_num) hr2) (L / 2) c s β η
      (SeparationInstance.valleyShape hw D) B x0 id (fun _ => (1 : ℝ)) ξ = fun _ => η := by
    funext t; simp [gain]
  rw [hg] at hstiff hflat
  have hrc' : ((min m n - 1 : ℕ) : ℝ) * c = 8 * ε := hrc
  exact core_sgd hβ0 hβ1 (by positivity : (0 : ℝ) < L / 2) hc hw hε (by positivity) hη hrc'
    hDw0 hDl hstiff hflat

end Paths

end LongTails.Proofs.MomentumSeparationLower
