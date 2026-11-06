import LongTails.Proofs.CovarianceAcceleratedParameters

namespace LongTails.Proofs.CovarianceAcceleratedTuning

open CovarianceAcceleratedParameters

lemma residual_confidence_bound {R σ L k T j ell : ℝ} (hR : 0 ≤ R) (hσ : 0 ≤ σ)
    (hL : 0 ≤ L) (hk : 0 ≤ k) (hT : 0 < T) (hell : 0 ≤ ell)
    (hej : ell ≤ j) (hjk : j ≤ k) (hkT : k ^ 2 ≤ T) :
    let M := 100 * (σ * T + L * R * k)
    48 * R * σ / Real.sqrt T + 48 * R * M * Real.sqrt (j * ell) / T ^ 2 +
      512 * R * M * ell / T ^ 2 ≤
        56048 * R * σ / Real.sqrt T + 56000 * L * R ^ 2 * k ^ 2 / T ^ 2 := by
  intro M
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hs : Real.sqrt (j * ell) ≤ k := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hk, ?_⟩
    calc
      j * ell ≤ k * k := mul_le_mul hjk (hej.trans hjk) hell hk
      _ = k ^ 2 := by ring
  have hkroot : k ≤ Real.sqrt T := (Real.le_sqrt hk hT.le).mpr hkT
  have hquot : k / T ≤ 1 / Real.sqrt T := by
    apply (div_le_div_iff₀ hT hsT).mpr
    have h := mul_le_mul_of_nonneg_right hkroot hsT.le
    nlinarith [Real.sq_sqrt hT.le]
  have h1 : 48 * R * M * Real.sqrt (j * ell) / T ^ 2 ≤ 48 * R * M * k / T ^ 2 := by
    gcongr
  have h2 : 512 * R * M * ell / T ^ 2 ≤ 512 * R * M * k / T ^ 2 := by
    gcongr
    exact hej.trans hjk
  have h3 : 56000 * R * σ * (k / T) ≤ 56000 * R * σ / Real.sqrt T := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hquot
      (show 0 ≤ 56000 * R * σ by positivity)
  calc
    _ ≤ 48 * R * σ / Real.sqrt T + 48 * R * M * k / T ^ 2 + 512 * R * M * k / T ^ 2 :=
      add_le_add (add_le_add le_rfl h1) h2
    _ = 48 * R * σ / Real.sqrt T + 56000 * R * σ * (k / T) +
        56000 * L * R ^ 2 * k ^ 2 / T ^ 2 := by dsimp [M]; field_simp; ring
    _ ≤ 48 * R * σ / Real.sqrt T + 56000 * R * σ / Real.sqrt T +
        56000 * L * R ^ 2 * k ^ 2 / T ^ 2 := add_le_add (add_le_add le_rfl h3) le_rfl
    _ = _ := by ring

lemma rounded_rate {R σ s L k T ell : ℝ} (hR : 0 ≤ R) (hσ : 0 ≤ σ) (hs : 0 ≤ s)
    (hL : 0 ≤ L) (hk : 1 ≤ k) (hT : 0 < T) :
    5 * L * R ^ 2 / T ^ 2 + 56000 * L * R ^ 2 * k ^ 2 / T ^ 2 +
      56048 * R * σ / Real.sqrt T + 208 * R * s * Real.sqrt ell / Real.sqrt T ≤
      65536 * (L * R ^ 2 * k ^ 2 / T ^ 2 + R * (σ + s * Real.sqrt ell) / Real.sqrt T) := by
  have hk2 : 1 ≤ k ^ 2 := by nlinarith
  have hbase : 5 * L * R ^ 2 / T ^ 2 ≤ 5 * L * R ^ 2 * k ^ 2 / T ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hk2 (show 0 ≤ 5 * L * R ^ 2 / T ^ 2 by positivity)
    convert h using 1 <;> ring
  have hdet : 0 ≤ L * R ^ 2 * k ^ 2 / T ^ 2 := by positivity
  have hn : 0 ≤ R * σ / Real.sqrt T := by positivity
  have hd : 0 ≤ R * s * Real.sqrt ell / Real.sqrt T := by positivity
  calc
    _ ≤ 5 * L * R ^ 2 * k ^ 2 / T ^ 2 + 56000 * L * R ^ 2 * k ^ 2 / T ^ 2 +
        56048 * R * σ / Real.sqrt T + 208 * R * s * Real.sqrt ell / Real.sqrt T := by linarith
    _ ≤ _ := by
      ring_nf at hdet hn hd ⊢
      linarith

lemma tuned_rate_bound {L R σ s k T j ell : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hσ : 0 ≤ σ) (hs : 0 ≤ s) (hk : 1 ≤ k) (hT : 0 < T) (hj : 0 < j)
    (hell : 0 < ell) (hej : ell ≤ j) (hjk : j ≤ k) (hkT : k ^ 2 ≤ T) :
    let M := 100 * (σ * T + L * R * k)
    let ν := σ ^ 2 * T + j * M ^ 2 * ell / T ^ 2
    let b := R / (32 * T * Real.sqrt ν)
    let η := 1 / (16 * R * s * T * Real.sqrt T / Real.sqrt ell + 64 * R * M + 64 * b * j * M ^ 2)
    5 * L * R ^ 2 / T ^ 2 + R ^ 2 / (b * T ^ 2) +
      1280 * η * R ^ 2 * s ^ 2 * T + 320 * b * σ ^ 2 * T + 8 * ell / (η * T ^ 2) ≤
      65536 * (L * R ^ 2 * k ^ 2 / T ^ 2 + R * (σ + s * Real.sqrt ell) / Real.sqrt T) := by
  intro M ν b η
  have hkpos : 0 < k := by linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have hν : 0 < ν := tuning_variance_pos hM hj hell hT
  have hb : 0 < b := by dsimp [b]; positivity
  have hη := (reciprocal_step_bounds hR hs hT hell hM hb hj).1
  have hD : 0 < 16 * R * s * T * Real.sqrt T / Real.sqrt ell + 64 * R * M + 64 * b * j * M ^ 2 := by positivity
  have heD : η * (16 * R * s * T * Real.sqrt T / Real.sqrt ell +
      64 * R * M + 64 * b * j * M ^ 2) = 1 := by
    dsimp [η]
    exact one_div_mul_cancel hD.ne'
  have hcap : η * (16 * R * s * T * Real.sqrt T / Real.sqrt ell) ≤ 1 := by
    calc
      _ ≤ η * (16 * R * s * T * Real.sqrt T / Real.sqrt ell +
          64 * R * M + 64 * b * j * M ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hη.le
        have h2 : 0 ≤ 64 * R * M := by positivity
        have h3 : 0 ≤ 64 * b * j * M ^ 2 := by positivity
        linarith
      _ = 1 := heD
  have hnoise := directional_noise_balance hR.le hs hT hell hcap
  have hconf := reciprocal_confidence hR hs hT hell hM hb hj
  have hmix := (mixture_balance (σ := σ) hR hT hj hell hM).2
  have hsqrt := mul_le_mul_of_nonneg_left (tuning_sqrt_bound hσ hM.le hj.le hell.le hT)
    (show 0 ≤ 48 * R by positivity)
  have hres := residual_confidence_bound hR.le hσ hL.le hkpos.le hT hell.le hej hjk hkT
  have hround := rounded_rate (ell := ell) hR.le hσ hs hL.le hk hT
  change 8 * ell / (η * T ^ 2) = _ at hconf
  change R ^ 2 / (b * T ^ 2) +
    (320 * σ ^ 2 * T + 512 * j * M ^ 2 * ell / T ^ 2) * b ≤
      48 * R * Real.sqrt ν / T at hmix
  change 48 * R * (Real.sqrt ν / T) ≤ _ at hsqrt
  change 48 * R * σ / Real.sqrt T + 48 * R * M * Real.sqrt (j * ell) / T ^ 2 +
      512 * R * M * ell / T ^ 2 ≤ _ at hres
  ring_nf at hnoise hconf hmix hsqrt hres hround ⊢
  linarith

lemma clipping_scalar_caps {α B η a b R M j : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (hj : 0 < j) (ha2 : a ^ 2 = b / η) (hz : 0 ≤ α * B) (hbound : α * B ≤ η * M)
    (hcap1 : 2 * η * R * M ≤ 1 / 32) (hcap2 : η * b * M ^ 2 ≤ 1 / (64 * j)) :
    2 * R * α * B ≤ 1 / 4 ∧ (α * a) ^ 2 * B ^ 2 ≤ 1 / (32 * j) := by
  have hfirst := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 2 * R by positivity)
  refine ⟨by nlinarith, ?_⟩
  have hsq : (α * B) ^ 2 ≤ (η * M) ^ 2 := by gcongr
  have hprod := mul_le_mul_of_nonneg_right hsq (sq_nonneg a)
  have he : (η * M) ^ 2 * a ^ 2 = η * b * M ^ 2 := by
    rw [ha2]
    field_simp
  rw [he] at hprod
  have he2 : (α * a) ^ 2 * B ^ 2 = (α * B) ^ 2 * a ^ 2 := by ring
  rw [he2]
  apply hprod.trans (hcap2.trans _)
  apply (div_le_div_iff₀ (show 0 < 64 * j by positivity) (show 0 < 32 * j by positivity)).mpr
  linarith

end LongTails.Proofs.CovarianceAcceleratedTuning
