import LongTails.Proofs.GeneralizedSmoothSmoothedChain
import LongTails.Proofs.GeneralizedSmoothHardChain
import LongTails.Proofs.GeneralizedSmoothTransientParameters

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace LongTails.Proofs.GeneralizedSmoothHardChainRadius

open GeneralizedSmoothHardChain GeneralizedSmoothHardTransfer

lemma tailSum_last {m : ℕ} (G : Fin m → ℝ) (i : Fin m) (hi : i.val + 1 = m) :
    tailSum G i = G i := by
  have he (k : Fin m) : (if i ≤ k then G k else 0) = if k = i then G i else 0 := by
    by_cases hk : k = i
    · subst k
      simp
    · have hn : ¬i ≤ k := by
        intro hh
        apply hk
        apply Fin.ext
        have hk' := k.isLt
        change i.val ≤ k.val at hh
        omega
      simp [hk, hn]
  simp only [tailSum, he, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

lemma tailSum_successor {m : ℕ} (G : Fin m → ℝ) (i j : Fin m) (hij : j.val = i.val + 1) :
    tailSum G i = G i + tailSum G j := by
  have he (k : Fin m) : (if i ≤ k then G k else 0) =
      (if k = i then G i else 0) + (if j ≤ k then G k else 0) := by
    by_cases hk : k = i
    · subst k
      have hn : ¬j ≤ i := by change ¬j.val ≤ i.val; omega
      simp [hn]
    · have hiff : i ≤ k ↔ j ≤ k := by
        have hne : k.val ≠ i.val := fun h => hk (Fin.ext h)
        change i.val ≤ k.val ↔ j.val ≤ k.val
        omega
      simp [hk, hiff]
  simp only [tailSum, he, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

lemma tailSum_geometric_bound {m : ℕ} (G : Fin m → ℝ) (S : ℝ) (hS : 0 < S)
    (hG : ∀ i, 0 ≤ G i)
    (hratio : ∀ i j, i < j → G j * (1 + 1 / S) ≤ G i) (i : Fin m) :
    tailSum G i ≤ (1 + S) * G i := by
  have hmain : ∀ n : ℕ, ∀ i : Fin m, m - 1 - i.val = n → tailSum G i ≤ (1 + S) * G i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hin
      by_cases hi : i.val + 1 < m
      · let j : Fin m := ⟨i.val + 1, hi⟩
        have hj : m - 1 - j.val < n := by dsimp [j]; omega
        have ht := ih (m - 1 - j.val) hj j rfl
        have hij : i < j := by change i.val < i.val + 1; omega
        have hr := mul_le_mul_of_nonneg_left (hratio i j hij) hS.le
        have he : S * (G j * (1 + 1 / S)) = (1 + S) * G j := by field_simp; ring
        rw [he] at hr
        rw [tailSum_successor G i j rfl]
        nlinarith only [ht, hr]
      · have hl : i.val + 1 = m := by have hh := i.isLt; omega
        rw [tailSum_last G i hl]
        nlinarith [mul_nonneg hS.le (hG i)]
  exact hmain _ i rfl

lemma weight_tail_bound {m : ℕ} (hm : 0 < m) (L₁ ε : ℝ) (hL₁ : 0 < L₁) (hε : 0 < ε)
    (i : Fin m) : tailSum (weight m L₁ ε) i ≤ (1 + Real.sqrt m) * weight m L₁ ε i :=
  tailSum_geometric_bound _ _ (by positivity) (fun j => (weight_pos m L₁ ε hL₁ hε j).le)
    (weight_ratio_lower hm L₁ ε hL₁ hε) i

lemma norm_bound_of_coordinate_bound {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) (M : ℝ)
    (hM : 0 ≤ M) (hx : ∀ i, |x i| ≤ M) : ‖x‖ ≤ Real.sqrt m * M := by
  have hs (i : Fin m) : (x i) ^ 2 ≤ M ^ 2 := by
    have hh := abs_le.mp (hx i)
    nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) (by linarith : 0 ≤ M + x i)]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hs i)
  rw [← EuclideanSpace.real_norm_sq_eq] at hh
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  have he := Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hn : 0 ≤ Real.sqrt m * M := mul_nonneg (Real.sqrt_nonneg _) hM
  nlinarith [norm_nonneg x]

lemma shiftCoordinate_bounds {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (i : Fin m) :
    0 ≤ shiftCoordinate L₀ L₁ (peak m L₁ ε) (weight m L₁ ε) i ∧
    shiftCoordinate L₀ L₁ (peak m L₁ ε) (weight m L₁ ε) i ≤
      2 * (Real.log (1 + L₁ * peak m L₁ ε / L₀) / L₁) + 2 / L₁ +
        (4 / L₁ * Real.log (1 + Real.sqrt m)) * (1 + Real.sqrt m) := by
  have hG := weight_pos m L₁ ε hL₁ hε
  have hp := peak_pos m L₁ ε hL₁ hε
  have hC : 0 ≤ 4 / L₁ * Real.log (1 + Real.sqrt m) := by
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg (by linarith [Real.sqrt_nonneg (m : ℝ)])
  have hlog : 0 ≤ Real.log (1 + L₁ * peak m L₁ ε / L₀) := by
    apply Real.log_nonneg
    have hh : 0 ≤ L₁ * peak m L₁ ε / L₀ := by positivity
    linarith
  have ht := mul_le_mul_of_nonneg_left (weight_tail_bound hm L₁ ε hL₁ hε i)
    (div_nonneg hC (hG i).le)
  have he : (4 / L₁ * Real.log (1 + Real.sqrt m)) / weight m L₁ ε i *
      ((1 + Real.sqrt m) * weight m L₁ ε i) =
        (4 / L₁ * Real.log (1 + Real.sqrt m)) * (1 + Real.sqrt m) := by
    field_simp [(hG i).ne']
  rw [he] at ht
  have htail : 0 ≤ tailSum (weight m L₁ ε) i :=
    (hG i).le.trans (tailSum_lower _ (fun j => (hG j).le) i)
  simp only [shiftCoordinate, one_div_one_div]
  constructor
  · exact add_nonneg (add_nonneg (mul_nonneg (by norm_num) (div_nonneg hlog hL₁.le))
      (by positivity)) (mul_nonneg (div_nonneg hC (hG i).le) htail)
  · linarith

lemma peak_log_bound {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) :
    Real.log (1 + L₁ * peak m L₁ ε / L₀) ≤
      Real.log (1 + 2 * ε * L₁ ^ 2 / L₀) + Real.sqrt m := by
  let a := 2 * ε * L₁ ^ 2 / L₀
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hs : 0 < Real.sqrt m := by positivity
  have ht : ((m : ℝ) - 1) / Real.sqrt m ≤ Real.sqrt m := by
    apply (div_le_iff₀ hs).mpr
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have he := Real.exp_le_exp.mpr ht
  have h1 : 1 ≤ Real.exp (Real.sqrt m) := Real.one_le_exp_iff.mpr (Real.sqrt_nonneg _)
  have hp : 1 + L₁ * peak m L₁ ε / L₀ ≤ (1 + a) * Real.exp (Real.sqrt m) := by
    unfold peak
    have he' := mul_le_mul_of_nonneg_left he ha
    have hmul : L₁ * (2 * ε * L₁ * Real.exp (((m : ℝ) - 1) / Real.sqrt m)) / L₀ =
        a * Real.exp (((m : ℝ) - 1) / Real.sqrt m) := by dsimp [a]; ring
    rw [hmul]
    nlinarith only [he', h1]
  have hlog := Real.log_le_log (by have hh := peak_pos m L₁ ε hL₁ hε; positivity) hp
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp] at hlog
  exact hlog

lemma shift_norm_bound {m : ℕ} (hm : 0 < m) (L₀ L₁ ε : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) :
    ‖shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε)‖ ≤
      Real.sqrt m * (2 * (Real.log (1 + L₁ * peak m L₁ ε / L₀) / L₁) + 2 / L₁ +
        (4 / L₁ * Real.log (1 + Real.sqrt m)) * (1 + Real.sqrt m)) := by
  have hc := shiftCoordinate_bounds hm L₀ L₁ ε hL₀ hL₁ hε
  have h0 := hc ⟨0, hm⟩
  apply norm_bound_of_coordinate_bound _ _ (h0.1.trans h0.2)
  intro i
  change |shiftCoordinate L₀ L₁ (peak m L₁ ε) (weight m L₁ ε) i| ≤ _
  rw [abs_of_nonneg (hc i).1]
  exact (hc i).2

lemma radius_scalar_bound (m : ℕ) (q s : ℝ) (hq : 0 ≤ q) (hs : 1 ≤ s)
    (hms : (m : ℝ) * s ≤ q / 2048) (hsq : s ≤ q / 32768) :
    Real.sqrt m * (4 * s + 2 * Real.sqrt m + 2 + 4 * s * (1 + Real.sqrt m)) ≤ q / 128 := by
  have hs0 : 0 ≤ s := by linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hr0 := Real.sqrt_nonneg (m : ℝ)
  have hrsq := Real.sq_sqrt hm0
  have h1 := mul_le_mul_of_nonneg_right hms hs0
  have h2 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ q / 2048 by positivity)
  have he : (Real.sqrt m * s) ^ 2 = (m : ℝ) * s ^ 2 := by rw [mul_pow, hrsq]
  have hroot : Real.sqrt m * s ≤ q / 8192 := by
    have hn : 0 ≤ Real.sqrt m * s := mul_nonneg hr0 hs0
    nlinarith only [h1, h2, he, hn, hq]
  have h3 := mul_nonneg (sub_nonneg.mpr hs) hr0
  have h4 := mul_nonneg (sub_nonneg.mpr hs) hm0
  have he' : Real.sqrt m * (4 * s + 2 * Real.sqrt m + 2 + 4 * s * (1 + Real.sqrt m)) =
      8 * Real.sqrt m * s + 2 * m + 2 * Real.sqrt m + 4 * m * s := by
    nlinarith only [hrsq, congrArg (fun t : ℝ => t * s) hrsq]
  rw [he']
  nlinarith only [hroot, hms, h3, h4, hq]

lemma shift_norm_scaled_bound {m : ℕ} (hm : 0 < m) (L₀ L₁ ε q s : ℝ)
    (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (hq : 0 ≤ q) (hs : 1 ≤ s)
    (hms : (m : ℝ) * s ≤ q / 2048) (hsq : s ≤ q / 32768)
    (ha : Real.log (1 + 2 * ε * L₁ ^ 2 / L₀) ≤ 2 * s)
    (hb : Real.log (1 + Real.sqrt m) ≤ s) :
    L₁ * ‖shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε)‖ ≤ q / 128 := by
  have hh := mul_le_mul_of_nonneg_left (shift_norm_bound hm L₀ L₁ ε hL₀ hL₁ hε) hL₁.le
  have he : L₁ * (Real.sqrt m *
      (2 * (Real.log (1 + L₁ * peak m L₁ ε / L₀) / L₁) + 2 / L₁ +
        (4 / L₁ * Real.log (1 + Real.sqrt m)) * (1 + Real.sqrt m))) =
      Real.sqrt m * (2 * Real.log (1 + L₁ * peak m L₁ ε / L₀) + 2 +
        4 * Real.log (1 + Real.sqrt m) * (1 + Real.sqrt m)) := by
    field_simp [hL₁.ne']
  rw [he] at hh
  have hlog := peak_log_bound hm L₀ L₁ ε hL₀ hL₁ hε
  have ht := mul_le_mul_of_nonneg_right hb (show 0 ≤ 1 + Real.sqrt m by positivity)
  apply hh.trans
  apply le_trans _ (radius_scalar_bound m q s hq hs hms hsq)
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  linarith only [hlog, ha, ht]

lemma tuned_shift_norm (p : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.Params)
    (hp : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.spec.valid p) (m : ℕ) (hm : 0 < m)
    (hmB : m ≤ ⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊ + 1) :
    ‖shift (p.L0 / 4) (p.L1 / 4) (peak m (p.L1 / 4) p.ε) (weight m (p.L1 / 4) p.ε)‖ ≤ p.R / 32 := by
  rcases hp with ⟨h0, h1, hR, hε, hq, _, hup, _⟩
  have hmreal : (m : ℝ) ≤ ((⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊ + 1 : ℕ) : ℝ) :=
    by exact_mod_cast hmB
  have hms := (mul_le_mul_of_nonneg_right hmreal
    (GeneralizedSmoothTransientParameters.log_pos _ hq).le).trans
    (GeneralizedSmoothTransientParameters.links_log_bound _ hq)
  have hh := shift_norm_scaled_bound hm (p.L0 / 4) (p.L1 / 4) p.ε
    (p.L1 * p.R) (Real.log (2 + p.L1 * p.R)) (by positivity) (by positivity) hε
    (by positivity) (GeneralizedSmoothTransientParameters.log_one_le _ hq)
    hms
    (GeneralizedSmoothTransientParameters.log_upper_linear _ hq)
    (GeneralizedSmoothTransientParameters.scaled_accuracy_log_bound p.L0 p.L1 p.R p.ε h0 h1 hR hε hup)
    (GeneralizedSmoothTransientParameters.sqrt_links_log_bound m _ hq
      (hmreal.trans (GeneralizedSmoothTransientParameters.links_le_q _ hq)))
  apply (mul_le_mul_iff_of_pos_left (show 0 < p.L1 / 4 by positivity)).mp
  convert hh using 1
  ring

noncomputable def kernelRadius (m : ℕ) (L₁ R : ℝ) : ℝ :=
  min (1 / (64 * L₁ * Real.sqrt m)) (R / (16 * Real.sqrt m))

lemma kernelRadius_pos {m : ℕ} (hm : 0 < m) (L₁ R : ℝ) (hL₁ : 0 < L₁) (hR : 0 < R) :
    0 < kernelRadius m L₁ R := by unfold kernelRadius; positivity

noncomputable def kernel {m : ℕ} (hm : 0 < m) (L₁ R : ℝ) (hL₁ : 0 < L₁) (hR : 0 < R) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin m)) where
  rIn := kernelRadius m L₁ R / 2
  rOut := kernelRadius m L₁ R
  rIn_pos := div_pos (kernelRadius_pos hm L₁ R hL₁ hR) (by norm_num)
  rIn_lt_rOut := by have hh := kernelRadius_pos hm L₁ R hL₁ hR; linarith

lemma center_norm_bound {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε : ℝ) :
    ‖GeneralizedSmoothSmoothedChain.center φ L₀ L₁ ε‖ ≤
      ‖shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε)‖ + Real.sqrt m * φ.rOut := by
  let σ := shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε)
  let z := GeneralizedSmoothSmoothedChain.center φ L₀ L₁ ε
  have hh : ‖z + σ‖ ≤ Real.sqrt m * φ.rOut := by
    apply norm_bound_of_coordinate_bound _ _ φ.rOut_pos.le
    intro i
    change |-shiftCoordinate L₀ L₁ (peak m L₁ ε) (weight m L₁ ε) i - φ.rOut +
      shiftCoordinate L₀ L₁ (peak m L₁ ε) (weight m L₁ ε) i| ≤ φ.rOut
    have he : -shiftCoordinate L₀ L₁ (peak m L₁ ε) (weight m L₁ ε) i - φ.rOut +
      shiftCoordinate L₀ L₁ (peak m L₁ ε) (weight m L₁ ε) i = -φ.rOut := by ring
    rw [he, abs_neg, abs_of_pos φ.rOut_pos]
  have ht := norm_sub_le (z + σ) σ
  rw [add_sub_cancel_right] at ht
  change ‖z‖ ≤ ‖σ‖ + Real.sqrt m * φ.rOut
  linarith

lemma kernel_radius_times_sqrt {m : ℕ} (hm : 0 < m) (L₁ R : ℝ) :
    Real.sqrt m * kernelRadius m L₁ R ≤ R / 16 := by
  have hs : 0 < Real.sqrt m := by positivity
  have hh := mul_le_mul_of_nonneg_left (min_le_right (1 / (64 * L₁ * Real.sqrt m))
    (R / (16 * Real.sqrt m))) hs.le
  have he : Real.sqrt m * (R / (16 * Real.sqrt m)) = R / 16 := by field_simp
  simpa only [he, kernelRadius] using hh

lemma kernel_local_radius {m : ℕ} (hm : 0 < m) (L₁ R : ℝ) (hL₁ : 0 < L₁) :
    kernelRadius m L₁ R ≤ 1 / (16 * L₁ * Real.sqrt m) := by
  apply (min_le_left _ _).trans
  apply one_div_le_one_div_of_le (by positivity)
  have hs : 0 < Real.sqrt m := by positivity
  nlinarith [mul_pos hL₁ hs]

lemma kernel_curvature_radius {m : ℕ} (hm : 0 < m) (L₁ R : ℝ) (hL₁ : 0 < L₁) :
    L₁ * kernelRadius m L₁ R ≤ 1 / 16 := by
  have hh := mul_le_mul_of_nonneg_left (kernel_local_radius hm L₁ R hL₁) hL₁.le
  have he : L₁ * (1 / (16 * L₁ * Real.sqrt m)) = 1 / (16 * Real.sqrt m) := by field_simp
  rw [he] at hh
  apply hh.trans
  apply one_div_le_one_div_of_le (by norm_num)
  have hs := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ m by exact_mod_cast hm)
  rw [Real.sqrt_one] at hs
  linarith

lemma kernel_center_bound {m : ℕ} (hm : 0 < m) (L₀ L₁ ε R : ℝ)
    (hL₁ : 0 < L₁) (hR : 0 < R)
    (hshift : ‖shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε)‖ ≤ R / 32) :
    ‖GeneralizedSmoothSmoothedChain.center (kernel hm L₁ R hL₁ hR) L₀ L₁ ε‖ ≤ R / 8 := by
  have hh := center_norm_bound (kernel hm L₁ R hL₁ hR) L₀ L₁ ε
  have hδ := kernel_radius_times_sqrt hm L₁ R
  change ‖GeneralizedSmoothSmoothedChain.center (kernel hm L₁ R hL₁ hR) L₀ L₁ ε‖ ≤
    ‖shift L₀ L₁ (peak m L₁ ε) (weight m L₁ ε)‖ + Real.sqrt m * kernelRadius m L₁ R at hh
  linarith

end LongTails.Proofs.GeneralizedSmoothHardChainRadius
