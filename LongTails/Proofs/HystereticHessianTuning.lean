import LongTails.Proofs.HystereticHessianCompletion
import LongTails.Proofs.GuardedHessianTuning

namespace LongTails.Proofs.HystereticHessianTuning

lemma batch_moment_tuning {σ α R t p B : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hR : 0 ≤ R) (ht : 0 < t)
    (hp : 1 < p) (hB : 0 < B)
    (hsize : (6 * (σ + α * R) / t) ^ (p / (p - 1)) ≤ B) :
    6 * (σ ^ p + α ^ p * R ^ p) / B ^ (p - 1) ≤ t ^ p := by
  have hp1 : 0 < p - 1 := by linarith
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity : 0 ≤ 6 * (σ + α * R) / t) _)
    hsize hp1.le
  rw [← Real.rpow_mul (by positivity : 0 ≤ 6 * (σ + α * R) / t), div_mul_cancel₀ p hp1.ne'] at hpow
  have hsum := Real.add_rpow_le_rpow_add hσ (mul_nonneg hα hR) hp.le
  rw [Real.mul_rpow hα hR] at hsum
  have hsix : (6 : ℝ) ≤ (6 : ℝ) ^ p := Real.self_le_rpow_of_one_le (by norm_num) hp.le
  have hscale : 6 * (σ ^ p + α ^ p * R ^ p) ≤ (6 * (σ + α * R)) ^ p := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (by positivity)]
    exact (mul_le_mul_of_nonneg_left hsum (by norm_num)).trans
      (mul_le_mul_of_nonneg_right hsix (by positivity))
  have he : t ^ p * (6 * (σ + α * R) / t) ^ p = (6 * (σ + α * R)) ^ p := by
    rw [← Real.mul_rpow ht.le (by positivity)]
    congr 1
    field_simp
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hB _)).mpr
  rw [← he] at hscale
  exact hscale.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

lemma affine_relative_scale {σ α U r : ℝ} (hσ : 0 ≤ σ) (hα : 0 ≤ α)
    (hU : 0 < U) (hr : 0 ≤ r) :
    (σ + α * r) / (U + r) ≤ σ / U + α := by
  apply (div_le_iff₀ (by positivity : 0 < U + r)).mpr
  have hσU := div_nonneg hσ hU.le
  have he : σ / U * U = σ := div_mul_cancel₀ σ hU.ne'
  nlinarith [mul_nonneg hσU hr, mul_nonneg hα hU.le]

lemma noise_radius_properties {e σ α : ℝ} (he : 0 < e) (hσ : 0 ≤ σ) (hα : 0 ≤ α) :
    let A := 1 + α
    let S := 1 + σ / e + α
    let U := e + σ / A
    1 ≤ A ∧ A ≤ S ∧ e ≤ U ∧ A * U = e * S ∧ σ / U + α ≤ 2 * A ∧
      σ + 4 * α * U ≤ 5 * e * S := by
  intro A S U
  have hA : 0 < A := by dsimp [A]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hAU : A * U = e * S := by
    dsimp [A, U, S]
    field_simp
    ring
  have hσU : σ ≤ A * U := by
    dsimp [U]
    rw [mul_add, mul_div_cancel₀ _ hA.ne']
    nlinarith
  have hrel : σ / U ≤ A := (div_le_iff₀ hU).mpr (by nlinarith)
  refine ⟨by dsimp [A]; linarith, ?_, ?_, hAU, ?_, ?_⟩
  · dsimp [A, S]
    linarith [div_nonneg hσ he.le]
  · dsimp [U]
    exact le_add_of_nonneg_right (div_nonneg hσ hA.le)
  · dsimp [A] at hrel ⊢
    linarith
  · have hαU : α * U ≤ A * U := mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) hU.le
    nlinarith

lemma pilot_batch_moment {σ α U A r p B : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (hU : 0 < U) (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hp : 1 < p) (hB : 0 < B) (hrel : σ / U + α ≤ 2 * A)
    (hsize : ((2 : ℝ) ^ 24 * A) ^ (p / (p - 1)) ≤ B) :
    6 * (σ ^ p + α ^ p * r ^ p) / B ^ (p - 1) ≤ (((U + r) / 256) / 1536) ^ p := by
  have hratio := (affine_relative_scale hσ hα hU hr).trans hrel
  have hsum : σ + α * r ≤ 2 * A * (U + r) :=
    (div_le_iff₀ (by positivity : 0 < U + r)).mp hratio
  have hbase : 6 * (σ + α * r) / (((U + r) / 256) / 1536) ≤ (2 : ℝ) ^ 24 * A := by
    apply (div_le_iff₀ (by positivity : 0 < ((U + r) / 256) / 1536)).mpr
    norm_num
    nlinarith [mul_nonneg hA (by positivity : 0 ≤ U + r)]
  apply batch_moment_tuning hσ hα hr (by positivity) hp hB
  exact (Real.rpow_le_rpow (by positivity) hbase (by positivity)).trans hsize

lemma refresh_batch_moment {σ α U e S r p B : ℝ}
    (hσ : 0 ≤ σ) (hα : 0 ≤ α) (he : 0 < e) (hS : 0 ≤ S) (hr : 0 ≤ r)
    (hp : 1 < p) (hB : 0 < B) (hrU : r ≤ 4 * U)
    (hscale : σ + 4 * α * U ≤ 5 * e * S)
    (hsize : ((2 : ℝ) ^ 24 * S) ^ (p / (p - 1)) ≤ B) :
    6 * (σ ^ p + α ^ p * r ^ p) / B ^ (p - 1) ≤ ((e / 256) / 1536) ^ p := by
  have hsum : σ + α * r ≤ 5 * e * S := by nlinarith [mul_le_mul_of_nonneg_left hrU hα]
  have hbase : 6 * (σ + α * r) / ((e / 256) / 1536) ≤ (2 : ℝ) ^ 24 * S := by
    apply (div_le_iff₀ (by positivity : 0 < (e / 256) / 1536)).mpr
    norm_num
    nlinarith [mul_nonneg he.le hS]
  apply batch_moment_tuning hσ hα hr (by positivity) hp hB
  exact (Real.rpow_le_rpow (by positivity) hbase (by positivity)).trans hsize

lemma transport_batch_power {ell m b q : ℝ} (hell : 0 < ell) (hm : 0 < m)
    (hq : 1 < q) (hsize : 256 * ell * (256 * m) ^ (1 / (q - 1)) ≤ b) :
    0 < b / (256 * ell) ∧ 256 * m ≤ (b / (256 * ell)) ^ (q - 1) := by
  have hroot : 0 < (256 * m) ^ (1 / (q - 1)) := Real.rpow_pos_of_pos (by positivity) _
  have hr : (256 * m) ^ (1 / (q - 1)) ≤ b / (256 * ell) :=
    (le_div_iff₀ (by positivity : 0 < 256 * ell)).mpr (by nlinarith [hsize])
  refine ⟨hroot.trans_le hr, ?_⟩
  have hh := Real.rpow_le_rpow hroot.le hr (by linarith : 0 ≤ q - 1)
  rw [← Real.rpow_mul (by positivity : 0 ≤ 256 * m)] at hh
  have he : 1 / (q - 1) * (q - 1) = 1 := by
    field_simp [ne_of_gt (show 0 < q - 1 by linarith)]
  simpa only [he, Real.rpow_one] using hh

lemma normalized_transport_bias {a m r q : ℝ} (ha : 0 < a) (hm : 0 ≤ m) (hr : 0 < r)
    (hpower : 256 * m ≤ r ^ (q - 1)) :
    m * a ^ q / (a * r) ^ (q - 1) ≤ a := by
  have haqp : 0 < a ^ (q - 1) := Real.rpow_pos_of_pos ha _
  have he : a ^ q = a * a ^ (q - 1) := by
    calc
      a ^ q = a ^ (1 + (q - 1)) := by congr 1; ring
      _ = a * a ^ (q - 1) := by rw [Real.rpow_add ha, Real.rpow_one]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (mul_pos ha hr) _)).mpr
  rw [Real.mul_rpow ha.le hr.le, he]
  have hm' : m ≤ r ^ (q - 1) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hm' (mul_nonneg ha.le haqp.le)]

lemma normalized_transport_variance {a ell m r q : ℝ}
    (ha : 0 < a) (hell : 0 < ell) (hm : 0 ≤ m) (hr : 0 < r)
    (hq : 1 ≤ q) (hpower : 256 * m ≤ r ^ (q - 1)) :
    m * (4 * a * r) ^ (2 - q) * a ^ q / (256 * ell * r) ≤ a ^ 2 / (256 * ell) := by
  have hrp : 0 ≤ r ^ (2 - q) := Real.rpow_nonneg hr.le _
  have hrid : r ^ (q - 1) * r ^ (2 - q) = r := by
    rw [← Real.rpow_add hr]
    norm_num
  have har : a ^ (2 - q) * a ^ q = a ^ 2 := by
    rw [← Real.rpow_add ha]
    norm_num
  have hfour : (4 : ℝ) ^ (2 - q) ≤ 4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (show 2 - q ≤ 1 by linarith)
    simpa only [Real.rpow_one] using hh
  have hmroot : 256 * m * r ^ (2 - q) ≤ r := by
    simpa only [mul_assoc, hrid] using mul_le_mul_of_nonneg_right hpower hrp
  have hex : (4 * a * r) ^ (2 - q) * a ^ q = (4 : ℝ) ^ (2 - q) * r ^ (2 - q) * a ^ 2 := by
    rw [Real.mul_rpow (by positivity : 0 ≤ 4 * a) hr.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) ha.le]
    calc
      _ = (4 : ℝ) ^ (2 - q) * r ^ (2 - q) * (a ^ (2 - q) * a ^ q) := by ring
      _ = _ := by rw [har]
  have hcoef : m * (4 : ℝ) ^ (2 - q) * r ^ (2 - q) ≤ r := by
    have hh := mul_le_mul_of_nonneg_left hfour (mul_nonneg hm hrp)
    nlinarith
  apply (div_le_iff₀ (by positivity : 0 < 256 * ell * r)).mpr
  rw [mul_assoc m, hex]
  have ht : a ^ 2 / (256 * ell) * (256 * ell * r) = a ^ 2 * r := by
    field_simp
  rw [ht]
  nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg a)]

lemma transport_energy_tuning {a ell N V : ℝ} (ha : 0 < a) (hell : 1 ≤ ell)
    (hN : 0 ≤ N) (hV : 0 ≤ V) (hNV : N * V ≤ a ^ 2 / (256 * ell)) :
    let C := a / (64 * ell)
    let θ := 2 * ell / a ^ 2
    θ * (2 * a * C + C ^ 2) ≤ 1 ∧
      N * ((θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * V) - θ * a ^ 2 ≤ -ell := by
  intro C θ
  have hell0 : 0 < ell := by linarith
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCa : C ≤ a := by
    dsimp [C]
    apply (div_le_iff₀ (by positivity : 0 < 64 * ell)).mpr
    nlinarith
  have hC2 : C ^ 2 ≤ a ^ 2 := by nlinarith
  have hsmall : θ * (2 * a * C + C ^ 2) = 1 / 16 + 1 / (2048 * ell) := by
    dsimp [θ, C]
    field_simp
    ring
  have hfrac : (1 : ℝ) / (2048 * ell) ≤ 1 / 2048 := by
    apply (div_le_iff₀ (by positivity : 0 < 2048 * ell)).mpr
    nlinarith
  refine ⟨by rw [hsmall]; linarith, ?_⟩
  have hcoef : θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2) ≤ θ + 10 * θ ^ 2 * a ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hC2 (sq_nonneg θ)]
  have hlarge : 0 ≤ θ + 10 * θ ^ 2 * a ^ 2 := by positivity
  have hbound := (mul_le_mul_of_nonneg_right hcoef (mul_nonneg hN hV)).trans
    (mul_le_mul_of_nonneg_left hNV hlarge)
  have hvalue : (θ + 10 * θ ^ 2 * a ^ 2) * (a ^ 2 / (256 * ell)) = (2 + 40 * ell) / 256 := by
    dsimp [θ]
    field_simp
    ring
  have hθa : θ * a ^ 2 = 2 * ell := by dsimp [θ]; field_simp
  rw [hvalue] at hbound
  nlinarith

lemma transport_clip_tuning {a ell m b q : ℝ}
    (ha : 0 < a) (hell : 0 < ell) (hm : 0 < m) (hq : 1 < q)
    (hsize : 256 * ell * (256 * m) ^ (1 / (q - 1)) ≤ b) :
    let τ := a * b / (128 * ell)
    0 < b ∧ 0 < τ ∧
      m * b * (a ^ q / (τ / 2) ^ (q - 1) / b) ≤ a ∧
      m * b * ((2 * τ) ^ (2 - q) * a ^ q / b ^ 2) ≤ a ^ 2 / (256 * ell) ∧
      2 * τ / b = a / (64 * ell) := by
  intro τ
  let r := b / (256 * ell)
  have hr := transport_batch_power hell hm hq hsize
  change 0 < r ∧ 256 * m ≤ r ^ (q - 1) at hr
  have hb : 0 < b := by
    have hh := (div_pos_iff.mp hr.1)
    rcases hh with hh | hh
    · exact hh.1
    · exfalso; linarith [hh.2]
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hbr : 256 * ell * r = b := by dsimp [r]; field_simp
  have hτ2 : τ / 2 = a * r := by dsimp [τ, r]; field_simp; ring
  have hτ4 : 2 * τ = 4 * a * r := by dsimp [τ, r]; field_simp; ring
  refine ⟨hb, hτ, ?_, ?_, ?_⟩
  · have hh := normalized_transport_bias ha hm.le hr.1 hr.2
    rw [hτ2]
    convert hh using 1
    field_simp
  · have hh := normalized_transport_variance ha hell hm.le hr.1 hq.le hr.2
    rw [hbr] at hh
    rw [hτ4]
    convert hh using 1
    field_simp
  · dsimp [τ]
    field_simp
    ring

lemma fine_step_tuning {L0 L1 U e H K : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (he : 0 < e) (heU : e ≤ U)
    (hH : 0 < H) (hscale : L0 + L1 * U ≤ H) (hK : K ≤ 4 * H) :
    let η := e / (524288 * H)
    0 < η ∧ L1 * η ≤ 1 / 4 ∧ L0 * η ≤ e / 512 ∧ L0 * η ≤ U ∧
      2 * (L0 + 4 * L1 * U) * η ≤ 31 * e / 64 ∧ 512 * K * η ≤ e / 256 := by
  intro η
  have hη : 0 < η := by dsimp [η]; positivity
  have heq : H * η = e / 524288 := by dsimp [η]; field_simp
  have hU : 0 ≤ U := he.le.trans heU
  have hL0H : L0 ≤ H := by nlinarith [mul_nonneg hL1 hU]
  have hL1e : L1 * e ≤ H := by nlinarith [mul_le_mul_of_nonneg_left heU hL1]
  have hsmall : L1 * η ≤ 1 / 4 := by
    have hh := mul_le_mul_of_nonneg_right hL1e hη.le
    nlinarith
  have hbase : L0 * η ≤ e / 512 := by
    have hh := mul_le_mul_of_nonneg_right hL0H hη.le
    nlinarith
  have hfour : L0 + 4 * L1 * U ≤ 4 * H := by nlinarith
  refine ⟨hη, hsmall, hbase, by linarith, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_right hfour hη.le
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right hK hη.le
    nlinarith

lemma coarse_cap_tuning {L0 L1 M : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hM : 0 < M) (hD : 0 < L0 + L1 * M) :
    let cap := M / (256 * (L0 + L1 * M))
    0 ≤ cap ∧ L1 * cap ≤ 1 / 4 ∧ L0 * cap ≤ M / 4 := by
  intro cap
  have hcap : 0 ≤ cap := by dsimp [cap]; positivity
  have he : 256 * (L0 + L1 * M) * cap = M := by dsimp [cap]; field_simp
  have hL0cap := mul_nonneg hL0 hcap
  have hL1cap := mul_nonneg hL1 hcap
  refine ⟨hcap, ?_, ?_⟩
  · nlinarith
  · nlinarith [mul_nonneg hM.le hL1cap]

lemma macro_budget_tuning {δ Δ e U H D C m : ℝ}
    (hδ : 0 ≤ δ) (hgap : δ ≤ Δ) (he : 0 < e) (hU : 0 < U) (hH : 0 < H)
    (hD : 0 < D) (hDH : D ≤ H) (hCH : C ≤ 4 * H) (hm : 0 < m) :
    let η := e / (524288 * H)
    let J := ⌈8388608 * Δ * H / (e ^ 2 * m) + 16384 * Δ * H / U ^ 2⌉₊ + 2
    δ / (31 * e * η / 256) + m *
      (δ / (U ^ 2 / (8192 * D)) + 2 * (24 * C * δ / (15 * U ^ 2 / 4)) + 1) < (J : ℝ) * m := by
  intro η J
  have hΔ : 0 ≤ Δ := hδ.trans hgap
  have hδH : δ * H ≤ Δ * H := mul_le_mul_of_nonneg_right hgap hH.le
  have hδD : δ * D ≤ Δ * H := mul_le_mul hgap hDH hD.le hΔ
  have hδC : C * δ ≤ 4 * (Δ * H) := by
    have hh := mul_le_mul hCH hgap hδ (by positivity : 0 ≤ 4 * H)
    nlinarith
  have hF : δ / (31 * e * η / 256) ≤ 8388608 * Δ * H / e ^ 2 := by
    have heq : δ / (31 * e * η / 256) = (134217728 / 31 : ℝ) * (δ * H) / e ^ 2 := by
      dsimp [η]
      field_simp
      ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ (sq_nonneg e)
    nlinarith [mul_nonneg hδ hH.le]
  have hCo : δ / (U ^ 2 / (8192 * D)) ≤ 8192 * Δ * H / U ^ 2 := by
    have heq : δ / (U ^ 2 / (8192 * D)) = 8192 * (δ * D) / U ^ 2 := by field_simp
    rw [heq]
    apply div_le_div_of_nonneg_right _ (sq_nonneg U)
    nlinarith
  have hX : 2 * (24 * C * δ / (15 * U ^ 2 / 4)) ≤ 64 * Δ * H / U ^ 2 := by
    have heq : 2 * (24 * C * δ / (15 * U ^ 2 / 4)) = (192 / 15 : ℝ) * (C * δ) / U ^ 2 := by
      field_simp
      ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ (sq_nonneg U)
    nlinarith [mul_nonneg hΔ hH.le]
  let x := 8388608 * Δ * H / (e ^ 2 * m) + 16384 * Δ * H / U ^ 2
  have hJ : x + 2 ≤ (J : ℝ) := by
    have hh : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    dsimp [J]
    push_cast
    dsimp [x] at hh
    linarith
  have hxm : x * m = 8388608 * Δ * H / e ^ 2 + m * (16384 * Δ * H / U ^ 2) := by
    dsimp [x]
    field_simp
  have hsum : δ / (U ^ 2 / (8192 * D)) + 2 * (24 * C * δ / (15 * U ^ 2 / 4)) + 1 ≤
      16384 * Δ * H / U ^ 2 + 1 := by
    have hn : 0 ≤ Δ * H / U ^ 2 := by positivity
    have hh := add_le_add hCo hX
    have hleft : 8192 * Δ * H / U ^ 2 + 64 * Δ * H / U ^ 2 = 8256 * (Δ * H / U ^ 2) := by ring
    have hright : 16384 * Δ * H / U ^ 2 = 16384 * (Δ * H / U ^ 2) := by ring
    rw [hleft] at hh
    rw [hright]
    linarith
  have hmSum := mul_le_mul_of_nonneg_left hsum hm.le
  have hmJ := mul_le_mul_of_nonneg_right hJ hm.le
  nlinarith

end LongTails.Proofs.HystereticHessianTuning
