import LongTails.Proofs.CompositeGeneralizedStep
import LongTails.Proofs.Execution

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeGeneralized

open LongTails.Setups.CompositeGeneralizedSmooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def run (L0 L1 R Δ : ℝ) (g : E → E) (prox : ℝ → E → E → E) (x0 : E) :
    ℕ → ℝ × E × E
  | 0 => (R ^ 2 / (2 * Δ), x0, x0)
  | n + 1 => step L0 L1 R g prox (run L0 L1 R Δ g prox x0 n)

lemma inv_run {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
    {L0 L1 R Δ : ℝ} (h : Hyp f ψ g Q prox L0 L1) (hR : 0 < R) (hΔ : 0 < Δ)
    {x0 xs : E} (hx0 : x0 ∈ Q) (hxs : xs ∈ Q) (hmin : IsMinOn (fun x => f x + ψ x) Q xs)
    (hdist : ‖x0 - xs‖ ≤ R) (hgap : f x0 + ψ x0 - (f xs + ψ xs) ≤ Δ) (n : ℕ) :
    Inv f ψ Q xs R (run L0 L1 R Δ g prox x0 n) := by
  induction n with
  | zero =>
    have hA : 0 < R ^ 2 / (2 * Δ) := by positivity
    refine ⟨hA, hx0, hx0, ?_, show ‖x0 - xs‖ ≤ 2 * R by linarith,
      show ‖x0 - xs‖ ≤ 2 * R by linarith⟩
    simp only [run]
    have h1 : R ^ 2 / (2 * Δ) * (f x0 + ψ x0 - (f xs + ψ xs)) ≤ R ^ 2 / (2 * Δ) * Δ :=
      mul_le_mul_of_nonneg_left hgap hA.le
    have h2 : R ^ 2 / (2 * Δ) * Δ = R ^ 2 / 2 := by field_simp
    have h3 : ‖x0 - xs‖ ^ 2 ≤ R ^ 2 := by
      have := norm_nonneg (x0 - xs)
      nlinarith
    linarith
  | succ n ih => exact inv_step h hR hxs hmin ih

lemma curvature_bound {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
    {L0 L1 R G : ℝ} (h : Hyp f ψ g Q prox L0 L1) {xs : E} (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun x => f x + ψ x) Q xs) (hG : ‖g xs‖ ≤ G) {s : ℝ × E × E}
    (hs : Inv f ψ Q xs R s) :
    L0 + L1 * ‖g s.2.1‖ ≤ 2 * (L0 + L1 * G) + 24 * (L1 ^ 2 * R ^ 2) / s.1 := by
  obtain ⟨A, x, z⟩ := s
  obtain ⟨hA, hx, hz, hΦ, hxd, hzd⟩ := hs
  simp only at hA hx hz hΦ hxd hzd ⊢
  have hL0 := h.hL0
  have hL1 := h.hL1
  set gs := g xs
  set M := L0 + L1 * ‖g x‖
  set γ := ‖g x - gs‖
  set H := f x - f xs - ⟪gs, x - xs⟫
  have hcoc : γ ^ 2 ≤ 8 * (M + L1 * γ) * H :=
    shifted_cocoercive hL0 hL1 h.convex h.grad h.cont h.smooth xs x
  have hoptx := optimality h.convex h.grad h.cont h.setConvex h.regConvex hxs hmin hx
  have hH0 : 0 ≤ H := by
    have := Gradient.convex_support h.convex h.grad xs x
    simp only [H]; linarith
  have hAH : A * H ≤ R ^ 2 := by
    have h1 : H ≤ f x + ψ x - (f xs + ψ xs) := by simp only [H]; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hA.le
    nlinarith [sq_nonneg ‖z - xs‖]
  set B := L1 ^ 2 * R ^ 2 / A
  have hB0 : 0 ≤ B := by positivity
  have hHB : L1 ^ 2 * H ≤ B := by
    simp only [B]
    rw [le_div_iff₀ hA]
    nlinarith [sq_nonneg L1]
  set u := L1 * γ
  have hu0 : 0 ≤ u := by positivity
  have hMu : M ≤ L0 + L1 * G + u := by
    have h1 : ‖g x‖ ≤ G + γ := by
      calc ‖g x‖ = ‖(g x - gs) + gs‖ := by congr 1; abel
        _ ≤ γ + ‖gs‖ := norm_add_le _ _
        _ ≤ G + γ := by linarith
    have := mul_le_mul_of_nonneg_left h1 hL1
    simp only [M, u]; linarith
  have hu2 : u ^ 2 ≤ 8 * (M + u) * B := by
    have h1 : u ^ 2 = L1 ^ 2 * γ ^ 2 := by simp only [u]; ring
    have h2 := mul_le_mul_of_nonneg_left hcoc (sq_nonneg L1)
    have hMu0 : 0 ≤ M + u := by positivity
    have h3 : 8 * (M + u) * (L1 ^ 2 * H) ≤ 8 * (M + u) * B :=
      mul_le_mul_of_nonneg_left hHB (by positivity)
    rw [h1]; nlinarith
  have hMs : 0 < L0 + L1 * G := by
    have : 0 ≤ G := (norm_nonneg _).trans hG
    positivity
  have hB24 : 24 * (L1 ^ 2 * R ^ 2) / A = 24 * B := by simp only [B]; ring
  rw [hB24]
  by_contra hcon
  push Not at hcon
  have hu1 : L0 + L1 * G + 24 * B < u := by linarith
  have hu3 : u ^ 2 ≤ 8 * (L0 + L1 * G) * B + 16 * u * B := by nlinarith
  nlinarith

set_option maxHeartbeats 2000000 in
lemma sqrt_growth {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
    {L0 L1 R G : ℝ} (h : Hyp f ψ g Q prox L0 L1) (hR : 0 < R) {xs : E} (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun x => f x + ψ x) Q xs) (hG : ‖g xs‖ ≤ G) {s : ℝ × E × E}
    (hs : Inv f ψ Q xs R s) :
    Real.sqrt s.1 + 1 / (4 * Real.sqrt (3 * (L0 + L1 * G))) ≤
        Real.sqrt (step L0 L1 R g prox s).1 ∨
      (1 + 1 / (3 + 96 * L1 * R)) * Real.sqrt s.1 ≤ Real.sqrt (step L0 L1 R g prox s).1 := by
  have hMb := curvature_bound h hxs hmin hG hs
  obtain ⟨A, x, z⟩ := s
  obtain ⟨hA, hx, hz, hΦ, hxd, hzd⟩ := hs
  simp only at hA hMb ⊢
  have hL0 := h.hL0
  have hL1 := h.hL1
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
  set Ms := L0 + L1 * G with hMsdef
  have hMs : 0 < Ms := by positivity
  set M := L0 + L1 * ‖g x‖ with hMdef
  have hM : 0 < M := by positivity
  set ρ := 1 / (3 + 96 * L1 * R) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ3 : ρ ≤ 1 / 3 := by
    simp only [ρ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [mul_nonneg hL1 hR.le]
  have hρLR : ρ * (L1 * R) ≤ 1 / 96 := by
    simp only [ρ]; rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hstepA : (step L0 L1 R g prox (A, x, z)).1 = A + weight L1 R A M := rfl
  rw [hstepA]
  have ha0 : 0 < weight L1 R A M := (weight_spec hL1 hR hA hM).1
  set a := weight L1 R A M with hadef
  set sA := Real.sqrt A with hsAdef
  have hsA0 : 0 ≤ sA := Real.sqrt_nonneg _
  have hsA2 : sA ^ 2 = A := Real.sq_sqrt hA.le
  set r := Real.sqrt (1 + 16 * M * A) with hrdef
  have hr2 : r ^ 2 = 1 + 16 * M * A := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hgeo : 3 * ρ * A ≤ a → (1 + ρ) * sA ≤ Real.sqrt (A + a) := by
    intro ha3
    rw [Real.le_sqrt (by positivity) (by linarith)]
    have : (1 + ρ) ^ 2 * A ≤ (1 + 3 * ρ) * A := by
      have : (1 + ρ) ^ 2 ≤ 1 + 3 * ρ := by nlinarith
      exact mul_le_mul_of_nonneg_right this hA.le
    nlinarith
  rcases le_total ((1 + r) / (8 * M)) (A / (1 + 32 * L1 * R)) with hcase | hcase
  · have ha : a = (1 + r) / (8 * M) := min_eq_left hcase
    by_cases hbig : 24 * (L1 ^ 2 * R ^ 2) ≤ Ms * A
    · left
      have hM3 : M ≤ 3 * Ms := by
        have : 24 * (L1 ^ 2 * R ^ 2) / A ≤ Ms := by rw [div_le_iff₀ hA]; linarith
        linarith
      set d := 1 / (4 * Real.sqrt (3 * Ms)) with hddef
      have hq : Real.sqrt (3 * Ms) ^ 2 = 3 * Ms := Real.sq_sqrt (by positivity)
      have hq0 : 0 < Real.sqrt (3 * Ms) := Real.sqrt_pos.mpr (by positivity)
      have hd0 : 0 < d := by positivity
      have hd2 : d ^ 2 * (48 * Ms) = 1 := by
        simp only [d]; rw [div_pow, one_pow, mul_pow, hq]; field_simp; ring
      have hMd : 16 * M * d ^ 2 ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hM3 (sq_nonneg d)
        linarith
      rw [Real.le_sqrt (by positivity) (by linarith)]
      have h1 : 16 * M * d * sA ≤ r := by
        rw [show r = Real.sqrt (1 + 16 * M * A) from rfl]
        apply Real.le_sqrt_of_sq_le
        have : (16 * M * d * sA) ^ 2 = 16 * M * A * (16 * M * d ^ 2) := by
          rw [← hsA2]; ring
        rw [this]
        nlinarith [mul_le_mul_of_nonneg_left hMd (show 0 ≤ 16 * M * A by positivity)]
      have h2 : 2 * d * sA ≤ r / (8 * M) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have h3 : d ^ 2 ≤ 1 / (8 * M) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have h4 : a = 1 / (8 * M) + r / (8 * M) := by rw [ha]; ring
      nlinarith
    · right
      push Not at hbig
      apply hgeo
      have hMA : M * A < 72 * (L1 ^ 2 * R ^ 2) := by
        have h1 : M * A ≤ (2 * Ms + 24 * (L1 ^ 2 * R ^ 2) / A) * A :=
          mul_le_mul_of_nonneg_right hMb hA.le
        have h2 : (2 * Ms + 24 * (L1 ^ 2 * R ^ 2) / A) * A =
            2 * (Ms * A) + 24 * (L1 ^ 2 * R ^ 2) := by field_simp
        linarith
      have hsq : (24 * ρ * M * A) ^ 2 ≤ r ^ 2 := by
        rw [hr2]
        have hMA0 : 0 ≤ M * A := by positivity
        have h2 : ρ ^ 2 * (M * A) ≤ ρ ^ 2 * (72 * (L1 ^ 2 * R ^ 2)) :=
          mul_le_mul_of_nonneg_left hMA.le (sq_nonneg ρ)
        have h3 : ρ ^ 2 * (72 * (L1 ^ 2 * R ^ 2)) = 72 * (ρ * (L1 * R)) ^ 2 := by ring
        have h4 : (ρ * (L1 * R)) ^ 2 ≤ (1 / 96) ^ 2 := by
          have : 0 ≤ ρ * (L1 * R) := by positivity
          nlinarith
        have h5 : ρ ^ 2 * (M * A) ≤ 72 * (1 / 96) ^ 2 := by nlinarith
        have h6 : (24 * ρ * M * A) ^ 2 = 576 * (ρ ^ 2 * (M * A)) * (M * A) := by ring
        have h7 : 576 * (ρ ^ 2 * (M * A)) * (M * A) ≤ 576 * (72 * (1 / 96) ^ 2) * (M * A) :=
          mul_le_mul_of_nonneg_right (by linarith) hMA0
        nlinarith
      have hle : 24 * ρ * M * A ≤ r := by
        have : 0 ≤ 24 * ρ * M * A := by positivity
        nlinarith
      rw [ha, le_div_iff₀ (by positivity)]
      nlinarith
  · right
    have ha : a = A / (1 + 32 * L1 * R) := min_eq_right hcase
    apply hgeo
    rw [ha]
    have : 3 * ρ = 1 / (1 + 32 * L1 * R) := by
      simp only [ρ]; field_simp; ring
    rw [show 3 * ρ * A = (3 * ρ) * A by ring, this]
    rw [div_mul_eq_mul_div, one_mul]

noncomputable def potential (δ ρ t : ℝ) : ℝ :=
  t / δ + (1 + ρ) / ρ * Real.log (min t (δ / ρ))

lemma potential_step {δ ρ s s' : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hρ3 : ρ ≤ 1 / 3)
    (hs : 0 < s) (hss : s ≤ s') (hstep : s + δ ≤ s' ∨ (1 + ρ) * s ≤ s') :
    potential δ ρ s + 3 / 4 ≤ potential δ ρ s' := by
  unfold potential
  have hcap : 0 < δ / ρ := by positivity
  have hc : 0 < (1 + ρ) / ρ := by positivity
  have hmin0 : 0 < min s (δ / ρ) := lt_min hs hcap
  have hmono : Real.log (min s (δ / ρ)) ≤ Real.log (min s' (δ / ρ)) :=
    (Real.log_le_log_iff hmin0 (lt_of_lt_of_le hmin0 (min_le_min_right _ hss))).mpr
      (min_le_min_right _ hss)
  have hlogc : 0 ≤ (1 + ρ) / ρ * (Real.log (min s' (δ / ρ)) - Real.log (min s (δ / ρ))) :=
    mul_nonneg hc.le (by linarith)
  rcases hstep with hadd | hgeo
  · have : s / δ + 1 ≤ s' / δ := by
      rw [div_add_one hδ.ne', div_le_div_iff_of_pos_right hδ]; linarith
    nlinarith
  · by_cases hsmall : (1 + ρ) * s ≤ δ / ρ
    · have hm1 : min s (δ / ρ) = s := min_eq_left (by nlinarith)
      have hm2 : (1 + ρ) * s ≤ min s' (δ / ρ) := le_min hgeo hsmall
      have hlog1 : Real.log ((1 + ρ) * s) ≤ Real.log (min s' (δ / ρ)) :=
        (Real.log_le_log_iff (by positivity) (lt_of_lt_of_le (by positivity) hm2)).mpr hm2
      rw [Real.log_mul (by positivity) hs.ne'] at hlog1
      have hl : 1 - (1 + ρ)⁻¹ ≤ Real.log (1 + ρ) := Real.one_sub_inv_le_log_of_pos (by positivity)
      have hk : (1 + ρ) / ρ * (1 - (1 + ρ)⁻¹) = 1 := by field_simp; ring
      have hlc : 1 ≤ (1 + ρ) / ρ * Real.log (1 + ρ) :=
        calc (1 : ℝ) = (1 + ρ) / ρ * (1 - (1 + ρ)⁻¹) := hk.symm
          _ ≤ (1 + ρ) / ρ * Real.log (1 + ρ) := mul_le_mul_of_nonneg_left hl hc.le
      have hss' : s / δ ≤ s' / δ := div_le_div_of_nonneg_right hss hδ.le
      rw [hm1] at hlogc ⊢
      have : (1 + ρ) / ρ * Real.log s + 1 ≤ (1 + ρ) / ρ * Real.log (min s' (δ / ρ)) := by
        have := mul_le_mul_of_nonneg_left hlog1 hc.le
        nlinarith
      linarith
    · push Not at hsmall
      have hgain : s / δ + 3 / 4 ≤ s' / δ := by
        have h1 : δ < ρ * ((1 + ρ) * s) := by
          rw [div_lt_iff₀ hρ] at hsmall; linarith
        have h2 : 3 / 4 * δ ≤ ρ * s := by nlinarith
        rw [div_add' _ _ _ hδ.ne', div_le_div_iff_of_pos_right hδ]
        nlinarith
      linarith

lemma potential_run {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
    {L0 L1 R Δ G : ℝ} (h : Hyp f ψ g Q prox L0 L1) (hR : 0 < R) (hΔ : 0 < Δ)
    {x0 xs : E} (hx0 : x0 ∈ Q) (hxs : xs ∈ Q) (hmin : IsMinOn (fun x => f x + ψ x) Q xs)
    (hdist : ‖x0 - xs‖ ≤ R) (hgap : f x0 + ψ x0 - (f xs + ψ xs) ≤ Δ) (hG : ‖g xs‖ ≤ G)
    (n : ℕ) :
    potential (1 / (4 * Real.sqrt (3 * (L0 + L1 * G)))) (1 / (3 + 96 * L1 * R))
        (Real.sqrt (run L0 L1 R Δ g prox x0 0).1) + 3 / 4 * n ≤
      potential (1 / (4 * Real.sqrt (3 * (L0 + L1 * G)))) (1 / (3 + 96 * L1 * R))
        (Real.sqrt (run L0 L1 R Δ g prox x0 n).1) := by
  have hL0 := h.hL0
  have hL1 := h.hL1
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
  have hδ : 0 < 1 / (4 * Real.sqrt (3 * (L0 + L1 * G))) := by
    have : 0 < Real.sqrt (3 * (L0 + L1 * G)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hρ : 0 < 1 / (3 + 96 * L1 * R) := by positivity
  have hρ3 : 1 / (3 + 96 * L1 * R) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [mul_nonneg hL1 hR.le]
  induction n with
  | zero => simp
  | succ n ih =>
    have hinv := inv_run h hR hΔ hx0 hxs hmin hdist hgap n
    have hA := hinv.1
    have hgrow := sqrt_growth h hR hxs hmin hG hinv
    have hstepA : (run L0 L1 R Δ g prox x0 (n + 1)).1 =
        (step L0 L1 R g prox (run L0 L1 R Δ g prox x0 n)).1 := rfl
    have hmono : (run L0 L1 R Δ g prox x0 n).1 ≤ (run L0 L1 R Δ g prox x0 (n + 1)).1 := by
      rw [hstepA]
      have hM : 0 < L0 + L1 * ‖g (run L0 L1 R Δ g prox x0 n).2.1‖ := by positivity
      have := (weight_spec hL1 hR hA hM).1
      simp only [step]
      linarith
    have hps := potential_step hδ hρ hρ3 (Real.sqrt_pos.mpr hA) (Real.sqrt_le_sqrt hmono)
      (by rw [hstepA]; exact hgrow)
    push_cast
    linarith

lemma le_of_sq_le_sq' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
  le_of_not_gt fun hlt => by nlinarith

lemma lt_of_sq_lt_sq' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 < b ^ 2) : a < b :=
  lt_of_not_ge fun hle => by nlinarith

set_option maxHeartbeats 2000000 in
lemma run_accuracy {f ψ : E → ℝ} {g : E → E} {Q : Set E} {prox : ℝ → E → E → E}
    {L0 L1 R Δ G ε : ℝ} (h : Hyp f ψ g Q prox L0 L1) (hR : 0 < R) (hΔ : 0 < Δ) (hε : 0 < ε)
    {x0 xs : E} (hx0 : x0 ∈ Q) (hxs : xs ∈ Q) (hmin : IsMinOn (fun x => f x + ψ x) Q xs)
    (hdist : ‖x0 - xs‖ ≤ R) (hgap : f x0 + ψ x0 - (f xs + ψ xs) ≤ Δ) (hG : ‖g xs‖ ≤ G)
    (K : ℕ) (hK : 10 * Real.sqrt ((L0 + L1 * G) * R ^ 2 / ε) +
      (6 + 128 * L1 * R) * Real.log (2 + (3 + 96 * L1 * R) * Real.sqrt (Δ / (L0 * R ^ 2))) ≤ K) :
    (run L0 L1 R Δ g prox x0 K).2.1 ∈ Q ∧
      f (run L0 L1 R Δ g prox x0 K).2.1 + ψ (run L0 L1 R Δ g prox x0 K).2.1 -
        (f xs + ψ xs) ≤ ε := by
  have hL0 := h.hL0
  have hL1 := h.hL1
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
  have hpot := potential_run h hR hΔ hx0 hxs hmin hdist hgap hG K
  obtain ⟨hA, hxK, hzK, hΦ, -, -⟩ := inv_run h hR hΔ hx0 hxs hmin hdist hgap K
  refine ⟨hxK, ?_⟩
  set A := (run L0 L1 R Δ g prox x0 K).1 with hAdef
  set x := (run L0 L1 R Δ g prox x0 K).2.1
  have hgap0 : 0 ≤ f x + ψ x - (f xs + ψ xs) := by
    have := hmin hxK
    simp only [mem_ofPred_eq] at this
    linarith
  have hAg : A * (f x + ψ x - (f xs + ψ xs)) ≤ R ^ 2 := by nlinarith [sq_nonneg ‖(run L0 L1 R Δ g prox x0 K).2.2 - xs‖]
  suffices hbig : R ^ 2 / ε ≤ A by
    have h1 : R ^ 2 / ε * (f x + ψ x - (f xs + ψ xs)) ≤ R ^ 2 :=
      (mul_le_mul_of_nonneg_right hbig hgap0).trans hAg
    rw [div_mul_eq_mul_div, div_le_iff₀ hε] at h1
    have hR2 : 0 < R ^ 2 := by positivity
    nlinarith
  by_contra hsmall
  push Not at hsmall
  set Ms := L0 + L1 * G with hMsdef
  have hMs : 0 < Ms := by positivity
  have hq0 : 0 < Real.sqrt (3 * Ms) := Real.sqrt_pos.mpr (by positivity)
  have hq2 : Real.sqrt (3 * Ms) ^ 2 = 3 * Ms := Real.sq_sqrt (by positivity)
  set δ := 1 / (4 * Real.sqrt (3 * Ms)) with hδdef
  set ρ := 1 / (3 + 96 * L1 * R) with hρdef
  have hδ : 0 < δ := by positivity
  have hρ : 0 < ρ := by positivity
  have hδ2 : δ ^ 2 * (48 * Ms) = 1 := by
    simp only [δ]; rw [div_pow, one_pow, mul_pow, hq2]; field_simp; ring
  set A0 := (run L0 L1 R Δ g prox x0 0).1 with hA0def
  have hA0 : A0 = R ^ 2 / (2 * Δ) := rfl
  have hA0pos : 0 < A0 := by rw [hA0]; positivity
  set s0 := Real.sqrt A0
  set sK := Real.sqrt A
  have hs0 : 0 < s0 := Real.sqrt_pos.mpr hA0pos
  have hsK : 0 < sK := Real.sqrt_pos.mpr hA
  have hs02 : s0 ^ 2 = A0 := Real.sq_sqrt hA0pos.le
  have hsK2 : sK ^ 2 = A := Real.sq_sqrt hA.le
  unfold potential at hpot
  set cap := δ / ρ
  have hcap : 0 < cap := by positivity
  set c := (1 + ρ) / ρ
  have hc : c = 4 + 96 * L1 * R := by simp only [c, ρ]; field_simp; ring
  have hup : Real.log (min sK cap) ≤ Real.log cap :=
    (Real.log_le_log_iff (lt_min hsK hcap) hcap).mpr (min_le_right _ _)
  set X := Real.sqrt (Δ / (L0 * R ^ 2))
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hX2 : X ^ 2 = Δ / (L0 * R ^ 2) := Real.sq_sqrt (by positivity)
  have hδX : δ ≤ X * s0 := by
    apply le_of_sq_le_sq' (by positivity)
    rw [mul_pow, hX2, hs02, hA0]
    have e : Δ / (L0 * R ^ 2) * (R ^ 2 / (2 * Δ)) = 1 / (2 * L0) := by field_simp
    rw [e]
    have : δ ^ 2 = 1 / (48 * Ms) := by rw [eq_div_iff (by positivity)]; linarith [hδ2]
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    have : L0 ≤ Ms := by simp only [Ms]; nlinarith [mul_nonneg hL1 hG0]
    linarith
  set Y := 2 + (3 + 96 * L1 * R) * X
  have hY : 2 ≤ Y := by simp only [Y]; nlinarith [mul_nonneg hL1 hR.le]
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hratio : cap / min s0 cap ≤ Y := by
    rcases le_total s0 cap with hle | hle
    · rw [min_eq_left hle, div_le_iff₀ hs0]
      have : cap = (3 + 96 * L1 * R) * δ := by simp only [cap, ρ]; field_simp
      rw [this]
      have h1 : (3 + 96 * L1 * R) * δ ≤ (3 + 96 * L1 * R) * (X * s0) :=
        mul_le_mul_of_nonneg_left hδX (by positivity)
      simp only [Y]; nlinarith
    · rw [min_eq_right hle, div_self hcap.ne']; linarith
  have hlogdiff : Real.log cap - Real.log (min s0 cap) ≤ Real.log Y := by
    rw [← Real.log_div hcap.ne' (lt_min hs0 hcap).ne']
    exact (Real.log_le_log_iff (div_pos hcap (lt_min hs0 hcap)) (by linarith)).mpr hratio
  have hsKδ : sK / δ < 15 / 2 * Real.sqrt (Ms * R ^ 2 / ε) := by
    have hm : sK / δ = 4 * Real.sqrt (3 * Ms) * sK := by simp only [δ]; field_simp
    rw [hm]
    apply lt_of_sq_lt_sq' (by positivity)
    rw [mul_pow, mul_pow, mul_pow, hq2, hsK2, Real.sq_sqrt (by positivity)]
    have : A * ε < R ^ 2 := by rwa [lt_div_iff₀ hε] at hsmall
    have h1 : 4 ^ 2 * (3 * Ms) * A = 48 * Ms * A := by ring
    rw [h1, show (15 / 2 : ℝ) ^ 2 * (Ms * R ^ 2 / ε) = 225 / 4 * Ms * R ^ 2 / ε by ring,
      lt_div_iff₀ hε]
    nlinarith
  have hs0δ : 0 ≤ s0 / δ := by positivity
  have hcl : c * Real.log Y ≤ 3 / 4 * (6 + 128 * L1 * R) * Real.log Y := by
    rw [hc]; exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hL1 hR.le]) hlogY
  have hc0 : 0 ≤ c := by positivity
  have hmain : 3 / 4 * (K : ℝ) < 15 / 2 * Real.sqrt (Ms * R ^ 2 / ε) + c * Real.log Y := by
    have h1 := mul_le_mul_of_nonneg_left hup hc0
    have h2 := mul_le_mul_of_nonneg_left hlogdiff hc0
    nlinarith
  linarith

def answerOf (p : Public) (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E) :
    Query p → p.E
  | .gradient x => grad x
  | .prox a z v => prox a z v

lemma execute_accelerated (p : Public) (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E)
    (n : ℕ) :
    execute { answer := fun _ q _ => answerOf p grad prox q.2 } (accelerated p) (fun _ => (3 * n)) =
      (run p.L0 p.L1 p.R p.Δ grad prox p.x0 n).2.1 := by
  let A := accelerated p
  let T := fun s => A.update s (answerOf p grad prox (A.query s).2)
  have hi : ∀ n, T^[3 * n] (A.initial ()) =
      ⟨0, (run p.L0 p.L1 p.R p.Δ grad prox p.x0 n).1,
        (run p.L0 p.L1 p.R p.Δ grad prox p.x0 n).2.1,
        (run p.L0 p.L1 p.R p.Δ grad prox p.x0 n).2.2, 0, 0⟩ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [show 3 * (n + 1) = ((3 * n + 1) + 1) + 1 by ring,
        Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih]
      rfl
  have he := execute_iterate (answerOf p grad prox) (accelerated p) (3 * n) ()
  refine he.trans ?_
  change A.output (T^[3 * n] (A.initial ())) = _
  rw [hi]
  rfl

end OracleTemplate.CompositeGeneralized
