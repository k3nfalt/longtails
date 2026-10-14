import LongTails.Proofs.SlidingStep
import LongTails.Proofs.CompositeGeneralizedRun

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GeneralizedSliding

open LongTails.Setups.SlidingGeneralizedSmooth

open CompositeGeneralized (shifted_cocoercive optimality potential potential_step
  le_of_sq_le_sq' lt_of_sq_lt_sq')

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma slide_curvature {f h : E → ℝ} {g : E → E} {Q : Set E} {L0 L1 R G : ℝ}
    (hy : Hyp f h g Q L0 L1) {xs : E} (hxs : xs ∈ Q)
    (hmin : IsMinOn (fun x => f x + h x) Q xs) (hG : ‖g xs‖ ≤ G) {A : ℝ} {x : E}
    (hA : 0 < A) (hx : x ∈ Q) (hΦ : A * (f x + h x - (f xs + h xs)) ≤ R ^ 2) :
    L0 + L1 * ‖g x‖ ≤ 2 * (L0 + L1 * G) + 24 * (L1 ^ 2 * R ^ 2) / A := by
  have hL0 := hy.hL0
  have hL1 := hy.hL1
  set gs := g xs
  set M := L0 + L1 * ‖g x‖
  set γ := ‖g x - gs‖
  set H := f x - f xs - ⟪gs, x - xs⟫
  have hcoc : γ ^ 2 ≤ 8 * (M + L1 * γ) * H :=
    shifted_cocoercive hL0 hL1 hy.convex hy.grad hy.cont hy.smooth xs x
  have hoptx := optimality hy.convex hy.grad hy.cont hy.setConvex hy.regConvex hxs hmin hx
  have hH0 : 0 ≤ H := by
    have := Gradient.convex_support hy.convex hy.grad xs x
    simp only [H]; linarith
  have hAH : A * H ≤ R ^ 2 := by
    have h1 : H ≤ f x + h x - (f xs + h xs) := by simp only [H]; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hA.le
    linarith
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
lemma slide_sqrt_growth {L1 R Ms A M : ℝ} (hL1 : 0 ≤ L1) (hR : 0 < R)
    (hMs : 0 < Ms) (hA : 0 < A) (hM : 0 < M) (hMb : M ≤ 2 * Ms + 24 * (L1 ^ 2 * R ^ 2) / A) :
    Real.sqrt A + 1 / (8 * Real.sqrt (3 * Ms)) ≤ Real.sqrt (A + slideWeight L1 R A M) ∨
      (1 + 1 / (3 + 240 * L1 * R)) * Real.sqrt A ≤ Real.sqrt (A + slideWeight L1 R A M) := by
  set ρ := 1 / (3 + 240 * L1 * R) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ3 : ρ ≤ 1 / 3 := by
    simp only [ρ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hL1 hR.le]
  have hρLR : ρ * (L1 * R) ≤ 1 / 240 := by
    simp only [ρ]; rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have ha0 : 0 < slideWeight L1 R A M := (slideWeight_spec hL1 hR hA hM).1
  set a := slideWeight L1 R A M with hadef
  set sA := Real.sqrt A with hsAdef
  have hsA0 : 0 ≤ sA := Real.sqrt_nonneg _
  have hsA2 : sA ^ 2 = A := Real.sq_sqrt hA.le
  set r := Real.sqrt (1 + 64 * M * A) with hrdef
  have hr2 : r ^ 2 = 1 + 64 * M * A := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hgeo : 3 * ρ * A ≤ a → (1 + ρ) * sA ≤ Real.sqrt (A + a) := by
    intro ha3
    rw [Real.le_sqrt (by positivity) (by linarith)]
    have : (1 + ρ) ^ 2 * A ≤ (1 + 3 * ρ) * A := by
      have : (1 + ρ) ^ 2 ≤ 1 + 3 * ρ := by nlinarith
      exact mul_le_mul_of_nonneg_right this hA.le
    nlinarith
  rcases le_total ((1 + r) / (32 * M)) (A / (1 + 80 * L1 * R)) with hcase | hcase
  · have ha : a = (1 + r) / (32 * M) := min_eq_left hcase
    by_cases hbig : 24 * (L1 ^ 2 * R ^ 2) ≤ Ms * A
    · left
      have hM3 : M ≤ 3 * Ms := by
        have : 24 * (L1 ^ 2 * R ^ 2) / A ≤ Ms := by rw [div_le_iff₀ hA]; linarith
        linarith
      set d := 1 / (8 * Real.sqrt (3 * Ms)) with hddef
      have hq : Real.sqrt (3 * Ms) ^ 2 = 3 * Ms := Real.sq_sqrt (by positivity)
      have hq0 : 0 < Real.sqrt (3 * Ms) := Real.sqrt_pos.mpr (by positivity)
      have hd0 : 0 < d := by positivity
      have hd2 : d ^ 2 * (192 * Ms) = 1 := by
        simp only [d]; rw [div_pow, one_pow, mul_pow, hq]; field_simp; ring
      have hMd : 64 * M * d ^ 2 ≤ 1 := by
        have := mul_le_mul_of_nonneg_right hM3 (sq_nonneg d)
        linarith
      rw [Real.le_sqrt (by positivity) (by linarith)]
      have h1 : 64 * M * d * sA ≤ r := by
        rw [show r = Real.sqrt (1 + 64 * M * A) from rfl]
        apply Real.le_sqrt_of_sq_le
        have : (64 * M * d * sA) ^ 2 = 64 * M * A * (64 * M * d ^ 2) := by
          rw [← hsA2]; ring
        rw [this]
        nlinarith [mul_le_mul_of_nonneg_left hMd (show 0 ≤ 64 * M * A by positivity)]
      have h2 : 2 * d * sA ≤ r / (32 * M) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have h3 : d ^ 2 ≤ 1 / (32 * M) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have h4 : a = 1 / (32 * M) + r / (32 * M) := by rw [ha]; ring
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
      have hsq : (96 * ρ * M * A) ^ 2 ≤ r ^ 2 := by
        rw [hr2]
        have hMA0 : 0 ≤ M * A := by positivity
        have h2 : ρ ^ 2 * (M * A) ≤ ρ ^ 2 * (72 * (L1 ^ 2 * R ^ 2)) :=
          mul_le_mul_of_nonneg_left hMA.le (sq_nonneg ρ)
        have h3 : ρ ^ 2 * (72 * (L1 ^ 2 * R ^ 2)) = 72 * (ρ * (L1 * R)) ^ 2 := by ring
        have h4 : (ρ * (L1 * R)) ^ 2 ≤ (1 / 240) ^ 2 := by
          have : 0 ≤ ρ * (L1 * R) := by positivity
          nlinarith
        have h5 : ρ ^ 2 * (M * A) ≤ 72 * (1 / 240) ^ 2 := by nlinarith
        have h6 : (96 * ρ * M * A) ^ 2 = 9216 * (ρ ^ 2 * (M * A)) * (M * A) := by ring
        have h7 : 9216 * (ρ ^ 2 * (M * A)) * (M * A) ≤ 9216 * (72 * (1 / 240) ^ 2) * (M * A) :=
          mul_le_mul_of_nonneg_right (by linarith) hMA0
        nlinarith
      have hle : 96 * ρ * M * A ≤ r := by
        have : 0 ≤ 96 * ρ * M * A := by positivity
        nlinarith
      rw [ha, le_div_iff₀ (by positivity)]
      nlinarith
  · right
    have ha : a = A / (1 + 80 * L1 * R) := min_eq_right hcase
    apply hgeo
    rw [ha]
    have : 3 * ρ = 1 / (1 + 80 * L1 * R) := by
      simp only [ρ]; field_simp; ring
    rw [show 3 * ρ * A = (3 * ρ) * A by ring, this]
    rw [div_mul_eq_mul_div, one_mul]

set_option maxHeartbeats 2000000 in
lemma slide_count {L0 L1 R Δ Ms ε A K : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hR : 0 < R)
    (hΔ : 0 < Δ) (hε : 0 < ε) (hMs : L0 ≤ Ms) (hA : 0 < A)
    (hpot : potential (1 / (8 * Real.sqrt (3 * Ms))) (1 / (3 + 240 * L1 * R))
        (Real.sqrt (R ^ 2 / (4 * Δ))) + 3 / 4 * K ≤
      potential (1 / (8 * Real.sqrt (3 * Ms))) (1 / (3 + 240 * L1 * R)) (Real.sqrt A))
    (hK : 20 * Real.sqrt (Ms * R ^ 2 / ε) +
      (6 + 320 * L1 * R) * Real.log (2 + (3 + 240 * L1 * R) * Real.sqrt (Δ / (L0 * R ^ 2))) ≤ K) :
    R ^ 2 / ε ≤ A := by
  by_contra hsmall
  push Not at hsmall
  have hMs0 : 0 < Ms := lt_of_lt_of_le hL0 hMs
  have hq0 : 0 < Real.sqrt (3 * Ms) := Real.sqrt_pos.mpr (by positivity)
  have hq2 : Real.sqrt (3 * Ms) ^ 2 = 3 * Ms := Real.sq_sqrt (by positivity)
  set δ := 1 / (8 * Real.sqrt (3 * Ms)) with hδdef
  set ρ := 1 / (3 + 240 * L1 * R) with hρdef
  have hδ : 0 < δ := by positivity
  have hρ : 0 < ρ := by positivity
  have hδ2 : δ ^ 2 * (192 * Ms) = 1 := by
    simp only [δ]; rw [div_pow, one_pow, mul_pow, hq2]; field_simp; ring
  set A0 := R ^ 2 / (4 * Δ) with hA0
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
  have hc : c = 4 + 240 * L1 * R := by simp only [c, ρ]; field_simp; ring
  have hup : Real.log (min sK cap) ≤ Real.log cap :=
    (Real.log_le_log_iff (lt_min hsK hcap) hcap).mpr (min_le_right _ _)
  set X := Real.sqrt (Δ / (L0 * R ^ 2))
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hX2 : X ^ 2 = Δ / (L0 * R ^ 2) := Real.sq_sqrt (by positivity)
  have hδX : δ ≤ X * s0 := by
    apply le_of_sq_le_sq' (by positivity)
    rw [mul_pow, hX2, hs02, hA0]
    have e : Δ / (L0 * R ^ 2) * (R ^ 2 / (4 * Δ)) = 1 / (4 * L0) := by field_simp
    rw [e]
    have : δ ^ 2 = 1 / (192 * Ms) := by rw [eq_div_iff (by positivity)]; linarith [hδ2]
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  set Y := 2 + (3 + 240 * L1 * R) * X
  have hY : 2 ≤ Y := by simp only [Y]; nlinarith [mul_nonneg hL1 hR.le]
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hratio : cap / min s0 cap ≤ Y := by
    rcases le_total s0 cap with hle | hle
    · rw [min_eq_left hle, div_le_iff₀ hs0]
      have : cap = (3 + 240 * L1 * R) * δ := by simp only [cap, ρ]; field_simp
      rw [this]
      have h1 : (3 + 240 * L1 * R) * δ ≤ (3 + 240 * L1 * R) * (X * s0) :=
        mul_le_mul_of_nonneg_left hδX (by positivity)
      simp only [Y]; nlinarith
    · rw [min_eq_right hle, div_self hcap.ne']; linarith
  have hlogdiff : Real.log cap - Real.log (min s0 cap) ≤ Real.log Y := by
    rw [← Real.log_div hcap.ne' (lt_min hs0 hcap).ne']
    exact (Real.log_le_log_iff (div_pos hcap (lt_min hs0 hcap)) (by linarith)).mpr hratio
  have hsKδ : sK / δ < 14 * Real.sqrt (Ms * R ^ 2 / ε) := by
    have hm : sK / δ = 8 * Real.sqrt (3 * Ms) * sK := by simp only [δ]; field_simp
    rw [hm]
    apply lt_of_sq_lt_sq' (by positivity)
    rw [mul_pow, mul_pow, mul_pow, hq2, hsK2, Real.sq_sqrt (by positivity)]
    have : A * ε < R ^ 2 := by rwa [lt_div_iff₀ hε] at hsmall
    have h1 : 8 ^ 2 * (3 * Ms) * A = 192 * Ms * A := by ring
    rw [h1, show (14 : ℝ) ^ 2 * (Ms * R ^ 2 / ε) = 196 * Ms * R ^ 2 / ε by ring,
      lt_div_iff₀ hε]
    nlinarith
  have hs0δ : 0 ≤ s0 / δ := by positivity
  have hcl : c * Real.log Y ≤ 3 / 4 * (6 + 320 * L1 * R) * Real.log Y := by
    rw [hc]; exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hL1 hR.le]) hlogY
  have hc0 : 0 ≤ c := by positivity
  have hmain : 3 / 4 * K < 14 * Real.sqrt (Ms * R ^ 2 / ε) + c * Real.log Y := by
    have h1 := mul_le_mul_of_nonneg_left hup hc0
    have h2 := mul_le_mul_of_nonneg_left hlogdiff hc0
    nlinarith
  have hsq0 : 0 ≤ Real.sqrt (Ms * R ^ 2 / ε) := Real.sqrt_nonneg _
  nlinarith

end OracleTemplate.GeneralizedSliding
