import LongTails.Proofs.NcConcaveRhoLip
import LongTails.Proofs.NcConcaveBlock
import LongTails.Proofs.NcConcaveGadgets

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveInstance

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions
open LongTails.Proofs.NcConcaveTransitionBounds LongTails.Proofs.NcConcavePsi
open LongTails.Proofs.NcConcavePartTwo LongTails.Proofs.NcConcaveHuber LongTails.Proofs.NcConcaveRhoLip
open LongTails.Proofs.NcConcaveBlock LongTails.Proofs.NcConcaveGadgets

variable {n m : ℕ}

noncomputable def psi0 (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) : ℝ :=
  hpart u + (1 / 2) * ∑ i, (a i - rho u i) ^ 2 + (1 / 2) * ∑ i, (b i - rb u i) ^ 2 +
    (1 / 2) * ∑ i, a i ^ 2 + (1 / 2) * ∑ i, b i ^ 2

noncomputable def baseF (τ : ℝ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ)
    (y : Fin n → Fin (m + 1) → ℝ) : ℝ :=
  psi0 u a b + ∑ i, blockVal τ (a i) (b i) (y i)

lemma psi_eq (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) :
    psi u a b = psi0 u a b + ∑ i, (a i - b i / 2) ^ 2 / 2 := by
  simp only [psi, psi0, Finset.mul_sum]
  rw [show (∑ i, 1 / 2 * (a i - b i / 2) ^ 2) = ∑ i, (a i - b i / 2) ^ 2 / 2 from
    Finset.sum_congr rfl fun i _ => by ring]

lemma baseF_le (τ : ℝ) (hτ : 0 < τ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ)
    (hb : ∀ i, |alpha m * b i / 2| ≤ τ) (y : Fin n → Fin (m + 1) → ℝ) :
    baseF τ u a b y ≤ psi u a b := by
  rw [psi_eq, baseF]
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => block_le (m := m) hτ (a i) (b i) (hb i) (y i))
  linarith

lemma baseF_star (τ : ℝ) (hτ : 0 < τ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ)
    (hb : ∀ i, |alpha m * b i / 2| ≤ τ) :
    baseF τ u a b (fun i => ystar (m := m) (a i) (b i)) = psi u a b := by
  rw [psi_eq, baseF]
  congr 1
  exact Finset.sum_congr rfl fun i _ => block_value_star hτ (a i) (b i) (hb i)

noncomputable def beta (θ s t : ℝ) : ℝ := zeta θ s * t + (s - zeta θ s) * zeta θ t

noncomputable def betaR (θ b x : ℝ) : ℝ := zeta θ b * rr x + (b - zeta θ b) * rr (zeta θ x)

noncomputable def zu (θ : ℝ) (u : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ := fun j => zeta θ (u j)

noncomputable def robP (θ : ℝ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) : ℝ :=
  -cη * u 0 - cη * ∑ j : Fin n, nu (zeta θ (u j.succ)) + cη / 2 * ∑ j, rr (zeta θ (u j)) ^ 2 +
    ∑ i, zeta θ (a i) ^ 2 - ∑ i, a i * rho (zu θ u) i + (1 / 2) * ∑ i, rho (zu θ u) i ^ 2 +
    ∑ i, zeta θ (b i) ^ 2 - ∑ i : Fin n, betaR θ (b i) (u i.succ) +
    (1 / 2) * ∑ i : Fin n, rr (zeta θ (u i.succ)) ^ 2

noncomputable def robB (θ τ : ℝ) (a b : ℝ) (y : Fin (m + 1) → ℝ) : ℝ :=
  -(alpha m ^ 2 / 2) * zeta θ (y 0) ^ 2 -
    ∑ k : Fin m, huber τ (zeta (2 * θ) (y k.castSucc - y k.succ)) +
    alpha m * beta θ a (y 0) - alpha m / 2 * beta θ b (y (Fin.last m)) -
    alpha m ^ 2 * m * zeta θ b ^ 2 / 8 -
    2 * alpha m * θ * (omega θ (y 0) + omega θ (y (Fin.last m)))

noncomputable def robF (θ τ : ℝ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ)
    (y : Fin n → Fin (m + 1) → ℝ) : ℝ :=
  robP θ u a b + ∑ i, robB θ τ (a i) (b i) (y i)

lemma zeta_sq_close {θ t : ℝ} (hθ : 0 < θ) : |zeta θ t ^ 2 - t ^ 2| ≤ 4 * θ * |t| + 4 * θ ^ 2 := by
  have h := zeta_sub_le (θ := θ) (t := t) hθ
  have e : zeta θ t ^ 2 - t ^ 2 = (zeta θ t - t) * (zeta θ t - t + 2 * t) := by ring
  rw [e, abs_mul]
  have h2 : |zeta θ t - t + 2 * t| ≤ 2 * θ + 2 * |t| := by
    calc _ ≤ |zeta θ t - t| + |2 * t| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul]; norm_num; linarith
  nlinarith [abs_nonneg (zeta θ t - t), abs_nonneg t]

lemma beta_close {θ s t : ℝ} (hθ : 0 < θ) : |beta θ s t - s * t| ≤ 4 * θ ^ 2 := by
  have e : beta θ s t - s * t = (s - zeta θ s) * (zeta θ t - t) := by simp only [beta]; ring
  rw [e, abs_mul]
  have h1 := zeta_sub_le (θ := θ) (t := s) hθ
  have h2 := zeta_sub_le (θ := θ) (t := t) hθ
  rw [abs_sub_comm] at h1
  nlinarith [abs_nonneg (s - zeta θ s), abs_nonneg (zeta θ t - t)]

lemma betaR_close {θ b x : ℝ} (hθ : 0 < θ) : |betaR θ b x - b * rr x| ≤ 4 * θ ^ 2 := by
  have e : betaR θ b x - b * rr x = (b - zeta θ b) * (rr (zeta θ x) - rr x) := by simp only [betaR]; ring
  rw [e, abs_mul]
  have h1 := zeta_sub_le (θ := θ) (t := b) hθ
  have h2 := (rr_lipschitz (zeta θ x) x).trans (zeta_sub_le (θ := θ) (t := x) hθ)
  rw [abs_sub_comm] at h1
  nlinarith [abs_nonneg (b - zeta θ b), abs_nonneg (rr (zeta θ x) - rr x)]

lemma lip_of_deriv {f f' : ℝ → ℝ} {C : ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hb : ∀ x, |f' x| ≤ C) (x y : ℝ) : |f x - f y| ≤ C * |x - y| := by
  rcases lt_trichotomy x y with h | h | h
  · obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope f f' h
      (fun t _ => (hf t).continuousAt.continuousWithinAt) (fun t _ => hf t)
    have hyx : 0 < y - x := by linarith
    have e : f x - f y = -(f' c * (y - x)) := by rw [hc]; field_simp; ring
    rw [e, abs_neg, abs_mul, abs_of_pos hyx, abs_sub_comm, abs_of_pos hyx]
    exact mul_le_mul_of_nonneg_right (hb c) hyx.le
  · subst h; simp
  · obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope f f' h
      (fun t _ => (hf t).continuousAt.continuousWithinAt) (fun t _ => hf t)
    have hxy : 0 < x - y := by linarith
    have e : f x - f y = f' c * (x - y) := by rw [hc]; field_simp
    rw [e, abs_mul, abs_of_pos hxy]
    exact mul_le_mul_of_nonneg_right (hb c) hxy.le

lemma nu_lipschitz (x y : ℝ) : |nu x - nu y| ≤ 3 / 2 * |x - y| :=
  lip_of_deriv nu_hasDerivAt (fun t => by rw [abs_of_nonneg (dnu_nonneg t)]; exact dnu_le t) x y

lemma nu_zeta_close {θ t : ℝ} (hθ : 0 < θ) : |nu (zeta θ t) - nu t| ≤ 3 * θ := by
  have h := nu_lipschitz (zeta θ t) t
  have hd := zeta_sub_le (θ := θ) (t := t) hθ
  linarith

lemma rr_sq_close {θ t : ℝ} (hθ : 0 < θ) : |rr (zeta θ t) ^ 2 - rr t ^ 2| ≤ 4 * θ * |t| + 4 * θ ^ 2 := by
  have h1 := (rr_lipschitz (zeta θ t) t).trans (zeta_sub_le (θ := θ) (t := t) hθ)
  have h2 := abs_rr_le t
  have e : rr (zeta θ t) ^ 2 - rr t ^ 2 = (rr (zeta θ t) - rr t) * (rr (zeta θ t) - rr t + 2 * rr t) := by
    ring
  rw [e, abs_mul]
  have h3 : |rr (zeta θ t) - rr t + 2 * rr t| ≤ 2 * θ + 2 * |t| := by
    calc _ ≤ |rr (zeta θ t) - rr t| + |2 * rr t| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul]; norm_num; linarith
  nlinarith [abs_nonneg (rr (zeta θ t) - rr t), abs_nonneg t]

lemma omega_le {θ t : ℝ} (hθ : 0 < θ) : 0 ≤ omega θ t ∧ omega θ t ≤ |t| := by
  rcases le_total 0 t with ht | ht
  · have hL := rampL_eq_zero hθ (by linarith : -θ ≤ t)
    have hb := (ramp_bounds (t / θ - 1)).2
    simp only [omega, hL, add_zero, rampR]
    have hR0 := rampR_nonneg θ t
    simp only [rampR] at hR0
    refine ⟨mul_nonneg hθ.le hR0, ?_⟩
    rw [abs_of_nonneg ht]
    rcases le_total 0 (t / θ - 1) with h | h
    · rw [max_eq_right h] at hb
      have : θ * (t / θ - 1) = t - θ := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hb hθ.le]
    · rw [max_eq_left h] at hb; nlinarith
  · have hR := rampR_eq_zero hθ (by linarith : t ≤ θ)
    have hb := (ramp_bounds (-t / θ - 1)).2
    simp only [omega, hR, zero_add, rampL]
    have hL0 := rampL_nonneg θ t
    simp only [rampL] at hL0
    refine ⟨mul_nonneg hθ.le hL0, ?_⟩
    rw [abs_of_nonpos ht]
    rcases le_total 0 (-t / θ - 1) with h | h
    · rw [max_eq_right h] at hb
      have : θ * (-t / θ - 1) = -t - θ := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hb hθ.le]
    · rw [max_eq_left h] at hb; nlinarith

lemma huber_lip {c : ℝ} (hc : 0 < c) (x y : ℝ) : |huber c x - huber c y| ≤ c * |x - y| :=
  lip_of_deriv (huber_hasDerivAt hc) (fun t => dhuber_abs hc.le t) x y

lemma sum_abs_bound {ι : Type*} [Fintype ι] (f : ι → ℝ) (B : ℝ) (h : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ Fintype.card ι * B := by
  calc |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, B := Finset.sum_le_sum fun i _ => h i
    _ = _ := by simp

lemma coord_le_of_sq {ι : Type*} [Fintype ι] (f : ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∑ i, f i ^ 2 ≤ B ^ 2) (i : ι) : |f i| ≤ B := by
  have h1 : f i ^ 2 ≤ ∑ j, f j ^ 2 :=
    Finset.single_le_sum (f := fun j => f j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have := h1.trans h
  rw [← sq_abs] at this
  exact abs_le_of_sq_le_sq' this hB |>.2 |> fun h => by
    have := abs_nonneg (f i); nlinarith [sq_nonneg (|f i| - B), sq_nonneg (|f i| + B)]

set_option maxHeartbeats 1000000 in
lemma robB_close {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (hτ2 : τ ≤ 2)
    (a b : ℝ) (hb : |b| ≤ 2) (y : Fin (m + 1) → ℝ) (Y : ℝ) (hY : ∀ k, |y k| ≤ Y) :
    |robB θ τ a b y - blockVal τ a b y| ≤ θ * (8 * (m + 1) + 12 * Y + 20) := by
  have hα := alpha_pos m
  have hα1 := alpha_le_one m
  have hα2 : alpha m ^ 2 * m ≤ 1 := by rw [alpha_sq]; rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hY0 : 0 ≤ Y := (abs_nonneg _).trans (hY 0)
  have t1 : |zeta θ (y 0) ^ 2 - y 0 ^ 2| ≤ 4 * θ * Y + 4 * θ ^ 2 := by
    have := zeta_sq_close (θ := θ) (t := y 0) hθ; nlinarith [hY 0]
  have t2 : |∑ k : Fin m, (huber τ (zeta (2 * θ) (y k.castSucc - y k.succ)) -
      huber τ (y k.castSucc - y k.succ))| ≤ m * (8 * θ) := by
    have := sum_abs_bound (fun k : Fin m => huber τ (zeta (2 * θ) (y k.castSucc - y k.succ)) -
      huber τ (y k.castSucc - y k.succ)) (8 * θ) (fun k => by
        have h1 := huber_lip hτ (zeta (2 * θ) (y k.castSucc - y k.succ)) (y k.castSucc - y k.succ)
        have h2 := zeta_sub_le (θ := 2 * θ) (t := y k.castSucc - y k.succ) (by linarith)
        nlinarith [abs_nonneg (zeta (2 * θ) (y k.castSucc - y k.succ) - (y k.castSucc - y k.succ))])
    simpa using this
  have t3 := beta_close (θ := θ) (s := a) (t := y 0) hθ
  have t4 := beta_close (θ := θ) (s := b) (t := y (Fin.last m)) hθ
  have t5 : |zeta θ b ^ 2 - b ^ 2| ≤ 8 * θ + 4 * θ ^ 2 := by
    have := zeta_sq_close (θ := θ) (t := b) hθ; nlinarith
  have t6 := omega_le (θ := θ) (t := y 0) hθ
  have t7 := omega_le (θ := θ) (t := y (Fin.last m)) hθ
  have e : robB θ τ a b y - blockVal τ a b y =
      -(alpha m ^ 2 / 2) * (zeta θ (y 0) ^ 2 - y 0 ^ 2) -
      ∑ k : Fin m, (huber τ (zeta (2 * θ) (y k.castSucc - y k.succ)) - huber τ (y k.castSucc - y k.succ)) +
      alpha m * (beta θ a (y 0) - a * y 0) - alpha m / 2 * (beta θ b (y (Fin.last m)) - b * y (Fin.last m)) -
      alpha m ^ 2 * m / 8 * (zeta θ b ^ 2 - b ^ 2) -
      2 * alpha m * θ * (omega θ (y 0) + omega θ (y (Fin.last m))) := by
    simp only [robB, blockVal, Finset.sum_sub_distrib]; ring
  rw [e]
  have hyl := hY (Fin.last m)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have bound1 : |-(alpha m ^ 2 / 2) * (zeta θ (y 0) ^ 2 - y 0 ^ 2)| ≤ 4 * θ * Y + 4 * θ ^ 2 := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity)]
    have : alpha m ^ 2 / 2 ≤ 1 := by nlinarith
    nlinarith [abs_nonneg (zeta θ (y 0) ^ 2 - y 0 ^ 2)]
  have bound3 : |alpha m * (beta θ a (y 0) - a * y 0)| ≤ 4 * θ ^ 2 := by
    rw [abs_mul, abs_of_pos hα]; nlinarith [abs_nonneg (beta θ a (y 0) - a * y 0)]
  have bound4 : |alpha m / 2 * (beta θ b (y (Fin.last m)) - b * y (Fin.last m))| ≤ 4 * θ ^ 2 := by
    rw [abs_mul, abs_of_pos (by positivity)]
    nlinarith [abs_nonneg (beta θ b (y (Fin.last m)) - b * y (Fin.last m))]
  have bound5 : |alpha m ^ 2 * m / 8 * (zeta θ b ^ 2 - b ^ 2)| ≤ 8 * θ + 4 * θ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have : alpha m ^ 2 * m / 8 ≤ 1 := by linarith
    nlinarith [abs_nonneg (zeta θ b ^ 2 - b ^ 2)]
  have bound6 : |2 * alpha m * θ * (omega θ (y 0) + omega θ (y (Fin.last m)))| ≤ 4 * θ * Y := by
    rw [abs_of_nonneg (mul_nonneg (by positivity) (add_nonneg t6.1 t7.1))]
    have h1 : omega θ (y 0) + omega θ (y (Fin.last m)) ≤ 2 * Y := by linarith [t6.2, t7.2, hY 0]
    have hαθ : 0 ≤ 2 * alpha m * θ := by positivity
    calc 2 * alpha m * θ * (omega θ (y 0) + omega θ (y (Fin.last m))) ≤ 2 * alpha m * θ * (2 * Y) :=
          mul_le_mul_of_nonneg_left h1 hαθ
      _ ≤ 4 * θ * Y := by nlinarith [mul_nonneg hθ.le hY0]
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have c1 := abs_le.mp bound1
  have c2 := abs_le.mp t2
  have c3 := abs_le.mp bound3
  have c4 := abs_le.mp bound4
  have c5 := abs_le.mp bound5
  have c6 := abs_le.mp bound6
  rw [abs_le]
  constructor <;> linarith [c1.1, c1.2, c2.1, c2.2, c3.1, c3.2, c4.1, c4.2, c5.1, c5.2, c6.1, c6.2,
    mul_nonneg hθ.le hY0, mul_nonneg hθ.le hm0]

lemma rho_close_parts {θ : ℝ} (hθ : 0 < θ) (u : Fin (n + 1) → ℝ) (a : Fin n → ℝ)
    (ha : ∀ i, |a i| ≤ 2) :
    |∑ i, a i * rho (zu θ u) i - ∑ i, a i * rho u i| ≤ 12 * θ * (n + 1) ^ 2 ∧
      |(1 / 2) * ∑ i, rho (zu θ u) i ^ 2 - (1 / 2) * ∑ i, rho u i ^ 2| ≤ 6 * θ * (n + 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hrl := rho_lipschitz u (zu θ u)
  have hzu : sq1 (fun j => zu θ u j - u j) ≤ (n + 1) * (2 * θ) ^ 2 := by
    have := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
      (by
        have h := zeta_sub_le (θ := θ) (t := u j) hθ
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2 :
        (zu θ u j - u j) ^ 2 ≤ (2 * θ) ^ 2))
    simpa [sq1, zu] using this
  have hdr : sq2 (fun i => rho (zu θ u) i - rho u i) ≤ 9 * ((n + 1) * (2 * θ) ^ 2) := by linarith
  set dr : Fin n → ℝ := fun i => rho (zu θ u) i - rho u i
  have hsdr : Real.sqrt (sq2 dr) ≤ 6 * θ * Real.sqrt (n + 1) := by
    rw [show 6 * θ * Real.sqrt (n + 1) = Real.sqrt ((6 * θ) ^ 2 * (n + 1)) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsq : Real.sqrt (n + 1) ≤ n + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hsa : Real.sqrt (sq2 a) ≤ 2 * Real.sqrt n := by
    rw [show 2 * Real.sqrt n = Real.sqrt (2 ^ 2 * n) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have := sum_abs_bound (fun i => a i ^ 2) 4 (fun i => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; nlinarith [ha i, abs_nonneg (a i)])
    simp only [Fintype.card_fin] at this
    have h0 : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [abs_of_nonneg h0] at this
    unfold sq2; linarith
  have hsqn : Real.sqrt n ≤ n + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hrho1 : |∑ i, a i * rho (zu θ u) i - ∑ i, a i * rho u i| ≤ 12 * θ * (n + 1) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    have e : ∑ i, (a i * rho (zu θ u) i - a i * rho u i) = ∑ i, a i * dr i :=
      Finset.sum_congr rfl fun i _ => by simp only [dr]; ring
    rw [e]
    calc _ ≤ Real.sqrt (sq2 a) * Real.sqrt (sq2 dr) := cs_bound a dr
      _ ≤ (2 * Real.sqrt n) * (6 * θ * Real.sqrt (n + 1)) :=
          mul_le_mul hsa hsdr (Real.sqrt_nonneg _) (by positivity)
      _ ≤ (2 * (n + 1)) * (6 * θ * (n + 1)) :=
          mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity)
            (by positivity)
      _ = 12 * θ * (n + 1) ^ 2 := by ring
  have hrho2 : |(1 / 2) * ∑ i, rho (zu θ u) i ^ 2 - (1 / 2) * ∑ i, rho u i ^ 2| ≤ 6 * θ * (n + 1) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    have e : ∑ i, (rho (zu θ u) i ^ 2 - rho u i ^ 2) = ∑ i, dr i * (rho (zu θ u) i + rho u i) :=
      Finset.sum_congr rfl fun i _ => by simp only [dr]; ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hs : Real.sqrt (sq2 fun i => rho (zu θ u) i + rho u i) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      have h1 := sq2_rho_le_one (zu θ u)
      have h2 := sq2_rho_le_one u
      have : sq2 (fun i => rho (zu θ u) i + rho u i) ≤ 2 * sq2 (rho (zu θ u)) + 2 * sq2 (rho u) := by
        unfold sq2; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (rho (zu θ u) i - rho u i)]
      linarith
    have := cs_bound dr (fun i => rho (zu θ u) i + rho u i)
    nlinarith [Real.sqrt_nonneg (sq2 dr), Real.sqrt_nonneg (sq2 fun i => rho (zu θ u) i + rho u i),
      mul_le_mul hsdr hs (Real.sqrt_nonneg _) (by positivity)]
  exact ⟨hrho1, hrho2⟩

lemma robP_sub_eq (θ : ℝ) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) :
    robP θ u a b - psi0 u a b =
      -cη * ∑ j : Fin n, (nu (zeta θ (u j.succ)) - nu (u j.succ)) +
      cη / 2 * ∑ j : Fin (n + 1), (rr (zeta θ (u j)) ^ 2 - rr (u j) ^ 2) +
      ∑ i : Fin n, (zeta θ (a i) ^ 2 - a i ^ 2) -
      (∑ i, a i * rho (zu θ u) i - ∑ i, a i * rho u i) +
      ((1 / 2) * ∑ i, rho (zu θ u) i ^ 2 - (1 / 2) * ∑ i, rho u i ^ 2) +
      ∑ i : Fin n, (zeta θ (b i) ^ 2 - b i ^ 2) -
      ∑ i : Fin n, (betaR θ (b i) (u i.succ) - b i * rb u i) +
      (1 / 2) * ∑ i : Fin n, (rr (zeta θ (u i.succ)) ^ 2 - rr (u i.succ) ^ 2) := by
  have hA : (1 / 2) * ∑ i, (a i - rho u i) ^ 2 + (1 / 2) * ∑ i, a i ^ 2 =
      ∑ i, a i ^ 2 - ∑ i, a i * rho u i + (1 / 2) * ∑ i, rho u i ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hB : (1 / 2) * ∑ i, (b i - rb u i) ^ 2 + (1 / 2) * ∑ i, b i ^ 2 =
      ∑ i, b i ^ 2 - ∑ i, b i * rb u i + (1 / 2) * ∑ i : Fin n, rr (u i.succ) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [rb]; ring
  have hp : psi0 u a b = hpart u + (∑ i, a i ^ 2 - ∑ i, a i * rho u i + (1 / 2) * ∑ i, rho u i ^ 2) +
      (∑ i, b i ^ 2 - ∑ i, b i * rb u i + (1 / 2) * ∑ i : Fin n, rr (u i.succ) ^ 2) := by
    rw [← hA, ← hB]; unfold psi0; ring
  have e : robP θ u a b - psi0 u a b =
      -cη * ∑ j : Fin n, (nu (zeta θ (u j.succ)) - nu (u j.succ)) +
      cη / 2 * ∑ j : Fin (n + 1), (rr (zeta θ (u j)) ^ 2 - rr (u j) ^ 2) +
      ∑ i : Fin n, (zeta θ (a i) ^ 2 - a i ^ 2) -
      (∑ i, a i * rho (zu θ u) i - ∑ i, a i * rho u i) +
      ((1 / 2) * ∑ i, rho (zu θ u) i ^ 2 - (1 / 2) * ∑ i, rho u i ^ 2) +
      ∑ i : Fin n, (zeta θ (b i) ^ 2 - b i ^ 2) -
      ∑ i : Fin n, (betaR θ (b i) (u i.succ) - b i * rb u i) +
      (1 / 2) * ∑ i : Fin n, (rr (zeta θ (u i.succ)) ^ 2 - rr (u i.succ) ^ 2) := by
    rw [hp]
    unfold robP hpart
    simp only [Finset.sum_sub_distrib]
    ring
  exact e

lemma robP_close {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ)
    (U : ℝ) (hU : ∀ j, |u j| ≤ U) (ha : ∀ i, |a i| ≤ 2) (hb : ∀ i, |b i| ≤ 2) :
    |robP θ u a b - psi0 u a b| ≤ θ * (cη * (n + 1) * (5 + 2 * U) + (n + 1) ^ 2 * (50 + 4 * U)) := by
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨hrho1, hrho2⟩ := rho_close_parts hθ u a ha
  have s1 := sum_abs_bound (fun j : Fin n => nu (zeta θ (u j.succ)) - nu (u j.succ)) (3 * θ)
    (fun j => nu_zeta_close hθ)
  have s2 := sum_abs_bound (fun j : Fin (n + 1) => rr (zeta θ (u j)) ^ 2 - rr (u j) ^ 2)
    (4 * θ * U + 4 * θ ^ 2) (fun j => (rr_sq_close hθ).trans (by nlinarith [hU j]))
  have s3 := sum_abs_bound (fun i : Fin n => zeta θ (a i) ^ 2 - a i ^ 2) (8 * θ + 4 * θ ^ 2)
    (fun i => (zeta_sq_close hθ).trans (by nlinarith [ha i]))
  have s4 := sum_abs_bound (fun i : Fin n => zeta θ (b i) ^ 2 - b i ^ 2) (8 * θ + 4 * θ ^ 2)
    (fun i => (zeta_sq_close hθ).trans (by nlinarith [hb i]))
  have s5 := sum_abs_bound (fun i : Fin n => betaR θ (b i) (u i.succ) - b i * rb u i) (4 * θ ^ 2)
    (fun i => betaR_close hθ)
  have s6 := sum_abs_bound (fun i : Fin n => rr (zeta θ (u i.succ)) ^ 2 - rr (u i.succ) ^ 2)
    (4 * θ * U + 4 * θ ^ 2) (fun i => (rr_sq_close hθ).trans (by nlinarith [hU i.succ]))
  simp only [Fintype.card_fin] at s1 s2 s3 s4 s5 s6
  have e := robP_sub_eq θ u a b
  rw [e]
  have hc : (0 : ℝ) < cη := by norm_num [cη]
  have c1 := abs_le.mp s1; have c2 := abs_le.mp s2; have c3 := abs_le.mp s3
  have c4 := abs_le.mp s4; have c5 := abs_le.mp s5; have c6 := abs_le.mp s6
  have c7 := abs_le.mp hrho1; have c8 := abs_le.mp hrho2
  have hc' : cη = 10000 := rfl
  rw [hc']
  have p1 := mul_le_mul_of_nonneg_right hθ2 hn
  have p2 := mul_nonneg (mul_nonneg hθ.le hn) hn
  have p3 := mul_nonneg hθ.le hU0
  have p4 := mul_nonneg (mul_nonneg hθ.le hU0) hn
  have p5 := mul_nonneg (mul_nonneg (mul_nonneg hθ.le hU0) hn) hn
  have p6 := mul_nonneg hθ.le hn
  push_cast at c1 c2 c3 c4 c5 c6
  have p7 := mul_le_mul_of_nonneg_right hθ2 (by linarith : (0 : ℝ) ≤ n + 1)
  rw [abs_le]
  constructor <;> linarith [c1.1, c1.2, c2.1, c2.2, c3.1, c3.2, c4.1, c4.2, c5.1, c5.2, c6.1, c6.2,
    c7.1, c7.2, c8.1, c8.2]

noncomputable def closeBound (n m : ℕ) (U Y : ℝ) : ℝ :=
  cη * (n + 1) * (5 + 2 * U) + (n + 1) ^ 2 * (50 + 4 * U) + n * (8 * (m + 1) + 12 * Y + 20)

theorem robF_close {θ τ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ) (hτ2 : τ ≤ 2)
    (u : Fin (n + 1) → ℝ) (a b : Fin n → ℝ) (y : Fin n → Fin (m + 1) → ℝ) (U Y : ℝ)
    (hU : ∀ j, |u j| ≤ U) (ha : ∀ i, |a i| ≤ 2) (hb : ∀ i, |b i| ≤ 2) (hY : ∀ i k, |y i k| ≤ Y) :
    |robF θ τ u a b y - baseF τ u a b y| ≤ θ * closeBound n m U Y := by
  have h1 := robP_close hθ hθ1 u a b U hU ha hb
  have h2 := sum_abs_bound (fun i => robB θ τ (a i) (b i) (y i) - blockVal τ (a i) (b i) (y i))
    (θ * (8 * (m + 1) + 12 * Y + 20)) (fun i => robB_close hθ hθ1 hτ hτ2 (a i) (b i) (hb i) (y i) Y (hY i))
  simp only [Fintype.card_fin] at h2
  have e : robF θ τ u a b y - baseF τ u a b y = (robP θ u a b - psi0 u a b) +
      ∑ i, (robB θ τ (a i) (b i) (y i) - blockVal τ (a i) (b i) (y i)) := by
    simp only [robF, baseF, Finset.sum_sub_distrib]; ring
  rw [e]
  calc _ ≤ |robP θ u a b - psi0 u a b| + |∑ i, (robB θ τ (a i) (b i) (y i) - blockVal τ (a i) (b i) (y i))| :=
        abs_add_le _ _
    _ ≤ _ := by unfold closeBound; nlinarith

end LongTails.Proofs.NcConcaveInstance
