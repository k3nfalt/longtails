import LongTails.Proofs.NsgdWindow
import LongTails.Proofs.NsgdAverage

namespace LongTails.Proofs.NsgdRegime

open MeasureTheory ProbabilityTheory
open LongTails.Proofs.SeparationInstance LongTails.Proofs.SeparationTrajectory
open LongTails.Proofs.GaussianBlocks LongTails.Proofs.NsgdProcess LongTails.Proofs.NsgdBounds
open LongTails.Proofs.NsgdWindow LongTails.Proofs.NsgdAverage
open scoped NNReal

section

variable {r : ℕ} {ℓ c s η : ℝ} {φ : FlatShape} {B : ℕ}

local notation "S" => state r ℓ c s η φ B
local notation "M" => mart (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B)
local notation "Dv" => dev (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B)

variable (hB : 0 < B)

include hB in
lemma mart_sq_eq (t n : ℕ) :
    (∫ ξ, M t n ξ ^ 2 ∂stdStream) = ∑ i ∈ Finset.range n, ∫ ξ, Dv (t + i) ξ ^ 2 ∂stdStream := by
  induction n with
  | zero => simp [mart]
  | succ n ih => rw [mart_sq_succ hB, ih, Finset.sum_range_succ]

variable (hs : 0 < s) (hc : 0 ≤ c) (hℓ : 0 ≤ ℓ)
  (hb : Real.sqrt (r - 1 : ℕ) * c ≤ Real.sqrt (s ^ 2 / B) / 4)

include hB hs hc hℓ hb in
lemma window_lower (hη : 0 ≤ η) (t k : ℕ) (hk : 1 ≤ k) :
    η * Real.sqrt k / 60 - η * (6 / 7 * ℓ / Real.sqrt (s ^ 2 / B)) *
        ∑ i ∈ Finset.range k, (∫ ξ, |(S ξ (t + i)).1| ∂stdStream) ≤
      (∫ ξ, |(S ξ t).1| ∂stdStream) + ∫ ξ, |(S ξ (t + k)).1| ∂stdStream := by
  set σ := Real.sqrt (s ^ 2 / B) with hσdef
  have hσ : 0 < σ := by
    have : (0 : ℝ) < B := by exact_mod_cast hB
    exact Real.sqrt_pos.mpr (by positivity)
  set m : ℕ → ℝ := fun j => ∫ ξ, |(S ξ j).1| ∂stdStream with hmdef
  have hm0 (j : ℕ) : 0 ≤ m j := integral_nonneg fun _ => abs_nonneg _
  have hpt (ξ : ℕ → ℝ) : η * |M t k ξ| ≤ |(S ξ t).1| + |(S ξ (t + k)).1| +
      η * ∑ i ∈ Finset.range k, (4 / 5 * ℓ / σ) * |(S ξ (t + i)).1| := by
    have hw := window_identity (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B)
      t k ξ
    have hA : |∑ i ∈ Finset.range k, meanStep r ℓ c s φ B (S ξ (t + i))| ≤
        ∑ i ∈ Finset.range k, (4 / 5 * ℓ / σ) * |(S ξ (t + i)).1| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      have h := meanStep_bound hB hs (r := r) (ℓ := ℓ) (c := c) (φ := φ) (S ξ (t + i))
      rw [abs_mul, abs_of_nonneg hℓ] at h
      calc |meanStep r ℓ c s φ B (S ξ (t + i))| ≤ 4 / 5 * (ℓ * |(S ξ (t + i)).1|) / σ := h
        _ = 4 / 5 * ℓ / σ * |(S ξ (t + i)).1| := by ring
    have he : η * M t k ξ = (S ξ t).1 - (S ξ (t + k)).1 -
        η * ∑ i ∈ Finset.range k, meanStep r ℓ c s φ B (S ξ (t + i)) := by
      rw [hw]; ring
    calc η * |M t k ξ| = |η * M t k ξ| := by rw [abs_mul, abs_of_nonneg hη]
      _ ≤ |(S ξ t).1| + |(S ξ (t + k)).1| +
          η * |∑ i ∈ Finset.range k, meanStep r ℓ c s φ B (S ξ (t + i))| := by
        rw [he]
        have h1 := abs_sub ((S ξ t).1 - (S ξ (t + k)).1)
          (η * ∑ i ∈ Finset.range k, meanStep r ℓ c s φ B (S ξ (t + i)))
        have h2 := abs_sub (S ξ t).1 (S ξ (t + k)).1
        rw [abs_mul, abs_of_nonneg hη] at h1
        linarith
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hA hη
        linarith
  have hiS (j : ℕ) : Integrable (fun ξ => |(S ξ j).1|) stdStream := integrable_state_abs hη j
  have hMm : Measurable (M t k) := measurable_mart t k
  have hMi : Integrable (fun ξ => |M t k ξ|) stdStream :=
    integrable_of_bound hMm.abs (C := 2 * k) fun ξ => by
      rw [abs_abs]; exact abs_mart_le t k ξ
  have hint1 : η * (∫ ξ, |M t k ξ| ∂stdStream) ≤ m t + m (t + k) +
      η * ∑ i ∈ Finset.range k, (4 / 5 * ℓ / σ) * m (t + i) := by
    rw [← integral_const_mul]
    have hiS2 : Integrable (fun ξ => |(S ξ t).1| + |(S ξ (t + k)).1|) stdStream :=
      (hiS t).add (hiS (t + k))
    have hiSum : Integrable (fun ξ => η * ∑ i ∈ Finset.range k,
        (4 / 5 * ℓ / σ) * |(S ξ (t + i)).1|) stdStream :=
      (integrable_finsetSum _ fun i _ => (hiS (t + i)).const_mul _).const_mul η
    have hR : Integrable (fun ξ => |(S ξ t).1| + |(S ξ (t + k)).1| +
        η * ∑ i ∈ Finset.range k, (4 / 5 * ℓ / σ) * |(S ξ (t + i)).1|) stdStream :=
      hiS2.add hiSum
    refine (integral_mono (hMi.const_mul η) hR hpt).trans (le_of_eq ?_)
    rw [integral_add hiS2 hiSum, integral_add (hiS t) (hiS (t + k)), integral_const_mul,
      integral_finsetSum _ fun i _ => (hiS (t + i)).const_mul _]
    simp only [integral_const_mul, hmdef]
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set a := 15 * Real.sqrt k with hadef
  have hsk : 1 ≤ Real.sqrt k := by rw [Real.one_le_sqrt]; exact hk0
  have hsk2 : Real.sqrt k ^ 2 = k := Real.sq_sqrt (by positivity)
  have ha : 0 < a := by positivity
  have hM2i : Integrable (fun ξ => M t k ξ ^ 2) stdStream :=
    integrable_of_bound (hMm.pow_const 2) (C := (2 * k) ^ 2) fun ξ => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_mart_le t k ξ) 2
  have hM4i : Integrable (fun ξ => M t k ξ ^ 4) stdStream :=
    integrable_of_bound (hMm.pow_const 4) (C := (2 * k) ^ 4) fun ξ => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_mart_le t k ξ) 4
  have hquart : (∫ ξ, M t k ξ ^ 2 ∂stdStream) / a - (∫ ξ, M t k ξ ^ 4 ∂stdStream) / (4 * a ^ 3) ≤
      ∫ ξ, |M t k ξ| ∂stdStream := by
    rw [← integral_div, ← integral_div, ← integral_sub (hM2i.div_const _) (hM4i.div_const _)]
    exact integral_mono ((hM2i.div_const _).sub (hM4i.div_const _)) hMi
      (fun ξ => abs_ge_quartic ha (M t k ξ))
  have hsq : (2 / 5 * k - 4 / 5 * ℓ / σ * ∑ i ∈ Finset.range k, m (t + i)) ≤
      ∫ ξ, M t k ξ ^ 2 ∂stdStream := by
    rw [mart_sq_eq hB]
    have h := Finset.sum_le_sum (s := Finset.range k) fun i _ =>
      dev_sq_lower hB hs hc hℓ hb (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ)
        (t + i) hη
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum, ← hσdef] at h
    have h' : (∑ i ∈ Finset.range k, ∫ ξ, |(S ξ (t + i)).1| ∂stdStream) =
        ∑ i ∈ Finset.range k, m (t + i) := rfl
    rw [h'] at h
    linarith
  have h4 := mart_fourth_le hB (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) t k
  set Sk := ∑ i ∈ Finset.range k, m (t + i) with hSkd
  have hSk0 : 0 ≤ Sk := Finset.sum_nonneg fun i _ => hm0 _
  have hsum4 : ∑ i ∈ Finset.range k, (4 / 5 * ℓ / σ) * m (t + i) = 4 / 5 * ℓ / σ * Sk := by
    rw [hSkd, Finset.mul_sum]
  rw [hsum4] at hint1
  set q := ℓ / σ with hq
  have hq0 : 0 ≤ q := div_nonneg hℓ hσ.le
  have e1 : 4 / 5 * ℓ / σ = 4 / 5 * q := by rw [hq]; ring
  have e2 : 6 / 7 * ℓ / σ = 6 / 7 * q := by rw [hq]; ring
  rw [e1] at hint1 hsq
  rw [e2]
  set R := Real.sqrt k with hR
  have hka : (k : ℝ) = R ^ 2 := hsk2.symm
  have hEM : R / 60 - 4 / 5 * q * Sk * (1 / 15) ≤ ∫ ξ, |M t k ξ| ∂stdStream := by
    have hA2 : (2 / 5 * k - 4 / 5 * q * Sk) / a ≤ (∫ ξ, M t k ξ ^ 2 ∂stdStream) / a :=
      div_le_div_of_nonneg_right hsq ha.le
    have hA4 : (∫ ξ, M t k ξ ^ 4 ∂stdStream) / (4 * a ^ 3) ≤ 112 * k ^ 2 / (4 * a ^ 3) :=
      div_le_div_of_nonneg_right h4 (by positivity)
    have hval : (2 / 5 * k - 4 / 5 * q * Sk) / a - 112 * k ^ 2 / (4 * a ^ 3) =
        2 / 75 * R - 112 / 13500 * R - 4 / 5 * q * Sk / (15 * R) := by
      rw [hadef, hka]
      have hR0 : R ≠ 0 := by positivity
      field_simp
      ring
    have hfrac : 4 / 5 * q * Sk / (15 * R) ≤ 4 / 5 * q * Sk * (1 / 15) := by
      rw [div_le_iff₀ (by positivity)]
      have : 0 ≤ 4 / 5 * q * Sk := by positivity
      nlinarith
    have hR1 : 0 ≤ R := by positivity
    nlinarith
  have := mul_le_mul_of_nonneg_left hEM hη
  nlinarith [mul_nonneg hη (mul_nonneg hq0 hSk0)]

include hB hs hc hℓ hb in
set_option maxHeartbeats 1000000 in
lemma nsgd_scalar_bound {ε θ : ℝ} {T : ℕ} (hℓp : 0 < ℓ) (hcp : 0 < c) (hη : 0 < η)
    (hε : 0 < ε) (hr : 2 ≤ r) (hθ : 0 < θ) (hfar : ∀ y ≤ θ, φ.slope y ≤ -(1 / 2))
    (hRc : 4 * ε ≤ (r - 1 : ℕ) * c)
    (hF3 : 4 * c * (2 + Real.log (Real.sqrt (s ^ 2 / B) / (Real.sqrt (r - 1 : ℕ) * c / 2))) ≤
      θ * ℓ)
    (hsucc : (∑ t ∈ Finset.range (T + 1), ∫ ξ, (|ℓ * (S ξ t).1| +
        (r - 1 : ℕ) * |c * φ.slope (S ξ t).2|) ∂stdStream) ≤ (T + 1) * ε) :
    θ * ℓ * (s ^ 2 / B) ≤ 490000 * ε ^ 2 * c *
      (2 + Real.log (Real.sqrt (s ^ 2 / B) / (Real.sqrt (r - 1 : ℕ) * c / 2))) * T := by
  set σ := Real.sqrt (s ^ 2 / B) with hσdef
  set Λ := 2 + Real.log (σ / (Real.sqrt (r - 1 : ℕ) * c / 2)) with hΛdef
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hσ : 0 < σ := Real.sqrt_pos.mpr (by positivity)
  have hσsq : σ ^ 2 = s ^ 2 / B := Real.sq_sqrt (by positivity)
  have hr1 : (1 : ℝ) ≤ (r - 1 : ℕ) := by
    have : 1 ≤ r - 1 := by omega
    exact_mod_cast this
  have hsr : 0 < Real.sqrt ((r - 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < Real.sqrt (r - 1 : ℕ) * c / 2 := by positivity
  have hb0σ : Real.sqrt (r - 1 : ℕ) * c / 2 ≤ σ := by linarith
  have hΛ : 0 < Λ := by
    have h8 : 1 ≤ σ / (Real.sqrt (r - 1 : ℕ) * c / 2) := by
      rw [le_div_iff₀ hb0]; linarith
    have := Real.log_nonneg h8
    linarith
  set m : ℕ → ℝ := fun j => ∫ ξ, |(S ξ j).1| ∂stdStream with hmdef
  have hm0 (j : ℕ) : 0 ≤ m j := integral_nonneg fun _ => abs_nonneg _
  have hslope : Measurable φ.slope := φ.continuous_slope.measurable
  have hiS (j : ℕ) : Integrable (fun ξ => |(S ξ j).1|) stdStream := integrable_state_abs hη.le j
  set R : ℝ := ((r - 1 : ℕ) : ℝ) with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hflat_m (t : ℕ) : Measurable (fun ξ => R * |c * φ.slope (S ξ t).2|) :=
    measurable_const.mul ((measurable_const.mul
      (hslope.comp (measurable_state r ℓ c s η φ B t).snd)).abs)
  have hflat_i (t : ℕ) : Integrable (fun ξ => R * |c * φ.slope (S ξ t).2|) stdStream :=
    integrable_of_bound (hflat_m t) (C := R * c) fun ξ => by
      rw [abs_of_nonneg (mul_nonneg hR0 (abs_nonneg _)), abs_mul, abs_of_pos hcp]
      have h1 := φ.bounded (S ξ t).2
      have h2 : c * |φ.slope (S ξ t).2| ≤ c := by nlinarith
      exact mul_le_mul_of_nonneg_left h2 hR0
  set F : ℕ → ℝ := fun t => ∫ ξ, R * |c * φ.slope (S ξ t).2| ∂stdStream with hFdef
  have hF0 (t : ℕ) : 0 ≤ F t := integral_nonneg fun _ => mul_nonneg hR0 (abs_nonneg _)
  have hsplit (t : ℕ) : (∫ ξ, (|ℓ * (S ξ t).1| + R * |c * φ.slope (S ξ t).2|) ∂stdStream) =
      ℓ * m t + F t := by
    simp_rw [abs_mul ℓ, abs_of_pos hℓp]
    rw [integral_add ((hiS t).const_mul ℓ) (hflat_i t), integral_const_mul]
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum] at hsucc
  set Sm := ∑ t ∈ Finset.range (T + 1), m t with hSm
  set SF := ∑ t ∈ Finset.range (T + 1), F t with hSF
  have hSF0 : 0 ≤ SF := Finset.sum_nonneg fun t _ => hF0 t
  have hT1 : (0 : ℝ) < T + 1 := by positivity
  set μ := Sm / (T + 1) with hμdef
  have hμ0 : 0 ≤ μ := div_nonneg (Finset.sum_nonneg fun t _ => hm0 t) hT1.le
  have hSmμ : Sm = (T + 1) * μ := by rw [hμdef]; field_simp
  have hst : ℓ * μ ≤ ε := by
    rw [hμdef, mul_div_assoc', div_le_iff₀ hT1]
    linarith
  have hkick : 1 ≤ T → 7 / 50 * η ≤ μ := by
    intro hT
    have hk := Finset.sum_le_sum (s := Finset.range T) fun t _ =>
      kick hB hs hc hb (r := r) (ℓ := ℓ) (φ := φ) hη.le t
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib] at hk
    have h1 : ∑ t ∈ Finset.range T, m t ≤ Sm :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun j _ _ => hm0 j)
    have h2 : ∑ t ∈ Finset.range T, m (t + 1) ≤ Sm := shifted_le hm0 (by omega)
    have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
    rw [hSmμ] at h1 h2
    nlinarith
  have hwin : ∀ k : ℕ, 1 ≤ k → 2 * k ≤ T + 1 →
      η * Real.sqrt k / 120 ≤ μ * (2 + 6 / 7 * (η * ℓ / σ) * k) := by
    intro k hk1 hk2
    have hq : 0 ≤ η * (6 / 7 * ℓ / σ) := by positivity
    have hav := window_average hm0 (T := T) (k := k) (by omega) hq
      (A := η * Real.sqrt k / 60) fun t _ =>
        window_lower hB hs hc hℓ hb (r := r) (φ := φ) hη.le t k hk1
    have hcast : ((T + 1 - k : ℕ) : ℝ) = (T : ℝ) + 1 - k := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hcast, ← hSm, hSmμ] at hav
    have hhalf : ((T : ℝ) + 1) / 2 ≤ (T : ℝ) + 1 - k := by
      have : (2 * k : ℝ) ≤ T + 1 := by exact_mod_cast hk2
      linarith
    have hA0 : 0 ≤ η * Real.sqrt k / 60 := by positivity
    have h1 : ((T : ℝ) + 1) / 2 * (η * Real.sqrt k / 60) ≤
        (2 + η * (6 / 7 * ℓ / σ) * k) * ((T + 1) * μ) :=
      (mul_le_mul_of_nonneg_right hhalf hA0).trans hav
    have he : η * (6 / 7 * ℓ / σ) * k = 6 / 7 * (η * ℓ / σ) * k := by ring
    rw [he] at h1
    nlinarith
  have hgood_le : ∫ ξ, goodInd r ℓ c s η φ B θ T ξ ∂stdStream ≤ 1 / 2 := by
    have hpt (t : ℕ) (ht : t ≤ T) (ξ : ℕ → ℝ) :
        goodInd r ℓ c s η φ B θ T ξ * (R * c / 2) ≤ R * |c * φ.slope (S ξ t).2| := by
      classical
      unfold goodInd
      split_ifs with hg
      · have hy := hfar _ (hg t ht)
        rw [one_mul, abs_mul, abs_of_pos hcp, abs_of_neg (by linarith)]
        nlinarith
      · rw [zero_mul]; exact mul_nonneg hR0 (abs_nonneg _)
    have hgi : Integrable (fun ξ => goodInd r ℓ c s η φ B θ T ξ) stdStream :=
      integrable_of_bound (measurable_good θ T) (C := 1) fun ξ => by
        unfold goodInd; split_ifs <;> simp
    have hsum : (T + 1) * ((∫ ξ, goodInd r ℓ c s η φ B θ T ξ ∂stdStream) * (R * c / 2)) ≤ SF := by
      have := Finset.sum_le_sum (s := Finset.range (T + 1)) fun t ht =>
        integral_mono (hgi.mul_const (R * c / 2)) (hflat_i t)
          (hpt t (by simp only [Finset.mem_range] at ht; omega))
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_mul_const] at this
      push_cast at this
      exact this
    have hSFε : SF ≤ (T + 1) * ε := by
      have : 0 ≤ ℓ * Sm := mul_nonneg hℓ (Finset.sum_nonneg fun t _ => hm0 t)
      linarith
    have hRc' : 4 * ε ≤ R * c := hRc
    have hg0 : 0 ≤ ∫ ξ, goodInd r ℓ c s η φ B θ T ξ ∂stdStream :=
      integral_nonneg fun ξ => by unfold goodInd; split_ifs <;> norm_num
    by_contra hcon
    push Not at hcon
    have : (T + 1) * (1 / 2 * (R * c / 2)) < (T + 1) * ((∫ ξ, goodInd r ℓ c s η φ B θ T ξ
        ∂stdStream) * (R * c / 2)) := by
      apply mul_lt_mul_of_pos_left _ hT1
      apply mul_lt_mul_of_pos_right hcon
      exact div_pos (mul_pos (by linarith) hcp) two_pos
    linarith [mul_le_mul_of_nonneg_left hRc' hT1.le]
  have htr : θ / 2 ≤ T * (η * c * (Λ / σ)) := by
    obtain ⟨hTi, hTe⟩ := travel_expectation hB hs (r := r) (ℓ := ℓ) (φ := φ) (θ := θ) hη.le hcp hr
      hfar hb0σ T
    have hgi : Integrable (fun ξ => goodInd r ℓ c s η φ B θ T ξ) stdStream :=
      integrable_of_bound (measurable_good θ T) (C := 1) fun ξ => by
        unfold goodInd; split_ifs <;> simp
    have hpt (ξ : ℕ → ℝ) : θ * (1 - goodInd r ℓ c s η φ B θ T ξ) ≤
        travel (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) θ T ξ := by
      classical
      by_cases hg : Good r ℓ c s η φ B θ T ξ
      · have h1 : goodInd r ℓ c s η φ B θ T ξ = 1 := by unfold goodInd; rw [ite_eq_left hg]
        rw [h1, sub_self, mul_zero]
        exact Finset.sum_nonneg fun u _ => travel_nonneg hη.le hcp hr hfar ξ u
      · have h1 : goodInd r ℓ c s η φ B θ T ξ = 0 := by unfold goodInd; rw [ite_eq_right hg]
        rw [h1, sub_zero, mul_one]
        exact travel_ge hη.le hcp hr hfar hθ.le T ξ hg
    have hθi : Integrable (fun ξ => θ - θ * goodInd r ℓ c s η φ B θ T ξ) stdStream :=
      (integrable_const θ).sub (hgi.const_mul θ)
    have hmono : (∫ ξ, (θ - θ * goodInd r ℓ c s η φ B θ T ξ) ∂stdStream) ≤
        ∫ ξ, travel (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) θ T ξ
          ∂stdStream :=
      integral_mono hθi hTi (fun ξ => by
        have := hpt ξ
        rw [mul_sub, mul_one] at this
        exact this)
    rw [integral_sub (integrable_const θ) (hgi.const_mul θ), integral_const, integral_const_mul]
      at hmono
    simp only [probReal_univ, smul_eq_mul, one_mul] at hmono
    have : θ / 2 ≤ θ - θ * ∫ ξ, goodInd r ℓ c s η φ B θ T ξ ∂stdStream := by nlinarith
    have hTe' : (∫ ξ, travel (r := r) (ℓ := ℓ) (c := c) (s := s) (η := η) (φ := φ) (B := B) θ T ξ
        ∂stdStream) ≤ T * (η * c * (Λ / σ)) := hTe
    linarith
  have hfinal := regime_time hℓp hcp hσ hη hθ hε hΛ hμ0 htr hst hkick hwin hF3
  rw [hσsq] at hfinal
  exact hfinal

end

end LongTails.Proofs.NsgdRegime
