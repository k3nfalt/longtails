import LongTails.Proofs.SeparationSuccess
import LongTails.Proofs.NsgdRegime
import LongTails.Proofs.NsgdLattice
import LongTails.Proofs.SgdSeparation

namespace LongTails.Proofs.SeparationLower

open MeasureTheory ProbabilityTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.BatchedDirection
open LongTails.Setups.BatchedSpectralSmooth
open LongTails.Proofs.DiagonalSpectral LongTails.Proofs.SeparationInstance
open LongTails.Proofs.SeparationModel LongTails.Proofs.SeparationTrajectory
open LongTails.Proofs.GaussianBlocks LongTails.Proofs.BatchedDirectionExecution
open LongTails.Proofs.BatchedMuonRate LongTails.Proofs.SeparationSuccess
open LongTails.Proofs.NsgdLattice

variable {m n : ℕ}

lemma objective_ge {ℓ c : ℝ} (hℓ : 0 ≤ ℓ) (hc : 0 ≤ c) (φ : FlatShape) {v : ℝ}
    (hv : ∀ u, v ≤ φ.value u) (hr : 0 < min m n) (x0 X : Space m n) :
    (min m n - 1 : ℕ) * (c * v) ≤ objective ℓ c φ x0 X := by
  unfold objective
  rw [show ((min m n - 1 : ℕ) : ℝ) * (c * v) = 0 + (min m n - 1 : ℕ) * (c * v) by ring,
    ← sum_stiff_split hr]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : stiff i
  · have h0 : i.val = 0 := hi
    rw [ite_eq_left hi, ite_eq_left h0]
    exact mul_nonneg (by linarith) (sq_nonneg _)
  · have h0 : ¬ i.val = 0 := hi
    rw [ite_eq_right hi, ite_eq_right h0]
    exact mul_le_mul_of_nonneg_left (hv _) hc

lemma objective_start_eq (ℓ c : ℝ) (φ : FlatShape) (hr : 0 < min m n) (x0 : Space m n) :
    objective ℓ c φ x0 x0 = (min m n - 1 : ℕ) * (c * φ.value 0) := by
  rw [objective_start, show ((min m n - 1 : ℕ) : ℝ) * (c * φ.value 0) =
    0 + (min m n - 1 : ℕ) * (c * φ.value 0) by ring, ← sum_stiff_split hr]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : stiff i
  · have h0 : i.val = 0 := hi
    rw [ite_eq_left hi, ite_eq_left h0]
  · have h0 : ¬ i.val = 0 := hi
    rw [ite_eq_right hi, ite_eq_right h0]

lemma nsgd_nuclear (ℓ c τ η : ℝ) (φ : FlatShape) (x0 : Space m n) (hr : 0 < min m n)
    {B : ℕ} (hB : 0 < B) (ξ : ℕ → ℝ) (t : ℕ) :
    nuclearNorm (gradient (objective ℓ c φ x0)
        (sampledIterate frobeniusNormalize η B x0 (sample ℓ c τ φ x0) ξ t)) =
      |ℓ * (nsgdScalar (min m n) ℓ c τ η φ B ξ t).1| +
        (min m n - 1 : ℕ) * |c * φ.slope (nsgdScalar (min m n) ℓ c τ η φ B ξ t).2| :=
  nuclear_scalar ℓ c φ x0 _ hr _ _ (nsgd_reduction ℓ c τ η φ x0 hr hB ξ t)

lemma sgd_nuclear (ℓ c τ η : ℝ) (φ : FlatShape) (x0 : Space m n) (hr : 0 < min m n)
    {B : ℕ} (hB : 0 < B) (ξ : ℕ → ℝ) (t : ℕ) :
    nuclearNorm (gradient (objective ℓ c φ x0)
        (sampledIterate id η B x0 (sample ℓ c τ φ x0) ξ t)) =
      |ℓ * (sgdScalar ℓ c τ η φ B ξ t).1| +
        (min m n - 1 : ℕ) * |c * φ.slope (sgdScalar ℓ c τ η φ B ξ t).2| :=
  nuclear_scalar ℓ c φ x0 _ hr _ _ (sgd_reduction ℓ c τ η φ x0 hB ξ t)

lemma measurable_nuclear_iterate {direction : Space m n → Space m n} (hdir : Measurable direction)
    (ℓ c τ η : ℝ) (φ : FlatShape) (x0 : Space m n) (B t : ℕ) :
    Measurable (fun ξ : ℕ → ℝ => nuclearNorm (gradient (objective ℓ c φ x0)
      (sampledIterate direction η B x0 (sample ℓ c τ φ x0) ξ t))) :=
  ((MatrixCovariance.continuous_nuclearNorm _ _).measurable.comp
    (MuonProcess.measurable_gradient _)).comp
    (measurable_sampledIterate hdir η B x0 (measurable_sample ℓ c τ φ x0) t)

lemma nsgd_integrable {ℓ c τ η : ℝ} (hη : 0 ≤ η) (φ : FlatShape) (x0 : Space m n)
    (hr : 0 < min m n) {B : ℕ} (hB : 0 < B) (t : ℕ) :
    Integrable (fun ξ => nuclearNorm (gradient (objective ℓ c φ x0)
      (sampledIterate frobeniusNormalize η B x0 (sample ℓ c τ φ x0) ξ t))) stdStream := by
  apply Integrable.of_bound (measurable_nuclear_iterate (measurable_frobeniusNormalize m n)
    ℓ c τ η φ x0 B t).aestronglyMeasurable (|ℓ| * (η * t) + (min m n - 1 : ℕ) * |c|)
  refine Filter.Eventually.of_forall fun ξ => ?_
  rw [nsgd_nuclear ℓ c τ η φ x0 hr hB ξ t, Real.norm_of_nonneg (by positivity)]
  have hx : |(nsgdScalar (min m n) ℓ c τ η φ B ξ t).1| ≤ η * t :=
    NsgdBounds.state_x_abs_le (r := min m n) (ℓ := ℓ) (c := c) (s := τ) (φ := φ) (B := B) hη ξ t
  have hs := φ.bounded (nsgdScalar (min m n) ℓ c τ η φ B ξ t).2
  rw [abs_mul, abs_mul]
  have h1 : |c| * |φ.slope (nsgdScalar (min m n) ℓ c τ η φ B ξ t).2| ≤ |c| :=
    mul_le_of_le_one_right (abs_nonneg c) hs
  have hR : (0 : ℝ) ≤ (min m n - 1 : ℕ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hx (abs_nonneg ℓ), mul_le_mul_of_nonneg_left h1 hR]

lemma sgd_integrable {ℓ c τ η : ℝ} (φ : FlatShape) (x0 : Space m n)
    (hr : 0 < min m n) {B : ℕ} (hB : 0 < B) (t : ℕ) :
    Integrable (fun ξ => nuclearNorm (gradient (objective ℓ c φ x0)
      (sampledIterate id η B x0 (sample ℓ c τ φ x0) ξ t))) stdStream := by
  have hx := ((LongTails.Proofs.SgdSeparation.stiff_abs_integral ℓ c τ η φ hB t).1).const_mul |ℓ|
  have hflat : Integrable (fun _ξ : ℕ → ℝ =>
      ((min m n - 1 : ℕ) : ℝ) * |c * φ.slope (sgdScalar ℓ c τ η φ B (fun _ => 0) t).2|)
      stdStream := integrable_const _
  refine (hx.add hflat).congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [sgd_nuclear ℓ c τ η φ x0 hr hB ξ t, abs_mul ℓ,
    LongTails.Proofs.SgdSeparation.flat_independent ℓ c τ η φ B ξ (fun _ => 0) t]
  rfl

lemma valley_ge_width {w : ℝ} (hw : 0 ≤ w) (D u : ℝ) : w ≤ valley w D u := by
  unfold valley
  calc w = Real.sqrt (w ^ 2) := (Real.sqrt_sq hw).symm
    _ ≤ Real.sqrt (w ^ 2 + (u - D) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (u - D)])

set_option maxHeartbeats 1000000 in
theorem nsgd_lower_bound (p : Public) (hp : spec.valid p) (hr : 2 ≤ min p.m p.n)
    (hLΔ : 128 * p.ε ^ 2 ≤ p.L * p.Δ)
    (hlog : 2 + Real.log (1 + p.s * Real.sqrt (min p.m p.n) / p.ε) ≤
      (min p.m p.n - 1 : ℕ) * p.L * p.Δ / (256 * p.ε ^ 2))
    {η : ℝ} (hη : 0 < η) {B T : ℕ} (hB : 0 < B)
    {A : Algorithm (Space p.m p.n) (Space p.m p.n) (Space p.m p.n)}
    (hA : FollowsBatched frobeniusNormalize η B T p.x0 A) :
    ∃ (f : Space p.m p.n → ℝ) (O : Oracle (Space p.m p.n) (Space p.m p.n)),
      spec.admissible p f O ∧
      (spec.successful p f (fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
          execute O A (fun _ => B * (T + 1)) z.1 z.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ →
        (min p.m p.n - 1 : ℕ) * p.L * p.Δ * p.s ^ 2 ≤
          21000000 * p.ε ^ 4 * (2 + Real.log (1 + p.s * Real.sqrt (min p.m p.n) / p.ε)) *
            (B * (T + 1))) := by
  obtain ⟨hL, hΔ, hs, hε⟩ := hp
  have hr0 : 0 < min p.m p.n := by omega
  have hm : 0 < p.m := lt_of_lt_of_le hr0 (min_le_left _ _)
  set R : ℝ := ((min p.m p.n - 1 : ℕ) : ℝ) with hRdef
  have hR1 : 1 ≤ R := by
    have : 1 ≤ min p.m p.n - 1 := by omega
    rw [hRdef]; exact_mod_cast this
  have hR0 : 0 < R := by linarith
  set Λ := 2 + Real.log (1 + p.s * Real.sqrt (min p.m p.n) / p.ε) with hΛdef
  have hΛ2 : 2 ≤ Λ := by
    have h1 : (1 : ℝ) ≤ 1 + p.s * Real.sqrt (min p.m p.n) / p.ε := by
      have : 0 ≤ p.s * Real.sqrt (min p.m p.n) / p.ε := by positivity
      linarith
    have := Real.log_nonneg h1
    linarith
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  set c := 4 * p.ε / R with hcdef
  have hc : 0 < c := by positivity
  have hRc : R * c = 4 * p.ε := by rw [hcdef]; field_simp
  have hεL : 0 < p.ε ^ 2 := by positivity
  by_cases hreg : p.s ^ 2 * R < 256 * p.ε ^ 2 * B
  · set w := 4 * p.ε / p.L with hwdef
    have hw : 0 < w := by positivity
    have hwL : p.L * w = 4 * p.ε := by rw [hwdef]; field_simp
    have hlip : 0 + R * (c * (1 / w)) ≤ p.L := by
      rw [zero_add, ← mul_assoc, hRc]
      rw [mul_one_div, div_le_iff₀ hw]
      linarith
    set h := η / Real.sqrt R with hhdef
    have hsr : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR0
    have hh : 0 < h := by positivity
    have hΔw : 32 * w ≤ p.Δ / p.ε := by
      rw [le_div_iff₀ hε, hwdef]
      rw [show 32 * (4 * p.ε / p.L) * p.ε = 128 * p.ε ^ 2 / p.L by ring, div_le_iff₀ hL]
      linarith
    by_cases hsmall : h < 2 * w
    · set D := p.Δ / (4 * p.ε) - w with hDdef
      have hDq : p.Δ / (4 * p.ε) = p.Δ / p.ε / 4 := by ring
      have hDw : 6 * w ≤ D - w := by rw [hDdef, hDq]; linarith
      have hD0 : 0 ≤ D := by linarith
      set φ := pairShape hw D D with hφ
      refine ⟨objective 0 c φ p.x0, gaussianOracle (sample 0 c 0 φ p.x0), ?_, ?_⟩
      · refine separation_admissible hm le_rfl hc.le le_rfl hs φ hlip hr0 0
          (objective_nonneg le_rfl hc.le φ p.x0) ?_
        rw [objective_start_eq 0 c φ hr0 p.x0, sub_zero]
        have hv := pairShape_value_zero hw (a := D) (b := D) hD0 le_rfl
        rw [sub_self, abs_zero, zero_div, add_zero] at hv
        have hv' : R * (c * φ.value 0) ≤ R * (c * (w + D)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hc.le) hR0.le
        have : R * (c * (w + D)) = p.Δ := by
          rw [← mul_assoc, hRc, hDdef]; field_simp; ring
        linarith
      · intro hsucc
        have hsum := success_sum (measurable_sample 0 c 0 φ p.x0)
          (measurable_frobeniusNormalize p.m p.n) hA
          (fun t => nsgd_integrable hη.le φ p.x0 hr0 hB t) hsucc
        set K := ⌊(D - w) / h⌋₊ with hKdef
        have hKh : (K : ℝ) * h ≤ D - w := by
          have := Nat.floor_le (show 0 ≤ (D - w) / h by
            apply div_nonneg _ hh.le; linarith)
          rw [← hKdef, le_div_iff₀ hh] at this
          exact this
        have hKlt : (D - w) / h < K + 1 := Nat.lt_floor_add_one _
        have hbad (t : ℕ) (ht : t ≤ K) : 2 * p.ε ≤ ∫ ξ, nuclearNorm (gradient (objective 0 c φ p.x0)
            (sampledIterate frobeniusNormalize η B p.x0 (sample 0 c 0 φ p.x0) ξ t)) ∂stdStream := by
          have hpt (ξ : ℕ → ℝ) : 2 * p.ε ≤ nuclearNorm (gradient (objective 0 c φ p.x0)
              (sampledIterate frobeniusNormalize η B p.x0 (sample 0 c 0 φ p.x0) ξ t)) := by
            rw [nsgd_nuclear 0 c 0 η φ p.x0 hr0 hB ξ t]
            have htK : (t : ℝ) * h ≤ D - w := by
              have : (t : ℝ) ≤ K := by exact_mod_cast ht
              nlinarith
            have hy := climb hr hc hη.le hw D B ξ t (by
              rw [← hhdef]; linarith)
            rw [← hhdef] at hy
            have hsl := pairShape_slope_left hw (a := D) (b := D) (u := (t : ℝ) * h) htK htK
            rw [hy, zero_mul, abs_zero, zero_add, abs_mul, abs_of_pos hc,
              abs_of_neg (by linarith)]
            nlinarith
          have := integral_mono (integrable_const (2 * p.ε))
            (nsgd_integrable hη.le φ p.x0 hr0 hB t) hpt
          simpa using this
        set J := min T K with hJdef
        have hsubset : (∑ t ∈ Finset.range (J + 1), 2 * p.ε) ≤
            ∑ t ∈ Finset.range (T + 1), ∫ ξ, nuclearNorm (gradient (objective 0 c φ p.x0)
              (sampledIterate frobeniusNormalize η B p.x0 (sample 0 c 0 φ p.x0) ξ t))
                ∂stdStream := by
          calc (∑ t ∈ Finset.range (J + 1), 2 * p.ε) ≤
                ∑ t ∈ Finset.range (J + 1), ∫ ξ, nuclearNorm (gradient (objective 0 c φ p.x0)
                  (sampledIterate frobeniusNormalize η B p.x0 (sample 0 c 0 φ p.x0) ξ t))
                    ∂stdStream :=
                Finset.sum_le_sum fun t ht => hbad t (by
                  simp only [Finset.mem_range] at ht; omega)
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.range_mono (by omega))
                (fun t _ _ => integral_nonneg fun _ => by
                  unfold nuclearNorm; positivity)
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsubset
        have h2J : 2 * ((J : ℝ) + 1) ≤ T + 1 := by
          have := hsubset.trans hsum
          push_cast at this
          nlinarith
        have hJK : J = K := by
          by_contra hne
          have hJT : J = T := by omega
          rw [hJT] at h2J
          linarith
        rw [hJK] at h2J
        have hT : (D - w) / w ≤ T + 1 := by
          have h1 : (D - w) / h < K + 1 := hKlt
          rw [div_lt_iff₀ hh] at h1
          rw [div_le_iff₀ hw]
          nlinarith
        have hTL : p.L * p.Δ ≤ 32 * p.ε ^ 2 * (T + 1) := by
          have hDw' : D - w = p.Δ / (4 * p.ε) - 2 * w := by rw [hDdef]; ring
          rw [hDw', div_le_iff₀ hw] at hT
          have hΔeq : p.Δ / (4 * p.ε) * p.L = p.L * p.Δ / (4 * p.ε) := by ring
          have hLw : p.L * (2 * w) = 8 * p.ε := by linarith
          have key : p.L * p.Δ / (4 * p.ε) ≤ (T + 1) * (4 * p.ε) + 8 * p.ε := by
            nlinarith [mul_le_mul_of_nonneg_left hT hL.le]
          rw [div_le_iff₀ (by positivity)] at key
          nlinarith
        have hsB : p.s ^ 2 * R ≤ 256 * p.ε ^ 2 * B := hreg.le
        have hLΔ0 : 0 ≤ p.L * p.Δ := by positivity
        calc R * p.L * p.Δ * p.s ^ 2 = (p.s ^ 2 * R) * (p.L * p.Δ) := by ring
          _ ≤ (256 * p.ε ^ 2 * B) * (32 * p.ε ^ 2 * (T + 1)) :=
              mul_le_mul hsB hTL hLΔ0 (by positivity)
          _ = 8192 * p.ε ^ 4 * (B * (T + 1)) := by ring
          _ ≤ 21000000 * p.ε ^ 4 * Λ * (B * (T + 1)) := by
              have : (0 : ℝ) ≤ p.ε ^ 4 * (B * (T + 1)) := by positivity
              nlinarith
    · push Not at hsmall
      set φ := pairShape hw w (h - w) with hφ
      have hab : |h - w - w| / 2 = (h - 2 * w) / 2 := by
        rw [abs_of_nonneg (by linarith)]; ring
      have hvmin : ∀ u, (h - 2 * w) / 2 ≤ φ.value u := fun u => by
        rw [← hab]; exact pairShape_value_ge hw w (h - w) u
      refine ⟨objective 0 c φ p.x0, gaussianOracle (sample 0 c 0 φ p.x0), ?_, ?_⟩
      · refine separation_admissible hm le_rfl hc.le le_rfl hs φ hlip hr0 (R * (c * ((h - 2 * w) / 2)))
          (objective_ge le_rfl hc.le φ hvmin hr0 p.x0) ?_
        rw [objective_start_eq 0 c φ hr0 p.x0]
        have hv := pairShape_value_zero hw (a := w) (b := h - w) hw.le (by linarith)
        rw [hab] at hv
        have hv' : R * (c * φ.value 0) ≤ R * (c * (w + w + (h - 2 * w) / 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hc.le) hR0.le
        have hgap : R * (c * (w + w + (h - 2 * w) / 2)) - R * (c * ((h - 2 * w) / 2)) =
            8 * p.ε * w := by
          have : R * (c * (w + w + (h - 2 * w) / 2)) - R * (c * ((h - 2 * w) / 2)) =
              (R * c) * (2 * w) := by ring
          rw [this, hRc]; ring
        have hwΔ : 8 * p.ε * w ≤ p.Δ := by
          have : 32 * w * p.ε ≤ p.Δ := by
            have := hΔw; rwa [le_div_iff₀ hε] at this
          nlinarith
        linarith
      · intro hsucc
        exfalso
        have hsum := success_sum (measurable_sample 0 c 0 φ p.x0)
          (measurable_frobeniusNormalize p.m p.n) hA
          (fun t => nsgd_integrable hη.le φ p.x0 hr0 hB t) hsucc
        have hbad (t : ℕ) : 2 * p.ε ≤ ∫ ξ, nuclearNorm (gradient (objective 0 c φ p.x0)
            (sampledIterate frobeniusNormalize η B p.x0 (sample 0 c 0 φ p.x0) ξ t)) ∂stdStream := by
          have hpt (ξ : ℕ → ℝ) : 2 * p.ε ≤ nuclearNorm (gradient (objective 0 c φ p.x0)
              (sampledIterate frobeniusNormalize η B p.x0 (sample 0 c 0 φ p.x0) ξ t)) := by
            rw [nsgd_nuclear 0 c 0 η φ p.x0 hr0 hB ξ t]
            have hsl := cycle_slope hr hc hw (η := η) (by rw [← hhdef]; exact hsmall) B ξ t
            rw [← hhdef] at hsl
            rw [zero_mul, abs_zero, zero_add, abs_mul, abs_of_pos hc]
            have : R * (c * (1 / 2)) ≤ R * (c * |φ.slope (nsgdScalar (min p.m p.n) 0 c 0 η φ B ξ t).2|) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsl hc.le) hR0.le
            nlinarith
          have := integral_mono (integrable_const (2 * p.ε))
            (nsgd_integrable hη.le φ p.x0 hr0 hB t) hpt
          simpa using this
        have := Finset.sum_le_sum (s := Finset.range (T + 1)) fun t _ => hbad t
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
        push_cast at this
        nlinarith
  · push Not at hreg
    have hspos : 0 < p.s := by
      rcases hs.lt_or_eq with h | h
      · exact h
      · rw [← h] at hreg; nlinarith
    set ℓ := p.L / 2 with hℓdef
    have hℓ : 0 < ℓ := by positivity
    set w := 8 * p.ε / p.L with hwdef
    have hw : 0 < w := by positivity
    set D := p.Δ / (4 * p.ε) with hDdef
    set φ := valleyShape hw D with hφ
    set θ := D - w with hθdef
    have hθℓ : 3 * (p.L * p.Δ) / (32 * p.ε) ≤ θ * ℓ := by
      have e : θ * ℓ = p.L * p.Δ / (8 * p.ε) - 4 * p.ε := by
        rw [hθdef, hDdef, hwdef, hℓdef]; field_simp; ring
      rw [e]
      have : 4 * p.ε ≤ p.L * p.Δ / (32 * p.ε) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have e2 : p.L * p.Δ / (8 * p.ε) = 4 * (p.L * p.Δ / (32 * p.ε)) := by field_simp; ring
      have e3 : 3 * (p.L * p.Δ) / (32 * p.ε) = 3 * (p.L * p.Δ / (32 * p.ε)) := by ring
      linarith
    have hθ : 0 < θ := by
      have : 0 < 3 * (p.L * p.Δ) / (32 * p.ε) := by
        have : 0 < p.L * p.Δ := by nlinarith
        positivity
      have := lt_of_lt_of_le this hθℓ
      exact pos_of_mul_pos_left this hℓ.le
    refine ⟨objective ℓ c φ p.x0, gaussianOracle (sample ℓ c p.s φ p.x0), ?_, ?_⟩
    · refine separation_admissible hm hℓ.le hc.le hs le_rfl φ ?_ hr0 (R * (c * w))
        (objective_ge hℓ.le hc.le φ (valley_ge_width hw.le D) hr0 p.x0) ?_
      · change ℓ + R * (c * (1 / w)) ≤ p.L
        rw [← mul_assoc, hRc, hℓdef, hwdef]
        field_simp
        ring_nf
        rfl
      · rw [objective_start_eq ℓ c φ hr0 p.x0]
        have hv : valley w D 0 ≤ w + D := by
          have := valley_le w D 0 hw.le
          rwa [zero_sub, abs_neg, abs_of_nonneg (by positivity)] at this
        have hv' : R * (c * φ.value 0) ≤ R * (c * (w + D)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hc.le) hR0.le
        have : R * (c * (w + D)) - R * (c * w) = p.Δ := by
          rw [show R * (c * (w + D)) - R * (c * w) = (R * c) * D by ring, hRc, hDdef]
          field_simp
        linarith
    · intro hsucc
      have hsum := success_sum (measurable_sample ℓ c p.s φ p.x0)
        (measurable_frobeniusNormalize p.m p.n) hA
        (fun t => nsgd_integrable hη.le φ p.x0 hr0 hB t) hsucc
      simp_rw [nsgd_nuclear ℓ c p.s η φ p.x0 hr0 hB] at hsum
      have hBpos : (0 : ℝ) < B := by linarith
      have hb4 : Real.sqrt R * c ≤ Real.sqrt (p.s ^ 2 / B) / 4 := by
        have hsq : (Real.sqrt R * c * 4) ^ 2 ≤ p.s ^ 2 / B := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hR0.le, le_div_iff₀ hBpos]
          have e : R * c ^ 2 * 4 ^ 2 * B * R = 256 * p.ε ^ 2 * B := by
            rw [show R * c ^ 2 * 4 ^ 2 * B * R = (R * c) ^ 2 * 16 * B by ring, hRc]; ring
          have : R * c ^ 2 * 4 ^ 2 * B * R ≤ p.s ^ 2 * R := by rw [e]; linarith
          exact le_of_mul_le_mul_right this hR0
        have := Real.le_sqrt_of_sq_le hsq
        linarith
      set σ := Real.sqrt (p.s ^ 2 / B) with hσdef
      have hσs : σ ≤ p.s := by
        rw [hσdef, Real.sqrt_le_left hs]
        rw [div_le_iff₀ hBpos]
        nlinarith [sq_nonneg p.s]
      have hratio : σ / (Real.sqrt R * c / 2) ≤ 1 + p.s * Real.sqrt (min p.m p.n) / p.ε := by
        have hsr : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR0
        have he : Real.sqrt R * c / 2 = 2 * p.ε / Real.sqrt R := by
          rw [hcdef]
          have : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR0.le
          field_simp
          nlinarith [this]
        rw [he, div_div_eq_mul_div]
        have hRr : Real.sqrt R ≤ Real.sqrt (min p.m p.n) := by
          apply Real.sqrt_le_sqrt
          rw [hRdef]
          exact_mod_cast Nat.sub_le _ _
        have h1 : σ * Real.sqrt R / (2 * p.ε) ≤ p.s * Real.sqrt (min p.m p.n) / p.ε := by
          rw [div_le_div_iff₀ (by positivity) hε]
          have := mul_le_mul hσs hRr (Real.sqrt_nonneg _) hs
          have h5 := mul_le_mul_of_nonneg_right this hε.le
          have h6 : 0 ≤ p.s * Real.sqrt (min p.m p.n) * p.ε := by positivity
          linarith
        linarith
      have hσpos : 0 < σ := Real.sqrt_pos.mpr (by positivity)
      have hratio0 : 0 < σ / (Real.sqrt R * c / 2) := by
        have : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR0
        positivity
      have hlogle : 2 + Real.log (σ / (Real.sqrt R * c / 2)) ≤ Λ := by
        have := Real.log_le_log hratio0 hratio
        rw [hΛdef]; linarith
      have hF3 : 4 * c * (2 + Real.log (σ / (Real.sqrt R * c / 2))) ≤ θ * ℓ := by
        have h1 : 4 * c * (2 + Real.log (σ / (Real.sqrt R * c / 2))) ≤ 4 * c * Λ :=
          mul_le_mul_of_nonneg_left hlogle (by positivity)
        have h2 : 4 * c * Λ ≤ p.L * p.Δ / (16 * p.ε) := by
          have hcR : 4 * c * Λ * R = 16 * p.ε * Λ := by
            rw [show 4 * c * Λ * R = 4 * (R * c) * Λ by ring, hRc]; ring
          have hl : Λ ≤ R * p.L * p.Δ / (256 * p.ε ^ 2) := by
            rw [hΛdef, hRdef]; simpa [mul_assoc] using hlog
          rw [le_div_iff₀ (by positivity)] at hl
          rw [le_div_iff₀ (by positivity)]
          have : 4 * c * Λ * (16 * p.ε) * R ≤ p.L * p.Δ * R := by
            rw [show 4 * c * Λ * (16 * p.ε) * R = 16 * p.ε * (4 * c * Λ * R) by ring, hcR]
            nlinarith
          exact le_of_mul_le_mul_right this hR0
        have h3 : p.L * p.Δ / (16 * p.ε) ≤ 3 * (p.L * p.Δ) / (32 * p.ε) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : 0 ≤ p.L * p.Δ := by positivity
          nlinarith
        linarith
      have hbound := LongTails.Proofs.NsgdRegime.nsgd_scalar_bound hB hspos hc.le hℓ.le hb4
        (r := min p.m p.n) (φ := φ) (T := T) (ε := p.ε) (θ := θ) hℓ hc hη hε hr hθ
        (fun y hy => valleySlope_far hw (by rw [hθdef] at hy; exact hy)) (by rw [hRc])
        hF3 hsum
      have hΛ' : 2 + Real.log (Real.sqrt (p.s ^ 2 / B) / (Real.sqrt R * c / 2)) ≤ Λ := hlogle
      have hB' : θ * ℓ * p.s ^ 2 ≤ 490000 * p.ε ^ 2 * c * Λ * T * B := by
        have h1 := hbound
        rw [div_eq_mul_inv, ← mul_assoc] at h1
        have h2 : 490000 * p.ε ^ 2 * c * (2 + Real.log (Real.sqrt (p.s ^ 2 / B) /
            (Real.sqrt R * c / 2))) * T ≤ 490000 * p.ε ^ 2 * c * Λ * T := by
          apply mul_le_mul_of_nonneg_right _ hT0
          exact mul_le_mul_of_nonneg_left hΛ' (by positivity)
        have h3 : θ * ℓ * p.s ^ 2 * (B : ℝ)⁻¹ ≤ 490000 * p.ε ^ 2 * c * Λ * T := h1.trans h2
        have h4 := mul_le_mul_of_nonneg_right h3 hBpos.le
        rwa [mul_assoc (θ * ℓ * p.s ^ 2), inv_mul_cancel₀ hBpos.ne', mul_one] at h4
      have hfin : 3 * (p.L * p.Δ) * p.s ^ 2 * R ≤
          62720000 * p.ε ^ 4 * Λ * (B * (T + 1)) := by
        have h1 : 3 * (p.L * p.Δ) / (32 * p.ε) * p.s ^ 2 ≤ θ * ℓ * p.s ^ 2 :=
          mul_le_mul_of_nonneg_right hθℓ (sq_nonneg _)
        have h2 := h1.trans hB'
        have h3 : 3 * (p.L * p.Δ) * p.s ^ 2 ≤ 32 * p.ε * (490000 * p.ε ^ 2 * c * Λ * T * B) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h2
          linarith
        have h4 : 3 * (p.L * p.Δ) * p.s ^ 2 * R ≤
            32 * p.ε * (490000 * p.ε ^ 2 * (R * c) * Λ * T * B) := by
          have := mul_le_mul_of_nonneg_right h3 hR0.le
          linarith
        rw [hRc] at h4
        have h5 : 32 * p.ε * (490000 * p.ε ^ 2 * (4 * p.ε) * Λ * T * B) =
            62720000 * p.ε ^ 4 * Λ * (B * T) := by ring
        rw [h5] at h4
        have : 62720000 * p.ε ^ 4 * Λ * (B * T) ≤ 62720000 * p.ε ^ 4 * Λ * (B * (T + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
        linarith
      have : R * p.L * p.Δ * p.s ^ 2 * 3 ≤ 62720000 * p.ε ^ 4 * Λ * (B * (T + 1)) := by
        linarith
      have hN : 0 ≤ p.ε ^ 4 * Λ * (B * (T + 1)) := by positivity
      linarith

set_option maxHeartbeats 1000000 in
theorem sgd_lower_bound (p : Public) (hp : spec.valid p) (hr : 2 ≤ min p.m p.n)
    (hLΔ : 128 * p.ε ^ 2 ≤ p.L * p.Δ)
    {η : ℝ} (hη : 0 < η) {B T : ℕ} (hB : 0 < B)
    {A : Algorithm (Space p.m p.n) (Space p.m p.n) (Space p.m p.n)}
    (hA : FollowsBatched id η B T p.x0 A) :
    ∃ (f : Space p.m p.n → ℝ) (O : Oracle (Space p.m p.n) (Space p.m p.n)),
      spec.admissible p f O ∧
      (spec.successful p f (fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
          execute O A (fun _ => B * (T + 1)) z.1 z.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ →
        (min p.m p.n - 1 : ℕ) * p.L * p.Δ * p.s ^ 2 ≤ 1728 * p.ε ^ 4 * (B * (T + 1))) := by
  obtain ⟨hL, hΔ, hs, hε⟩ := hp
  have hr0 : 0 < min p.m p.n := by omega
  have hm : 0 < p.m := lt_of_lt_of_le hr0 (min_le_left _ _)
  set R : ℝ := ((min p.m p.n - 1 : ℕ) : ℝ) with hRdef
  have hR1 : 1 ≤ R := by
    have : 1 ≤ min p.m p.n - 1 := by omega
    rw [hRdef]; exact_mod_cast this
  have hR0 : 0 < R := by linarith
  set c := 4 * p.ε / R with hcdef
  have hc : 0 < c := by positivity
  have hRc : R * c = 4 * p.ε := by rw [hcdef]; field_simp
  set ℓ := p.L / 2 with hℓdef
  have hℓ : 0 < ℓ := by positivity
  set w := 8 * p.ε / p.L with hwdef
  have hw : 0 < w := by positivity
  set D := p.Δ / (4 * p.ε) with hDdef
  set φ := valleyShape hw D with hφ
  have hθℓ : 3 * (p.L * p.Δ) / (32 * p.ε) ≤ (D - w) * ℓ := by
    have e : (D - w) * ℓ = p.L * p.Δ / (8 * p.ε) - 4 * p.ε := by
      rw [hDdef, hwdef, hℓdef]; field_simp; ring
    rw [e]
    have : 4 * p.ε ≤ p.L * p.Δ / (32 * p.ε) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have e2 : p.L * p.Δ / (8 * p.ε) = 4 * (p.L * p.Δ / (32 * p.ε)) := by field_simp; ring
    have e3 : 3 * (p.L * p.Δ) / (32 * p.ε) = 3 * (p.L * p.Δ / (32 * p.ε)) := by ring
    linarith
  have hLΔpos : 0 < p.L * p.Δ := by nlinarith
  have hDw : 0 < D - w := by
    have : 0 < 3 * (p.L * p.Δ) / (32 * p.ε) := by positivity
    exact pos_of_mul_pos_left (lt_of_lt_of_le this hθℓ) hℓ.le
  refine ⟨objective ℓ c φ p.x0, gaussianOracle (sample ℓ c p.s φ p.x0), ?_, ?_⟩
  · refine separation_admissible hm hℓ.le hc.le hs le_rfl φ ?_ hr0 (R * (c * w))
      (objective_ge hℓ.le hc.le φ (valley_ge_width hw.le D) hr0 p.x0) ?_
    · change ℓ + R * (c * (1 / w)) ≤ p.L
      rw [← mul_assoc, hRc, hℓdef, hwdef]
      field_simp
      ring_nf
      rfl
    · rw [objective_start_eq ℓ c φ hr0 p.x0]
      have hv : valley w D 0 ≤ w + D := by
        have := valley_le w D 0 hw.le
        rwa [zero_sub, abs_neg, abs_of_nonneg (by positivity)] at this
      have hv' : R * (c * φ.value 0) ≤ R * (c * (w + D)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hc.le) hR0.le
      have : R * (c * (w + D)) - R * (c * w) = p.Δ := by
        rw [show R * (c * (w + D)) - R * (c * w) = (R * c) * D by ring, hRc, hDdef]
        field_simp
      linarith
  · intro hsucc
    have hsum := success_sum (measurable_sample ℓ c p.s φ p.x0) measurable_id hA
      (fun t => sgd_integrable φ p.x0 hr0 hB t) hsucc
    simp_rw [sgd_nuclear ℓ c p.s η φ p.x0 hr0 hB] at hsum
    have hD34 : 3 / 4 ≤ ℓ * (D - w) / c := by
      rw [le_div_iff₀ hc]
      have h1 : 3 * (p.L * p.Δ) / (32 * p.ε) * R ≤ (D - w) * ℓ * R :=
        mul_le_mul_of_nonneg_right hθℓ hR0.le
      have h2 : 3 / 4 * c * R = 3 * p.ε := by rw [show 3 / 4 * c * R = 3 / 4 * (R * c) by ring, hRc]; ring
      have h3 : 3 * p.ε ≤ 3 * (p.L * p.Δ) / (32 * p.ε) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have h4 : 3 / 4 * c * R ≤ ℓ * (D - w) * R := by nlinarith
      exact le_of_mul_le_mul_right h4 hR0
    have hbound := LongTails.Proofs.SgdSeparation.sgd_scalar_bound (R := min p.m p.n - 1)
      hℓ hc hη hε hw hB hRc hD34 hDw hsum
    have h1 : 3 * (p.L * p.Δ) / (32 * p.ε) * p.s ^ 2 ≤ ℓ * p.s ^ 2 * (D - w) := by
      have := mul_le_mul_of_nonneg_right hθℓ (sq_nonneg p.s)
      linarith [show (D - w) * ℓ * p.s ^ 2 = ℓ * p.s ^ 2 * (D - w) by ring]
    have h2 : ℓ * p.s ^ 2 * (D - w) ≤ 81 / 2 * c * p.ε ^ 2 * (B * (T + 1)) := by
      rw [div_le_iff₀ (by positivity)] at hbound
      linarith
    have h3 : 3 * (p.L * p.Δ) * p.s ^ 2 ≤ 32 * p.ε * (81 / 2 * c * p.ε ^ 2 * (B * (T + 1))) := by
      have := h1.trans h2
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
      linarith
    have h4 : 3 * (p.L * p.Δ) * p.s ^ 2 * R ≤
        32 * p.ε * (81 / 2 * (R * c) * p.ε ^ 2 * (B * (T + 1))) := by
      have := mul_le_mul_of_nonneg_right h3 hR0.le
      linarith
    rw [hRc] at h4
    nlinarith

end LongTails.Proofs.SeparationLower
