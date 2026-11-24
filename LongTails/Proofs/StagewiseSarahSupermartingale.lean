import LongTails.Proofs.StagewiseSarahPotential

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace OracleTemplate.StagewiseSarah

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type} [MeasurableSpace Ω]

noncomputable def epochPot (f : E → ℝ) (fstar μ σ : ℝ) (e : Epoch) (i : ℕ) (z : E × E) : ℝ :=
  if i < e.B then
    (f z.1 - fstar) + e.η * ((e.m : ℝ) + 1) / (e.B : ℝ) ^ 2 *
      (‖z.2 - (i : ℝ) • gradient f z.1‖ ^ 2 + ((e.B : ℝ) - i) * σ ^ 2)
  else
    (f z.1 - fstar) / (1 - e.η * μ) ^ (i - e.B) +
      e.η * ((e.m : ℝ) + 1 - ((i - e.B : ℕ) : ℝ)) * ‖z.2 - gradient f z.1‖ ^ 2

noncomputable def pot (f : E → ℝ) (fstar μ σ : ℝ) (c : Ctl) (z : E × E) : ℝ :=
  match c.todo with
  | [] => f z.1 - fstar
  | e :: rest => after μ σ rest (gain μ e * epochPot f fstar μ σ e c.i z)

section Unfold

variable {f : E → ℝ} {g : E → Ω → E} {fstar μ σ : ℝ} {e : Epoch} {rest : List Epoch} {i : ℕ}
  {x w : E} {ω : Ω}

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma pot_nil (z : E × E) : pot f fstar μ σ ⟨[], i⟩ z = f z.1 - fstar := rfl

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma pot_cons (z : E × E) : pot f fstar μ σ ⟨e :: rest, i⟩ z =
    slope μ rest * gain μ e * epochPot f fstar μ σ e i z + after μ σ rest 0 := by
  change after μ σ rest (gain μ e * epochPot f fstar μ σ e i z) = _
  rw [after_affine]
  ring

lemma ctlNext_cons_lt (h : i + 1 < e.B + e.m) :
    ctlNext ⟨e :: rest, i⟩ = ⟨e :: rest, i + 1⟩ := by
  simp only [ctlNext, h, ↓reduceIte]

lemma ctlNext_cons_ge (h : ¬ i + 1 < e.B + e.m) : ctlNext ⟨e :: rest, i⟩ = ⟨rest, 0⟩ := by
  simp only [ctlNext, h, ↓reduceIte]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma sampleNext_nil (z : E × E) : sampleNext g ⟨[], i⟩ z ω = z := rfl

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma sampleNext_anchor_acc (hA : i < e.B) (h1 : i + 1 < e.B) :
    sampleNext g ⟨e :: rest, i⟩ (x, w) ω = (x, w + g x ω) := by
  simp only [sampleNext, zNext, pairQuery, hA, h1, ↓reduceIte]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma sampleNext_anchor_done (hA : i < e.B) (h1 : ¬ i + 1 < e.B) (h2 : i + 1 < e.B + e.m) :
    sampleNext g ⟨e :: rest, i⟩ (x, w) ω = (x, (1 / (e.B : ℝ)) • (w + g x ω)) := by
  simp only [sampleNext, zNext, pairQuery, hA, h1, h2, ↓reduceIte]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma sampleNext_anchor_final (hA : i < e.B) (h1 : ¬ i + 1 < e.B) (h2 : ¬ i + 1 < e.B + e.m) :
    sampleNext g ⟨e :: rest, i⟩ (x, w) ω =
      (x - e.η • ((1 / (e.B : ℝ)) • (w + g x ω)), 0) := by
  simp only [sampleNext, zNext, pairQuery, hA, h1, h2, ↓reduceIte]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma sampleNext_inner (hA : ¬ i < e.B) (h2 : i + 1 < e.B + e.m) :
    sampleNext g ⟨e :: rest, i⟩ (x, w) ω =
      (x - e.η • w, w + (g (x - e.η • w) ω - g x ω)) := by
  simp only [sampleNext, zNext, pairQuery, hA, h2, ↓reduceIte]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma sampleNext_inner_final (hA : ¬ i < e.B) (h2 : ¬ i + 1 < e.B + e.m) :
    sampleNext g ⟨e :: rest, i⟩ (x, w) ω =
      (x - e.η • w - e.η • (w + (g (x - e.η • w) ω - g x ω)), 0) := by
  simp only [sampleNext, zNext, pairQuery, hA, h2, ↓reduceIte]

end Unfold

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma pot_fresh (f : E → ℝ) (fstar μ σ : ℝ) (l : List Epoch) (hB : ∀ e ∈ l, 1 ≤ e.B) (x : E) :
    pot f fstar μ σ ⟨l, 0⟩ (x, 0) = after μ σ l (f x - fstar) := by
  cases l with
  | nil => rfl
  | cons e rest =>
    have hB' : 0 < e.B := hB e List.mem_cons_self
    have hB0 : (e.B : ℝ) ≠ 0 := by exact_mod_cast hB'.ne'
    change after μ σ rest (gain μ e * epochPot f fstar μ σ e 0 (x, 0)) =
      after μ σ rest (gain μ e * (f x - fstar + noise σ e))
    congr 2
    simp only [epochPot, hB', ↓reduceIte, Nat.cast_zero, zero_smul, sub_zero, norm_zero, noise]
    field_simp
    ring

section Step

variable {p : Measure Ω} [IsProbabilityMeasure p]

omit [MeasurableSpace Ω] in
lemma lintegral_ofReal_affine_le {mΩ : MeasurableSpace Ω} {p : Measure Ω} [IsProbabilityMeasure p]
    {h Ub : Ω → ℝ} {a b Y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hUb : ∀ ω, 0 ≤ Ub ω) (hle : ∀ ω, h ω ≤ a * Ub ω + b) (hint : Integrable Ub p)
    (hY : ∫ ω, Ub ω ∂p ≤ Y) :
    ∫⁻ ω, ENNReal.ofReal (h ω) ∂p ≤ ENNReal.ofReal (a * Y + b) := by
  calc ∫⁻ ω, ENNReal.ofReal (h ω) ∂p ≤ ∫⁻ ω, ENNReal.ofReal (a * Ub ω + b) ∂p :=
        lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hle ω))
    _ = ENNReal.ofReal (∫ ω, (a * Ub ω + b) ∂p) :=
        (ofReal_integral_eq_lintegral_ofReal ((hint.const_mul a).add (integrable_const b))
          (Filter.Eventually.of_forall (fun ω => add_nonneg (mul_nonneg ha (hUb ω)) hb))).symm
    _ ≤ ENNReal.ofReal (a * Y + b) := by
        apply ENNReal.ofReal_le_ofReal
        rw [integral_add (hint.const_mul a) (integrable_const b), integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
        nlinarith [mul_le_mul_of_nonneg_left hY ha]

omit [MeasurableSpace Ω] in
lemma integral_affine_le {mΩ : MeasurableSpace Ω} {p : Measure Ω} [IsProbabilityMeasure p]
    {X : Ω → ℝ} (hX : Integrable X p) {a b c M : ℝ} (hc : 0 ≤ c)
    (hM : ∫ ω, X ω ∂p ≤ M) :
    Integrable (fun ω => a + c * (X ω + b)) p ∧
      ∫ ω, (a + c * (X ω + b)) ∂p ≤ a + c * (M + b) := by
  have h1 : Integrable (fun ω => c * (X ω + b)) p := (hX.add (integrable_const b)).const_mul c
  refine ⟨(integrable_const a).add h1, ?_⟩
  rw [integral_add (integrable_const a) h1, integral_const_mul,
    integral_add hX (integrable_const b)]
  simp only [integral_const, probReal_univ, one_smul]
  nlinarith [mul_le_mul_of_nonneg_left hM hc]

variable {f : E → ℝ} {g : E → Ω → E} {L Lbar μ σ fstar : ℝ}

omit [BorelSpace E] [SecondCountableTopology E] in
lemma anchor_bound (H : Hyp p f g L Lbar μ σ fstar) {e : Epoch} (he : Good L Lbar μ e)
    {i : ℕ} (hA : i < e.B) (x w : E) (K : ℝ) (hK : 0 ≤ K)
    (hKi : 1 + K = (e.B : ℝ) - i) :
    (∀ ω, 0 ≤ (f x - fstar) + e.η * ((e.m : ℝ) + 1) / (e.B : ℝ) ^ 2 *
      (‖(w - (i : ℝ) • gradient f x) + (g x ω - gradient f x)‖ ^ 2 + K * σ ^ 2)) ∧
    Integrable (fun ω => (f x - fstar) + e.η * ((e.m : ℝ) + 1) / (e.B : ℝ) ^ 2 *
      (‖(w - (i : ℝ) • gradient f x) + (g x ω - gradient f x)‖ ^ 2 + K * σ ^ 2)) p ∧
    ∫ ω, ((f x - fstar) + e.η * ((e.m : ℝ) + 1) / (e.B : ℝ) ^ 2 *
      (‖(w - (i : ℝ) • gradient f x) + (g x ω - gradient f x)‖ ^ 2 + K * σ ^ 2)) ∂p ≤
      epochPot f fstar μ σ e i (x, w) := by
  have hη := he.hη
  have hc1 : 0 ≤ e.η * ((e.m : ℝ) + 1) / (e.B : ℝ) ^ 2 := by positivity
  obtain ⟨hint, hle⟩ := H.noise_step (w - (i : ℝ) • gradient f x) x
  obtain ⟨h1, h2⟩ := integral_affine_le (a := f x - fstar) (b := K * σ ^ 2) hint hc1 hle
  refine ⟨fun ω => ?_, h1, h2.trans (le_of_eq ?_)⟩
  · have := H.gap_nonneg x
    have h3 : 0 ≤ ‖(w - (i : ℝ) • gradient f x) + (g x ω - gradient f x)‖ ^ 2 + K * σ ^ 2 := by
      positivity
    nlinarith [mul_nonneg hc1 h3]
  · simp only [epochPot, hA, ↓reduceIte]
    rw [← hKi]
    ring

omit [BorelSpace E] [SecondCountableTopology E] in
lemma inner_bound (H : Hyp p f g L Lbar μ σ fstar) {e : Epoch} (he : Good L Lbar μ e)
    {i t : ℕ} (hA : ¬ i < e.B) (ht : i - e.B = t) (htm : t + 1 ≤ e.m) (x w : E) :
    (∀ ω, 0 ≤ (f (x - e.η • w) - fstar) / (1 - e.η * μ) ^ (t + 1) +
      e.η * ((e.m : ℝ) + 1 - ((t + 1 : ℕ) : ℝ)) *
        ‖(w - gradient f x) + ((g (x - e.η • w) ω - g x ω) -
          (gradient f (x - e.η • w) - gradient f x))‖ ^ 2) ∧
    Integrable (fun ω => (f (x - e.η • w) - fstar) / (1 - e.η * μ) ^ (t + 1) +
      e.η * ((e.m : ℝ) + 1 - ((t + 1 : ℕ) : ℝ)) *
        ‖(w - gradient f x) + ((g (x - e.η • w) ω - g x ω) -
          (gradient f (x - e.η • w) - gradient f x))‖ ^ 2) p ∧
    ∫ ω, ((f (x - e.η • w) - fstar) / (1 - e.η * μ) ^ (t + 1) +
      e.η * ((e.m : ℝ) + 1 - ((t + 1 : ℕ) : ℝ)) *
        ‖(w - gradient f x) + ((g (x - e.η • w) ω - g x ω) -
          (gradient f (x - e.η • w) - gradient f x))‖ ^ 2) ∂p ≤
      epochPot f fstar μ σ e i (x, w) := by
  have hη := he.hη
  obtain ⟨hθlo, hθhi⟩ := he.theta_bounds H.hμ
  obtain ⟨hplo, phhi⟩ := he.pow_bounds H.hμ (t + 1) (by omega)
  obtain ⟨hqlo, hqhi⟩ := he.pow_bounds H.hμ t (by omega)
  have hk : (0 : ℝ) ≤ (e.m : ℝ) + 1 - ((t + 1 : ℕ) : ℝ) := by
    have : ((t + 1 : ℕ) : ℝ) ≤ (e.m : ℝ) := by exact_mod_cast htm
    linarith
  have hkm : (e.m : ℝ) + 1 - ((t + 1 : ℕ) : ℝ) ≤ (e.m : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    linarith
  have hc : 0 ≤ e.η * ((e.m : ℝ) + 1 - ((t + 1 : ℕ) : ℝ)) := mul_nonneg hη.le hk
  obtain ⟨hint, hle⟩ := H.diff_step (w - gradient f x) x (x - e.η • w)
  have hnorm : ‖x - e.η • w - x‖ ^ 2 = e.η ^ 2 * ‖w‖ ^ 2 := by
    rw [show x - e.η • w - x = -(e.η • w) by abel, norm_neg, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]
  rw [hnorm] at hle
  obtain ⟨h1, h2⟩ := integral_affine_le
    (a := (f (x - e.η • w) - fstar) / (1 - e.η * μ) ^ (t + 1)) (b := 0) hint hc hle
  have hpos : 0 < (1 - e.η * μ) ^ (t + 1) := by linarith
  have hd := H.descent hη.le he.hL x w
  refine ⟨fun ω => ?_, ?_, ?_⟩
  · have h3 := H.gap_nonneg (x - e.η • w)
    have h4 : 0 ≤ (f (x - e.η • w) - fstar) / (1 - e.η * μ) ^ (t + 1) := div_nonneg h3 hpos.le
    have h5 := mul_nonneg hc (sq_nonneg ‖(w - gradient f x) + ((g (x - e.η • w) ω - g x ω) -
      (gradient f (x - e.η • w) - gradient f x))‖)
    linarith
  · simpa only [add_zero] using h1
  · simp only [add_zero] at h2
    refine h2.trans ?_
    have hreal := inner_step_real (θ := 1 - e.η * μ) (P := (1 - e.η * μ) ^ t)
      (d := f x - fstar) (d' := f (x - e.η • w) - fstar) (V := ‖w‖ ^ 2)
      (N := ‖w - gradient f x‖ ^ 2) (η := e.η) (Lbar := Lbar)
      (k := (e.m : ℝ) + 1 - ((t + 1 : ℕ) : ℝ)) (m := (e.m : ℝ))
      (by rw [← pow_succ']; exact hplo) (by rw [← pow_succ']; exact phhi) (by linarith)
      (by linarith) hη.le (sq_nonneg _) (sq_nonneg _) hkm he.hbar hd
    rw [← pow_succ'] at hreal
    simp only [epochPot, hA, ↓reduceIte, ht]
    have hcast : (e.m : ℝ) + 1 - ((t + 1 : ℕ) : ℝ) + 1 = (e.m : ℝ) + 1 - (t : ℝ) := by
      push_cast
      ring
    rw [hcast] at hreal
    have hrw : e.η * ((e.m : ℝ) + 1 - ((t + 1 : ℕ) : ℝ)) *
        (‖w - gradient f x‖ ^ 2 + Lbar ^ 2 * (e.η ^ 2 * ‖w‖ ^ 2)) =
        e.η * ((e.m : ℝ) + 1 - ((t + 1 : ℕ) : ℝ)) *
        (‖w - gradient f x‖ ^ 2 + Lbar ^ 2 * e.η ^ 2 * ‖w‖ ^ 2) := by ring
    rw [hrw]
    exact hreal

omit [BorelSpace E] [SecondCountableTopology E] in
theorem pot_step (H : Hyp p f g L Lbar μ σ fstar) (c : Ctl) (z : E × E)
    (hgood : ∀ e ∈ c.todo, Good L Lbar μ e)
    (hi : ∀ e rest, c.todo = e :: rest → c.i < e.B + e.m) :
    ∫⁻ ω, ENNReal.ofReal (pot f fstar μ σ (ctlNext c) (sampleNext g c z ω)) ∂p ≤
      ENNReal.ofReal (pot f fstar μ σ c z) := by
  obtain ⟨todo, i⟩ := c
  obtain ⟨x, w⟩ := z
  cases todo with
  | nil =>
    have h1 : ctlNext ⟨[], i⟩ = ⟨[], i⟩ := rfl
    simp only [h1, sampleNext_nil, lintegral_const, measure_univ, mul_one, le_refl]
  | cons e rest =>
    have he : Good L Lbar μ e := hgood e List.mem_cons_self
    have hrest : ∀ e' ∈ rest, Good L Lbar μ e' :=
      fun e' h => hgood e' (List.mem_cons_of_mem _ h)
    have hrestB : ∀ e' ∈ rest, 1 ≤ e'.B := fun e' h => (hrest e' h).hB
    have hlt : i < e.B + e.m := hi e rest rfl
    have hs := slope_nonneg H.hμ rest hrest
    have hb := after_zero_nonneg H.hμ σ rest hrest
    obtain ⟨hglo, hghi⟩ := he.gain_bounds H.hμ
    have ha : 0 ≤ slope μ rest * gain μ e := mul_nonneg hs (by linarith)
    have hη := he.hη
    have hBpos : 0 < e.B := he.hB
    have hB0 : (e.B : ℝ) ≠ 0 := by exact_mod_cast hBpos.ne'
    rw [pot_cons]
    by_cases hA : i < e.B
    · have hid : ∀ ω, w + g x ω - ((i : ℝ) + 1) • gradient f x =
          (w - (i : ℝ) • gradient f x) + (g x ω - gradient f x) := by
        intro ω
        rw [add_smul, one_smul]
        abel
      by_cases h1 : i + 1 < e.B
      · have h2 : i + 1 < e.B + e.m := by omega
        have hK : (0 : ℝ) ≤ (e.B : ℝ) - i - 1 := by
          have : ((i + 1 : ℕ) : ℝ) ≤ (e.B : ℝ) := by exact_mod_cast h1.le
          push_cast at this
          linarith
        obtain ⟨hn, hint, hle⟩ := anchor_bound H he hA x w ((e.B : ℝ) - i - 1) hK (by ring)
        rw [ctlNext_cons_lt h2]
        simp only [sampleNext_anchor_acc hA h1, pot_cons]
        refine lintegral_ofReal_affine_le ha hb hn (fun ω => le_of_eq ?_) hint hle
        simp only [epochPot, h1, ↓reduceIte, Nat.cast_add, Nat.cast_one]
        rw [hid ω]
        ring
      · have hBi : (e.B : ℝ) = (i : ℝ) + 1 := by
          have : e.B = i + 1 := by omega
          rw [this]
          push_cast
          ring
        obtain ⟨hn, hint, hle⟩ := anchor_bound H he hA x w 0 le_rfl (by rw [hBi]; ring)
        have hv0 : ∀ ω, (1 / (e.B : ℝ)) • (w + g x ω) - gradient f x =
            (1 / (e.B : ℝ)) • ((w - (i : ℝ) • gradient f x) + (g x ω - gradient f x)) := by
          intro ω
          rw [← hid ω, ← hBi, smul_sub, smul_smul, one_div, inv_mul_cancel₀ hB0, one_smul]
        have hnorm : ∀ ω, e.η * ‖(1 / (e.B : ℝ)) • (w + g x ω) - gradient f x‖ ^ 2 =
            e.η / (e.B : ℝ) ^ 2 *
              ‖(w - (i : ℝ) • gradient f x) + (g x ω - gradient f x)‖ ^ 2 := by
          intro ω
          rw [hv0 ω, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
          field_simp
        by_cases h2 : i + 1 < e.B + e.m
        · rw [ctlNext_cons_lt h2]
          simp only [sampleNext_anchor_done hA h1 h2, pot_cons]
          refine lintegral_ofReal_affine_le ha hb hn (fun ω => le_of_eq ?_) hint hle
          have hsub : i + 1 - e.B = 0 := by omega
          simp only [epochPot, h1, ↓reduceIte, hsub, pow_zero, div_one, Nat.cast_zero, sub_zero,
            zero_mul, add_zero]
          have hnω := hnorm ω
          have h3 : e.η * ((e.m : ℝ) + 1) * ‖(1 / (e.B : ℝ)) • (w + g x ω) - gradient f x‖ ^ 2 =
              e.η * ((e.m : ℝ) + 1) / (e.B : ℝ) ^ 2 *
                ‖(w - (i : ℝ) • gradient f x) + (g x ω - gradient f x)‖ ^ 2 := by
            calc e.η * ((e.m : ℝ) + 1) * ‖(1 / (e.B : ℝ)) • (w + g x ω) - gradient f x‖ ^ 2
                = ((e.m : ℝ) + 1) *
                  (e.η * ‖(1 / (e.B : ℝ)) • (w + g x ω) - gradient f x‖ ^ 2) := by ring
              _ = ((e.m : ℝ) + 1) * (e.η / (e.B : ℝ) ^ 2 *
                  ‖(w - (i : ℝ) • gradient f x) + (g x ω - gradient f x)‖ ^ 2) := by rw [hnω]
              _ = _ := by ring
          rw [h3]
        · have hm0 : e.m = 0 := by omega
          rw [ctlNext_cons_ge h2]
          simp only [sampleNext_anchor_final hA h1 h2]
          refine lintegral_ofReal_affine_le ha hb hn (fun ω => ?_) hint hle
          rw [pot_fresh f fstar μ σ rest hrestB, after_affine]
          have hfin := H.final_step he x ((1 / (e.B : ℝ)) • (w + g x ω))
          rw [hm0, pow_zero, div_one, hnorm ω] at hfin
          have hmul := mul_le_mul_of_nonneg_left hfin hs
          simp only [hm0, Nat.cast_zero, zero_add, mul_one, zero_mul, add_zero]
          linarith
    · obtain ⟨t, ht⟩ : ∃ t, i - e.B = t := ⟨_, rfl⟩
      have htm : t + 1 ≤ e.m := by omega
      obtain ⟨hn, hint, hle⟩ := inner_bound H he hA ht htm x w
      have hid : ∀ ω, w + (g (x - e.η • w) ω - g x ω) - gradient f (x - e.η • w) =
          (w - gradient f x) + ((g (x - e.η • w) ω - g x ω) -
            (gradient f (x - e.η • w) - gradient f x)) := by
        intro ω
        abel
      by_cases h2 : i + 1 < e.B + e.m
      · rw [ctlNext_cons_lt h2]
        simp only [sampleNext_inner hA h2, pot_cons]
        refine lintegral_ofReal_affine_le ha hb hn (fun ω => le_of_eq ?_) hint hle
        have hA' : ¬ i + 1 < e.B := by omega
        have hsub : i + 1 - e.B = t + 1 := by omega
        simp only [epochPot, hA', ↓reduceIte, hsub]
        rw [hid ω]
      · have htm' : t + 1 = e.m := by omega
        rw [ctlNext_cons_ge h2]
        simp only [sampleNext_inner_final hA h2]
        refine lintegral_ofReal_affine_le ha hb hn (fun ω => ?_) hint hle
        rw [pot_fresh f fstar μ σ rest hrestB, after_affine]
        have hfin := H.final_step he (x - e.η • w) (w + (g (x - e.η • w) ω - g x ω))
        rw [hid ω] at hfin
        have hmul := mul_le_mul_of_nonneg_left hfin hs
        have hone : (e.m : ℝ) + 1 - ((t + 1 : ℕ) : ℝ) = 1 := by
          rw [htm']
          ring
        rw [hone, mul_one, htm']
        linarith

end Step

end OracleTemplate.StagewiseSarah
