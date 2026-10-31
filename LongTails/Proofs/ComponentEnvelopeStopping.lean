import LongTails.Proofs.ComponentEnvelopeProx
import LongTails.Proofs.ComponentEnvelopeExecution

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.ComponentEnvelope

open LongTails.Proofs.RecursiveEnvelopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma inner_step_fejer {f : E → ℝ} {g : E → E} {L0 L1 μ : ℝ}
    (h0 : 0 < L0) (h1 : 0 ≤ L1) (hμ : 0 ≤ μ)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hcont : Continuous g) (hs : CompositeGeneralized.SymmetricSmooth g L0 L1)
    (c x p : E) (hmin : ∀ y, regularized f μ c p ≤ regularized f μ c y) :
    let r := g x + μ • (x - c)
    let η := 1 / (16 * (L0 + μ + L1 * ‖g x‖ + L1 * ‖r‖))
    ‖innerStep L0 L1 μ c x (g x) - p‖ ^ 2 ≤
      (1 - μ * η) * ‖x - p‖ ^ 2 - 5 / 2 * η ^ 2 * ‖r‖ ^ 2 := by
  exact regularized_observable_fejer h0 h1 hμ hc hg hcont hs c x p hmin

lemma inner_step_distance {f : E → ℝ} {g : E → E} {L0 L1 μ : ℝ}
    (h0 : 0 < L0) (h1 : 0 ≤ L1) (hμ : 0 ≤ μ)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hcont : Continuous g) (hs : CompositeGeneralized.SymmetricSmooth g L0 L1)
    (c x p : E) (hmin : ∀ y, regularized f μ c p ≤ regularized f μ c y) :
    ‖innerStep L0 L1 μ c x (g x) - p‖ ≤ ‖x - p‖ := by
  have hf := inner_step_fejer h0 h1 hμ hc hg hcont hs c x p hmin
  dsimp only at hf
  set r := g x + μ • (x - c)
  set η := 1 / (16 * (L0 + μ + L1 * ‖g x‖ + L1 * ‖r‖))
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hm : 0 ≤ μ * η * ‖x - p‖ ^ 2 := by positivity
  have hn : 0 ≤ 5 / 2 * η ^ 2 * ‖r‖ ^ 2 := by positivity
  change ‖innerStep L0 L1 μ c x (g x) - p‖ ^ 2 ≤
    (1 - μ * η) * ‖x - p‖ ^ 2 - 5 / 2 * η ^ 2 * ‖r‖ ^ 2 at hf
  nlinarith [norm_nonneg (innerStep L0 L1 μ c x (g x) - p), norm_nonneg (x - p)]

lemma inner_path_distance {f : E → ℝ} {g : E → E} {L0 L1 μ : ℝ}
    (h0 : 0 < L0) (h1 : 0 ≤ L1) (hμ : 0 ≤ μ)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hcont : Continuous g) (hs : CompositeGeneralized.SymmetricSmooth g L0 L1)
    (c p : E) (hmin : ∀ y, regularized f μ c p ≤ regularized f μ c y) (k : ℕ) :
    ‖innerPath g L0 L1 μ c k - p‖ ≤ ‖c - p‖ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      unfold innerPath
      rw [Function.iterate_succ_apply']
      exact (inner_step_distance h0 h1 hμ hc hg hcont hs c _ p hmin).trans ih

lemma inner_large_drop {μ η L B D r a b : ℝ}
    (hμ : 0 ≤ μ) (hη : 0 ≤ η) (ha : 0 ≤ a)
    (hD : D ≤ B + 2 * L * r) (hlarge : B ≤ L * r)
    (hidentity : 16 * D * η = 1)
    (hstep : b ≤ (1 - μ * η) * a - 5 / 2 * η ^ 2 * r ^ 2) :
    1 ≤ 1152 * L ^ 2 * (a - b) := by
  have hh : 1 ≤ 48 * (η * L * r) := by
    have hm := mul_le_mul_of_nonneg_right (show D ≤ 3 * L * r by linarith) hη
    nlinarith
  have hs : 1 ≤ 2304 * (η * L * r) ^ 2 := by nlinarith
  have hd : 2 * η ^ 2 * r ^ 2 ≤ a - b := by
    nlinarith [mul_nonneg (mul_nonneg hμ hη) ha, mul_nonneg (sq_nonneg η) (sq_nonneg r)]
  have hm := mul_le_mul_of_nonneg_left hd (sq_nonneg L)
  nlinarith

lemma inner_small_contraction {μ η L B D r a b : ℝ}
    (hμ : 0 ≤ μ) (hη : 0 ≤ η) (hB : 0 < B) (ha : 0 ≤ a)
    (hD : D ≤ B + 2 * L * r) (hsmall : L * r ≤ B)
    (hidentity : 16 * D * η = 1)
    (hstep : b ≤ (1 - μ * η) * a - 5 / 2 * η ^ 2 * r ^ 2) :
    b ≤ (1 - μ / (48 * B)) * a := by
  have hh : 1 ≤ 48 * B * η := by
    have hm := mul_le_mul_of_nonneg_right (show D ≤ 3 * B by linarith) hη
    nlinarith
  have hηlower : 1 / (48 * B) ≤ η := by
    apply (div_le_iff₀ (by positivity : 0 < 48 * B)).mpr
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hηlower (mul_nonneg hμ ha)
  have hn := mul_nonneg (sq_nonneg η) (sq_nonneg r)
  have he : μ * a * (1 / (48 * B)) = μ / (48 * B) * a := by ring
  rw [he] at hm
  nlinarith


lemma inner_path_dichotomy {f : E → ℝ} {g : E → E} {L0 L1 μ : ℝ}
    (h0 : 0 < L0) (h1 : 0 ≤ L1) (hμ : 0 ≤ μ)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hcont : Continuous g) (hs : CompositeGeneralized.SymmetricSmooth g L0 L1)
    (c p : E) (hmin : ∀ y, regularized f μ c p ≤ regularized f μ c y) (k : ℕ) :
    let x := innerPath g L0 L1 μ c k
    let B := L0 + μ + 2 * μ * L1 * ‖c - p‖
    (B ≤ L1 * ‖g x + μ • (x - c)‖ →
      1 ≤ 1152 * L1 ^ 2 * (‖x - p‖ ^ 2 - ‖innerPath g L0 L1 μ c (k + 1) - p‖ ^ 2)) ∧
    (L1 * ‖g x + μ • (x - c)‖ ≤ B →
      ‖innerPath g L0 L1 μ c (k + 1) - p‖ ^ 2 ≤
        (1 - μ / (48 * B)) * ‖x - p‖ ^ 2) := by
  dsimp only
  set x := innerPath g L0 L1 μ c k
  set B := L0 + μ + 2 * μ * L1 * ‖c - p‖
  set r := ‖g x + μ • (x - c)‖
  set D := L0 + μ + L1 * ‖g x‖ + L1 * r
  set η := 1 / (16 * D)
  have hDpos : 0 < D := by dsimp [D, r]; positivity
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hid : 16 * D * η = 1 := by dsimp [η]; field_simp
  have hd := inner_path_distance h0 h1 hμ hc hg hcont hs c p hmin k
  have hden := regularized_denominator_bound (g := g) (L0 := L0) h1 hμ c x p hd
  change D ≤ B + 2 * L1 * r at hden
  have hstep := inner_step_fejer h0 h1 hμ hc hg hcont hs c x p hmin
  change ‖innerStep L0 L1 μ c x (g x) - p‖ ^ 2 ≤
    (1 - μ * η) * ‖x - p‖ ^ 2 - 5 / 2 * η ^ 2 * r ^ 2 at hstep
  have he : innerPath g L0 L1 μ c (k + 1) = innerStep L0 L1 μ c x (g x) := by
    exact Function.iterate_succ_apply' _ _ _
  rw [he]
  constructor
  · intro hh
    exact inner_large_drop hμ hη (sq_nonneg _) hden hh hid hstep
  · intro hh
    exact inner_small_contraction hμ hη hBpos (sq_nonneg _) hden hh hid hstep


noncomputable def stepCount (large : ℕ → Prop) (k : ℕ) : ℕ := by
  classical
  exact ((Finset.range k).filter large).card

lemma stepCount_zero (large : ℕ → Prop) : stepCount large 0 = 0 := by
  simp [stepCount]

lemma stepCount_succ (large : ℕ → Prop) [DecidablePred large] (k : ℕ) :
    stepCount large (k + 1) = stepCount large k + if large k then 1 else 0 := by
  by_cases h : large k <;> simp [stepCount, Finset.range_add_one, Finset.filter_insert, h]

lemma stepCount_partition (large : ℕ → Prop) [DecidablePred large] (k : ℕ) :
    stepCount large k + stepCount (fun j => ¬large j) k = k := by
  induction k with
  | zero => simp [stepCount_zero]
  | succ k ih =>
      rw [stepCount_succ, stepCount_succ]
      by_cases h : large k <;> simp [h] <;> omega

lemma dichotomy_sum_decrease (large : ℕ → Prop) [DecidablePred large]
    (a : ℕ → ℝ) {c : ℝ}
    (hstep : ∀ k, a (k + 1) + c * (if large k then 1 else 0) ≤ a k) (K : ℕ) :
    c * stepCount large K ≤ a 0 - a K := by
  induction K with
  | zero => simp [stepCount_zero]
  | succ K ih =>
      rw [stepCount_succ]
      have hh := hstep K
      by_cases h : large K <;> simp [h] at * <;> nlinarith

lemma dichotomy_exp_decrease (large : ℕ → Prop) [DecidablePred large]
    (a : ℕ → ℝ) {α : ℝ} (ha : ∀ k, 0 ≤ a k)
    (hlarge : ∀ k, large k → a (k + 1) ≤ a k)
    (hsmall : ∀ k, ¬large k → a (k + 1) ≤ (1 - α) * a k) (K : ℕ) :
    a K ≤ a 0 * Real.exp (-α * stepCount (fun j => ¬large j) K) := by
  induction K with
  | zero => simp [stepCount_zero]
  | succ K ih =>
      rw [stepCount_succ]
      by_cases h : large K
      · simpa [h] using (hlarge K h).trans ih
      · simp only [h, not_false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one]
        have he : 1 - α ≤ Real.exp (-α) := by linarith [Real.add_one_le_exp (-α)]
        have hs := (hsmall K h).trans (mul_le_mul_of_nonneg_right he (ha K))
        have hm := mul_le_mul_of_nonneg_left ih (Real.exp_nonneg (-α))
        have hx : Real.exp (-α) * (a 0 * Real.exp (-α * stepCount (fun j => ¬large j) K)) =
            a 0 * Real.exp (-α * (stepCount (fun j => ¬large j) K + 1)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
        exact hs.trans (hm.trans_eq hx)


lemma inner_path_counts {f : E → ℝ} {g : E → E} {L0 L1 μ : ℝ}
    (h0 : 0 < L0) (h1 : 0 ≤ L1) (hμ : 0 ≤ μ)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hcont : Continuous g) (hs : CompositeGeneralized.SymmetricSmooth g L0 L1)
    (c p : E) (hmin : ∀ y, regularized f μ c p ≤ regularized f μ c y) (K : ℕ) :
    let B := L0 + μ + 2 * μ * L1 * ‖c - p‖
    let large := fun k => B ≤ L1 * ‖g (innerPath g L0 L1 μ c k) +
      μ • (innerPath g L0 L1 μ c k - c)‖
    (stepCount large K : ℝ) ≤ 1152 * (L1 * ‖c - p‖) ^ 2 ∧
    ‖innerPath g L0 L1 μ c K - p‖ ^ 2 ≤ ‖c - p‖ ^ 2 *
      Real.exp (-(μ / (48 * B)) * stepCount (fun k => ¬large k) K) := by
  classical
  dsimp only
  set B := L0 + μ + 2 * μ * L1 * ‖c - p‖
  let a := fun k => ‖innerPath g L0 L1 μ c k - p‖ ^ 2
  let large := fun k => B ≤ L1 * ‖g (innerPath g L0 L1 μ c k) +
    μ • (innerPath g L0 L1 μ c k - c)‖
  have ha : ∀ k, 0 ≤ a k := fun k => sq_nonneg _
  have hmono : ∀ k, a (k + 1) ≤ a k := by
    intro k
    have hh := inner_step_distance h0 h1 hμ hc hg hcont hs c
      (innerPath g L0 L1 μ c k) p hmin
    have he : innerPath g L0 L1 μ c (k + 1) =
        innerStep L0 L1 μ c (innerPath g L0 L1 μ c k) (g (innerPath g L0 L1 μ c k)) :=
      Function.iterate_succ_apply' _ _ _
    dsimp [a]
    rw [he]
    exact pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hdi := inner_path_dichotomy h0 h1 hμ hc hg hcont hs c p hmin
  have hdec : ∀ k, 1152 * L1 ^ 2 * a (k + 1) + (if large k then 1 else 0) ≤
      1152 * L1 ^ 2 * a k := by
    intro k
    by_cases hh : large k
    · have ht := (hdi k).1 hh
      simp only [hh, ↓reduceIte]
      change 1 ≤ 1152 * L1 ^ 2 * (a k - a (k + 1)) at ht
      nlinarith
    · simp only [hh, ↓reduceIte, add_zero]
      exact mul_le_mul_of_nonneg_left (hmono k) (by positivity)
  have hc' := dichotomy_sum_decrease large (fun k => 1152 * L1 ^ 2 * a k)
    (c := 1) (by simpa using hdec) K
  have hsmall : ∀ k, ¬large k → a (k + 1) ≤ (1 - μ / (48 * B)) * a k := by
    intro k hh
    exact (hdi k).2 (le_of_lt (not_le.mp hh))
  have he := dichotomy_exp_decrease large a ha (fun k _ => hmono k) hsmall K
  constructor
  · change (stepCount large K : ℝ) ≤ _
    have hn : 0 ≤ 1152 * L1 ^ 2 * a K := by positivity
    have hz : a 0 = ‖c - p‖ ^ 2 := rfl
    simp only [one_mul, hz] at hc'
    nlinarith
  · exact he


lemma exponential_distance_threshold {d δ α t a : ℝ}
    (hd : 0 ≤ d)
    (hratio : d ≤ δ * Real.exp (α * t / 2))
    (ha : a ≤ d ^ 2 * Real.exp (-α * t)) : a ≤ δ ^ 2 := by
  have hs := pow_le_pow_left₀ hd hratio 2
  have hm := mul_le_mul_of_nonneg_right hs (Real.exp_nonneg (-α * t))
  have he : (δ * Real.exp (α * t / 2)) ^ 2 * Real.exp (-α * t) = δ ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  exact ha.trans (hm.trans_eq he)

lemma exponential_distance_log_threshold {d δ A α t a : ℝ}
    (hd : 0 ≤ d) (hδ : 0 ≤ δ) (hA : 0 < A)
    (hratio : d ≤ δ * A ^ 3) (ht : 6 * Real.log A ≤ α * t)
    (ha : a ≤ d ^ 2 * Real.exp (-α * t)) : a ≤ δ ^ 2 := by
  apply exponential_distance_threshold hd (ha := ha)
  apply hratio.trans
  apply mul_le_mul_of_nonneg_left _ hδ
  rw [← Real.exp_log hA, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  norm_num
  linarith

lemma residual_threshold_properties {B L ζ : ℝ} (hB : 0 < B)
    (hL : 0 ≤ L) (hζ : 0 < ζ) :
    let δ := ζ / (2 * B + 2 * L * ζ)
    0 < δ ∧ L * δ ≤ 1 / 2 ∧ 2 * B * δ ≤ ζ := by
  dsimp only
  have hden : 0 < 2 * B + 2 * L * ζ := by positivity
  constructor
  · exact div_pos hζ hden
  constructor
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hL (sq_nonneg ζ)]

lemma inner_low_count_threshold {μ B q ell t : ℝ}
    (hμ : 0 < μ) (hB : 0 < B) (hell : 0 ≤ ell)
    (hBupper : B ≤ 2 * μ * (1 + q))
    (ht : 576 * (1 + q) * ell ≤ t) :
    6 * ell ≤ μ / (48 * B) * t := by
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 48 * B)).mpr
  have hb := mul_le_mul_of_nonneg_right hBupper hell
  have hm := mul_le_mul_of_nonneg_left ht hμ.le
  nlinarith

lemma inner_path_threshold {f : E → ℝ} {g : E → E} {L0 L1 μ δ A : ℝ}
    (h0 : 0 < L0) (h1 : 0 ≤ L1) (hμ : 0 < μ) (h0μ : L0 ≤ μ)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hcont : Continuous g) (hs : CompositeGeneralized.SymmetricSmooth g L0 L1)
    (c p : E) (hmin : ∀ y, regularized f μ c p ≤
      regularized f μ c y)
    (hδ : 0 ≤ δ) (hA : 1 ≤ A) (hratio : ‖c - p‖ ≤ δ * A ^ 3) (K : ℕ)
    (hK : 1152 * (L1 * ‖c - p‖) ^ 2 +
      576 * (1 + L1 * ‖c - p‖) * Real.log A ≤ K) :
    ‖innerPath g L0 L1 μ c K - p‖ ≤ δ := by
  classical
  let B := L0 + μ + 2 * μ * L1 * ‖c - p‖
  let large := fun k => B ≤ L1 * ‖g (innerPath g L0 L1 μ c k) +
    μ • (innerPath g L0 L1 μ c k - c)‖
  have hcounts := inner_path_counts h0 h1 hμ.le hc hg hcont hs c p hmin K
  change (stepCount large K : ℝ) ≤ 1152 * (L1 * ‖c - p‖) ^ 2 ∧
    ‖innerPath g L0 L1 μ c K - p‖ ^ 2 ≤ ‖c - p‖ ^ 2 *
      Real.exp (-(μ / (48 * B)) * stepCount (fun k => ¬large k) K) at hcounts
  have hpartition := stepCount_partition large K
  have hp : (stepCount large K : ℝ) + stepCount (fun k => ¬large k) K = K := by
    exact_mod_cast hpartition
  have ht : 576 * (1 + L1 * ‖c - p‖) * Real.log A ≤
      (stepCount (fun k => ¬large k) K : ℝ) := by linarith [hcounts.1]
  have hB : 0 < B := by dsimp [B]; positivity
  have hBu : B ≤ 2 * μ * (1 + L1 * ‖c - p‖) := by dsimp [B]; nlinarith
  have hlow := inner_low_count_threshold hμ hB (Real.log_nonneg hA) hBu ht
  have hh := exponential_distance_log_threshold (norm_nonneg (c - p)) hδ
    (show 0 < A by linarith) hratio hlow hcounts.2
  nlinarith [norm_nonneg (innerPath g L0 L1 μ c K - p)]


omit [CompleteSpace E] in
lemma innerPlan_stops {n : ℕ} (g : Fin n → E → E) (i : Fin n)
    (L0 L1 μ ζ : ℝ) (c : E) (j fuel k : ℕ)
    (hfuel : j < fuel)
    (hstop : ‖g i (innerPath (g i) L0 L1 μ c (k + j)) +
      μ • (innerPath (g i) L0 L1 μ c (k + j) - c)‖ ≤ ζ) :
    ∃ t ≤ j,
      Program.eval (fun q => g q.1 q.2)
        (innerPlan L0 L1 μ ζ i c fuel (innerPath (g i) L0 L1 μ c k)) =
        μ • (c - innerPath (g i) L0 L1 μ c (k + t)) ∧
      ‖g i (innerPath (g i) L0 L1 μ c (k + t)) +
        μ • (innerPath (g i) L0 L1 μ c (k + t) - c)‖ ≤ ζ ∧
      Program.cost (fun q => g q.1 q.2)
        (innerPlan L0 L1 μ ζ i c fuel (innerPath (g i) L0 L1 μ c k)) ≤ j + 1 := by
  induction j generalizing fuel k with
  | zero =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Nat.add_zero] at hstop
          refine ⟨0, le_refl _, ?_, ?_, ?_⟩
          · simp [innerPlan, Program.eval, hstop]
          · simpa using hstop
          · simp [innerPlan, Program.cost, hstop]
  | succ j ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          by_cases hh : ‖g i (innerPath (g i) L0 L1 μ c k) +
            μ • (innerPath (g i) L0 L1 μ c k - c)‖ ≤ ζ
          · refine ⟨0, Nat.zero_le _, ?_, ?_, ?_⟩
            · simp [innerPlan, Program.eval, hh]
            · simpa using hh
            · simp [innerPlan, Program.cost, hh]
          · have hs : ‖g i (innerPath (g i) L0 L1 μ c (k + 1 + j)) +
                μ • (innerPath (g i) L0 L1 μ c (k + 1 + j) - c)‖ ≤ ζ := by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstop
            obtain ⟨t, ht, he, hr, hw⟩ := ih fuel (k + 1) (by omega) hs
            have hpath : innerPath (g i) L0 L1 μ c (k + 1) =
                innerStep L0 L1 μ c (innerPath (g i) L0 L1 μ c k)
                  (g i (innerPath (g i) L0 L1 μ c k)) :=
              Function.iterate_succ_apply' _ _ _
            refine ⟨t + 1, by omega, ?_, ?_, ?_⟩
            · simp only [innerPlan, Program.eval, hh, ↓reduceIte]
              rw [← hpath, he]
              congr 3; omega
            · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr
            · simp only [innerPlan, Program.cost, hh, ↓reduceIte]
              rw [← hpath]
              omega


lemma inner_threshold_ratio {d R L μ B ζ : ℝ}
    (hR : 0 < R) (hL : 0 ≤ L) (hμ : 0 < μ)
    (hB : 0 < B) (hζ : 0 < ζ) (hdR : d ≤ 2 * R)
    (hBu : B ≤ 2 * μ * (1 + L * d)) :
    let A := 4 + L * R + μ * R * (1 + L * R) / ζ
    d ≤ (ζ / (2 * B + 2 * L * ζ)) * A ^ 3 := by
  let A := 4 + L * R + μ * R * (1 + L * R) / ζ
  change d ≤ (ζ / (2 * B + 2 * L * ζ)) * A ^ 3
  have hA : 4 ≤ A := by
    have hp : 0 ≤ μ * R * (1 + L * R) / ζ := by positivity
    dsimp [A]
    nlinarith [mul_nonneg hL hR.le]
  have hq : L * d ≤ 2 * (L * R) := by nlinarith [mul_le_mul_of_nonneg_left hdR hL]
  have hb : B ≤ 4 * μ * (1 + L * R) := by nlinarith
  have hdB := mul_le_mul_of_nonneg_left hdR hB.le
  have hBR := mul_le_mul_of_nonneg_right hb hR.le
  have hLdz := mul_le_mul_of_nonneg_right hq hζ.le
  have hid : A * ζ = 4 * ζ + L * R * ζ + μ * R * (1 + L * R) := by
    dsimp [A]
    field_simp
  have hnum : d * (2 * B + 2 * L * ζ) ≤ 16 * A * ζ := by
    nlinarith [mul_nonneg hL (mul_nonneg hR.le hζ.le)]
  have hcube : 16 * A ≤ A ^ 3 := by nlinarith [sq_nonneg (A - 4)]
  have hden : 0 < 2 * B + 2 * L * ζ := by positivity
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).mpr
  nlinarith [mul_le_mul_of_nonneg_right hcube hζ.le]



lemma inner_total_cost_bound {q ell : ℝ} (hell : 1 ≤ ell) :
    1152 * q ^ 2 + 576 * (1 + q) * ell + 3 ≤ 4096 * ell * (1 + q ^ 2) := by
  have h1 := mul_nonneg (sub_nonneg.mpr hell) (sq_nonneg q)
  have h2 := mul_nonneg (show 0 ≤ ell by linarith) (sq_nonneg (q - 1))
  nlinarith


lemma component_path_residual [ProperSpace E] {f : E → ℝ} {g : E → E}
    {L0 L1 μ R ζ : ℝ} (h0 : 0 < L0) (h1 : 0 ≤ L1) (hμ : 0 < μ)
    (h0μ : L0 ≤ μ) (hR : 0 < R) (hζ : 0 < ζ)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hcont : Continuous g) (hs : CompositeGeneralized.SymmetricSmooth g L0 L1)
    {u : E} (hmin : ∀ y, f u ≤ f y) (c : E) (hd : ‖c - prox g μ c‖ ≤ 2 * R)
    (K : ℕ) (hK : 1152 * (L1 * ‖c - prox g μ c‖) ^ 2 +
      576 * (1 + L1 * ‖c - prox g μ c‖) *
        Real.log (4 + L1 * R + μ * R * (1 + L1 * R) / ζ) ≤ K) :
    ‖g (innerPath g L0 L1 μ c K) + μ • (innerPath g L0 L1 μ c K - c)‖ ≤ ζ := by
  let p := prox g μ c
  let B := L0 + μ + 2 * μ * L1 * ‖c - p‖
  let δ := ζ / (2 * B + 2 * L1 * ζ)
  let A := 4 + L1 * R + μ * R * (1 + L1 * R) / ζ
  have hB : 0 < B := by dsimp [B]; positivity
  have hBu : B ≤ 2 * μ * (1 + L1 * ‖c - p‖) := by dsimp [B]; nlinarith
  have hδ := residual_threshold_properties hB h1 hζ
  have hA : 1 ≤ A := by
    have hn : 0 ≤ μ * R * (1 + L1 * R) / ζ := by positivity
    dsimp [A]
    nlinarith [mul_nonneg h1 hR.le]
  have hr := inner_threshold_ratio hR h1 hμ hB hζ hd hBu
  have hm : ∀ y, regularized f μ c p ≤ regularized f μ c y := by
    intro y
    have hh := component_prox_minimum hc hg hμ hmin c y
    have hn : 0 ≤ μ / 2 * ‖y - p‖ ^ 2 := by positivity
    change regularized f μ c p + μ / 2 * ‖y - p‖ ^ 2 ≤ _ at hh
    linarith
  have hdist := inner_path_threshold h0 h1 hμ h0μ hc hg hcont hs c p hm
    hδ.1.le hA hr K hK
  have hrad : L1 * ‖innerPath g L0 L1 μ c K - p‖ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hdist h1).trans hδ.2.1
  have hres := component_local_residual h0.le h1 hμ hg hcont hs hmin c
    (innerPath g L0 L1 μ c K) hrad
  exact hres.trans ((mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ 2 * B)).trans hδ.2.2)


lemma component_innerPlan_error_cost [ProperSpace E] {n : ℕ}
    (f : Fin n → E → ℝ) (g : Fin n → E → E) (i : Fin n)
    {L0 L1 μ R ζ : ℝ} (h0 : 0 < L0) (h1 : 0 ≤ L1) (hμ : 0 < μ)
    (h0μ : L0 ≤ μ) (hR : 0 < R) (hζ : 0 < ζ)
    (hc : ConvexOn ℝ univ (f i)) (hg : ∀ x, HasGradientAt (f i) (g i x) x)
    (hcont : Continuous (g i)) (hs : CompositeGeneralized.SymmetricSmooth (g i) L0 L1)
    {u : E} (hmin : ∀ y, f i u ≤ f i y) (c : E)
    (hd : ‖c - prox (g i) μ c‖ ≤ 2 * R) (fuel : ℕ)
    (hell : 1 ≤ Real.log (4 + L1 * R + μ * R * (1 + L1 * R) / ζ))
    (hfuel : 4096 * Real.log (4 + L1 * R + μ * R * (1 + L1 * R) / ζ) *
      (1 + (L1 * ‖c - prox (g i) μ c‖) ^ 2) ≤ fuel) :
    ‖Program.eval (fun q => g q.1 q.2) (innerPlan L0 L1 μ ζ i c fuel c) -
      envelopeField (g i) μ c‖ ≤ ζ ∧
    (Program.cost (fun q => g q.1 q.2) (innerPlan L0 L1 μ ζ i c fuel c) : ℝ) ≤
      4096 * Real.log (4 + L1 * R + μ * R * (1 + L1 * R) / ζ) *
        (1 + (L1 * ‖c - prox (g i) μ c‖) ^ 2) := by
  let q := L1 * ‖c - prox (g i) μ c‖
  let ell := Real.log (4 + L1 * R + μ * R * (1 + L1 * R) / ζ)
  let a := 1152 * q ^ 2 + 576 * (1 + q) * ell
  let K := ⌈a⌉₊
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have he : 0 ≤ ell := by dsimp [ell]; linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hround : (K : ℝ) < a + 1 := Nat.ceil_lt_add_one ha
  have hbound : a + 3 ≤ 4096 * ell * (1 + q ^ 2) := inner_total_cost_bound hell
  have hKfuel : K < fuel := by
    change 4096 * ell * (1 + q ^ 2) ≤ (fuel : ℝ) at hfuel
    have hh : (K : ℝ) < (fuel : ℝ) := by linarith
    exact_mod_cast hh
  have hr := component_path_residual h0 h1 hμ h0μ hR hζ hc hg hcont hs hmin c hd K
    (Nat.le_ceil a)
  obtain ⟨t, ht, hout, hres, hcost⟩ := innerPlan_stops g i L0 L1 μ ζ c K fuel 0 hKfuel
    (by simpa using hr)
  simp only [Nat.zero_add] at hout hres
  change Program.eval (fun q => g q.1 q.2) (innerPlan L0 L1 μ ζ i c fuel c) = _ at hout
  change Program.cost (fun q => g q.1 q.2) (innerPlan L0 L1 μ ζ i c fuel c) ≤ K + 1 at hcost
  constructor
  · rw [hout]
    exact (component_residual_error hc hg hμ hmin c (innerPath (g i) L0 L1 μ c t)).trans hres
  · have hc' : (Program.cost (fun q => g q.1 q.2) (innerPlan L0 L1 μ ζ i c fuel c) : ℝ) ≤
        (K : ℝ) + 1 := by exact_mod_cast hcost
    change _ ≤ 4096 * ell * (1 + q ^ 2)
    linarith


end OracleTemplate.ComponentEnvelope
