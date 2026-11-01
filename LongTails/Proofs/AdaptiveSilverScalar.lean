import LongTails.Proofs.SilverNonexpansive
import LongTails.Proofs.WeaklyConvexSilverInduction

namespace LongTails.Proofs.AdaptiveSilverScalar

open LongTails.Algorithms.SilverSchedule
open LongTails.Proofs.SilverCertificate
open LongTails.Proofs.SilverTrace

noncomputable def pr (μ : ℝ) (hs : List ℝ) : ℝ := (hs.map (fun h => 1 - h * μ)).prod

lemma pr_nil (μ : ℝ) : pr μ [] = 1 := rfl

lemma pr_cons (μ h : ℝ) (hs : List ℝ) : pr μ (h :: hs) = (1 - h * μ) * pr μ hs := by
  simp [pr]

lemma pr_append (μ : ℝ) (a b : List ℝ) : pr μ (a ++ b) = pr μ a * pr μ b := by
  simp [pr]

lemma pr_reverse (μ : ℝ) (a : List ℝ) : pr μ a.reverse = pr μ a := by
  simp [pr, List.map_reverse, List.prod_reverse]

lemma run_scalar (μ : ℝ) (hs : List ℝ) (x : ℝ) :
    run (fun y : ℝ => μ * y) hs x = pr μ hs * x := by
  induction hs generalizing x with
  | nil => simp [run, pr_nil]
  | cons h t ih =>
    simp only [run, ih, pr_cons, smul_eq_mul]
    ring

lemma run_mem_nodes_prefix {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → E) (l r : List ℝ) (x : E) : run g l x ∈ nodes g (l ++ r) x := by
  induction l generalizing x with
  | nil => simpa [run] using start_mem_nodes g r x
  | cons h t ih =>
    simp only [run, List.cons_append, nodes]
    exact List.mem_cons_of_mem _ (ih _)

lemma scalar_defect {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (u v : ℝ) :
    0 ≤ defect (μ * u ^ 2 / 2) (μ * v ^ 2 / 2) u v (μ * u) (μ * v) := by
  simp only [defect, Real.norm_eq_abs, sq_abs, RCLike.inner_apply, conj_trivial]
  nlinarith [mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1)) (sq_nonneg (u - v))]

lemma prefix_bound {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (k : ℕ) {l : List ℝ}
    (hl : l <+: steps k) : |pr μ l| ≤ 1 := by
  obtain ⟨r, hr⟩ := hl
  have hz : (fun y : ℝ => μ * y) 0 = 0 := by simp
  have hn := LongTails.Proofs.SilverNonexpansive.nonexpansive (fun y : ℝ => μ * y ^ 2 / 2)
    (fun y : ℝ => μ * y) (fun u v => scalar_defect h0 h1 u v) k 1 0 hz
  have hm := run_mem_nodes_prefix (fun y : ℝ => μ * y) l r 1
  rw [hr] at hm
  have := hn _ hm
  simpa [run_scalar, Real.norm_eq_abs] using this

lemma steps_reverse (k : ℕ) : (steps k).reverse = steps k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [steps, ih]

lemma suffix_bound {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (k : ℕ) {l : List ℝ}
    (hl : l <:+ steps k) : |pr μ l| ≤ 1 := by
  have hp : l.reverse <+: steps k := by
    have := hl.reverse
    rwa [steps_reverse] at this
  rw [← pr_reverse]
  exact prefix_bound h0 h1 k hp

noncomputable def window (k : ℕ) : ℝ := max 1 (ratio ^ k / ratio ^ 2)

lemma window_mono (k : ℕ) : window k ≤ window (k + 1) := by
  unfold window
  apply max_le_max le_rfl
  apply div_le_div_of_nonneg_right _ (by positivity)
  have := ratio_gt_two
  exact pow_le_pow_right₀ (by linarith) (Nat.le_succ k)

lemma one_le_window (k : ℕ) : 1 ≤ window k := le_max_left _ _

lemma middle_bound {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (k : ℕ) :
    |1 - (1 + ratio ^ k / ratio) * μ| ≤ window (k + 1) := by
  have hr := ratio_gt_two
  have hq : 0 ≤ ratio ^ k / ratio := div_nonneg (by positivity) (by linarith)
  have heq : ratio ^ (k + 1) / ratio ^ 2 = ratio ^ k / ratio := by
    rw [pow_succ, pow_two]
    field_simp
  unfold window
  rw [heq]
  rw [abs_le]
  constructor
  · have : (1 + ratio ^ k / ratio) * μ ≤ 1 + ratio ^ k / ratio := by nlinarith
    have := le_max_right 1 (ratio ^ k / ratio)
    linarith
  · have : 0 ≤ (1 + ratio ^ k / ratio) * μ := by positivity
    have := le_max_left 1 (ratio ^ k / ratio)
    linarith

lemma single_prefix_bound {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) (k : ℕ) {l : List ℝ}
    (hl : l <+: [1 + ratio ^ k / ratio]) : |pr μ l| ≤ window (k + 1) := by
  rw [List.prefix_iff_eq_take] at hl
  have hlen : l.length ≤ 1 := by
    have := congrArg List.length hl
    rw [List.length_take] at this
    simp at this
    omega
  interval_cases h : l.length
  · rw [List.length_eq_zero_iff.mp h]
    simp [pr_nil, one_le_window]
  · rw [hl]
    simp only [List.take_one, List.head?_cons, Option.toList_some, pr_cons, pr_nil, mul_one]
    exact middle_bound h0 h1 k

lemma infix_bound {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) :
    ∀ (k : ℕ) {l : List ℝ}, l <:+: steps k → |pr μ l| ≤ window k
  | 0, l, hl => by
    have : l = [] := List.eq_nil_of_infix_nil hl
    subst this
    simp [pr_nil, one_le_window]
  | k + 1, l, hl => by
    have hstep : steps (k + 1) = steps k ++ ([1 + ratio ^ k / ratio] ++ steps k) := by
      simp [steps]
    rw [hstep] at hl
    have ih := fun {l : List ℝ} (h : l <:+: steps k) => infix_bound h0 h1 k h
    have hw := window_mono k
    rcases List.infix_append_iff.mp hl with h | h | ⟨l₁, l₂, rfl, hl₁, hl₂⟩
    · exact (ih h).trans hw
    · rcases List.infix_append_iff.mp h with h' | h' | ⟨a, b, rfl, ha, hb⟩
      · rcases List.infix_cons_iff.mp h' with h'' | h''
        · exact single_prefix_bound h0 h1 k h''
        · have := List.eq_nil_of_infix_nil h''
          subst this
          simp [pr_nil, one_le_window]
      · exact (ih h').trans hw
      · rw [pr_append, abs_mul]
        have hb' := prefix_bound h0 h1 k hb
        have ha' : |pr μ a| ≤ window (k + 1) := by
          rcases List.suffix_cons_iff.mp ha with h'' | h''
          · rw [h'']
            simp only [pr_cons, pr_nil, mul_one]
            exact middle_bound h0 h1 k
          · have := List.eq_nil_of_suffix_nil h''
            subst this
            simp [pr_nil, one_le_window]
        calc |pr μ a| * |pr μ b| ≤ window (k + 1) * 1 :=
              mul_le_mul ha' hb' (abs_nonneg _) (by linarith [one_le_window (k + 1)])
          _ = window (k + 1) := mul_one _
    · rw [pr_append, abs_mul]
      have ha' := suffix_bound h0 h1 k hl₁
      have hb' : |pr μ l₂| ≤ window (k + 1) := by
        rcases List.infix_append_iff.mp hl₂.isInfix with h' | h' | ⟨a, b, hab, ha, hb⟩
        · rcases List.infix_cons_iff.mp h' with h'' | h''
          · exact single_prefix_bound h0 h1 k h''
          · have := List.eq_nil_of_infix_nil h''
            subst this
            simp [pr_nil, one_le_window]
        · exact (ih h').trans hw
        · rw [hab, pr_append, abs_mul]
          have hb'' := prefix_bound h0 h1 k hb
          have ha'' : |pr μ a| ≤ window (k + 1) := by
            rcases List.suffix_cons_iff.mp ha with h'' | h''
            · rw [h'']
              simp only [pr_cons, pr_nil, mul_one]
              exact middle_bound h0 h1 k
            · have := List.eq_nil_of_suffix_nil h''
              subst this
              simp [pr_nil, one_le_window]
          calc |pr μ a| * |pr μ b| ≤ window (k + 1) * 1 :=
                mul_le_mul ha'' hb'' (abs_nonneg _) (by linarith [one_le_window (k + 1)])
            _ = window (k + 1) := mul_one _
      calc |pr μ l₁| * |pr μ l₂| ≤ 1 * window (k + 1) :=
            mul_le_mul ha' hb' (abs_nonneg _) (by norm_num)
        _ = window (k + 1) := one_mul _

lemma block_certificate {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) {K : ℕ} (hK : 2 ≤ K) :
    ((steps K).sum + 1) * μ * pr μ (steps K) ^ 2 ≤ 2 * (1 - pr μ (steps K) ^ 2) := by
  have hb := LongTails.Proofs.WeaklyConvexSilverInduction.block_descent
    (f := fun y : ℝ => μ * y ^ 2 / 2) (g := fun y : ℝ => μ * y) (ρ := 0) le_rfl
    (fun x y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg h0]
      exact mul_le_of_le_one_left (abs_nonneg _) h1)
    (fun u v => by simpa using scalar_defect h0 h1 u v) hK (by norm_num) 1
  simp only [run_scalar, mul_one, Real.norm_eq_abs, sq_abs] at hb
  rcases h0.lt_or_eq with hpos | hzero
  · have hS : 0 ≤ (steps K).sum := by rw [steps_sum]; linarith [one_le_pow₀ (n := K) (by linarith [ratio_gt_two] : (1:ℝ) ≤ ratio)]
    nlinarith [sq_nonneg (pr μ (steps K))]
  · subst hzero
    simp [pr]

end LongTails.Proofs.AdaptiveSilverScalar
