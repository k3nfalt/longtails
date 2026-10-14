import LongTails.Proofs.AdaptiveEntropicGeometry
import LongTails.Proofs.AdaptiveEntropicSmooth

open scoped RealInnerProductSpace

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

noncomputable def linearPotential {d : ℕ} (B : ℝ) (s : Vector d) (x : simplex d) : ℝ :=
  ⟪s, x.val⟫ + B * entropy x

lemma uniform_entropy (q : Public) : entropy (uniform q) = 0 := by
  have hlog (i : Fin q.d) : Real.log ((uniform q).val i) = -Real.log q.d := by
    simpa [uniform] using softmax_log (by have := q.hd; omega) (0 : Vector q.d) i
  unfold entropy
  simp_rw [hlog]
  rw [← Finset.sum_mul, (uniform q).property.2]
  ring

lemma potential_step {d : ℕ} (hd : 0 < d) {B B' : ℝ} (hB : 0 < B)
    (hBB : B ≤ B') (s g : Vector d) (a : ℝ) (z' : simplex d) :
    let z := softmax hd (-(1 / B) • s)
    a * ⟪g, z'.val⟫ + B / 4 * oneNorm (z'.val - z.val) ^ 2 ≤
      linearPotential B' (s + a • g) z' - linearPotential B s z := by
  intro z
  have hopt := softmax_regularized_lower hd hB s z'
  have hn := mul_nonneg (sub_nonneg.mpr hBB) (entropy_nonneg hd z')
  dsimp only [linearPotential]
  rw [inner_add_left, real_inner_smul_left]
  change B / 4 * oneNorm (z'.val - z.val) ^ 2 ≤
    (⟪s, z'.val⟫ + B * entropy z') - (⟪s, z.val⟫ + B * entropy z) at hopt
  nlinarith

lemma potential_min {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 0 < B)
    (s : Vector d) (x : simplex d) :
    linearPotential B s (softmax hd (-(1 / B) • s)) ≤ linearPotential B s x := by
  have h := softmax_regularized_lower hd hB s x
  have hn : 0 ≤ B / 4 * oneNorm (x.val - (softmax hd (-(1 / B) • s)).val) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  change B / 4 * oneNorm (x.val - (softmax hd (-(1 / B) • s)).val) ^ 2 ≤
    linearPotential B s x - linearPotential B s (softmax hd (-(1 / B) • s)) at h
  linarith

lemma ftrl_regret (q : Public) (B a : ℕ → ℝ) (g : ℕ → Vector q.d)
    (hB : ∀ n, 0 < B n) (hmono : Monotone B) (N : ℕ) (x : simplex q.d) :
    let S := fun n => ∑ i ∈ Finset.range n, a i • g i
    let z := fun n => softmax (by have := q.hd; omega) (-(1 / B n) • S n)
    (∑ i ∈ Finset.range N, a i * ⟪g i, (z (i + 1)).val - x.val⟫) +
      (∑ i ∈ Finset.range N, B i / 4 *
        oneNorm ((z (i + 1)).val - (z i).val) ^ 2) ≤ B N * entropy x := by
  intro S z
  have hS (n : ℕ) : S (n + 1) = S n + a n • g n := Finset.sum_range_succ _ _
  have hzero : z 0 = uniform q := by simp [z, S, uniform]
  have hsum (n : ℕ) :
      (∑ i ∈ Finset.range n, a i * ⟪g i, (z (i + 1)).val⟫) +
        (∑ i ∈ Finset.range n, B i / 4 *
          oneNorm ((z (i + 1)).val - (z i).val) ^ 2) ≤
        linearPotential (B n) (S n) (z n) := by
    induction n with
    | zero => simp [hzero, S, linearPotential, uniform_entropy]
    | succ n ih =>
      have hp := potential_step (by have := q.hd; omega) (hB n)
        (hmono (Nat.le_succ n)) (S n) (g n) (a n) (z (n + 1))
      change a n * ⟪g n, (z (n + 1)).val⟫ + B n / 4 *
        oneNorm ((z (n + 1)).val - (z n).val) ^ 2 ≤
        linearPotential (B (n + 1)) (S n + a n • g n) (z (n + 1)) -
          linearPotential (B n) (S n) (z n) at hp
      rw [← hS n] at hp
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith
  have hp := potential_min (by have := q.hd; omega) (hB N) (S N) x
  change linearPotential (B N) (S N) (z N) ≤ linearPotential (B N) (S N) x at hp
  have hs := (hsum N).trans hp
  have hin : ⟪S N, x.val⟫ = ∑ i ∈ Finset.range N, a i * ⟪g i, x.val⟫ := by
    simp [S, sum_inner, real_inner_smul_left]
  dsimp only [linearPotential] at hs
  rw [hin] at hs
  simp_rw [inner_sub_right, mul_sub]
  rw [Finset.sum_sub_distrib]
  linarith

lemma potential_min_mono {d : ℕ} (hd : 0 < d) {B B' : ℝ}
    (hB : 0 < B) (hBB : B ≤ B') (s : Vector d) :
    linearPotential B s (softmax hd (-(1 / B) • s)) ≤
      linearPotential B' s (softmax hd (-(1 / B') • s)) := by
  have hp := potential_min hd hB s (softmax hd (-(1 / B') • s))
  have hn := mul_nonneg (sub_nonneg.mpr hBB)
    (entropy_nonneg hd (softmax hd (-(1 / B') • s)))
  dsimp only [linearPotential] at *
  linarith

lemma ftrl_recomputed_regret (q : Public) (B a : ℕ → ℝ) (g : ℕ → Vector q.d)
    (hB : ∀ n, 0 < B n) (hmono : Monotone B) (N : ℕ) (x : simplex q.d) :
    let S := fun n => ∑ i ∈ Finset.range n, a i • g i
    let pre := fun n => softmax (by have := q.hd; omega) (-(1 / B n) • S n)
    let post := fun n => softmax (by have := q.hd; omega) (-(1 / B n) • S (n + 1))
    (∑ i ∈ Finset.range N, a i * ⟪g i, (post i).val - x.val⟫) +
      (∑ i ∈ Finset.range N, B i / 4 *
        oneNorm ((post i).val - (pre i).val) ^ 2) ≤ B N * entropy x := by
  intro S pre post
  have hd : 0 < q.d := by have := q.hd; omega
  have hS (n : ℕ) : S (n + 1) = S n + a n • g n := Finset.sum_range_succ _ _
  have hzero : pre 0 = uniform q := by simp [pre, S, uniform]
  have hsum (n : ℕ) :
      (∑ i ∈ Finset.range n, a i * ⟪g i, (post i).val⟫) +
        (∑ i ∈ Finset.range n, B i / 4 *
          oneNorm ((post i).val - (pre i).val) ^ 2) ≤
        linearPotential (B n) (S n) (pre n) := by
    induction n with
    | zero => simp [hzero, S, linearPotential, uniform_entropy]
    | succ n ih =>
      have hp := potential_step hd (hB n) (le_refl (B n))
        (S n) (g n) (a n) (post n)
      change a n * ⟪g n, (post n).val⟫ + B n / 4 *
        oneNorm ((post n).val - (pre n).val) ^ 2 ≤
        linearPotential (B n) (S n + a n • g n) (post n) -
          linearPotential (B n) (S n) (pre n) at hp
      rw [← hS n] at hp
      have hm := potential_min_mono hd (hB n) (hmono (Nat.le_succ n)) (S (n + 1))
      change linearPotential (B n) (S (n + 1)) (post n) ≤
        linearPotential (B (n + 1)) (S (n + 1)) (pre (n + 1)) at hm
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith
  have hp := potential_min hd (hB N) (S N) x
  change linearPotential (B N) (S N) (pre N) ≤ linearPotential (B N) (S N) x at hp
  have hs := (hsum N).trans hp
  have hin : ⟪S N, x.val⟫ = ∑ i ∈ Finset.range N, a i * ⟪g i, x.val⟫ := by
    simp [S, sum_inner, real_inner_smul_left]
  dsimp only [linearPotential] at hs
  rw [hin] at hs
  simp_rw [inner_sub_right, mul_sub]
  rw [Finset.sum_sub_distrib]
  linarith

lemma oracle_error_split {d : ℕ} {a B L : ℝ} (ha : 0 ≤ a) (hB : 0 < B)
    (hLB : 8 * L ≤ B) (u b : Vector d) (pre post xstar : simplex d) :
    a * ⟪-u - b, post.val - xstar.val⟫ +
        (L - B / 4) * oneNorm (post.val - pre.val) ^ 2 ≤
      -a * ⟪u, pre.val - xstar.val⟫ +
        2 * a ^ 2 * dualNorm u ^ 2 / B + 2 * a * dualNorm b := by
  let r := oneNorm (post.val - pre.val)
  have he : ⟪-u - b, post.val - xstar.val⟫ =
      -⟪u, pre.val - xstar.val⟫ - ⟪u, post.val - pre.val⟫ -
        ⟪b, post.val - xstar.val⟫ := by
    simp only [inner_sub_left, inner_sub_right, inner_neg_left]
    ring
  have hu : -⟪u, post.val - pre.val⟫ ≤ dualNorm u * r :=
    (neg_le_abs _).trans (abs_inner_le_dual_one u _)
  have hb : -⟪b, post.val - xstar.val⟫ ≤ 2 * dualNorm b := by
    calc
      _ ≤ |⟪b, post.val - xstar.val⟫| := neg_le_abs _
      _ ≤ dualNorm b * oneNorm (post.val - xstar.val) := abs_inner_le_dual_one b _
      _ ≤ dualNorm b * 2 := mul_le_mul_of_nonneg_left (simplex_diameter post xstar)
        (norm_nonneg _)
      _ = _ := by ring
  have hY : a * dualNorm u * r - B / 8 * r ^ 2 ≤ 2 * a ^ 2 * dualNorm u ^ 2 / B := by
    apply (le_div_iff₀ hB).mpr
    nlinarith [sq_nonneg (B * r - 4 * a * dualNorm u)]
  have hL := mul_le_mul_of_nonneg_right hLB (sq_nonneg r)
  have hua := mul_le_mul_of_nonneg_left hu ha
  have hba := mul_le_mul_of_nonneg_left hb ha
  rw [he]
  change a * (-⟪u, pre.val - xstar.val⟫ - ⟪u, post.val - pre.val⟫ -
    ⟪b, post.val - xstar.val⟫) + (L - B / 4) * r ^ 2 ≤ _
  nlinarith

lemma accelerated_energy (q : Public) {f : Vector q.d → ℝ}
    (hL : 0 ≤ q.L) (hc : ConvexOn ℝ (simplex q.d) f)
    (hg : ∀ x ∈ simplex q.d, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ simplex q.d, ∀ y ∈ simplex q.d,
      dualNorm (gradient f x - gradient f y) ≤ q.L * oneNorm (x - y))
    (B : ℕ → ℝ) (g u b : ℕ → Vector q.d) (y : ℕ → simplex q.d)
    (hB : ∀ n, 0 < B n) (hmono : Monotone B) (hLB : ∀ n, 8 * q.L ≤ B n)
    (N : ℕ) (xstar : simplex q.d) :
    let S := fun n => ∑ i ∈ Finset.range n, ((i : ℝ) + 1) • g i
    let pre := fun n => softmax (by have := q.hd; omega) (-(1 / B n) • S n)
    let post := fun n => softmax (by have := q.hd; omega) (-(1 / B n) • S (n + 1))
    (∀ n, y (n + 1) = mix n (y n) (post n)) →
    (∀ n, gradient f (mix n (y n) (pre n)) - g n = -u n - b n) →
    (N : ℝ) * (N + 1) / 2 * (f (y N) - f xstar) ≤
      B N * entropy xstar + ∑ n ∈ Finset.range N,
        (-((n : ℝ) + 1) * ⟪u n, (pre n).val - xstar.val⟫ +
          2 * ((n : ℝ) + 1) ^ 2 * dualNorm (u n) ^ 2 / B n +
          2 * ((n : ℝ) + 1) * dualNorm (b n)) := by
  intro S pre post hy herr
  let cost := fun (n : ℕ) => -((n : ℝ) + 1) * ⟪u n, (pre n).val - xstar.val⟫ +
    2 * ((n : ℝ) + 1) ^ 2 * dualNorm (u n) ^ 2 / B n +
    2 * ((n : ℝ) + 1) * dualNorm (b n)
  let regret := fun (n : ℕ) => ((n : ℝ) + 1) * ⟪g n, (post n).val - xstar.val⟫ +
    B n / 4 * oneNorm ((post n).val - (pre n).val) ^ 2
  have hstep (n : ℕ) :
      ((n : ℝ) + 1) * (n + 2) / 2 * (f (y (n + 1)) - f xstar) -
        (n : ℝ) * (n + 1) / 2 * (f (y n) - f xstar) ≤ regret n + cost n := by
    have hs := accelerated_weighted_step hL hc hg hlip n (y n) (pre n) (post n) xstar
    rw [← hy n] at hs
    have he := oracle_error_split (by positivity : (0 : ℝ) ≤ n + 1)
      (hB n) (hLB n) (u n) (b n) (pre n) (post n) xstar
    have hgrad : gradient f (mix n (y n) (pre n)) = g n + (-u n - b n) := by
      rw [← herr n]
      module
    rw [hgrad, inner_add_left] at hs
    dsimp [regret, cost]
    linarith
  have hsum (n : ℕ) :
      (n : ℝ) * (n + 1) / 2 * (f (y n) - f xstar) ≤
        ∑ i ∈ Finset.range n, regret i + ∑ i ∈ Finset.range n, cost i := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hs := hstep n
      push_cast
      linarith
  have hf := ftrl_recomputed_regret q B (fun n => (n : ℝ) + 1) g hB hmono N xstar
  change (∑ i ∈ Finset.range N, ((i : ℝ) + 1) * ⟪g i, (post i).val - xstar.val⟫) +
      (∑ i ∈ Finset.range N, B i / 4 * oneNorm ((post i).val - (pre i).val) ^ 2) ≤
        B N * entropy xstar at hf
  have hr : (∑ i ∈ Finset.range N, regret i) ≤ B N * entropy xstar := by
    simpa only [regret, Finset.sum_add_distrib] using hf
  exact (hsum N).trans (add_le_add_left hr _)

lemma weighted_increment_sqrt {x a b D : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a)
    (hb : 0 < b) (hD : 0 ≤ D) (hbound : x + a ≤ D * b ^ 2) :
    a / b ≤ 2 * Real.sqrt D * (Real.sqrt (x + a) - Real.sqrt x) := by
  have hr : Real.sqrt (x + a) ≤ Real.sqrt D * b := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · simpa only [mul_pow, Real.sq_sqrt hD] using hbound
  have hd : 0 ≤ Real.sqrt (x + a) - Real.sqrt x :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hfirst : a ≤ 2 * Real.sqrt (x + a) * (Real.sqrt (x + a) - Real.sqrt x) := by
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt (add_nonneg hx ha),
      sq_nonneg (Real.sqrt (x + a) - Real.sqrt x)]
  have hsecond := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2)) hd
  apply (div_le_iff₀ hb).mpr
  calc
    a ≤ 2 * Real.sqrt (x + a) * (Real.sqrt (x + a) - Real.sqrt x) := hfirst
    _ ≤ 2 * (Real.sqrt D * b) * (Real.sqrt (x + a) - Real.sqrt x) := hsecond
    _ = _ := by ring

lemma weighted_sum_sqrt_bound (a b : ℕ → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 < b n)
    (hbound : ∀ n, (∑ i ∈ Finset.range (n + 1), a i) ≤ D * (b n) ^ 2) (N : ℕ) :
    (∑ i ∈ Finset.range N, a i / b i) ≤
      2 * Real.sqrt D * Real.sqrt (∑ i ∈ Finset.range N, a i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hc := hbound N
    rw [Finset.sum_range_succ] at hc
    have h := weighted_increment_sqrt (Finset.sum_nonneg (fun i _ => ha i))
      (ha N) (hb N) hD hc
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

lemma normalized_quadratic_range {w c U B D K : ℝ}
    (hc : 0 ≤ c) (hu : c ≤ U) (hB : 0 < B) (hD : 0 ≤ D) (hK : 0 < K)
    (hw : w ≤ 4 * c ^ 2) (hcap : c ≤ B * D / (4 * K)) :
    w / B ≤ U * D / K := by
  have hcap' := (le_div_iff₀ (show 0 < 4 * K by positivity)).mp hcap
  have h1 := mul_le_mul_of_nonneg_right hw hK.le
  have h2 := mul_le_mul_of_nonneg_right hcap' hc
  have h3 := mul_le_mul_of_nonneg_left hu (mul_nonneg hB.le hD)
  apply (div_le_iff₀ hB).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hK).mpr
  nlinarith

lemma quadratic_concentration_transfer {observed conditional pairConditional pairObserved b H : ℝ}
    (hf : observed ≤ 2 * conditional + 2 * b * H)
    (hv : conditional ≤ pairConditional)
    (hi : pairConditional ≤ 2 * pairObserved + 4 * b * H) :
    2 * observed ≤ 8 * pairObserved + 20 * b * H := by
  linarith

lemma clipped_increment_le_regularization_sq {c B D K : ℝ}
    (hc : 0 ≤ c) (hD : 0 ≤ D) (hK : 1 ≤ K) (hDK : D ≤ K)
    (hcap : c ≤ B * D / (4 * K)) : 4 * c ^ 2 ≤ D * B ^ 2 / 4 := by
  have hKpos : 0 < K := by linarith
  have hKsq : K ≤ K ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hK hKpos.le
    nlinarith
  have hratio : D / K ^ 2 ≤ 1 := (div_le_one₀ (sq_pos_of_pos hKpos)).mpr (hDK.trans hKsq)
  have hp := pow_le_pow_left₀ hc hcap 2
  calc
    4 * c ^ 2 ≤ 4 * (B * D / (4 * K)) ^ 2 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = D * B ^ 2 / 4 * (D / K ^ 2) := by field_simp
    _ ≤ D * B ^ 2 / 4 := mul_le_of_le_one_right (by positivity) hratio

end OracleTemplate.AdaptiveHeavyTailSimplex
