import LongTails.Proofs.ArrowHurwiczMultiplier
import LongTails.Proofs.ArrowHurwiczRate

open Real Finset
open scoped RealInnerProductSpace

namespace OracleTemplate.ArrowHurwicz

noncomputable def padSeq {G : Type*} [AddCommGroup G] (x : ℕ → G) (T : ℕ) (k : ℤ) : G :=
  if 1 ≤ k ∧ k ≤ (T : ℤ) then x k.toNat - x 0 else 0

lemma padSeq_zero {G : Type*} [AddCommGroup G] (x : ℕ → G) (T : ℕ) (k : ℤ) (hk : ¬ (1 ≤ k ∧ k ≤ (T : ℤ))) :
    padSeq x T k = 0 := by
  unfold padSeq; rw [ite_eq_right hk]

lemma padSeq_nat {G : Type*} [AddCommGroup G] (x : ℕ → G) (T t : ℕ) (ht : t ≤ T) :
    padSeq x T (t : ℤ) = x t - x 0 := by
  unfold padSeq
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h; simp
  · rw [ite_eq_left (by omega)]; simp

variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

section Friction

variable (K : E →L[ℝ] F) (adj : F → E) (g : E → ℝ) (h : F → ℝ) (X : Set E) (Y : Set F)
  (x : ℕ → E) (y : ℕ → F) (η L R M : ℝ) (T : ℕ)

noncomputable def padPot (k : ℤ) : ℝ :=
  if 1 ≤ k ∧ k ≤ (T : ℤ) then (g (x k.toNat) + h (y k.toNat)) - (g (x 0) + h (y 0)) else 0

noncomputable def resid (t : ℕ) (s : ℤ) : ℝ :=
  ⟪x t - η • adj (y t) - x (t + 1), padSeq x T s⟫ + ⟪y t + η • K (x (t + 1)) - y (t + 1), padSeq y T s⟫

lemma padSeq_norm {G : Type*} [NormedAddCommGroup G] (x : ℕ → G) (S : Set G) (hm : ∀ t, x t ∈ S)
    (hb : ∀ a ∈ S, ‖a‖ ≤ R) (k : ℤ) : ‖padSeq x T k‖ ≤ 2 * R := by
  have hR : 0 ≤ R := le_trans (norm_nonneg _) (hb _ (hm 0))
  unfold padSeq
  split_ifs
  · calc _ ≤ ‖x k.toNat‖ + ‖x 0‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hb _ (hm _)) (hb _ (hm _))
      _ = 2 * R := by ring
  · simp; linarith

lemma padSeq_mem {G : Type*} [AddCommGroup G] (x : ℕ → G) (S : Set G) (hm : ∀ t, x t ∈ S) (k : ℤ) :
    x 0 + padSeq x T k ∈ S := by
  unfold padSeq
  split_ifs
  · simpa using hm _
  · simpa using hm 0

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
lemma padPot_eq (k : ℤ) :
    padPot g h x y T k = (g (x 0 + padSeq x T k) + h (y 0 + padSeq y T k)) - (g (x 0) + h (y 0)) := by
  unfold padPot padSeq
  split_ifs <;> simp

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
lemma padPot_abs (memx : ∀ t, x t ∈ X) (memy : ∀ t, y t ∈ Y) (bX : ∀ a ∈ X, ‖a‖ ≤ R)
    (bY : ∀ a ∈ Y, ‖a‖ ≤ R) (hM : 0 ≤ M) (lipg : ∀ a ∈ X, ∀ b ∈ X, |g a - g b| ≤ M * ‖a - b‖)
    (liph : ∀ a ∈ Y, ∀ b ∈ Y, |h a - h b| ≤ M * ‖a - b‖) (k : ℤ) :
    |padPot g h x y T k| ≤ 4 * (M * R) := by
  rw [padPot_eq]
  have e : g (x 0 + padSeq x T k) + h (y 0 + padSeq y T k) - (g (x 0) + h (y 0)) =
      (g (x 0 + padSeq x T k) - g (x 0)) + (h (y 0 + padSeq y T k) - h (y 0)) := by ring
  rw [e]
  have a1 := lipg _ (padSeq_mem T x X memx k) _ (memx 0)
  have a2 := liph _ (padSeq_mem T y Y memy k) _ (memy 0)
  simp only [add_sub_cancel_left] at a1 a2
  have n1 := padSeq_norm R T x X memx bX k
  have n2 := padSeq_norm R T y Y memy bY k
  calc _ ≤ |g (x 0 + padSeq x T k) - g (x 0)| + |h (y 0 + padSeq y T k) - h (y 0)| := abs_add_le _ _
    _ ≤ M * (2 * R) + M * (2 * R) := add_le_add (a1.trans (mul_le_mul_of_nonneg_left n1 hM))
        (a2.trans (mul_le_mul_of_nonneg_left n2 hM))
    _ = 4 * (M * R) := by ring

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
lemma padPot_supp (k : ℤ) (hk : padPot g h x y T k ≠ 0) : 1 ≤ k ∧ k ≤ T := by
  by_contra hc; apply hk; unfold padPot; rw [ite_eq_right hc]

lemma bandH_reflect_sum (t : ℕ) (ht : t < T) :
    ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) = 0 := by
  rw [win_reflect (3 * T + 3) ((t : ℤ) + 1) (bandH T) (by
    intro k hk
    have := bandH_supp T k hk
    rw [abs_le] at this ⊢
    constructor
    · constructor <;> omega
    · rw [abs_le]; constructor <;> omega)]
  exact bandH_sum T

lemma friction_lower (memx : ∀ t, x t ∈ X) (memy : ∀ t, y t ∈ Y)
    (bX : ∀ a ∈ X, ‖a‖ ≤ R) (bY : ∀ a ∈ Y, ‖a‖ ≤ R) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (lipg : ∀ a ∈ X, ∀ b ∈ X, |g a - g b| ≤ M * ‖a - b‖)
    (liph : ∀ a ∈ Y, ∀ b ∈ Y, |h a - h b| ≤ M * ‖a - b‖)
    (vix : ∀ t, ∀ w ∈ X, ⟪x t - η • adj (y t) - x (t + 1), w - x (t + 1)⟫ ≤ η * (g w - g (x (t + 1))))
    (viy : ∀ t, ∀ w ∈ Y, ⟪y t + η • K (x (t + 1)) - y (t + 1), w - y (t + 1)⟫ ≤ η * (h w - h (y (t + 1)))) :
    ∑ t ∈ range T, (⟪x t - η • adj (y t) - x (t + 1), x (t + 1) - x t⟫ +
        ⟪y t + η • K (x (t + 1)) - y (t + 1), y (t + 1) - y t⟫) - η * (4 * (M * R)) * 13.79 ≤
      ∑ t ∈ range T, ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * resid K adj x y η T t s := by
  obtain ⟨hβ, -, -, hβK⟩ := bandBeta_facts T
  set ψ := padPot g h x y T
  have step : ∀ t ∈ range T,
      (⟪x t - η • adj (y t) - x (t + 1), x (t + 1) - x t⟫ +
        ⟪y t + η • K (x (t + 1)) - y (t + 1), y (t + 1) - y t⟫) +
        bandBeta T * η * ∑ s ∈ win (3 * T + 3), bandU T ((t : ℤ) + 1 - s) * (ψ ((t : ℤ) + 1) - ψ s) ≤
      ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * resid K adj x y η T t s := by
    intro t ht
    have ht' := mem_range.mp ht
    set D : ℤ → ℝ := fun s => resid K adj x y η T t s - resid K adj x y η T t ((t : ℤ) + 1)
    have e0 : ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * resid K adj x y η T t s =
        ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * D s := by
      simp only [D, mul_sub, sum_sub_distrib, ← sum_mul, bandH_reflect_sum T t ht', zero_mul, sub_zero]
    have hmem : (t : ℤ) ∈ win (3 * T + 3) := mem_win.mpr (by rw [abs_of_nonneg (by omega)]; omega)
    have e1 : ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * D s =
        -D t - bandBeta T * ∑ s ∈ win (3 * T + 3), bandU T ((t : ℤ) + 1 - s) * D s := by
      unfold bandH
      simp only [sub_mul, sum_sub_distrib, mul_sum]
      have z0 : ∑ s ∈ win (3 * T + 3), (if (t : ℤ) + 1 - s = 0 then 1 + bandBeta T * bandMass T else 0) * D s = 0 := by
        apply sum_eq_zero; intro s _
        by_cases hs : (t : ℤ) + 1 - s = 0
        · have : s = (t : ℤ) + 1 := by omega
          subst this; simp [D]
        · rw [ite_eq_right hs, zero_mul]
      have z1 : ∑ s ∈ win (3 * T + 3), (if (t : ℤ) + 1 - s = 1 then (1 : ℝ) else 0) * D s = D t := by
        rw [sum_eq_single (t : ℤ)]
        · rw [ite_eq_left (by ring)]; ring
        · intro s _ hs; rw [ite_eq_right (by omega), zero_mul]
        · intro h; exact absurd hmem h
      rw [z0, z1]
      simp only [mul_assoc]; ring
    have dt : -D t = ⟪x t - η • adj (y t) - x (t + 1), x (t + 1) - x t⟫ +
        ⟪y t + η • K (x (t + 1)) - y (t + 1), y (t + 1) - y t⟫ := by
      simp only [D, resid]
      have p1 := padSeq_nat x T t (by omega)
      have p2 := padSeq_nat x T (t + 1) (by omega)
      have p3 := padSeq_nat y T t (by omega)
      have p4 := padSeq_nat y T (t + 1) (by omega)
      push_cast at p2 p4
      rw [p1, p2, p3, p4]
      have q1 : x (t + 1) - x t = (x (t + 1) - x 0) - (x t - x 0) := by abel
      have q2 : y (t + 1) - y t = (y (t + 1) - y 0) - (y t - y 0) := by abel
      simp only [inner_sub_right]; ring
    have ds : ∀ s, η * (ψ ((t : ℤ) + 1) - ψ s) ≤ -D s := by
      intro s
      have w1 := vix t _ (padSeq_mem T x X memx s)
      have w2 := viy t _ (padSeq_mem T y Y memy s)
      have p2 := padSeq_nat x T (t + 1) (by omega)
      have p4 := padSeq_nat y T (t + 1) (by omega)
      push_cast at p2 p4
      simp only [ψ, padPot_eq, D, resid]
      rw [p2, p4]
      simp only [add_sub_cancel]
      have q1 : x 0 + padSeq x T s - x (t + 1) = -((x (t + 1) - x 0) - padSeq x T s) := by abel
      have q2 : y 0 + padSeq y T s - y (t + 1) = -((y (t + 1) - y 0) - padSeq y T s) := by abel
      rw [q1, inner_neg_right, inner_sub_right] at w1
      rw [q2, inner_neg_right, inner_sub_right] at w2
      nlinarith
    rw [e0, e1, ← dt]
    have hu : ∀ s ∈ win (3 * T + 3), bandU T ((t : ℤ) + 1 - s) * (η * (ψ ((t : ℤ) + 1) - ψ s)) ≤
        bandU T ((t : ℤ) + 1 - s) * (-D s) := fun s _ => mul_le_mul_of_nonneg_left (ds s) (bandU_nonneg _ _)
    have := sum_le_sum hu
    have h2 : bandBeta T * ∑ s ∈ win (3 * T + 3), bandU T ((t : ℤ) + 1 - s) * (η * (ψ ((t : ℤ) + 1) - ψ s)) ≤
        bandBeta T * ∑ s ∈ win (3 * T + 3), bandU T ((t : ℤ) + 1 - s) * (-D s) :=
      mul_le_mul_of_nonneg_left this hβ.le
    have e3 : bandBeta T * ∑ s ∈ win (3 * T + 3), bandU T ((t : ℤ) + 1 - s) * (η * (ψ ((t : ℤ) + 1) - ψ s)) =
        bandBeta T * η * ∑ s ∈ win (3 * T + 3), bandU T ((t : ℤ) + 1 - s) * (ψ ((t : ℤ) + 1) - ψ s) := by
      simp only [mul_sum]; apply sum_congr rfl; intro s _; ring
    have e4 : bandBeta T * ∑ s ∈ win (3 * T + 3), bandU T ((t : ℤ) + 1 - s) * (-D s) =
        -(bandBeta T * ∑ s ∈ win (3 * T + 3), bandU T ((t : ℤ) + 1 - s) * D s) := by
      rw [← mul_neg, ← sum_neg_distrib]; congr 1; apply sum_congr rfl; intro s _; ring
    linarith
  have lb := lag_bound T (3 * T + 3) (bandU T) ψ (4 * (M * R)) (padPot_supp g h x y T)
    (padPot_abs g h X Y x y R M T memx memy bX bY hM lipg liph) (by
      intro k hk
      rcases bandU_supp T k hk with h1 | h1 <;> rw [abs_le] <;> constructor <;> omega) (by omega)
  have lb' := (abs_le.mp lb).1
  have hsum := sum_le_sum step
  rw [sum_add_distrib, ← mul_sum] at hsum
  have hk : bandBeta T * η * (4 * (M * R) * ∑ k ∈ win (3 * T + 3), |(k : ℝ)| * bandU T k) ≤
      η * (4 * (M * R)) * 13.79 := by
    have hR : 0 ≤ R := le_trans (norm_nonneg _) (bX _ (memx 0))
    have : 0 ≤ η * (4 * (M * R)) := by positivity
    have e : bandBeta T * η * (4 * (M * R) * ∑ k ∈ win (3 * T + 3), |(k : ℝ)| * bandU T k) =
        η * (4 * (M * R)) * (bandBeta T * ∑ k ∈ win (3 * T + 3), |(k : ℝ)| * bandU T k) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left hβK this
  have hu0 : ∀ k, |bandU T k| = bandU T k := fun k => abs_of_nonneg (bandU_nonneg T k)
  simp only [hu0] at lb'
  have hb2 : bandBeta T * η * (-(4 * (M * R) * ∑ k ∈ win (3 * T + 3), |(k : ℝ)| * bandU T k)) ≤
      bandBeta T * η * ∑ t ∈ range T, ∑ s ∈ win (3 * T + 3), bandU T ((t : ℤ) + 1 - s) * (ψ ((t : ℤ) + 1) - ψ s) :=
    mul_le_mul_of_nonneg_left lb' (by positivity)
  linarith

lemma inner_K_abs {L : ℝ} (hK : ‖K‖ ≤ L) (u : F) (v : E) : |⟪u, K v⟫| ≤ L * (‖u‖ * ‖v‖) := by
  have hL : 0 ≤ L := le_trans (norm_nonneg _) hK
  calc |⟪u, K v⟫| ≤ ‖u‖ * ‖K v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖ * (L * ‖v‖) := mul_le_mul_of_nonneg_left (le_trans (K.le_opNorm v) (by gcongr)) (norm_nonneg _)
    _ = L * (‖u‖ * ‖v‖) := by ring

lemma resid_split (hadj : ∀ a b, ⟪adj a, b⟫ = ⟪a, K b⟫) (t : ℕ) (ht : t < T) (s : ℤ) :
    resid K adj x y η T t s =
      ((⟪padSeq x T t, padSeq x T s⟫ + ⟪padSeq y T t, padSeq y T s⟫) -
        (⟪padSeq x T ((t : ℤ) + 1), padSeq x T s⟫ + ⟪padSeq y T ((t : ℤ) + 1), padSeq y T s⟫) -
        η * ⟪padSeq y T t, K (padSeq x T s)⟫ + η * ⟪padSeq y T s, K (padSeq x T ((t : ℤ) + 1))⟫) +
      η * (⟪padSeq y T s, K (x 0)⟫ - ⟪y 0, K (padSeq x T s)⟫) := by
  have p1 := padSeq_nat x T t (by omega)
  have p2 := padSeq_nat x T (t + 1) (by omega)
  have p3 := padSeq_nat y T t (by omega)
  have p4 := padSeq_nat y T (t + 1) (by omega)
  push_cast at p2 p4
  rw [p1, p2, p3, p4]
  unfold resid
  simp only [inner_sub_left, inner_add_left, inner_smul_left, hadj, map_sub, inner_sub_right,
    RCLike.conj_to_real]
  rw [real_inner_comm (K (x (t + 1))) (padSeq y T s)]
  ring

noncomputable def cayForm (xp : ℤ → E) (yp : ℤ → F) (t s : ℤ) : ℝ :=
  (⟪xp t, xp s⟫ + ⟪yp t, yp s⟫) - (⟪xp (t + 1), xp s⟫ + ⟪yp (t + 1), yp s⟫) -
    η * ⟪yp t, K (xp s)⟫ + η * ⟪yp s, K (xp (t + 1))⟫

lemma friction_upper (hadj : ∀ a b, ⟪adj a, b⟫ = ⟪a, K b⟫) (memx : ∀ t, x t ∈ X) (memy : ∀ t, y t ∈ Y)
    (bX : ∀ a ∈ X, ‖a‖ ≤ R) (bY : ∀ a ∈ Y, ‖a‖ ≤ R) (hK : ‖K‖ ≤ L) (hη : 0 ≤ η) (hηL : η * L ≤ 1 / 2) :
    ∑ t ∈ range T, ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * resid K adj x y η T t s ≤
      150 * R ^ 2 := by
  have hR : 0 ≤ R := le_trans (norm_nonneg _) (bX _ (memx 0))
  have hL : 0 ≤ L := le_trans (norm_nonneg _) hK
  have nx : ∀ k, ‖padSeq x T k‖ ≤ 2 * R := padSeq_norm R T x X memx bX
  have ny : ∀ k, ‖padSeq y T k‖ ≤ 2 * R := padSeq_norm R T y Y memy bY
  have nx0 : ‖x 0‖ ≤ R := bX _ (memx 0)
  have ny0 : ‖y 0‖ ≤ R := bY _ (memy 0)
  have hmass := bandH_mass T
  set a : ℤ → ℝ := fun s => η * (⟪padSeq y T s, K (x 0)⟫ - ⟪y 0, K (padSeq x T s)⟫) with ha
  have e1 : ∑ t ∈ range T, ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * resid K adj x y η T t s =
      ∑ t ∈ range T, ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * cayForm K η (padSeq x T) (padSeq y T) t s +
        ∑ t ∈ range T, ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * a s := by
    rw [← sum_add_distrib]; apply sum_congr rfl; intro t ht
    rw [← sum_add_distrib]; apply sum_congr rfl; intro s _
    rw [resid_split K adj x y η T hadj t (mem_range.mp ht) s]
    simp only [cayForm, a]; ring
  have cz : ∀ t s : ℤ, ¬ (0 ≤ t ∧ t < (T : ℤ) + 1) → cayForm K η (padSeq x T) (padSeq y T) t s = 0 := by
    intro t s ht
    have h1 := padSeq_zero x T t (by omega)
    have h2 := padSeq_zero x T (t + 1) (by omega)
    have h3 := padSeq_zero y T t (by omega)
    have h4 := padSeq_zero y T (t + 1) (by omega)
    simp [cayForm, h1, h2, h3, h4]
  have split : ∑ t ∈ win (3 * T + 3), ∑ s ∈ win (3 * T + 3), bandH T (t + 1 - s) *
        cayForm K η (padSeq x T) (padSeq y T) t s =
      ∑ t ∈ range T, ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * cayForm K η (padSeq x T) (padSeq y T) t s +
        ∑ s ∈ win (3 * T + 3), bandH T ((T : ℤ) + 1 - s) * cayForm K η (padSeq x T) (padSeq y T) T s := by
    rw [win_sum_range (3 * T + 3) 0 (T + 1) _ (by
      intro t ht; by_contra hc; apply ht
      exact sum_eq_zero fun s _ => by rw [cz t s (by push_cast at hc; omega), mul_zero]) (by omega) (by omega)]
    rw [sum_range_succ]; simp only [zero_add]
  have hfull : ∑ t ∈ win (3 * T + 3), ∑ s ∈ win (3 * T + 3), bandH T (t + 1 - s) *
      cayForm K η (padSeq x T) (padSeq y T) t s ≤ 0 :=
    qfull_nonpos K hK hη hηL T (padSeq x T) (padSeq y T) (padSeq_zero x T) (padSeq_zero y T)
  have cT : ∀ s, |cayForm K η (padSeq x T) (padSeq y T) T s| ≤ 10 * R ^ 2 := by
    intro s
    have z1 := padSeq_zero x T ((T : ℤ) + 1) (by omega)
    have z2 := padSeq_zero y T ((T : ℤ) + 1) (by omega)
    simp only [cayForm, z1, z2, inner_zero_left, map_zero, inner_zero_right, add_zero, sub_zero, mul_zero]
    have i1 : |⟪padSeq x T T, padSeq x T s⟫| ≤ 4 * R ^ 2 := by
      calc _ ≤ ‖padSeq x T T‖ * ‖padSeq x T s‖ := abs_real_inner_le_norm _ _
        _ ≤ (2 * R) * (2 * R) := mul_le_mul (nx _) (nx _) (norm_nonneg _) (by linarith)
        _ = 4 * R ^ 2 := by ring
    have i2 : |⟪padSeq y T T, padSeq y T s⟫| ≤ 4 * R ^ 2 := by
      calc _ ≤ ‖padSeq y T T‖ * ‖padSeq y T s‖ := abs_real_inner_le_norm _ _
        _ ≤ (2 * R) * (2 * R) := mul_le_mul (ny _) (ny _) (norm_nonneg _) (by linarith)
        _ = 4 * R ^ 2 := by ring
    have i3 : |⟪padSeq y T T, K (padSeq x T s)⟫| ≤ L * (4 * R ^ 2) := by
      calc _ ≤ L * (‖padSeq y T T‖ * ‖padSeq x T s‖) := inner_K_abs K hK _ _
        _ ≤ L * ((2 * R) * (2 * R)) := mul_le_mul_of_nonneg_left
            (mul_le_mul (ny _) (nx _) (norm_nonneg _) (by linarith)) hL
        _ = L * (4 * R ^ 2) := by ring
    have i4 : η * |⟪padSeq y T T, K (padSeq x T s)⟫| ≤ 2 * R ^ 2 := by
      calc _ ≤ η * (L * (4 * R ^ 2)) := mul_le_mul_of_nonneg_left i3 hη
        _ = (η * L) * (4 * R ^ 2) := by ring
        _ ≤ 1 / 2 * (4 * R ^ 2) := mul_le_mul_of_nonneg_right hηL (by positivity)
        _ = 2 * R ^ 2 := by ring
    calc _ ≤ |⟪padSeq x T T, padSeq x T s⟫ + ⟪padSeq y T T, padSeq y T s⟫| +
          |η * ⟪padSeq y T T, K (padSeq x T s)⟫| := abs_sub _ _
      _ ≤ (|⟪padSeq x T T, padSeq x T s⟫| + |⟪padSeq y T T, padSeq y T s⟫|) +
          η * |⟪padSeq y T T, K (padSeq x T s)⟫| := by
          gcongr
          · exact abs_add_le _ _
          · rw [abs_mul, abs_of_nonneg hη]
      _ ≤ 10 * R ^ 2 := by linarith
  have hET : -(∑ s ∈ win (3 * T + 3), bandH T ((T : ℤ) + 1 - s) * cayForm K η (padSeq x T) (padSeq y T) T s) ≤
      120 * R ^ 2 := by
    have r := win_reflect (3 * T + 3) ((T : ℤ) + 1) (fun k => |bandH T k|) (by
      intro k hk
      have hk' : bandH T k ≠ 0 := by intro h0; apply hk; simp [h0]
      have := bandH_supp T k hk'
      rw [abs_le] at this ⊢
      constructor
      · constructor <;> omega
      · rw [abs_le]; constructor <;> omega)
    calc _ ≤ |∑ s ∈ win (3 * T + 3), bandH T ((T : ℤ) + 1 - s) * cayForm K η (padSeq x T) (padSeq y T) T s| :=
          neg_le_abs _
      _ ≤ ∑ s ∈ win (3 * T + 3), |bandH T ((T : ℤ) + 1 - s) * cayForm K η (padSeq x T) (padSeq y T) T s| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ win (3 * T + 3), |bandH T ((T : ℤ) + 1 - s)| * (10 * R ^ 2) := by
          apply sum_le_sum; intro s _; rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (cT s) (abs_nonneg _)
      _ = (∑ k ∈ win (3 * T + 3), |bandH T k|) * (10 * R ^ 2) := by rw [← sum_mul, r]
      _ ≤ 12 * (10 * R ^ 2) := mul_le_mul_of_nonneg_right hmass.1 (by positivity)
      _ = 120 * R ^ 2 := by ring
  have asupp : ∀ k, a k ≠ 0 → 1 ≤ k ∧ k ≤ T := by
    intro k hk; by_contra hc; apply hk
    simp [a, padSeq_zero x T k hc, padSeq_zero y T k hc]
  have aabs : ∀ k, |a k| ≤ 2 * R ^ 2 := by
    intro k
    have j1 := inner_K_abs K hK (padSeq y T k) (x 0)
    have j2 := inner_K_abs K hK (y 0) (padSeq x T k)
    have k1 : ‖padSeq y T k‖ * ‖x 0‖ ≤ 2 * R * R := mul_le_mul (ny k) nx0 (norm_nonneg _) (by linarith)
    have k2 : ‖y 0‖ * ‖padSeq x T k‖ ≤ R * (2 * R) := mul_le_mul ny0 (nx k) (norm_nonneg _) hR
    have m1 : |⟪padSeq y T k, K (x 0)⟫ - ⟪y 0, K (padSeq x T k)⟫| ≤ L * (4 * R ^ 2) := by
      calc _ ≤ |⟪padSeq y T k, K (x 0)⟫| + |⟪y 0, K (padSeq x T k)⟫| := abs_sub _ _
        _ ≤ L * (2 * R * R) + L * (R * (2 * R)) := add_le_add (j1.trans (mul_le_mul_of_nonneg_left k1 hL))
            (j2.trans (mul_le_mul_of_nonneg_left k2 hL))
        _ = L * (4 * R ^ 2) := by ring
    simp only [a]
    rw [abs_mul, abs_of_nonneg hη]
    calc _ ≤ η * (L * (4 * R ^ 2)) := mul_le_mul_of_nonneg_left m1 hη
      _ = (η * L) * (4 * R ^ 2) := by ring
      _ ≤ 1 / 2 * (4 * R ^ 2) := mul_le_mul_of_nonneg_right hηL (by positivity)
      _ = 2 * R ^ 2 := by ring
  have hC : ∑ t ∈ range T, ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * a s ≤ 30 * R ^ 2 := by
    have lb := lag_bound T (3 * T + 3) (bandH T) a (2 * R ^ 2) asupp aabs (bandH_supp T) (by omega)
    have e : ∑ t ∈ range T, ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * a s =
        -∑ t ∈ range T, ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * (a ((t : ℤ) + 1) - a s) := by
      rw [← sum_neg_distrib]; apply sum_congr rfl; intro t ht
      have z := bandH_reflect_sum T t (mem_range.mp ht)
      have : ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * a ((t : ℤ) + 1) = 0 := by
        rw [← sum_mul, z, zero_mul]
      simp only [mul_sub, sum_sub_distrib, this]; ring
    rw [e]
    have h2 : 2 * R ^ 2 * ∑ k ∈ win (3 * T + 3), |(k : ℝ)| * |bandH T k| ≤ 2 * R ^ 2 * 15 :=
      mul_le_mul_of_nonneg_left hmass.2 (by positivity)
    have := neg_le_abs (∑ t ∈ range T, ∑ s ∈ win (3 * T + 3), bandH T ((t : ℤ) + 1 - s) * (a ((t : ℤ) + 1) - a s))
    linarith
  rw [e1]
  linarith

lemma friction_sum (hadj : ∀ a b, ⟪adj a, b⟫ = ⟪a, K b⟫) (memx : ∀ t, x t ∈ X) (memy : ∀ t, y t ∈ Y)
    (bX : ∀ a ∈ X, ‖a‖ ≤ R) (bY : ∀ a ∈ Y, ‖a‖ ≤ R) (hK : ‖K‖ ≤ L) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hηL : η * L ≤ 1 / 2)
    (lipg : ∀ a ∈ X, ∀ b ∈ X, |g a - g b| ≤ M * ‖a - b‖)
    (liph : ∀ a ∈ Y, ∀ b ∈ Y, |h a - h b| ≤ M * ‖a - b‖)
    (vix : ∀ t, ∀ w ∈ X, ⟪x t - η • adj (y t) - x (t + 1), w - x (t + 1)⟫ ≤ η * (g w - g (x (t + 1))))
    (viy : ∀ t, ∀ w ∈ Y, ⟪y t + η • K (x (t + 1)) - y (t + 1), w - y (t + 1)⟫ ≤ η * (h w - h (y (t + 1)))) :
    ∑ t ∈ range T, (⟪x t - η • adj (y t) - x (t + 1), x (t + 1) - x t⟫ +
        ⟪y t + η • K (x (t + 1)) - y (t + 1), y (t + 1) - y t⟫) ≤ 150 * R ^ 2 + 56 * (η * M * R) := by
  have lo := friction_lower K adj g h X Y x y η R M T memx memy bX bY hM hη lipg liph vix viy
  have up := friction_upper K adj X Y x y η L R T hadj memx memy bX bY hK hη hηL
  have hR : 0 ≤ R := le_trans (norm_nonneg _) (bX _ (memx 0))
  have : 0 ≤ η * M * R := by positivity
  nlinarith

end Friction

universe u v

section Uniform

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {X : Set E} {Y : Set F} {K : E →L[ℝ] F} {g : E → ℝ} {h : F → ℝ} {adj : F → E}
  {px : E × ℝ → E} {py : F × ℝ → F} {η R L M : ℝ} {x0 : E} {y0 : F}

lemma Hyp.friction_le (H : Hyp X Y K g h adj px py η R L M x0 y0) (hηL : η * L ≤ 1 / 2) (T : ℕ) :
    ∑ t ∈ range T, fr adj K px py η x0 y0 t ≤ 150 * R ^ 2 + 56 * (η * M * R) := by
  unfold fr
  exact friction_sum K adj g h X Y (xs adj K px py η x0 y0) (ys adj K px py η x0 y0) η L R M T H.hadj
    (fun t => (H.mem t).1) (fun t => (H.mem t).2) H.boundX H.boundY H.normK H.hM H.hη.le hηL H.lipg H.liph
    (fun t w hw => H.vix t hw) (fun t w hw => H.viy t hw)

lemma Hyp.lyap_drop (H : Hyp X Y K g h adj px py η R L M x0 y0) {xh : E} {yh : F}
    (hxh : xh ∈ X) (hyh : yh ∈ Y) (T : ℕ) :
    lyap adj K px py η x0 y0 xh yh 0 - lyap adj K px py η x0 y0 xh yh T ≤ 4 * R ^ 2 + 3 * (η * L) * R ^ 2 := by
  have hη := H.hη
  have m0 := H.mem 0
  have mT := H.mem T
  unfold lyap
  have a1 := H.dist_sq_le m0.1 hxh
  have a2 := H.dist_sq_le' m0.2 hyh
  have a3 := sq_nonneg ‖xs adj K px py η x0 y0 T - xh‖
  have a4 := sq_nonneg ‖ys adj K px py η x0 y0 T - yh‖
  have b1 := abs_le.mp (H.inner_le m0.1 m0.2)
  have b2 := abs_le.mp (H.inner_le mT.1 mT.2)
  have b3 := abs_le.mp (H.inner_le hxh m0.2)
  have b4 := abs_le.mp (H.inner_le hxh mT.2)
  have c1 := mul_le_mul_of_nonneg_left b1.1 hη.le
  have c2 := mul_le_mul_of_nonneg_left b1.2 hη.le
  have c3 := mul_le_mul_of_nonneg_left b2.1 hη.le
  have c4 := mul_le_mul_of_nonneg_left b2.2 hη.le
  have c5 := mul_le_mul_of_nonneg_left b3.1 hη.le
  have c6 := mul_le_mul_of_nonneg_left b3.2 hη.le
  have c7 := mul_le_mul_of_nonneg_left b4.1 hη.le
  have c8 := mul_le_mul_of_nonneg_left b4.2 hη.le
  nlinarith

lemma Hyp.uniform_total (H : Hyp X Y K g h adj px py η R L M x0 y0) {xh : E} {yh : F}
    (hxh : xh ∈ X) (hyh : yh ∈ Y) (hηL : η * L ≤ 1 / 2) (T : ℕ) :
    ∑ t ∈ range T, η * gapTerm K g h (xs adj K px py η x0 y0 (t + 1)) (ys adj K px py η x0 y0 (t + 1)) xh yh ≤
      81 * R ^ 2 + 28 * (η * M * R) := by
  have h1 := H.one_step_sum hxh hyh T
  have h2 := H.lyap_drop hxh hyh T
  have h3 := H.friction_le hηL T
  have hR : 0 ≤ R := le_trans (norm_nonneg _) (H.boundX _ H.memx)
  have : η * L * R ^ 2 ≤ 1 / 2 * R ^ 2 := mul_le_mul_of_nonneg_right hηL (sq_nonneg R)
  nlinarith

end Uniform

lemma uniform_tuning {R L M ε : ℝ} (hR : 0 < R) (hL : 0 < L) (hM : 0 ≤ M) (hε : 0 < ε) (T : ℕ)
    (hT : 200 * R * (L * R + M) / ε ≤ T) :
    1 ≤ T ∧ (81 * R ^ 2 + 28 * (1 / (2 * L) * M * R)) / (1 / (2 * L) * T) ≤ ε := by
  have hc : 0 < 200 * R * (L * R + M) / ε := by positivity
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le hc hT
  have hT1 : 1 ≤ T := by
    have : 0 < T := by exact_mod_cast hTpos
    omega
  refine ⟨hT1, ?_⟩
  rw [div_le_iff₀ hε] at hT
  have e : (81 * R ^ 2 + 28 * (1 / (2 * L) * M * R)) / (1 / (2 * L) * T) = (162 * L * R ^ 2 + 28 * M * R) / T := by
    field_simp; ring
  rw [e, div_le_iff₀ hTpos]
  nlinarith [mul_nonneg hM hR.le, mul_pos hL (mul_pos hR hR)]

end OracleTemplate.ArrowHurwicz
