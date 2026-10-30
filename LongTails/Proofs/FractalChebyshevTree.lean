import LongTails.Algorithms.FractalChebyshevSteps
import Mathlib.Tactic

namespace OracleTemplate.FractalChebyshev

noncomputable def fac (x x0 θ : ℝ) : ℝ := (x + Real.cos θ) / (x0 + Real.cos θ)

noncomputable def prodF (x x0 : ℝ) (l : List ℝ) : ℝ := (l.map (fac x x0)).prod

def dbl (x : ℝ) : ℝ := 2 * x ^ 2 - 1

lemma prodF_nil (x x0 : ℝ) : prodF x x0 [] = 1 := by simp [prodF]

lemma prodF_append (x x0 : ℝ) (l l' : List ℝ) :
    prodF x x0 (l ++ l') = prodF x x0 l * prodF x x0 l' := by
  simp [prodF, List.map_append, List.prod_append]

lemma prodF_cons (x x0 θ : ℝ) (l : List ℝ) :
    prodF x x0 (θ :: l) = fac x x0 θ * prodF x x0 l := by
  simp [prodF]

lemma angles_length (k : ℕ) : (angles k).length = 2 ^ k := by
  induction k with
  | zero => simp [angles]
  | succ k ih =>
    have h : ∀ l : List ℝ, (l.flatMap split).length = 2 * l.length := by
      intro l
      induction l with
      | nil => simp
      | cons a l ihl => simp [List.flatMap_cons, split, ihl]; ring
    rw [angles, h, ih, pow_succ]; ring

lemma split_mem {ψ θ : ℝ} (hψ : 0 < ψ ∧ ψ < Real.pi) (hθ : θ ∈ split ψ) :
    0 < θ ∧ θ < Real.pi := by
  simp only [split, List.mem_cons, List.not_mem_nil, or_false] at hθ
  rcases hθ with rfl | rfl <;> constructor <;> linarith [Real.pi_pos]

lemma angles_mem {k : ℕ} {θ : ℝ} (hθ : θ ∈ angles k) : 0 < θ ∧ θ < Real.pi := by
  induction k generalizing θ with
  | zero =>
    simp only [angles, List.mem_cons, List.not_mem_nil, or_false] at hθ
    subst hθ; constructor <;> linarith [Real.pi_pos]
  | succ k ih =>
    rw [angles, List.mem_flatMap] at hθ
    obtain ⟨ψ, hψ, hθ⟩ := hθ
    exact split_mem (ih hψ) hθ

lemma cos_first (ψ : ℝ) : Real.cos (Real.pi / 2 - ψ / 2) = Real.sin (ψ / 2) :=
  Real.cos_pi_div_two_sub _

lemma cos_second (ψ : ℝ) : Real.cos (Real.pi / 2 + ψ / 2) = - Real.sin (ψ / 2) := by
  rw [show Real.pi / 2 + ψ / 2 = ψ / 2 + Real.pi / 2 by ring, Real.cos_add_pi_div_two]

lemma cos_eq_half (ψ : ℝ) : Real.cos ψ = 1 - 2 * Real.sin (ψ / 2) ^ 2 := by
  have h := Real.cos_two_mul (ψ / 2)
  rw [show 2 * (ψ / 2) = ψ by ring] at h
  nlinarith [Real.sin_sq_add_cos_sq (ψ / 2)]

lemma fac_pair (x x0 ψ : ℝ) (hx0 : 1 < x0) :
    fac x x0 (Real.pi / 2 - ψ / 2) * fac x x0 (Real.pi / 2 + ψ / 2) =
      fac (dbl x) (dbl x0) ψ := by
  unfold fac dbl
  rw [cos_first, cos_second, cos_eq_half ψ]
  set s := Real.sin (ψ / 2)
  have hs : s ≤ 1 := Real.sin_le_one _
  have hs' : -1 ≤ s := Real.neg_one_le_sin _
  have h1 : x0 + s ≠ 0 := by linarith
  have h2 : x0 + -s ≠ 0 := by linarith
  have h3 : 2 * x0 ^ 2 - 1 + (1 - 2 * s ^ 2) ≠ 0 := by nlinarith
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero h1 h2) h3]
  ring

lemma prodF_flatMap (x x0 : ℝ) (hx0 : 1 < x0) (l : List ℝ) :
    prodF x x0 (l.flatMap split) = prodF (dbl x) (dbl x0) l := by
  induction l with
  | nil => simp [prodF]
  | cons ψ l ih =>
    rw [List.flatMap_cons, prodF_append, ih, prodF_cons]
    congr 1
    simp only [split, prodF, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact fac_pair x x0 ψ hx0

lemma take_flatMap_split (l : List ℝ) (t : ℕ) :
    ∃ m ≤ l.length, ∃ e : List ℝ,
      (l.flatMap split).take t = (l.take m).flatMap split ++ e ∧
      (e = [] ∨ ∃ ψ ∈ l, e = [Real.pi / 2 - ψ / 2]) := by
  induction l generalizing t with
  | nil => exact ⟨0, le_rfl, [], by simp, Or.inl rfl⟩
  | cons ψ l ih =>
    rcases t with _ | _ | t
    · exact ⟨0, Nat.zero_le _, [], by simp, Or.inl rfl⟩
    · refine ⟨0, Nat.zero_le _, [Real.pi / 2 - ψ / 2], ?_, Or.inr ⟨ψ, by simp, rfl⟩⟩
      simp [List.flatMap_cons, split]
    · obtain ⟨m, hm, e, he, he'⟩ := ih t
      refine ⟨m + 1, by simp [hm], e, ?_, ?_⟩
      · simp [List.flatMap_cons, split, he]
      · rcases he' with h | ⟨φ, hφ, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨φ, List.mem_cons_of_mem _ hφ, h⟩

lemma dbl_bounds {x x0 : ℝ} (hx0 : 1 < x0) (hx : -1 ≤ x ∧ x ≤ x0) :
    -1 ≤ dbl x ∧ dbl x ≤ dbl x0 := by
  unfold dbl
  constructor
  · nlinarith [sq_nonneg x]
  · nlinarith

lemma one_lt_dbl {x0 : ℝ} (hx0 : 1 < x0) : 1 < dbl x0 := by
  unfold dbl; nlinarith

lemma abs_fac_first_le {x x0 ψ : ℝ} (hx0 : 1 < x0) (hx : -1 ≤ x ∧ x ≤ x0)
    (hψ : 0 < ψ ∧ ψ < Real.pi) : |fac x x0 (Real.pi / 2 - ψ / 2)| ≤ 1 := by
  unfold fac
  rw [cos_first]
  have hs : 0 ≤ Real.sin (ψ / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith
  have hpos : 0 < x0 + Real.sin (ψ / 2) := by linarith
  rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
  constructor <;> linarith

theorem prefix_le_one (k t : ℕ) {x x0 : ℝ} (hx0 : 1 < x0) (hx : -1 ≤ x ∧ x ≤ x0) :
    |prodF x x0 ((angles k).take t)| ≤ 1 := by
  induction k generalizing t x x0 with
  | zero =>
    rcases t with _ | t
    · simp [prodF]
    · simp only [angles, List.take_succ_cons, List.take_nil, prodF, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one, fac,
        Real.cos_pi_div_two, add_zero]
      have hpos : 0 < x0 := by linarith
      rw [abs_div, abs_of_pos hpos, div_le_one hpos, abs_le]
      constructor <;> linarith
  | succ k ih =>
    obtain ⟨m, -, e, he, he'⟩ := take_flatMap_split (angles k) t
    rw [angles, he, prodF_append, prodF_flatMap x x0 hx0, abs_mul]
    have h1 : |prodF (dbl x) (dbl x0) ((angles k).take m)| ≤ 1 :=
      ih m (one_lt_dbl hx0) (dbl_bounds hx0 hx)
    have h2 : |prodF x x0 e| ≤ 1 := by
      rcases he' with rfl | ⟨ψ, hψ, rfl⟩
      · simp [prodF]
      · simp only [prodF, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        exact abs_fac_first_le hx0 hx (angles_mem hψ)
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1

end OracleTemplate.FractalChebyshev
