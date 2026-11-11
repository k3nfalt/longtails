import LongTails.Proofs.SmoothConvexFiniteAveraging
import LongTails.Proofs.FiniteSumNondualLowerBound
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SmoothConvexFiniteExpectation

open SmoothConvexFiniteWall SmoothConvexFiniteAveraging
open FiniteSumNondualLowerAveraging FiniteSumNondualLowerBound

lemma exists_failure {d k : ℕ} {S Ω : Type*} [MeasurableSpace Ω]
    (L R δ a D ε : ℝ) (hL : 0 ≤ L) (hR : 0 < R) (hδ : 0 < δ) (ha : 0 ≤ a)
    (hrad : ((k : ℝ) + 1) * a ^ 2 ≤ R ^ 2) (hscale : ((k : ℝ) + 1) * δ ≤ a / 8)
    (hD : 0 < D) (hDs : D + (k + 1 : ℕ) ≤ d)
    (hsize : 2 * (k + 1 : ℕ) ^ 2 * ((3 * R) ^ 2 / (δ / 4) ^ 2) ≤ D)
    (hε : 2 * ε < L * a ^ 2 / (8192 * ((k : ℝ) + 1)))
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : Ω → S) (P : ProbabilityMeasure Ω) :
    ∃ π : Fin (k + 1) ↪ Fin d,
      let loss := fun ω => objective L R δ a π
        (output ((fun s => update s (field L R δ a π (query s)))^[k] (initial ω)))
      ¬ (Integrable loss (P : Measure Ω) ∧ (∫ ω, loss ω ∂(P : Measure Ω)) ≤ ε) := by
  classical
  by_contra h
  push Not at h
  let loss := fun (w : CoordinateWords d k) (ω : Ω) =>
    objective L R δ a (coordinateEmbedding w)
      (output ((fun s => update s (field L R δ a (coordinateEmbedding w) (query s)))^[k] (initial ω)))
  have hi (w : CoordinateWords d k) : Integrable (loss w) (P : Measure Ω) :=
    (h (coordinateEmbedding w)).1
  have hu (w : CoordinateWords d k) : (∫ ω, loss w ω ∂(P : Measure Ω)) ≤ ε :=
    (h (coordinateEmbedding w)).2
  have hs : Integrable (fun ω => ∑ w, loss w ω) (P : Measure Ω) :=
    integrable_finsetSum Finset.univ (fun w _ => hi w)
  have hp := integral_mono (integrable_const
    ((L * a ^ 2 / (8192 * ((k : ℝ) + 1))) * Fintype.card (CoordinateWords d k)))
    (hs.const_mul 2) (fun ω => execution_average_gap L R δ a D hL hR hδ ha hrad hscale
      hD hDs hsize query output update (initial ω))
  have he := integral_finsetSum Finset.univ (fun w (_ : w ∈ Finset.univ) => hi w)
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul, he] at hp
  have hb : (∑ w : CoordinateWords d k, ∫ ω, loss w ω ∂(P : Measure Ω)) ≤
      Fintype.card (CoordinateWords d k) * ε := by
    calc
      _ ≤ ∑ _ : CoordinateWords d k, ε := Finset.sum_le_sum (fun w _ => hu w)
      _ = _ := by simp
  have hd : k + 1 ≤ d := by
    have hh : ((k + 1 : ℕ) : ℝ) ≤ d := by linarith
    exact_mod_cast hh
  have hc : (0 : ℝ) < Fintype.card (CoordinateWords d k) := by
    exact_mod_cast coordinateWords_card_pos d k hd
  have hstrict := mul_lt_mul_of_pos_right hε hc
  change _ ≤ 2 * ∑ w : CoordinateWords d k, ∫ ω, loss w ω ∂(P : Measure Ω) at hp
  nlinarith only [hp, hb, hstrict]

lemma exists_failure_of_dimension {d k : ℕ} {S Ω : Type*} [MeasurableSpace Ω]
    (L R ε : ℝ) (hL : 0 ≤ L) (hR : 0 < R)
    (hd : 65536 * (k + 1) ^ 5 ≤ d)
    (hgap : 16384 * ((k : ℝ) + 1) ^ 2 * ε < L * R ^ 2)
    (query output : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : Ω → S) (P : ProbabilityMeasure Ω) :
    let a := R / Real.sqrt ((k : ℝ) + 1)
    let δ := a / (8 * ((k : ℝ) + 1))
    ∃ π : Fin (k + 1) ↪ Fin d,
      let loss := fun ω => objective L R δ a π
        (output ((fun s => update s (field L R δ a π (query s)))^[k] (initial ω)))
      ¬ (Integrable loss (P : Measure Ω) ∧ (∫ ω, loss ω ∂(P : Measure Ω)) ≤ ε) := by
  let K : ℝ := (k : ℝ) + 1
  let a := R / Real.sqrt K
  let δ := a / (8 * K)
  let D := 32768 * K ^ 5
  have hK : 0 < K := by dsimp [K]; positivity
  have hKone : 1 ≤ K := by dsimp [K]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have ha : 0 < a := div_pos hR (Real.sqrt_pos.mpr hK)
  have hδ : 0 < δ := div_pos ha (by positivity)
  have ha_sq : a ^ 2 = R ^ 2 / K := by
    dsimp [a]
    rw [div_pow, Real.sq_sqrt hK.le]
  have hrad : K * a ^ 2 = R ^ 2 := by rw [ha_sq, mul_div_cancel₀ _ hK.ne']
  have hscale : K * δ = a / 8 := by dsimp [δ]; field_simp
  have hD : 0 < D := by dsimp [D]; positivity
  have hpow : K ≤ K ^ 5 := by simpa using pow_le_pow_right₀ hKone (by decide : 1 ≤ 5)
  have hd' : 65536 * K ^ 5 ≤ (d : ℝ) := by dsimp [K]; exact_mod_cast hd
  have hDs : D + (k + 1 : ℕ) ≤ (d : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    change D + K ≤ (d : ℝ)
    dsimp [D]
    nlinarith
  have hδsq : (δ / 4) ^ 2 = R ^ 2 / (1024 * K ^ 3) := by
    dsimp [δ]
    rw [div_pow, div_pow, ha_sq]
    field_simp
    ring
  have hratio : (3 * R) ^ 2 / (δ / 4) ^ 2 = 9216 * K ^ 3 := by
    rw [hδsq]
    field_simp
    ring
  have hsize : 2 * (k + 1 : ℕ) ^ 2 * ((3 * R) ^ 2 / (δ / 4) ^ 2) ≤ D := by
    rw [hratio, Nat.cast_add, Nat.cast_one]
    change 2 * K ^ 2 * (9216 * K ^ 3) ≤ 32768 * K ^ 5
    nlinarith [pow_pos hK 5]
  have hε : 2 * ε < L * a ^ 2 / (8192 * K) := by
    apply (lt_div_iff₀ (by positivity : 0 < 8192 * K)).mpr
    rw [ha_sq, ← mul_div_assoc]
    apply (lt_div_iff₀ hK).mpr
    change 16384 * K ^ 2 * ε < L * R ^ 2 at hgap
    nlinarith only [hgap]
  exact exists_failure L R δ a D ε hL hR hδ ha.le hrad.le hscale.le hD hDs hsize hε
    query output update initial P

lemma floor_budget_insufficient (L R ε : ℝ) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hregime : 262144 * ε ≤ L * R ^ 2) :
    16384 * ((⌊Real.sqrt (L * R ^ 2 / ε) / 512⌋₊ : ℝ) + 1) ^ 2 * ε < L * R ^ 2 := by
  let s := Real.sqrt (L * R ^ 2 / ε)
  have hx : 0 ≤ L * R ^ 2 / ε := by positivity
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = L * R ^ 2 / ε := Real.sq_sqrt hx
  have hratio : 262144 ≤ L * R ^ 2 / ε := (le_div_iff₀ hε).mpr hregime
  have hs512 : 512 ≤ s := by nlinarith
  have hf : (⌊s / 512⌋₊ : ℝ) ≤ s / 512 := Nat.floor_le (by positivity)
  have hf0 : (0 : ℝ) ≤ ⌊s / 512⌋₊ := Nat.cast_nonneg _
  have hk : (⌊s / 512⌋₊ : ℝ) + 1 ≤ s / 256 := by linarith
  have hsmall : 16384 * ((⌊s / 512⌋₊ : ℝ) + 1) ^ 2 < s ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (⌊s / 512⌋₊ : ℝ) + 1) hk 2
    nlinarith
  have hm := mul_lt_mul_of_pos_right hsmall hε
  rw [hs2, div_mul_cancel₀ _ hε.ne'] at hm
  exact hm

end LongTails.Proofs.SmoothConvexFiniteExpectation
