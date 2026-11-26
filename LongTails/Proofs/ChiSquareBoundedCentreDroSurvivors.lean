import LongTails.Proofs.ChiSquareBoundedCentreDroSampling
import LongTails.Proofs.ChiSquareBoundedCentreDroCandidate

open MeasureTheory Set
namespace OracleTemplate.ChiSquareBoundedCentreDro
open LongTails.Setups.ChiSquareConstrainedDro
open ChiSquareDro (Adm radius)

noncomputable section
variable {q : Params} {I : Instance q} {proj : q.E → q.E}

lemma estimate_past (w : Candidate q.E) (m : ℕ) {ξ ζ : ℕ → q.Ξ} (H : ∀ i < m, ξ i = ζ i) :
    estimate I proj w m ξ = estimate I proj w m ζ := by
  unfold estimate
  simp_rw [show ∀ i : Fin m, ξ i = ζ i from fun i => H i i.isLt]

lemma advance_past (r h : ℕ) (xs : ℕ → Candidate q.E) (ξ ζ : ℕ → q.Ξ)
    (H : ∀ i < 2^h*(batchSize q r+batchSize q r), ξ i = ζ i) :
    advance I proj r h xs ξ = advance I proj r h xs ζ := by
  funext k
  let i := k % 2^h
  let m := batchSize q r
  have hi : i < 2^h := Nat.mod_lt _ (by positivity)
  have hu := Nat.mul_le_mul_right (m+m) hi
  rw [Nat.succ_mul] at hu
  change ∀ j < 2^h*(m+m), ξ j = ζ j at H
  have h1 : ∀ j < m, ξ (i*(m+m)+j) = ζ (i*(m+m)+j) := fun j hj => H _ (by omega)
  have h2 : ∀ j < m, ξ (i*(m+m)+(m+j)) = ζ (i*(m+m)+(m+j)) := fun j hj => H _ (by omega)
  simp only [advance,victor]
  rw [estimate_past (I := I) (proj := proj) (xs (2*i)) m h1,
    estimate_past (I := I) (proj := proj) (xs (2*i+1)) m h2]

def ValidCandidate (I : Instance q) (b : ℝ) (x : Candidate q.E) :=
  x.1 ∈ I.domain ∧ x.2 ∈ Icc (-b) q.B

lemma advance_valid {b : ℝ} {xs : ℕ → Candidate q.E} {r h : ℕ}
    (hx : ∀ i < 2^(h+1), ValidCandidate I b (xs i)) (ξ : ℕ → q.Ξ) (k : ℕ) :
    ValidCandidate I b (advance I proj r h xs ξ k) := by
  have hi := Nat.mod_lt k (by positivity : 0 < 2^h)
  rw [pow_succ] at hx
  simp only [advance,victor]; split <;> apply hx <;> omega

lemma match_expected (hI : Adm q I proj) (hq : spec.valid q) {x y : Candidate q.E}
    (hx : x.1 ∈ I.domain) (hy : y.1 ∈ I.domain) (r k : ℕ) :
    let P := streamLaw I.law.toMeasure
    let m := batchSize q r
    (∫ ξ, trueScore I (victor I proj m x y (fun t => ξ (k+t))) ∂P) ≤
      min (trueScore I x) (trueScore I y)+2*allowance q r := by
  classical
  intro P m
  let fx := fun ξ : ℕ → q.Ξ => estimate I proj x m (fun t => ξ (k+t))
  let fy := fun ξ : ℕ → q.Ξ => estimate I proj y m (fun t => ξ (k+m+t))
  let sx := trueScore I x
  let sy := trueScore I y
  let R := fun ξ => if fx ξ ≤ fy ξ then sx else sy
  have hmX : Measurable fx := (estimate_meas hI m).comp ((measurable_const (a := x)).prodMk
    (shift_law I.law.toMeasure k).measurable)
  have hmY : Measurable fy := (estimate_meas hI m).comp ((measurable_const (a := y)).prodMk
    (shift_law I.law.toMeasure (k+m)).measurable)
  have hiR : Integrable R P := Integrable.piecewise (measurableSet_le hmX hmY)
    (integrable_const sx).integrableOn (integrable_const sy).integrableOn
  have HE1 := estimate_error hI hq (w := x) hx r k
  have HE2 := estimate_error hI hq (w := y) hy r (k+m)
  change Integrable (fun ξ => |fx ξ-sx|) P ∧ (∫ ξ, |fx ξ-sx| ∂P) ≤ allowance q r at HE1
  change Integrable (fun ξ => |fy ξ-sy|) P ∧ (∫ ξ, |fy ξ-sy| ∂P) ≤ allowance q r at HE2
  have hp ξ : R ξ ≤ min sx sy + |fx ξ-sx| + |fy ξ-sy| := by
    dsimp only [R]
    rcases le_total sx sy with H|H <;> (first | rw [min_eq_left H] | rw [min_eq_right H]) <;> split <;>
      linarith [abs_nonneg (fx ξ-sx),abs_nonneg (fy ξ-sy),le_abs_self (fx ξ-sx),
        neg_le_abs (fx ξ-sx),le_abs_self (fy ξ-sy),neg_le_abs (fy ξ-sy)]
  have H := integral_mono hiR (((integrable_const _).add HE1.1).add HE2.1) hp
  change (∫ ξ, R ξ ∂P) ≤ ∫ ξ, min sx sy + |fx ξ-sx| + |fy ξ-sy| ∂P at H
  rw [integral_add (f := fun ξ => min sx sy + |fx ξ-sx|) (g := fun ξ => |fy ξ-sy|)
    ((integrable_const _).add HE1.1) HE2.1,integral_add (integrable_const _) HE1.1,
    integral_const,probReal_univ,one_smul] at H
  have he ξ : trueScore I (victor I proj m x y (fun t => ξ (k+t))) = R ξ := by
    unfold victor R fx fy
    simp only [Nat.add_assoc]
    split <;> rfl
  simp_rw [he]
  change _ ≤ min sx sy+2*allowance q r
  linarith [HE1.2,HE2.2]

lemma champion_expected (hI : Adm q I proj) (hq : spec.valid q) {b : ℝ} (hb : 0 ≤ b)
    (r h : ℕ) (xs : ℕ → Candidate q.E) (hx : ∀ i < 2^h, ValidCandidate I b (xs i))
    (i : ℕ) (hi : i < 2^h) :
    (∫ ξ, trueScore I (champion I proj r h xs ξ) ∂streamLaw I.law.toMeasure) ≤
      trueScore I (xs i) + 12*allowance q r := by
  let P := streamLaw I.law.toMeasure
  have hε := hq.2.2.2.2
  induction h generalizing r xs i with
  | zero =>
    have hi0 : i = 0 := by simpa using hi
    subst i
    simp [champion,allowance]; positivity
  | succ h ih =>
    let m := batchSize q r
    let n := 2^h*(m+m)
    let X := advance I proj r h xs
    let F := fun ys (ξ : ℕ → q.Ξ) => trueScore I (champion I proj (r+1) h ys ξ)
    have hX : Measurable X := (advance_meas hI r h).comp ((measurable_const (a := xs)).prodMk measurable_id)
    have hF : Measurable (Function.uncurry F) := (score_meas hI).comp (champion_meas hI (r+1) h)
    have hvalid ξ j := advance_valid (proj := proj) (r := r) hx ξ j
    have hB (w : Candidate q.E) (hw : ValidCandidate I b w) :
        ‖trueScore I w‖ ≤ q.B+radius q*(q.B+b) :=
      (score_bounds hI hq.1 hq.2.2.1 hw.1 hb hw.2).2
    have hbd ξ ζ := hB _ (champion_property (I := I) (proj := proj) (W := ValidCandidate I b) (r+1) h (X ξ) (fun j _ => hvalid ξ j) ζ)
    have he := fresh_block I.law.toMeasure n X hX (advance_past r h xs) F hF hbd
    change (∫ ξ, F (X ξ) (fun t => ξ (n+t)) ∂P) ≤ _
    rw [he]
    let j := i/2
    have hj : j < 2^h := by dsimp [j]; rw [pow_succ] at hi; omega
    let G := fun ξ => trueScore I (X ξ j)
    have hGi : Integrable G P := Integrable.of_bound
      ((score_meas hI).comp ((measurable_pi_apply j).comp hX)).aestronglyMeasurable _
      (ae_of_all _ fun ξ => hB _ (hvalid ξ j))
    have hFi : Integrable (fun ξ => ∫ ζ, F (X ξ) ζ ∂P) P := Integrable.of_bound
      (((hF.stronglyMeasurable.integral_prod_right' (ν := P)).measurable.comp hX).aestronglyMeasurable)
      (q.B+radius q*(q.B+b)) (ae_of_all _ fun ξ => (norm_integral_le_of_norm_le_const (ae_of_all _ (hbd ξ))).trans_eq (by simp))
    have hmono := integral_mono hFi (hGi.add (integrable_const (12*allowance q (r+1))))
      (fun ξ => ih (r+1) (X ξ) (fun j _ => hvalid ξ j) j hj)
    change _ ≤ ∫ ξ, G ξ+12*allowance q (r+1) ∂P at hmono
    rw [ChiSquareDro.integral_add_const' P hGi] at hmono
    have hx' : 2*j < 2^(h+1) := by rw [pow_succ]; omega
    have hy' : 2*j+1 < 2^(h+1) := by rw [pow_succ]; omega
    have H := match_expected hI hq (x := xs (2*j)) (y := xs (2*j+1)) (hx _ hx').1 (hx _ hy').1 r (j*(m+m))
    have heG ξ : G ξ = trueScore I (victor I proj m (xs (2*j)) (xs (2*j+1))
        (fun t => ξ (j*(m+m)+t))) := by simp [G,X,advance,Nat.mod_eq_of_lt hj,m]
    change (∫ ξ, trueScore I (victor I proj m (xs (2*j)) (xs (2*j+1))
      (fun t => ξ (j*(m+m)+t))) ∂P) ≤ _ at H
    simp_rw [← heG] at H
    have hmin : min (trueScore I (xs (2*j))) (trueScore I (xs (2*j+1))) ≤ trueScore I (xs i) := by
      have : i = 2*j ∨ i = 2*j+1 := by dsimp [j]; omega
      rcases this with hh|hh <;> rw [hh] <;> first | exact min_le_left _ _ | exact min_le_right _ _
    have ha : allowance q (r+1) = allowance q r*(5/6) := by unfold allowance; rw [pow_succ]; ring
    change (∫ ξ, G ξ ∂P) ≤ _ at H
    linarith

end
end OracleTemplate.ChiSquareBoundedCentreDro
