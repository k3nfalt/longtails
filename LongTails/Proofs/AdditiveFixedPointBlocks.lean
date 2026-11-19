import LongTails.Proofs.AdditiveFixedPointTesting
import LongTails.Proofs.AdditiveFixedPointFamily

open MeasureTheory
open scoped ENNReal

namespace LongTails.Proofs.AdditiveFixedPointBlocks

open AdditiveFixedPointTesting AdditiveFixedPointNoise AdditiveFixedPointProcess
open AdditiveFixedPointFamily LongTails.Setups.AdditiveCubeFixedPoint

variable {p : Params} {S : Type*} [MeasurableSpace S]

def step (query : S → Cube p) (update : S → Point p → S) {h : ℝ} (hh : 0 ≤ h)
    (s : ℕ → Bool) (m : ℕ) (x : S) (z : Point p) : S :=
  update x ((map hh s m (query x)).val + z)

lemma mean_measurable {query : S → Cube p} (hq : Measurable query) {h : ℝ} (hh : 0 ≤ h)
    (s : ℕ → Bool) (m : ℕ) : Measurable (fun x => (map hh s m (query x)).val) :=
  measurable_subtype_coe.comp ((map_lipschitz hh s m).continuous.measurable.comp hq)

lemma step_measurable {query : S → Cube p} {update : S → Point p → S}
    (hq : Measurable query) (hu : Measurable update.uncurry) {h : ℝ} (hh : 0 ≤ h)
    (s : ℕ → Bool) (m : ℕ) : Measurable (step query update hh s m).uncurry :=
  hu.comp (measurable_fst.prodMk (((mean_measurable hq hh s m).comp measurable_fst).add measurable_snd))

lemma select_block (π : ProbabilityMeasure S) {query : S → Cube p} {update : S → Point p → S}
    (hq : Measurable query) (hu : Measurable update.uncurry) {h : ℝ} (hh : 0 ≤ h)
    (s : ℕ → Bool) (l k n : ℕ) (v : NNReal) (η : ℝ≥0∞)
    (hn : (n ≤ 1 ∧ (n : ℝ≥0∞) / 2 ^ k ≤ η) ∨
      (v ≠ 0 ∧ ENNReal.ofReal (Real.exp (k * ((2 * h) ^ 2 / v))) ^ n *
        ((n : ℝ≥0∞) / 2 ^ k) ≤ η ^ 2)) :
    ∃ w : Fin k → Bool,
      ∑ j : Fin n, risk π (law v 0) (step query update hh (writeWord s l w) (l + k))
        (test (fun x => guess l k (query x)) w) j ≤ n * η := by
  classical
  let base := step query update hh s l
  let g := fun x => guess l k (query x)
  have hg : Measurable g := (guess_measurable l k).comp hq
  obtain ⟨w, hw⟩ := rare_word hg (fun j : Fin n => stateLaw π (law v 0) base j)
  have htot : ∑ j : Fin n, risk π (law v 0) base (test g w) j ≤ n / (2 : ℝ≥0∞) ^ k := by
    simpa [risk] using hw
  let next := step query update hh (writeWord s l w) (l + k)
  have hbase := step_measurable hq hu hh s l
  have hnext := step_measurable hq hu hh (writeWord s l w) (l + k)
  have htest := test_measurable hg w
  refine ⟨w, ?_⟩
  suffices hall : ∀ j : Fin n, risk π (law v 0) next (test g w) j ≤ η by
    simpa using (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hall j))
  intro j
  have hj : risk π (law v 0) base (test g w) j ≤ n / (2 : ℝ≥0∞) ^ k :=
    (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j)).trans htot
  rcases hn with ⟨hn, he⟩ | ⟨hv, he⟩
  · have hj0 : j.val = 0 := by omega
    simpa only [hj0, risk, stateLaw_integral π _ hbase htest,
      stateLaw_integral π _ hnext htest, AdditiveFixedPointProcess.average_zero, base, next] using hj.trans he
  · let B := (k : ℝ) * ((2 * h) ^ 2 / v)
    have hb : 1 ≤ ENNReal.ofReal (Real.exp B) := by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      exact Real.one_le_exp (by positivity)
    have hsame : map (p := p) hh (writeWord s l w) l = map hh s l :=
      map_congr hh (fun _ hi => writeWord_before s l w hi)
    have hbnd (x : S) : ∑ i, ((map hh (writeWord s l w) (l + k) (query x)).val i -
        (map hh s l (query x)).val i) ^ 2 / v ≤ B := by
      rw [← hsame]
      simpa [B] using block_energy hh (writeWord s l w) (Nat.le_add_right l k) (query x)
        (show (0 : ℝ) < v by positivity)
    have hsq := integrated_compare π hv (mean_measurable hq hh s l)
      (mean_measurable hq hh (writeWord s l w) (l + k)) hu htest (test_sq g w) hbnd j.val
    have hr : risk π (law v 0) next (test g w) j ^ 2 ≤ ENNReal.ofReal (Real.exp B) ^ j.val *
        risk π (law v 0) base (test g w) j := by
      unfold risk
      rw [stateLaw_integral π _ hnext htest, stateLaw_integral π _ hbase htest]
      exact hsq
    have ht : risk π (law v 0) next (test g w) j ^ 2 ≤ η ^ 2 := hr.trans
      ((mul_le_mul' (pow_le_pow_right' hb j.isLt.le) hj).trans he)
    simpa only [AdditiveFixedPointGaussian.half_pow_square] using
      ENNReal.rpow_le_rpow ht (by norm_num : (0 : ℝ) ≤ 1 / 2)

lemma choose_signs (π : ProbabilityMeasure S) {query output : S → Cube p} {update : S → Point p → S}
    (hq : Measurable query) (ho : Measurable output) (hu : Measurable update.uncurry)
    {h : ℝ} (hh : 0 ≤ h) (s : ℕ → Bool) (l k : ℕ) (v : NNReal) (η : ℝ≥0∞)
    (blocks : List ℕ) (hn : ∀ n ∈ blocks,
      (n ≤ 1 ∧ (n : ℝ≥0∞) / 2 ^ k ≤ η) ∨
      (v ≠ 0 ∧ ENNReal.ofReal (Real.exp (k * ((2 * h) ^ 2 / v))) ^ n *
        ((n : ℝ≥0∞) / 2 ^ k) ≤ η ^ 2)) :
    let L := l + blocks.length * k
    ∃ t : ℕ → Bool, (∀ i < l, t i = s i) ∧
      risk π (law v 0) (step query update hh t (L + 1))
        (test (fun x => guess L 1 (output x) 0) (t L)) blocks.sum ≤
        1 / 2 + blocks.sum * η := by
  classical
  induction blocks generalizing s l π with
  | nil =>
    let g := fun x => guess l 1 (output x) 0
    have hg : Measurable g := (measurable_pi_apply 0).comp ((guess_measurable l 1).comp ho)
    obtain ⟨w, hw⟩ := rare_word hg (n := 1) (fun _ => π)
    let t := Function.update s l w
    refine ⟨t, fun i hi => Function.update_of_ne (Nat.ne_of_lt hi) _ _, ?_⟩
    simp only [List.length_nil, List.sum_nil, Nat.cast_zero, zero_mul, add_zero]
    rw [risk, stateLaw_integral π _ (step_measurable hq hu hh _ _) (test_measurable hg _)]
    simpa [AdditiveFixedPointProcess.average_zero, t, g] using hw
  | cons n bs ih =>
    let L := l + (n :: bs).length * k
    let G := fun x => guess l k (query x)
    have hg : Measurable G := (guess_measurable l k).comp hq
    obtain ⟨w, hw⟩ := select_block π hq hu hh s l k n v η (hn n (by simp))
    let pre := writeWord s l w
    let next := step query update hh pre (l + k)
    have hnext := step_measurable hq hu hh pre (l + k)
    let π' := stateLaw π (law v 0) next n
    obtain ⟨t, ht, hi⟩ := ih π' pre (l + k) (fun j hj => hn j (by simp [hj]))
    have hL : l + k + bs.length * k = L := by simp [L, Nat.add_mul]; omega
    rw [hL] at hi
    let full := step query update hh t (L + 1)
    have hfull := step_measurable hq hu hh t (L + 1)
    let P := test (fun x => guess L 1 (output x) 0) (t L)
    have hP : Measurable P := test_measurable ((measurable_pi_apply 0).comp
      ((guess_measurable L 1).comp ho)) _
    have hagree (x : S) (hx : G x ≠ w) (z : Point p) : full x z = next x z := by
      have hsize : l + k ≤ L + 1 := by omega
      unfold full next step
      rw [agree_off_word hh hsize w ht (query x) hx]
    have htail := average_measurable (law v 0) hfull hP bs.sum
    have hcouple := risk_coupling π (law v 0) hnext hfull hg w hagree htail
      (average_le_one _ _ (fun x => by unfold P test; split <;> simp) _) n
    have hi' : risk π (law v 0) next (AdditiveFixedPointProcess.average (law v 0) full P bs.sum) n ≤
        1 / 2 + bs.sum * η := by
      change (∫⁻ x, AdditiveFixedPointProcess.average _ _ _ _ x ∂(π' : Measure S)) ≤ _
      change risk π' (law v 0) full P bs.sum ≤ _ at hi
      exact (stateLaw_integral π' _ hfull hP bs.sum).symm.le.trans hi
    refine ⟨t, fun i hi => (ht i (by omega)).trans (writeWord_before s l w hi), ?_⟩
    change risk π (law v 0) full P (n + bs.sum) ≤ 1 / 2 + ((n + bs.sum : ℕ) : ℝ≥0∞) * η
    rw [risk_add π _ hfull hP]
    exact hcouple.trans ((add_le_add hi' hw).trans_eq (by push_cast; ring))

end LongTails.Proofs.AdditiveFixedPointBlocks
