import LongTails.Proofs.AdditiveFixedPointChain
import LongTails.Setups.AdditiveCubeFixedPoint

namespace LongTails.Proofs.AdditiveFixedPointFamily

open AdditiveFixedPointChain LongTails.Setups.AdditiveCubeFixedPoint

def extend {d : ℕ} (x : Fin d → ℝ) (i : ℕ) : ℝ := if hi : i < d then x ⟨i, hi⟩ else 0

lemma extend_close {d : ℕ} (x y : Fin d → ℝ) (i : ℕ) :
    |extend x i - extend y i| ≤ ‖x - y‖ := by
  by_cases hi : i < d
  · simpa [extend, hi, Real.norm_eq_abs] using norm_le_pi_norm (x - y) (⟨i, hi⟩ : Fin d)
  · simp [extend, hi]

def value {p : Params} (h : ℝ) (s : ℕ → Bool) (m : ℕ) (x : Cube p) (i : Fin p.d) : ℝ :=
  move h (x.val i) (if i.val < m then orient (s i.val) (score p.R s (extend x.val) i.val) else 0)

lemma score_le (a : ℝ) (s : ℕ → Bool) (x : ℕ → ℝ) (i : ℕ) : score a s x i ≤ a := by
  induction i with
  | zero => rfl
  | succ i ih => exact (min_le_left _ _).trans ih

lemma abs_orient (b : Bool) (v : ℝ) : |orient b v| = |v| := by cases b <;> simp [orient]

lemma value_mem {p : Params} {h : ℝ} (hh : 0 ≤ h) (s : ℕ → Bool) (m : ℕ) (x : Cube p) :
    ‖value h s m x‖ ≤ (p.R : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg p.R.coe_nonneg).2
  intro i
  have hx := (pi_norm_le_iff_of_nonneg p.R.coe_nonneg).1 x.property i
  rw [Real.norm_eq_abs, abs_le] at hx ⊢
  let c := if i.val < m then orient (s i.val) (score p.R s (extend x.val) i.val) else 0
  have hc : |c| ≤ p.R := by
    dsimp only [c]
    split
    · rw [abs_orient, abs_of_nonneg (score_nonneg p.R.coe_nonneg _ _ _)]
      exact score_le _ _ _ _
    · simp
  change -(p.R : ℝ) ≤ min (x.val i + h) (max (x.val i - h) c) ∧ _ ≤ _
  have hc' := abs_le.mp hc
  constructor
  · exact le_min (by linarith [hx.1]) (le_trans hc'.1 (le_max_right _ _))
  · exact le_trans (min_le_right _ _) (max_le (by linarith [hx.2]) hc'.2)

def map {p : Params} {h : ℝ} (hh : 0 ≤ h) (s : ℕ → Bool) (m : ℕ) : Cube p → Cube p :=
  fun x => ⟨value h s m x, value_mem hh s m x⟩

lemma map_lipschitz {p : Params} {h : ℝ} (hh : 0 ≤ h) (s : ℕ → Bool) (m : ℕ) :
    LipschitzWith 1 (map (p := p) hh s m) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  have hxy := norm_le_pi_norm (x.val - y.val) i
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hxy ⊢
  change |move h _ _ - move h _ _| ≤ _
  apply min_close (by simpa using hxy)
  apply max_close (by simpa using hxy)
  by_cases hi : i.val < m
  · simp only [hi, ↓reduceIte, orient_dist]
    exact score_close _ _ (norm_nonneg _) (extend_close x.val y.val) _
  · simp [hi]

lemma suffix_eq {p : Params} {h : ℝ} (hh : 0 ≤ h) (s : ℕ → Bool) {m M i : ℕ}
    (him : i < m) (x : Cube p) (hx : orient (s i) (extend x.val i) ≤ 0) :
    map hh s (max m M) x = map hh s m x := by
  apply Subtype.ext
  funext j
  change value h s (max m M) x j = value h s m x j
  unfold value
  by_cases hj : j.val < m
  · simp [hj, lt_of_lt_of_le hj (le_max_left m M)]
  · have hz := score_failure p.R.coe_nonneg s (extend x.val) (show i < j.val by omega) hx
    simp [hj, hz, orient]

lemma residual_recovers {p : Params} {h e : ℝ} (he : 0 ≤ e) (hh : e < h)
    (s : ℕ → Bool) {m : ℕ} (hm : m ≤ p.d) (ha : m * e < p.R) (x : Cube p)
    (hr : dist (map (he.trans hh.le) s m x) x ≤ e) :
    ∀ i < m, 0 < orient (s i) (extend x.val i) := by
  apply signs_of_residual he hh ha
  intro i hi
  have hid : i < p.d := by omega
  have hb := (pi_norm_le_iff_of_nonneg he).1
    (show ‖(map (he.trans hh.le) s m x).val - x.val‖ ≤ e from hr) (⟨i, hid⟩ : Fin p.d)
  simpa [map, value, step, hi, extend, hid, Real.norm_eq_abs] using hb

lemma block_energy {p : Params} {h : ℝ} (hh : 0 ≤ h) (s : ℕ → Bool)
    {l m : ℕ} (hlm : l ≤ m) (x : Cube p) {v : ℝ} (hv : 0 < v) :
    ∑ i, ((map hh s m x).val i - (map hh s l x).val i) ^ 2 / v ≤
      (m - l : ℕ) * ((2 * h) ^ 2 / v) := by
  classical
  let I : Finset (Fin p.d) := Finset.univ.filter (fun i => l ≤ i.val ∧ i.val < m)
  have hcard : I.card ≤ m - l := by
    have hb : I.card ≤ (Finset.Ico l m).card := by
      apply Finset.card_le_card_of_injOn Fin.val
      · intro i hi
        simpa [I] using hi
      · exact Fin.val_injective.injOn
    simpa using hb
  have hbound (j : ℕ) (i : Fin p.d) : |(map hh s j x).val i - x.val i| ≤ h := move_size hh _ _
  calc
    _ = ∑ i ∈ I, ((map hh s m x).val i - (map hh s l x).val i) ^ 2 / v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hnot : ¬(l ≤ i.val ∧ i.val < m) := by simpa [I] using hi
      by_cases hil : i.val < l
      · simp [map, value, hil, lt_of_lt_of_le hil hlm]
      · have him : ¬ i.val < m := by omega
        simp [map, value, hil, him]
    _ ≤ ∑ _i ∈ I, (2 * h) ^ 2 / v := by
      apply Finset.sum_le_sum
      intro i _
      apply div_le_div_of_nonneg_right _ hv.le
      have hx := abs_le.mp (hbound m i)
      have hy := abs_le.mp (hbound l i)
      have habs : |(map hh s m x).val i - (map hh s l x).val i| ≤ 2 * h :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr habs
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      gcongr

def writeWord {k : ℕ} (s : ℕ → Bool) (l : ℕ) (w : Fin k → Bool) (i : ℕ) : Bool :=
  if hi : l ≤ i ∧ i < l + k then w ⟨i - l, by omega⟩ else s i

lemma writeWord_before {k : ℕ} (s : ℕ → Bool) (l : ℕ) (w : Fin k → Bool) {i : ℕ}
    (hi : i < l) : writeWord s l w i = s i := by simp [writeWord, Nat.not_le_of_lt hi]

lemma writeWord_at {k : ℕ} (s : ℕ → Bool) (l : ℕ) (w : Fin k → Bool) (i : Fin k) :
    writeWord s l w (l + i) = w i := by
  simp [writeWord, i.isLt]

noncomputable def guess {p : Params} (l k : ℕ) (x : Cube p) : Fin k → Bool :=
  fun i => if 0 < extend x.val (l + i) then true else false

lemma guess_measurable {p : Params} (l k : ℕ) : Measurable (guess (p := p) l k) := by
  refine Measurable.of_eval fun i => ?_
  by_cases hi : l + i.val < p.d
  · simp only [guess, extend, hi, ↓reduceDIte]
    exact Measurable.ite (measurableSet_lt measurable_const ((measurable_pi_apply _).comp
      measurable_subtype_coe)) measurable_const measurable_const
  · simp [guess, extend, hi, measurable_const]

lemma score_congr (a : ℝ) (s t : ℕ → Bool) (x : ℕ → ℝ) (n : ℕ)
    (h : ∀ i < n, s i = t i) : score a s x n = score a t x n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [score, score, h n (by omega), ih (fun i hi => h i (by omega))]

lemma map_congr {p : Params} {h : ℝ} (hh : 0 ≤ h) {s t : ℕ → Bool} {m : ℕ}
    (hst : ∀ i < m, s i = t i) : map hh s m = (map hh t m : Cube p → Cube p) := by
  funext x
  apply Subtype.ext
  funext i
  change value h s m x i = value h t m x i
  unfold value
  by_cases hi : i.val < m
  · simp only [hi, ↓reduceIte, hst _ hi, score_congr _ s t _ i.val
      (fun j hj => hst j (hj.trans hi))]
  · simp [hi]

lemma agree_off_word {p : Params} {h : ℝ} (hh : 0 ≤ h) {s t : ℕ → Bool}
    {l k M : ℕ} (hM : l + k ≤ M) (w : Fin k → Bool)
    (hst : ∀ i < l + k, s i = writeWord t l w i) (x : Cube p)
    (hx : guess l k x ≠ w) : map hh s M x = map hh (writeWord t l w) (l + k) x := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, guess l k x j ≠ w j := Function.ne_iff.mp hx
  have hi : l + j.val < l + k := by omega
  have hs : s (l + j.val) = w j := (hst _ hi).trans (writeWord_at t l w j)
  have hz : orient (s (l + j.val)) (extend x.val (l + j.val)) ≤ 0 := by
    rw [hs]
    cases he : w j <;> simp [guess, he, orient] at hj ⊢ <;> linarith
  rw [← max_eq_right hM, suffix_eq hh s hi x hz, map_congr hh hst]

end LongTails.Proofs.AdditiveFixedPointFamily
