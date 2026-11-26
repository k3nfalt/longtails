import LongTails.Proofs.EscapeChainReveal
import LongTails.Proofs.EscapeChainFamily

open MeasureTheory

namespace LongTails.Proofs.EscapeChainInvariance

open scoped RealInnerProductSpace BigOperators
open EscapeChainProfiles EscapeChainGates EscapeChainCalculus EscapeChainFunction
open EscapeChainCoordinates EscapeChainOracle EscapeChainSimulator EscapeChainSmooth
open EscapeChainHiding EscapeChainFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

variable {u u' v v' : ℕ → E}

omit [CompleteSpace E] in
lemma link_congr {l : ℕ} (hu : ∀ m ≤ l, u' m = u m) (hv : v' l = v l) : link u' v' l = link u v l := by
  funext x
  unfold link
  rw [hv, hu l le_rfl]
  cases l with
  | zero => rfl
  | succ l => simp only [prevPsi, hu l (by omega)]

omit [CompleteSpace E] in
lemma resid_congr {l : ℕ} (hu : ∀ m < l, u' m = u m) (hv : ∀ m < l, v' m = v m) :
    resid u' v' l = resid u v l := by
  funext x
  unfold resid
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hu m (Finset.mem_range.1 hm), hv m (Finset.mem_range.1 hm)]

omit [CompleteSpace E] in
lemma saddle_congr {l : ℕ} (hu : ∀ m < l, u' m = u m) (hv : ∀ m ≤ l, v' m = v m) :
    saddle u' v' l = saddle u v l := by
  funext x
  unfold saddle window quarter
  rw [resid_congr hu (fun m hm => hv m hm.le), hv l le_rfl]
  cases l with
  | zero => rfl
  | succ l => simp only [prevGam, hu l (by omega)]

omit [CompleteSpace E] in
lemma hidden_congr {j : ℕ} (hu : ∀ m < j, u' m = u m) (hv : ∀ m < j, v' m = v m) :
    hidden j u' v' = hidden j u v := by
  funext x
  unfold EscapeChainFunction.hidden
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  rw [link_congr (fun m hm => hu m (by omega)) (hv l hl'),
    saddle_congr (fun m hm => hu m (by omega)) (fun m hm => hv m (by omega))]

omit [CompleteSpace E] in
lemma objJ_congr (K : ℕ) {j : ℕ} (hu : ∀ m < j, u' m = u m) (hv : ∀ m < j, v' m = v m) :
    objJ K j u' v' = objJ K j u v := by
  funext x; unfold objJ; rw [hidden_congr hu hv]

lemma mvec_congr (K : ℕ) {l : ℕ} (hu : ∀ m < l, u' m = u m) (hv : ∀ m ≤ l, v' m = v m) :
    mvec K u' v' l = mvec K u v l := by
  funext y; unfold mvec smask; rw [saddle_congr hu hv]

lemma prob_congr (K : ℕ) (A : ℝ) {l : ℕ} (hu : ∀ m < l, u' m = u m) (hv : ∀ m ≤ l, v' m = v m) :
    prob K A u' v' l = prob K A u v l := by
  funext y; unfold prob; rw [mvec_congr K hu hv]

lemma start_congr (K : ℕ) (A : ℝ) {l : ℕ} (hu : ∀ m < l, u' m = u m) (hv : ∀ m < l, v' m = v m) :
    start K A u' v' l = start K A u v l := by
  funext y
  unfold start
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_range.1 hm
  rw [prob_congr K A (fun i hi => hu i (by omega)) (fun i hi => hv i (by omega))]

lemma answerS_congr (K : ℕ) {j : ℕ} (A : ℝ) (hu : ∀ m < j, u' m = u m) (hv : ∀ m < j, v' m = v m) :
    answerS K j A u' v' = answerS K j A u v := by
  funext y U
  unfold answerS
  rw [objJ_congr K hu hv]
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  rw [start_congr K A (fun m hm => hu m (by omega)) (fun m hm => hv m (by omega)),
    prob_congr K A (fun m hm => hu m (by omega)) (fun m hm => hv m (by omega)),
    mvec_congr K (fun m hm => hu m (by omega)) (fun m hm => hv m (by omega))]

lemma reveals_congr (K : ℕ) (A : ℝ) {l : ℕ} (hu : ∀ m < l, u' m = u m) (hv : ∀ m ≤ l, v' m = v m)
    (y : E) (U : ℝ) : reveals K A u' v' l y U ↔ reveals K A u v l y U := by
  unfold reveals
  rw [start_congr K A hu (fun m hm => hv m hm.le), prob_congr K A hu hv]

omit [CompleteSpace E] in
lemma projL_congr {l : ℕ} (hu : ∀ m < l, u' m = u m) (hv : ∀ m < l, v' m = v m) :
    projL u' v' l = projL u v l := by
  unfold projL
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hu m (Finset.mem_range.1 hm), hv m (Finset.mem_range.1 hm)]

variable {d n b : ℕ}

lemma dirOf_swap (hnb : n * b ≤ d) (θ : Hid n b) {i k m : Fin n} (hik : i ≤ k) (hm : m < i) :
    dirOf hnb (θ.1 * Equiv.swap i k, θ.2) m = dirOf hnb θ m := by
  have h1 : m ≠ i := ne_of_lt hm
  have h2 : m ≠ k := ne_of_lt (lt_of_lt_of_le hm hik)
  simp only [dirOf, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]

lemma dirOf_sign (hnb : n * b ≤ d) (θ : Hid n b) {k m : Fin n} (hm : m ≠ k)
    (σs : Fin b → Bool) : dirOf hnb (θ.1, Function.update θ.2 (θ.1 k) σs) m = dirOf hnb θ m := by
  have h : θ.1 m ≠ θ.1 k := fun he => hm (θ.1.injective he)
  simp only [dirOf, Function.update_of_ne h]

lemma uOf_swap (hnb : n * b ≤ d) (θ : Hid n b) {i k : Fin n} (hik : i ≤ k) {l : ℕ}
    (hl : 2 * l < i) : uOf hnb (θ.1 * Equiv.swap i k, θ.2) l = uOf hnb θ l := by
  have hn : 2 * l < n := lt_trans hl i.2
  simp only [uOf, dite_eq_left hn]
  exact dirOf_swap hnb θ hik (Fin.mk_lt_mk.2 hl |>.trans_le le_rfl)

lemma vOf_swap (hnb : n * b ≤ d) (θ : Hid n b) {i k : Fin n} (hik : i ≤ k) {l : ℕ}
    (hl : 2 * l + 1 < i) : vOf hnb (θ.1 * Equiv.swap i k, θ.2) l = vOf hnb θ l := by
  have hn : 2 * l + 1 < n := lt_trans hl i.2
  simp only [vOf, dite_eq_left hn]
  exact dirOf_swap hnb θ hik (Fin.mk_lt_mk.2 hl |>.trans_le le_rfl)

lemma uOf_sign (hnb : n * b ≤ d) (θ : Hid n b) {k : Fin n} {l : ℕ} (hl : 2 * l < k)
    (σs : Fin b → Bool) : uOf hnb (θ.1, Function.update θ.2 (θ.1 k) σs) l = uOf hnb θ l := by
  have hn : 2 * l < n := lt_trans hl k.2
  simp only [uOf, dite_eq_left hn]
  exact dirOf_sign hnb θ (fun he => by rw [Fin.ext_iff] at he; simp at he; omega) σs

lemma vOf_sign (hnb : n * b ≤ d) (θ : Hid n b) {k : Fin n} {l : ℕ} (hl : 2 * l + 1 < k)
    (σs : Fin b → Bool) : vOf hnb (θ.1, Function.update θ.2 (θ.1 k) σs) l = vOf hnb θ l := by
  have hn : 2 * l + 1 < n := lt_trans hl k.2
  simp only [vOf, dite_eq_left hn]
  exact dirOf_sign hnb θ (fun he => by rw [Fin.ext_iff] at he; simp at he; omega) σs

end LongTails.Proofs.EscapeChainInvariance
