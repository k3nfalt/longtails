import LongTails.Proofs.ChiSquareBoundedCentreDroExecution
import LongTails.Proofs.ChiSquareBoundedCentreDroSelection
import LongTails.Proofs.ChiSquareConstants

open MeasureTheory Set
namespace OracleTemplate.ChiSquareBoundedCentreDro
open LongTails.Setups.ChiSquareConstrainedDro
open ChiSquareDro (radius Adm tail)
open ComponentEnvelope (Program)
noncomputable section
variable {q : Params} {I : Instance q} {proj : q.E → q.E}

lemma interpret_collect {α : Type*} (response : ℕ → q.E → q.E × ℝ × q.E)
    (jobs : ℕ → Plan q α) {m : ℕ} (h : ∀ i, Depth m (jobs i)) (k n : ℕ) (i : Fin n) :
    interpret response (collect jobs n) k i = interpret response (jobs i) (k+i.val*m) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [collect,interpret_bind response (depth_collect q jobs h n)]
    unfold Program.map
    rw [interpret_bind response (h n)]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [interpret]
    · simpa [interpret] using ih j

def estimate (I : Instance q) (proj : q.E → q.E) (w : Candidate q.E) (m : ℕ) (ξ : ℕ → q.Ξ) :=
  w.2+radius q*Real.sqrt ((∑ i : Fin m, tail (I.loss (proj w.1)) w.2 (ξ i)^2)/m)

def victor (I : Instance q) (proj : q.E → q.E) (m : ℕ) (x y : Candidate q.E) (ξ : ℕ → q.Ξ) :=
  if estimate I proj x m ξ ≤ estimate I proj y m (fun i => ξ (m+i)) then x else y

def advance (I : Instance q) (proj : q.E → q.E) (r h : ℕ) (xs : ℕ → Candidate q.E) (ξ : ℕ → q.Ξ)
    (k : ℕ) :=
  let i := k % 2^h
  let m := batchSize q r
  victor I proj m (xs (2*i)) (xs (2*i+1)) (fun j => ξ (i*(m+m)+j))

def champion (I : Instance q) (proj : q.E → q.E) (r : ℕ) :
    ℕ → (ℕ → Candidate q.E) → (ℕ → q.Ξ) → Candidate q.E
  | 0, xs, _ => xs 0
  | h+1, xs, ξ => champion I proj (r+1) h (advance I proj r h xs ξ)
      (fun t => ξ (2^h*(batchSize q r+batchSize q r)+t))

def response (I : Instance q) (proj : q.E → q.E) (ξ : ℕ → q.Ξ) (t : ℕ) (x : q.E) :=
  (proj x,I.loss (proj x) (ξ t),I.sub (proj x) (ξ t))

lemma interpret_score (w : Candidate q.E) (m k : ℕ) (ξ : ℕ → q.Ξ) :
    interpret (response I proj ξ) (score q w m m 0) k = estimate I proj w m (fun i => ξ (k+i)) := by
  let f := fun i => tail (I.loss (proj w.1)) w.2 (ξ (k+i))^2
  have H (n t : ℕ) (ht : t+n=m) :
      interpret (response I proj ξ) (score q w m n (∑ i ∈ Finset.range t, f i)) (k+t) =
        estimate I proj w m (fun i => ξ (k+i)) := by
    induction n generalizing t with
    | zero =>
      simp only [Nat.add_zero] at ht; subst t
      change w.2+radius q*Real.sqrt ((∑ i ∈ Finset.range m, f i)/m) =
        w.2+radius q*Real.sqrt ((∑ i : Fin m, f i)/m)
      rw [Fin.sum_univ_eq_sum_range f]
    | succ n ih =>
      simpa [score,interpret,Finset.sum_range_succ,response,tail,f,Nat.add_assoc] using ih (t+1) (by omega)
  simpa using H m 0 (by omega)

lemma interpret_match (x y : Candidate q.E) (r k : ℕ) (ξ : ℕ → q.Ξ) :
    interpret (response I proj ξ) (matchPair q r x y) k =
      victor I proj (batchSize q r) x y (fun i => ξ (k+i)) := by
  unfold matchPair
  rw [interpret_bind _ (depth_score q _ _ _ _)]
  unfold Program.map
  rw [interpret_bind _ (depth_score q _ _ _ _)]
  simp [interpret,interpret_score,victor,Nat.add_assoc]

lemma interpret_tournament (r h : ℕ) (xs : ℕ → Candidate q.E) (ξ : ℕ → q.Ξ) (k : ℕ) :
    interpret (response I proj ξ) (tournament q r h xs) k =
      (champion I proj r h xs (fun i => ξ (k+i))).1 := by
  induction h generalizing r xs k with
  | zero => rfl
  | succ h ih =>
    rw [tournament,interpret_bind _ (depth_collect q _ (fun i => depth_match q _ _ _) _),ih]
    rw [champion]
    apply congrArg Prod.fst
    congr 1
    · funext i
      rw [interpret_collect _ _ (fun i => depth_match q _ _ _),interpret_match]
      simp [advance,Nat.add_assoc]
    · funext i; simp [Nat.add_assoc]

lemma champion_property {W : Candidate q.E → Prop} (r h : ℕ) (xs : ℕ → Candidate q.E)
    (hx : ∀ i < 2^h, W (xs i)) (ξ : ℕ → q.Ξ) : W (champion I proj r h xs ξ) := by
  induction h generalizing r xs ξ with
  | zero => exact hx 0 (by norm_num)
  | succ h ih =>
    apply ih
    intro i hi
    unfold advance victor
    simp only [Nat.mod_eq_of_lt hi]
    rw [pow_succ] at hx
    split <;> apply hx <;> omega

lemma estimate_meas (hI : Adm q I proj) (m : ℕ) :
    Measurable (fun p : Candidate q.E × (ℕ → q.Ξ) => estimate I proj p.1 m p.2) := by
  unfold estimate tail
  have hL (i : Fin m) : Measurable (fun p : Candidate q.E × (ℕ → q.Ξ) => I.loss (proj p.1.1) (p.2 i)) := hI.loss_meas.comp
    ((hI.proj_meas.comp (measurable_fst.comp (measurable_fst (β := ℕ → q.Ξ)))).prodMk
      ((measurable_pi_apply (i:ℕ)).comp measurable_snd))
  exact (measurable_snd.comp measurable_fst).add
    (measurable_const.mul ((Finset.measurable_sum _ fun i _ =>
      (((hL i).sub (measurable_snd.comp measurable_fst)).max measurable_const).pow_const 2).div_const _).sqrt)

lemma advance_meas (hI : Adm q I proj) (r h : ℕ) :
    Measurable (fun p : (ℕ → Candidate q.E) × (ℕ → q.Ξ) => advance I proj r h p.1 p.2) := by
  apply Measurable.of_eval
  intro k
  let i := k % 2^h
  let m := batchSize q r
  have hx : Measurable (fun p : (ℕ → Candidate q.E) × (ℕ → q.Ξ) => p.1 (2*i)) :=
    (measurable_pi_apply _).comp measurable_fst
  have hy : Measurable (fun p : (ℕ → Candidate q.E) × (ℕ → q.Ξ) => p.1 (2*i+1)) :=
    (measurable_pi_apply _).comp measurable_fst
  unfold advance victor
  apply Measurable.ite _ hx hy
  apply measurableSet_le
  · exact (estimate_meas hI m).comp (hx.prodMk (Measurable.of_eval fun j =>
      (measurable_pi_apply (i*(m+m)+j)).comp measurable_snd))
  · exact (estimate_meas hI m).comp (hy.prodMk (Measurable.of_eval fun j =>
      (measurable_pi_apply (i*(m+m)+(m+j))).comp measurable_snd))

lemma champion_meas (hI : Adm q I proj) (r h : ℕ) :
    Measurable (fun p : (ℕ → Candidate q.E) × (ℕ → q.Ξ) => champion I proj r h p.1 p.2) := by
  induction h generalizing r with
  | zero => exact (measurable_pi_apply 0).comp measurable_fst
  | succ h ih =>
    exact (ih (r+1)).comp ((advance_meas hI r h).prodMk (Measurable.of_eval fun j =>
      (measurable_pi_apply (2^h*(batchSize q r+batchSize q r)+j)).comp measurable_snd))

end
end OracleTemplate.ChiSquareBoundedCentreDro
