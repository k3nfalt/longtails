import LongTails.Algorithms.AdditiveCubeAnchoring
import LongTails.Proofs.AdditiveFixedPointBatch

open MeasureTheory
open LongTails.Setups.AdditiveCubeFixedPoint LongTails.Algorithms.AdditiveCubeAnchoring

namespace LongTails.Proofs.AdditiveCubeAnchoringExecution

open OracleTemplate HeavyTailedProductProcess AdditiveFixedPointProcess AdditiveFixedPointBatch

variable {p : Params}

lemma project_lipschitz (p : Params) : LipschitzWith 1 (project p) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Subtype.dist_eq, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact ((LipschitzWith.projIcc (show -(p.R : ℝ) ≤ p.R by linarith [p.R.coe_nonneg])).dist_le_mul
    (x i) (y i) |>.trans_eq (one_mul _)).trans (norm_le_pi_norm (x-y) i)

lemma project_fix (x : Cube p) : project p x.val = x := by
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (Set.projIcc_of_mem (show -(p.R : ℝ) ≤ p.R by linarith [p.R.coe_nonneg]) (abs_le.mp
    ((pi_norm_le_iff_of_nonneg p.R.coe_nonneg).mp x.property i)))

lemma policy (p : Params) : measurablePolicy (algorithm p) := by
  let _ : MeasurableSpace (List Command) := ⊤
  let _ : MeasurableSingletonClass (List Command) := ⟨fun _ => trivial⟩
  refine ⟨inferInstanceAs (MeasurableSpace (List Command × Data p)), measurable_const,
    measurable_const.prodMk ((project_lipschitz p).continuous.measurable.comp measurable_snd.fst), ?_,
    (project_lipschitz p).continuous.measurable.comp measurable_snd.fst⟩
  have hfixed (cmds : List Command) : Measurable (fun z : Data p × Point p => update (cmds,z.1) z.2) := by
    cases cmds with
    | nil => exact measurable_const.prodMk measurable_fst
    | cons cmd cs =>
      apply measurable_const.prodMk
      cases cmd with
      | none => unfold applyReply; fun_prop
      | some c =>
        rcases c with ⟨M,n,b⟩
        cases b <;> simp only [applyReply, Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have haux : Measurable (fun z : (Data p × Point p) × List Command => update (z.2,z.1.1) z.1.2) :=
    measurable_from_prod_countable_left hfixed
  exact haux.comp ((measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst)

noncomputable def mean (T : Cube p → Cube p) (x : Point p) := (T (project p x)).val

noncomputable def run (T : Cube p → Cube p) (ξ : ℕ → Point p) : List Command → ℕ → Data p → Data p
  | [], _, s => s
  | cmd :: cs, off, s => run T ξ cs (off+1) (applyReply cmd s (mean T s.1 + ξ off))

lemma run_append (T : Cube p → Cube p) (ξ : ℕ → Point p) (xs ys : List Command)
    (off : ℕ) (s : Data p) :
    run T ξ (xs++ys) off s = run T ξ ys (off+xs.length) (run T ξ xs off s) := by
  induction xs generalizing s off with
  | nil => simp [run]
  | cons c cs ih => simp only [List.cons_append, run, ih, List.length_cons]; congr 1; omega

lemma trajectory_program (T : Cube p → Cube p) (ξ : ℕ → Point p) (cs : List Command)
    (n : ℕ) (hn : cs.length ≤ n) (off : ℕ) (s : Data p) :
    trajectory (fun (st : List Command × Data p) z => update st (mean T st.2.1 + z))
      n (cs,s) (fun i => ξ (off+i)) = ([],run T ξ cs off s) := by
  induction n generalizing cs off s with
  | zero => have : cs = [] := List.length_eq_zero_iff.mp (by omega); subst cs; rfl
  | succ n ih =>
    cases cs with
    | nil =>
      simpa [trajectory, update, run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ih [] (by simp) (off+1) s)
    | cons c cs =>
      simp only [List.length_cons] at hn
      simpa [trajectory, run, update, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih cs (by omega) (off+1) (applyReply c s (mean T s.1 + ξ off))

lemma execute_run (P : ProbabilityMeasure (ℕ → Point p)) (T : Cube p → Cube p) (b : ℕ)
    (hb : (program (depth p) (replicas p)).length ≤ b) (ξ : ℕ → Point p) :
    output p { Seed := fun _ => Point p, law := P, answer := fun _ (_, x) z => (T x).val + z }
      (fun _ => b) ξ = project p (run T ξ (program (depth p) (replicas p)) 0 (0,0,0)).1 := by
  apply (execute_trajectory P T (algorithm p) b () ξ).trans
  have h := trajectory_program T ξ _ b hb 0 (0,0,0)
  simp only [Nat.zero_add] at h
  exact congrArg (fun s : List Command × Data p => project p s.2.1) h

def blockSum (ξ : ℕ → Point p) (off n : ℕ) := sampleSum n (fun i => ξ (off+i))

lemma blockSum_succ (ξ : ℕ → Point p) (off n : ℕ) :
    blockSum ξ off (n+1) = blockSum ξ off n + ξ (off+n) := by simp [blockSum, sampleSum, Finset.sum_range_succ]

lemma carry (T : Cube p → Cube p) (ξ : ℕ → Point p) (off n : ℕ) (x b : Point p) :
    run T ξ (List.replicate n none) off (x,b,0) =
      (x,b,(n : ℝ) • mean T x + blockSum ξ off n) := by
  induction n with
  | zero => simp [run, blockSum, sampleSum]
  | succ n ih =>
    rw [List.replicate_succ', run_append, ih]
    simp only [List.length_replicate, run, applyReply, Nat.cast_succ, add_smul, one_smul, blockSum_succ]
    congr 2
    abel

noncomputable def picard (T : Cube p → Cube p) (M : ℕ) (b x noise : Point p) : Point p :=
  (1 + (M : ℝ)⁻¹)⁻¹ • (b + (mean T x + noise))

lemma run_batch (T : Cube p → Cube p) (ξ : ℕ → Point p) (off M n : ℕ) (hn : 0 < n)
    (last : Bool) (x b : Point p) :
    let z := picard T M b x ((n : ℝ)⁻¹ • blockSum ξ off n)
    run T ξ (batch M n last) off (x,b,0) =
      (z, if last then b + (7*(M : ℝ)⁻¹) • z else b, 0) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [batch, run_append, carry, List.length_replicate, run, applyReply, picard]
  have hid : (j : ℝ) • mean T x + blockSum ξ off j + (mean T x + ξ (off+j)) =
      ((j+1 : ℕ) : ℝ) • mean T x + blockSum ξ off (j+1) := by
    rw [blockSum_succ, Nat.cast_succ, add_smul, one_smul]
    abel
  simp only [Nat.succ_sub_one]
  have hmean : ((j+1 : ℕ) : ℝ)⁻¹ • (((j+1 : ℕ) : ℝ) • mean T x + blockSum ξ off (j+1)) =
      mean T x + ((j+1 : ℕ) : ℝ)⁻¹ • blockSum ξ off (j+1) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  rw [hid, hmean]

lemma batch_length (M n : ℕ) (hn : 0 < n) (last : Bool) : (batch M n last).length = n := by
  simp [batch]
  omega

lemma flat_length (xs : List Command) (k : ℕ) :
    (List.replicate k xs).flatten.length = k * xs.length := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

lemma stage_length (M n : ℕ) (hM : 0 < M) (hn : 0 < n) : (stage M n).length = 6*M*n := by
  simp only [stage, List.length_append, flat_length, batch_length M n hn]
  rw [← Nat.succ_mul]
  congr 1
  omega

noncomputable def iter (T : Cube p → Cube p) (ξ : ℕ → Point p) (off M n : ℕ)
    (b x : Point p) : ℕ → Point p
  | 0 => x
  | j+1 => picard T M b (iter T ξ off M n b x j)
      ((n : ℝ)⁻¹ • blockSum ξ (off+j*n) n)

lemma run_plain (T : Cube p → Cube p) (ξ : ℕ → Point p) (off M n : ℕ) (hn : 0 < n)
    (b x : Point p) (k : ℕ) :
    run T ξ (List.replicate k (batch M n false)).flatten off (x,b,0) =
      (iter T ξ off M n b x k,b,0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', List.flatten_append, run_append, ih, flat_length, batch_length _ _ hn]
    simpa [iter] using run_batch T ξ (off+k*n) M n hn false (iter T ξ off M n b x k) b

lemma run_stage (T : Cube p → Cube p) (ξ : ℕ → Point p) (off M n : ℕ) (hM : 0 < M)
    (hn : 0 < n) (b x : Point p) :
    let z := iter T ξ off M n b x (6*M)
    run T ξ (stage M n) off (x,b,0) = (z,b + (7*(M : ℝ)⁻¹) • z,0) := by
  let j := 6*M-1
  have hj : j+1 = 6*M := by dsimp [j]; omega
  rw [stage, run_append, run_plain _ _ _ _ _ hn, flat_length, batch_length _ _ hn]
  simpa only [← hj, iter, ↓reduceIte, Nat.add_sub_cancel] using
    run_batch T ξ (off+j*n) M n hn true (iter T ξ off M n b x j) b

end LongTails.Proofs.AdditiveCubeAnchoringExecution
