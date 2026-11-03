import LongTails.Proofs.FiniteScaleConvolutionalSgdTuning
import LongTails.Proofs.Execution

open Classical MeasureTheory OracleTemplate

namespace LongTails.Proofs.FiniteScaleConvolutionalSgdExecution

open LongTails.Setups.FiniteScaleConvolutionalSgd
open LongTails.Algorithms.FiniteScaleConvolutionalSgd (algorithm output)

noncomputable def step (p : Public) (data : Data p) (η scale : ℝ) (period : ℕ+)
    (s : ScanState p) : ScanState p :=
  scanUpdate p η scale period s (answer p data (scanQuery p s))

noncomputable def stateAt (p : Public) (data : Data p) (η scale : ℝ) (period : ℕ+)
    (ω : p.sampling.Ω) (k : ℕ) : ScanState p :=
  (step p data η scale period)^[k] (initial p scale ω)

lemma execute_stateAt (p : Public) (data : Data p)
    (O : Oracle (Query p) (Reply p.dimension))
    (hO : ∀ history q ξ, O.answer history (0, q) ξ = answer p data q)
    (η scale : ℝ) (period : ℕ+) (K : ℕ) (ω : p.sampling.Ω)
    (ξ : (k : ℕ) → O.Seed k) :
    output p η scale period O K ω ξ = (stateAt p data η scale period ω K).point := by
  exact (execute_eq_of_answer_eq O (answer p data) hO
    (algorithm p η scale period) K ω ξ).trans
    (execute_iterate (answer p data) (algorithm p η scale period) K ω)

lemma step_frozen (p : Public) (data : Data p) (η scale : ℝ) (period : ℕ+)
    (s : ScanState p) (hs : s.frozen = true) : step p data η scale period s = s := by
  simp [step, scanUpdate, hs]

lemma iterate_frozen (p : Public) (data : Data p) (η scale : ℝ) (period : ℕ+)
    (s : ScanState p) (hs : s.frozen = true) (k : ℕ) :
    (step p data η scale period)^[k] s = s := by
  exact Function.IsFixedPt.iterate (step_frozen p data η scale period s hs) k

lemma stateAt_add (p : Public) (data : Data p) (η scale : ℝ) (period : ℕ+)
    (ω : p.sampling.Ω) (k t : ℕ) :
    stateAt p data η scale period ω (k + t) =
      (step p data η scale period)^[t] (stateAt p data η scale period ω k) := by
  simp only [stateAt, Nat.add_comm k t, Function.iterate_add_apply]

noncomputable def scanPrefix (p : Public) (data : Data p) (w : Space p.dimension)
    (ω : p.sampling.Ω) (b k : ℕ) (hk : k < p.count) : ScanState p := by
  classical
  exact ⟨ω, w, ⟨k, hk⟩, false,
    decide (∃ i : Fin p.count, i.val < k ∧ (answer p data (i, w)).margin ≤ 0), b, false⟩

lemma scanPrefix_step (p : Public) (data : Data p) (w : Space p.dimension)
    (ω : p.sampling.Ω) (η scale : ℝ) (period : ℕ+) (b k : ℕ)
    (hk : k < p.count) (hnext : k + 1 < p.count) :
    step p data η scale period (scanPrefix p data w ω b k hk) =
      scanPrefix p data w ω b (k + 1) hnext := by
  classical
  have he := NoisyBatchQuadraticPerceptronExecution.prefix_exists_succ
    (fun i : Fin p.count => (answer p data (i, w)).margin ≤ 0) hk
  simp only [Nat.lt_succ_iff] at he
  simp [step, scanPrefix, scanQuery, scanUpdate, hnext, he]

lemma scanPrefix_terminal_state (p : Public) (data : Data p) (w : Space p.dimension)
    (ω : p.sampling.Ω) (η scale : ℝ) (period : ℕ+) (b k : ℕ)
    (hk : k < p.count) (hlast : k + 1 = p.count) :
    step p data η scale period (scanPrefix p data w ω b k hk) =
      if Separates p data w then { scanPrefix p data w ω b k hk with frozen := true }
      else { scanPrefix p data w ω b k hk with training := true, violated := true } := by
  classical
  have he := NoisyBatchQuadraticPerceptronExecution.prefix_exists_succ
    (fun i : Fin p.count => (answer p data (i, w)).margin ≤ 0) hk
  rw [hlast] at he
  simp only [Fin.is_lt, true_and] at he
  have hsep : Separates p data w ↔ ¬∃ i : Fin p.count, (answer p data (i, w)).margin ≤ 0 := by
    simp [Separates, answer]
  have hn : ¬k + 1 < p.count := by omega
  by_cases h : Separates p data w
  · have he' := he.not.mp (hsep.mp h)
    simp [step, scanPrefix, scanQuery, scanUpdate, hn, h, he']
  · have hex : ∃ i : Fin p.count, (answer p data (i, w)).margin ≤ 0 := by
      by_contra hh
      exact h (hsep.mpr hh)
    have he' := he.mp hex
    simp [step, scanPrefix, scanQuery, scanUpdate, hn, h, he']

lemma scanPrefix_iterate (p : Public) (data : Data p) (w : Space p.dimension)
    (ω : p.sampling.Ω) (η scale : ℝ) (period : ℕ+) (b k : ℕ) (hk : k < p.count) :
    (step p data η scale period)^[k] (scanPrefix p data w ω b 0 p.count.pos) =
      scanPrefix p data w ω b k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp : k < p.count := by omega
    rw [Function.iterate_succ_apply', ih hp]
    exact scanPrefix_step p data w ω η scale period b k hp hk

lemma full_scan (p : Public) (data : Data p) (w : Space p.dimension)
    (ω : p.sampling.Ω) (η scale : ℝ) (period : ℕ+) (b : ℕ) :
    (step p data η scale period)^[p.count] (scanPrefix p data w ω b 0 p.count.pos) =
      if Separates p data w then
        { scanPrefix p data w ω b (p.count - 1) (by have := p.count.pos; omega) with frozen := true }
      else
        { scanPrefix p data w ω b (p.count - 1) (by have := p.count.pos; omega) with
          training := true, violated := true } := by
  have hk : (p.count : ℕ) - 1 < p.count := by have := p.count.pos; omega
  have he : (p.count : ℕ) - 1 + 1 = p.count := by have := p.count.pos; omega
  conv_lhs => rw [← he]
  rw [Function.iterate_succ_apply', scanPrefix_iterate p data w ω η scale period b _ hk]
  exact scanPrefix_terminal_state p data w ω η scale period b _ hk he

noncomputable def trainingPoint (p : Public) (data : Data p) (η scale : ℝ) (period : ℕ+)
    (ω : p.sampling.Ω) : ℕ → Space p.dimension
  | 0 => start p scale
  | k + 1 => if (k + 1) % period = 0 then start p scale else
      let w := trainingPoint p data η scale period ω k
      let reply := answer p data (p.sampling.sample k ω, w)
      w + (η / (1 + Real.exp reply.margin)) • reply.direction

lemma full_cycle (p : Public) (data : Data p) (w : Space p.dimension)
    (ω : p.sampling.Ω) (η scale : ℝ) (period : ℕ+) (b : ℕ) :
    (step p data η scale period)^[p.count + 1] (scanPrefix p data w ω b 0 p.count.pos) =
      if Separates p data w then
        { scanPrefix p data w ω b (p.count - 1) (by have := p.count.pos; omega) with frozen := true }
      else scanPrefix p data
        (if (b + 1) % period = 0 then start p scale else
          w + (η / (1 + Real.exp (answer p data (p.sampling.sample b ω, w)).margin)) •
            (answer p data (p.sampling.sample b ω, w)).direction)
        ω (b + 1) 0 p.count.pos := by
  classical
  rw [Function.iterate_succ_apply', full_scan]
  by_cases hs : Separates p data w
  · simp only [ite_eq_left hs]
    exact step_frozen p data η scale period _ rfl
  · simp [hs, step, scanQuery, scanUpdate, scanPrefix]

lemma cycle_boundary (p : Public) (data : Data p) (η scale : ℝ) (period : ℕ+)
    (ω : p.sampling.Ω) (t : ℕ) :
    let s := stateAt p data η scale period ω (((p.count : ℕ) + 1) * t)
    (s.frozen = true ∧ Separates p data s.point) ∨
      s = scanPrefix p data (trainingPoint p data η scale period ω t) ω t 0 p.count.pos := by
  induction t with
  | zero =>
    right
    simp [stateAt, initial, trainingPoint, scanPrefix]
  | succ t ih =>
    dsimp only at ih ⊢
    rw [Nat.mul_succ, stateAt_add]
    rcases ih with ⟨hf, hs⟩ | he
    · rw [iterate_frozen p data η scale period _ hf]
      exact Or.inl ⟨hf, hs⟩
    · rw [he, full_cycle]
      by_cases hs : Separates p data (trainingPoint p data η scale period ω t)
      · simp only [ite_eq_left hs]
        exact Or.inl ⟨by trivial, hs⟩
      · simp only [ite_eq_right hs]
        exact Or.inr rfl

lemma success_persists (p : Public) (data : Data p) (η scale : ℝ) (period : ℕ+)
    (ω : p.sampling.Ω) (k n : ℕ) (hkn : k ≤ n)
    (hs : (stateAt p data η scale period ω k).frozen = true ∧
      Separates p data (stateAt p data η scale period ω k).point) :
    (stateAt p data η scale period ω n).frozen = true ∧
      Separates p data (stateAt p data η scale period ω n).point := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [stateAt_add, iterate_frozen p data η scale period _ hs.1]
  exact hs

lemma cycle_success (p : Public) (data : Data p) (η scale : ℝ) (period : ℕ+)
    (ω : p.sampling.Ω) (t : ℕ)
    (hs : Separates p data (trainingPoint p data η scale period ω t)) :
    (stateAt p data η scale period ω (((p.count : ℕ) + 1) * (t + 1))).frozen = true ∧
      Separates p data (stateAt p data η scale period ω (((p.count : ℕ) + 1) * (t + 1))).point := by
  rcases cycle_boundary p data η scale period ω t with h | he
  · exact success_persists p data η scale period ω _ _ (Nat.mul_le_mul_left _ (Nat.le_succ t)) h
  · rw [Nat.mul_succ, stateAt_add, he, full_cycle, ite_eq_left hs]
    exact ⟨rfl, hs⟩

lemma failure_past_cycle (p : Public) (data : Data p) (η scale : ℝ) (period : ℕ+)
    (ω : p.sampling.Ω) (t calls : ℕ) (ht : ((p.count : ℕ) + 1) * (t + 1) ≤ calls)
    (hf : ¬Separates p data (stateAt p data η scale period ω calls).point) :
    ¬Separates p data (trainingPoint p data η scale period ω t) := by
  intro hs
  exact hf (success_persists p data η scale period ω _ calls ht
    (cycle_success p data η scale period ω t hs)).2

noncomputable def physicalPath (p : Public) (data : Data p) (η : ℝ)
    (w : Space p.dimension) (samples : ℕ → Fin p.count) : ℕ → Space p.dimension
  | 0 => w
  | k + 1 =>
      let x := physicalPath p data η w samples k
      let reply := answer p data (samples k, x)
      x + (η / (1 + Real.exp reply.margin)) • reply.direction

lemma trainingPoint_restart (p : Public) (data : Data p) (η scale : ℝ) (period : ℕ+)
    (ω : p.sampling.Ω) (j : ℕ) :
    trainingPoint p data η scale period ω (j * period) = start p scale := by
  cases h : j * (period : ℕ) with
  | zero => rfl
  | succ n =>
    have hm : (n + 1) % period = 0 := by rw [← h]; simp
    simp [trainingPoint, hm]

lemma trainingPoint_block (p : Public) (data : Data p) (η scale : ℝ) (period : ℕ+)
    (ω : p.sampling.Ω) (j k : ℕ) (hk : k < period) :
    trainingPoint p data η scale period ω (j * period + k) =
      physicalPath p data η (start p scale) (fun l => p.sampling.sample (j * period + l) ω) k := by
  induction k with
  | zero => simpa [physicalPath] using trainingPoint_restart p data η scale period ω j
  | succ k ih =>
    have hprev : k < period := by omega
    have hm : (j * (period : ℕ) + k + 1) % period ≠ 0 := by
      simp [Nat.add_assoc, Nat.add_mod, Nat.mod_eq_of_lt hk]
    rw [Nat.add_succ, trainingPoint, ite_eq_right hm, ih hprev]
    rfl

open ManySampleConvolutionalPerceptronDynamics (State)
open ManySampleConvolutionalPerceptronGeometry (decode plusFeature minusFeature)
open FiniteScaleConvolutionalSgdGeometry
open FiniteScaleConvolutionalSgdProcess

lemma physicalPath_normalized (p : Public) (data : Data p) (G : Geometry p data)
    (η scale : ℝ) (hη : η ≠ 0) (x : State (Features p.dimension))
    (samples : ℕ → Fin p.count) (hd : 0 < p.dimension)
    (hx : inner ℝ (axis p.dimension) x.z = 0) (k : ℕ) :
    physicalPath p data η (scale • decode (η * p.contrast) x) samples k =
      scale • decode (η * p.contrast)
        (trajectory (scale ^ 2 / η) ((η * p.contrast) ^ 2)
          (fun i => η * G.background i) (fun i => plusFeature (G.defect i))
          (fun i => minusFeature (G.defect i)) x samples k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [physicalPath, ih, answer, trajectory]
    apply physical_next p data G η scale hη _ _ hd
    exact trajectory_orthogonal _ _ _ _ _ _ _ _ hx (plus_centered p data G) (minus_centered p data G) k

lemma physicalPath_start (p : Public) (data : Data p) (G : Geometry p data)
    (η scale : ℝ) (hη : η ≠ 0) (hs : scale ≠ 0) (hε : η * p.contrast ≠ 0)
    (samples : ℕ → Fin p.count) (hd : 0 < p.dimension) (k : ℕ) :
    physicalPath p data η (start p scale) samples k =
      scale • decode (η * p.contrast)
        (trajectory (scale ^ 2 / η) ((η * p.contrast) ^ 2)
          (fun i => η * G.background i) (fun i => plusFeature (G.defect i))
          (fun i => minusFeature (G.defect i)) (initialState p scale (η * p.contrast)) samples k) := by
  rw [start_decode p scale (η * p.contrast) hs hε]
  exact physicalPath_normalized p data G η scale hη _ samples hd
    (initialState_centered p scale (η * p.contrast) hd) k

lemma separates_normalized (p : Public) (data : Data p) (G : Geometry p data)
    (η scale : ℝ) (hη : 0 < η) (hs : scale ≠ 0) (x : State (Features p.dimension))
    (hd : 0 < p.dimension) (hx : inner ℝ (axis p.dimension) x.z = 0) :
    Separates p data (scale • decode (η * p.contrast) x) ↔
      SeparatesState ((η * p.contrast) ^ 2) (fun i => η * G.background i)
        (fun i => plusFeature (G.defect i)) (fun i => minusFeature (G.defect i)) x := by
  have hK : 0 < scale ^ 2 / η := div_pos (sq_pos_of_ne_zero hs) hη
  simp only [Separates, SeparatesState]
  simp_rw [physical_score p data G η scale hη.ne' x _ hd hx, mul_pos_iff_of_pos_left hK]

lemma physicalPath_separates_iff (p : Public) (data : Data p) (G : Geometry p data)
    (η scale : ℝ) (hη : 0 < η) (hs : scale ≠ 0) (hε : η * p.contrast ≠ 0)
    (samples : ℕ → Fin p.count) (hd : 0 < p.dimension) (k : ℕ) :
    Separates p data (physicalPath p data η (start p scale) samples k) ↔
      SeparatesState ((η * p.contrast) ^ 2) (fun i => η * G.background i)
        (fun i => plusFeature (G.defect i)) (fun i => minusFeature (G.defect i))
        (trajectory (scale ^ 2 / η) ((η * p.contrast) ^ 2)
          (fun i => η * G.background i) (fun i => plusFeature (G.defect i))
          (fun i => minusFeature (G.defect i)) (initialState p scale (η * p.contrast)) samples k) := by
  rw [physicalPath_start p data G η scale hη.ne' hs hε samples hd k]
  apply separates_normalized p data G η scale hη hs _ hd
  exact trajectory_orthogonal _ _ _ _ _ _ _ _ (initialState_centered p scale _ hd)
    (plus_centered p data G) (minus_centered p data G) k

lemma output_failure_blocks (p : Public) (data : Data p) (G : Geometry p data)
    (η scale : ℝ) (period : ℕ+) (hη : 0 < η) (hs : scale ≠ 0) (hε : η * p.contrast ≠ 0)
    (hd : 0 < p.dimension) (ω : p.sampling.Ω) (T M calls : ℕ) (hT : T < period)
    (hcost : ((p.count : ℕ) + 1) * (M * period) ≤ calls)
    (hf : ¬Separates p data (stateAt p data η scale period ω calls).point) :
    ∀ j < M, FiniteScaleConvolutionalSgdStopping.NoSeparation (scale ^ 2 / η) ((η * p.contrast) ^ 2)
      (fun i => η * G.background i) (fun i => plusFeature (G.defect i))
      (fun i => minusFeature (G.defect i)) (initialState p scale (η * p.contrast))
      (fun k => p.sampling.sample (j * period + k) ω) T := by
  intro j hj k hk hsep
  have hkP : k < period := hk.trans_lt hT
  have hcycle : j * (period : ℕ) + k + 1 ≤ M * period := by
    have hh := Nat.mul_le_mul_right (period : ℕ) (Nat.succ_le_of_lt hj)
    nlinarith
  have hcall := (Nat.mul_le_mul_left ((p.count : ℕ) + 1) hcycle).trans hcost
  apply failure_past_cycle p data η scale period ω (j * period + k) calls hcall hf
  rw [trainingPoint_block p data η scale period ω j k hkP]
  exact (physicalPath_separates_iff p data G η scale hη hs hε _ hd k).2 hsep

end LongTails.Proofs.FiniteScaleConvolutionalSgdExecution
