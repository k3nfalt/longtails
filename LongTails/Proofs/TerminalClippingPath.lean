import LongTails.Proofs.TerminalClippingThreshold
import LongTails.Proofs.TerminalClippingSchedule

set_option backward.isDefEq.respectTransparency false

open MeasureTheory

namespace OracleTemplate.TerminalClipping

open LongTails.Setups.TerminalClippingConvex

lemma run_feasible {Ω : Type*} (q : Public) (g : Vector q.d → Ω → Vector q.d)
    (projection : Vector q.d → Vector q.d) {X : Set (Vector q.d)}
    (hp : ∀ x, projection x ∈ X) (n t : ℕ) {x : Vector q.d} (hx : x ∈ X)
    (p : Vector q.d) (ξ : ℕ → Ω) : run q g projection n t x p ξ ∈ X := by
  induction n generalizing t x p ξ with
  | zero => exact hx
  | succ n ih => exact ih (t + 1) (hp _) _ _

lemma terminal_feasible {Ω : Type*} (q : Public) (g : Vector q.d → Ω → Vector q.d)
    (projection : Vector q.d → Vector q.d) {X : Set (Vector q.d)}
    (hp : ∀ x, projection x ∈ X) (hx : q.x0 ∈ X) (ξ : ℕ → Ω) :
    terminal q g projection ξ ∈ X := run_feasible q g projection hp q.T 0 hx 0 ξ

lemma nextAuxiliary_measurable (q : Public) (t : ℕ) :
    Measurable (fun z : Vector q.d × Vector q.d =>
      nextAuxiliary q.B q.δ q.T t z.1 z.2) := by
  unfold nextAuxiliary
  fun_prop

lemma nextPoint_measurable (q : Public) (t : ℕ) :
    Measurable (fun z : (Vector q.d × Vector q.d) × Vector q.d =>
      nextPoint id q.B q.G q.δ q.T t z.1.1 z.1.2 z.2) := by
  have hU : Measurable (fun z : (Vector q.d × Vector q.d) × Vector q.d =>
      influenceScale q.B q.δ q.T t • (z.1.1 - z.1.2)) := by fun_prop
  have hC := (threshold_measurable (E := Vector q.d) q.B q.G q.T).comp
    (measurable_fst.fst.prodMk hU)
  have hc := measurable_variable_clip hC (measurable_snd :
    Measurable (fun z : (Vector q.d × Vector q.d) × Vector q.d => z.2))
  exact measurable_fst.fst.sub (hc.const_smul (stepSize q.B q.δ q.T t))

lemma run_measurable {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    {g : Vector q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {projection : Vector q.d → Vector q.d} (hp : Measurable projection) (n t : ℕ) :
    Measurable (fun z : (Vector q.d × Vector q.d) × (ℕ → Ω) =>
      run q g projection n t z.1.1 z.1.2 z.2) := by
  induction n generalizing t with
  | zero => exact measurable_fst.fst
  | succ n ih =>
    have hu : Measurable (fun z : (Vector q.d × Vector q.d) × (ℕ → Ω) =>
        z.1.1 - q.x0) := by fun_prop
    have hsample : Measurable (fun z : (Vector q.d × Vector q.d) × (ℕ → Ω) => z.2 0) :=
      (measurable_pi_apply 0).comp measurable_snd
    have hgrad : Measurable (fun z : (Vector q.d × Vector q.d) × (ℕ → Ω) => g z.1.1 (z.2 0)) :=
      hg.comp (measurable_fst.fst.prodMk hsample)
    have hy := hp.comp ((measurable_const : Measurable (fun _ : (Vector q.d × Vector q.d) × (ℕ → Ω) => q.x0)).add ((nextPoint_measurable q t).comp
      ((hu.prodMk measurable_fst.snd).prodMk hgrad)))
    have haux := (nextAuxiliary_measurable q t).comp (hu.prodMk measurable_fst.snd)
    have hshift : Measurable (fun z : (Vector q.d × Vector q.d) × (ℕ → Ω) =>
        fun k => z.2 (k + 2)) := by fun_prop
    exact (ih (t + 1)).comp ((hy.prodMk haux).prodMk hshift)

lemma terminal_measurable {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    {g : Vector q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {projection : Vector q.d → Vector q.d} (hp : Measurable projection) :
    Measurable (terminal q g projection) :=
  (run_measurable q hg hp q.T 0).comp ((measurable_const : Measurable (fun _ : ℕ → Ω => (q.x0, (0 : Vector q.d)))).prodMk measurable_id)

lemma transition_measurable {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    {g : Vector q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {projection : Vector q.d → Vector q.d} (hp : Measurable projection) :
    Measurable (Function.uncurry (transition q g projection)) := by
  have hnp : Measurable (fun z : ℕ × ((Vector q.d × Vector q.d) × Vector q.d) =>
      nextPoint id q.B q.G q.δ q.T z.1 z.2.1.1 z.2.1.2 z.2.2) :=
    measurable_from_prod_countable_right (nextPoint_measurable q)
  have hpa : Measurable (fun z : ℕ × (Vector q.d × Vector q.d) =>
      nextAuxiliary q.B q.δ q.T z.1 z.2.1 z.2.2) :=
    measurable_from_prod_countable_right (nextAuxiliary_measurable q)
  have hu : Measurable (fun z : (ℕ × (Vector q.d × Vector q.d)) × Ω =>
      z.1.2.1 - q.x0) := by fun_prop
  have hgrad : Measurable (fun z : (ℕ × (Vector q.d × Vector q.d)) × Ω =>
      g z.1.2.1 z.2) := hg.comp (measurable_fst.snd.fst.prodMk measurable_snd)
  have hy := hp.comp ((measurable_const : Measurable
    (fun _ : (ℕ × (Vector q.d × Vector q.d)) × Ω => q.x0)).add
    (hnp.comp (measurable_fst.fst.prodMk
      ((hu.prodMk measurable_fst.snd.snd).prodMk hgrad))))
  have haux := hpa.comp (measurable_fst.fst.prodMk (hu.prodMk measurable_fst.snd.snd))
  exact (measurable_fst.fst.add_const 1).prodMk (hy.prodMk haux)

lemma trajectory_time {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (ξ : ℕ → Ω) (n : ℕ) : (trajectory q g projection ξ n).1 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [trajectory, transition] using congrArg (fun k => k + 1) ih

lemma trajectory_feasible {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    {X : Set (Vector q.d)} (hx : q.x0 ∈ X) (hp : ∀ x, projection x ∈ X)
    (ξ : ℕ → Ω) (n : ℕ) : (trajectory q g projection ξ n).2.1 ∈ X := by
  cases n with
  | zero => exact hx
  | succ n => exact hp _

lemma trajectory_auxiliary_norm {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (hB : 0 < q.B) (hδ : 0 < q.δ) (hδ1 : q.δ < 1)
    (ξ : ℕ → Ω) {r : ℝ} (hr : 0 ≤ r) (n : ℕ) (hn : n ≤ q.T)
    (hx : ∀ t < n, ‖(trajectory q g projection ξ t).2.1 - q.x0‖ ≤ r) :
    ‖(trajectory q g projection ξ n).2.2‖ ≤ r := by
  induction n with
  | zero => simpa only [trajectory, norm_zero] using hr
  | succ n ih =>
    have hp := ih (by omega) (fun t ht => hx t (by omega))
    change ‖nextAuxiliary q.B q.δ q.T (trajectory q g projection ξ n).1
      ((trajectory q g projection ξ n).2.1 - q.x0) (trajectory q g projection ξ n).2.2‖ ≤ r
    rw [trajectory_time]
    exact nextAuxiliary_norm hB hδ hδ1 (by omega) (hx n (by omega)) hp

end OracleTemplate.TerminalClipping
