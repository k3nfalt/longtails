import LongTails.Algorithms.ComparisonTrustRegion
import LongTails.Proofs.Execution

namespace LongTails.Proofs.ComparisonTrustVisits

open OracleTemplate LongTails.Algorithms.ComparisonTrustRegion

noncomputable section

section Generic

variable {E U V S : Type*}

def Cov (Φ : (E → Prop) → U → Prop) : {k : ℕ} → QueryPlan (E × E) Bool U k → (E → Prop) → Prop
  | _, .done v, P => Φ P v
  | _, .ask q next, P => ∀ r, Cov Φ (next r) (fun x => P x ∨ x = q.1 ∨ x = q.2)

lemma cov_bind_any {k m : ℕ} (p : QueryPlan (E × E) Bool U k)
    (next : U → QueryPlan (E × E) Bool V m) (Ψ : (E → Prop) → V → Prop) (P : E → Prop)
    (h : ∀ P' : E → Prop, (∀ x, P x → P' x) → ∀ u, Cov Ψ (next u) P') :
    Cov Ψ (QueryPlan.bind p next) P := by
  induction p generalizing P with
  | done v => exact h P (fun _ hx => hx) v
  | ask q rest ih =>
      intro r
      exact ih r _ (fun P' hP' u => h P' (fun x hx => hP' x (Or.inl hx)) u)

lemma cov_bind {k m : ℕ} (p : QueryPlan (E × E) Bool U k)
    (next : U → QueryPlan (E × E) Bool V m) (Φ : (E → Prop) → U → Prop)
    (Ψ : (E → Prop) → V → Prop) (P : E → Prop) (h1 : Cov Φ p P)
    (h2 : ∀ P' u, Φ P' u → Cov Ψ (next u) P') :
    Cov Ψ (QueryPlan.bind p next) P := by
  induction p generalizing P with
  | done v => exact h2 P v h1
  | ask q rest ih =>
      intro r
      exact ih r _ (h1 r)

lemma cov_map {k : ℕ} (f : U → V) (p : QueryPlan (E × E) Bool U k)
    (Φ : (E → Prop) → U → Prop) (Ψ : (E → Prop) → V → Prop) (P : E → Prop) (h1 : Cov Φ p P)
    (h2 : ∀ P' u, Φ P' u → Ψ P' (f u)) :
    Cov Ψ (QueryPlan.map f p) P := by
  induction p generalizing P with
  | done v => exact h2 P v h1
  | ask q rest ih =>
      intro r
      exact ih r _ (h1 r)

lemma cov_weaken {k : ℕ} (p : QueryPlan (E × E) Bool U k) (Φ Ψ : (E → Prop) → U → Prop)
    (P : E → Prop) (h1 : Cov Φ p P) (h2 : ∀ P' u, Φ P' u → Ψ P' u) : Cov Ψ p P := by
  induction p generalizing P with
  | done v => exact h2 P v h1
  | ask q rest ih =>
      intro r
      exact ih r _ (h1 r)

lemma cov_sub {k : ℕ} (p : QueryPlan (E × E) Bool U k) (Φ : (E → Prop) → U → Prop)
    (P : E → Prop) (h : Cov Φ p P) :
    Cov (fun P' u => (∀ x, P x → P' x) ∧ Φ P' u) p P := by
  induction p generalizing P with
  | done v => exact ⟨fun _ hx => hx, h⟩
  | ask q rest ih =>
      intro r
      exact cov_weaken _ _ _ _ (ih r _ (h r))
        (fun P' u hu => ⟨fun x hx => hu.1 x (Or.inl hx), hu.2⟩)

lemma cov_mono {k : ℕ} (p : QueryPlan (E × E) Bool U k) (Φ : (E → Prop) → U → Prop)
    (hΦ : ∀ P P' u, (∀ x, P x → P' x) → Φ P u → Φ P' u) (P P' : E → Prop)
    (hP : ∀ x, P x → P' x) (h : Cov Φ p P) : Cov Φ p P' := by
  induction p generalizing P P' with
  | done v => exact hΦ P P' v hP h
  | ask q rest ih =>
      intro r
      refine ih r _ _ ?_ (h r)
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl (hP x hx)
      · exact Or.inr hx

lemma cov_loop (c : ℕ) (step : ℕ → S → QueryPlan (E × E) Bool S c)
    (inv : ℕ → (E → Prop) → S → Prop)
    (hstep : ∀ j P s, inv j P s → Cov (inv (j + 1)) (step j s) P) :
    ∀ (k i : ℕ) (s : S) (P : E → Prop), inv i P s → Cov (inv (i + k)) (loop c step k i s) P := by
  intro k
  induction k with
  | zero => intro i s P h; exact h
  | succ k ih =>
      intro i s P h
      refine cov_bind (step i s) (fun s' => loop c step k (i + 1) s') (inv (i + 1)) _ P
        (hstep i P s h) ?_
      intro P' u hu
      have := ih (i + 1) u P' hu
      rwa [show i + 1 + k = i + (k + 1) by omega] at this

lemma cov_traverse {c : ℕ} : ∀ (k : ℕ) (plans : Fin k → QueryPlan (E × E) Bool U c)
    (P : E → Prop), Cov (fun _ l => l.length = k) (QueryPlan.traverse k plans) P := by
  intro k
  induction k with
  | zero => intro plans P; exact (rfl : ([] : List U).length = 0)
  | succ k ih =>
      intro plans P
      show Cov _ (QueryPlan.bind (plans 0) (fun value =>
        QueryPlan.map (value :: ·) (QueryPlan.traverse k (fun i => plans i.succ)))) P
      refine cov_bind_any (plans 0) _ _ P ?_
      intro P' _ u
      exact cov_map _ _ _ _ P' (ih (fun i => plans i.succ) P')
        (fun _ l hl => by simp [hl])

end Generic

section Trace

variable {E : Type*}

def Seen (x0 : E) (h : List ((Fin 1 × (E × E)) × Bool)) (x : E) : Prop :=
  x = x0 ∨ ∃ e ∈ h, x = e.1.2.1 ∨ x = e.1.2.2

lemma seen_append (x0 : E) (h : List ((Fin 1 × (E × E)) × Bool)) (e : (Fin 1 × (E × E)) × Bool)
    (x : E) (hx : Seen x0 h x ∨ x = e.1.2.1 ∨ x = e.1.2.2) : Seen x0 (h ++ [e]) x := by
  rcases hx with (hx | ⟨e', he', hx⟩) | hx
  · exact Or.inl hx
  · exact Or.inr ⟨e', List.mem_append_left _ he', hx⟩
  · exact Or.inr ⟨e, List.mem_append_right _ (List.mem_singleton_self _), hx⟩

lemma seen_mono (x0 : E) (h : List ((Fin 1 × (E × E)) × Bool)) (e : (Fin 1 × (E × E)) × Bool)
    (x : E) (hx : Seen x0 h x) : Seen x0 (h ++ [e]) x :=
  seen_append x0 h e x (Or.inl hx)

theorem trace_visits {S : Type} [MeasurableSpace S] (law : MeasureTheory.ProbabilityMeasure S)
    (x0 : E) (K : ℕ) (plan : S → QueryPlan (E × E) Bool (List E) K)
    (hplan : ∀ s, Cov (fun P l => ∀ y ∈ l, P y) (plan s) (fun y => y = x0))
    (O : Oracle (E × E) Bool) (budget : Fin 1 → ℕ) (seed : S) (oracleSeed : (k : ℕ) → O.Seed k) :
    ∀ x ∈ (executeWithTrace O (QueryPlan.algorithm law (x0, x0) [] K plan) budget seed
        oracleSeed).1,
      x = x0 ∨ ∃ e ∈ (executeWithTrace O (QueryPlan.algorithm law (x0, x0) [] K plan) budget seed
        oracleSeed).2, x = e.1.2.1 ∨ x = e.1.2.2 := by
  have hb : budget = fun _ => budget 0 := funext fun i => by rw [Subsingleton.elim i 0]
  rw [hb, executeWithTrace_indexed O (QueryPlan.algorithm law (x0, x0) [] K plan) (budget 0) seed
    oracleSeed]
  have hΦ : ∀ (P P' : E → Prop) (u : List E), (∀ x, P x → P' x) →
      (fun P l => ∀ y ∈ l, P y) P u → (fun P l => ∀ y ∈ l, P y) P' u :=
    fun P P' u hP hu y hy => hP y (hu y hy)
  let step := fun sc : (Σ k, QueryPlan (E × E) Bool (List E) k) ×
      List ((Fin 1 × (E × E)) × Bool) =>
    (QueryPlan.update sc.1
        (O.answer sc.2 (0, QueryPlan.query (x0, x0) sc.1) (oracleSeed sc.2.length)),
      sc.2 ++ [((0, QueryPlan.query (x0, x0) sc.1),
        O.answer sc.2 (0, QueryPlan.query (x0, x0) sc.1) (oracleSeed sc.2.length))])
  let Inv := fun sc : (Σ k, QueryPlan (E × E) Bool (List E) k) ×
      List ((Fin 1 × (E × E)) × Bool) =>
    Cov (fun P l => ∀ y ∈ l, P y) sc.1.2 (Seen x0 sc.2)
  have hstep : ∀ sc, Inv sc → Inv (step sc) := by
    rintro ⟨⟨k, pl⟩, hist⟩ hinv
    cases pl with
    | done v =>
        exact cov_mono (QueryPlan.done v) _ hΦ _ _ (seen_mono x0 hist _) hinv
    | ask q next =>
        exact cov_mono _ _ hΦ _ _ (fun x hx => seen_append x0 hist _ x hx) (hinv _)
  have hinit : Inv (⟨K, plan seed⟩, []) :=
    cov_mono (plan seed) _ hΦ _ _ (fun x hx => Or.inl hx) (hplan seed)
  have hiter : ∀ n sc, Inv sc → Inv (step^[n] sc) := by
    intro n
    induction n with
    | zero => intro sc h; exact h
    | succ n ih => intro sc h; rw [Function.iterate_succ_apply]; exact ih _ (hstep sc h)
  have hfin := hiter (budget 0) (⟨K, plan seed⟩, []) hinit
  change ∀ x ∈ QueryPlan.output [] (step^[budget 0] (⟨K, plan seed⟩, [])).1,
    Seen x0 (step^[budget 0] (⟨K, plan seed⟩, [])).2 x
  generalize step^[budget 0] (⟨K, plan seed⟩, []) = sc at hfin ⊢
  obtain ⟨⟨k, pl⟩, hist⟩ := sc
  cases pl with
  | done v => exact hfin
  | ask q next => intro x hx; simp [QueryPlan.output] at hx

end Trace

section Epoch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma length_cands (t : Tuning) (x y : E) (results : List (GuessResult E)) :
    ((y :: (results.map (guessCands t x)).flatten)).length = 4 * results.length + 1 := by
  induction results with
  | nil => rfl
  | cons a l ih =>
      simp only [List.length_cons, List.map_cons, List.flatten_cons, List.length_append] at ih ⊢
      simp only [guessCands, List.length_cons, List.length_nil]
      omega

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma select_cov (cands : List E) (j : ℕ) (best : E) (P : E → Prop)
    (h : P best ∧ ∀ i < j, ∀ y, cands[i]? = some y → P y) :
    Cov (fun P' b => P' b ∧ ∀ i < j + 1, ∀ y, cands[i]? = some y → P' y)
      (selectStep cands j best) P := by
  intro r
  show (fun x => P x ∨ x = cands.getD j best ∨ x = best)
      (if r then cands.getD j best else best) ∧
    ∀ i < j + 1, ∀ y, cands[i]? = some y → (fun x => P x ∨ x = cands.getD j best ∨ x = best) y
  refine ⟨?_, ?_⟩
  · cases r
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  · intro i hi y hy
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact Or.inl (h.2 i hi y hy)
    · subst hi
      refine Or.inr (Or.inl ?_)
      rw [List.getD_eq_getElem?_getD, hy, Option.getD_some]

lemma epoch_cov (t : Tuning) (x : E) (P : E → Prop) (hx : P x) :
    Cov (fun P' r => P' r.1 ∧ ∀ y ∈ r.2, P' y) (epochPlan t x) P := by
  unfold epochPlan
  refine cov_bind_any _ _ _ P ?_
  intro P1 h1 u
  refine cov_bind_any _ _ _ P1 ?_
  intro P2 h2 lh
  refine cov_bind_any _ _ _ P2 ?_
  intro P3 h3 du
  refine cov_bind _ _ (fun P' l => (∀ y, P3 y → P' y) ∧ l.length = t.J) _ P3
    (cov_sub _ _ P3 (cov_traverse _ _ _)) ?_
  intro P4 results ⟨h4, hlen⟩
  dsimp only
  set cands := (x - (t.r / 8) • u) :: (results.map (guessCands t x)).flatten with hcands
  have hl : cands.length = 4 * t.J + 1 := by rw [hcands, length_cands, hlen]
  refine cov_map _ _ (fun P' b => P' b ∧ ∀ i < 0 + (4 * t.J + 1), ∀ y, cands[i]? = some y → P' y)
    _ P4 ?_ ?_
  · refine cov_loop 1 (selectStep cands) (fun j P' b => P' b ∧ ∀ i < j, ∀ y, cands[i]? = some y → P' y)
      (fun j P' s hs => select_cov cands j s P' hs) (4 * t.J + 1) 0 x P4
      ⟨h4 x (h3 x (h2 x (h1 x hx))), fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  · intro P' b hb
    refine ⟨hb.1, fun y hy => ?_⟩
    have hy' : y ∈ cands := hy
    obtain ⟨i, hi, hiy⟩ := List.getElem_of_mem hy'
    exact hb.2 i (by omega) y (by rw [List.getElem?_eq_getElem hi, hiy])

lemma outer_cov (t : Tuning) (x0 : E) :
    Cov (fun P l => ∀ y ∈ l, P y) (QueryPlan.map Prod.snd (outerPlan t x0)) (fun y => y = x0) := by
  refine cov_map _ _ (fun P' st => P' st.1 ∧ ∀ y ∈ st.2, P' y) _ _ ?_ (fun _ _ h => h.2)
  have := cov_loop _ (outerStep t) (fun _ P' st => P' st.1 ∧ ∀ y ∈ st.2, P' y) ?_ t.T 0 (x0, [x0])
    (fun y => y = x0) ⟨rfl, fun y hy => List.mem_singleton.mp hy⟩
  · exact this
  · intro j P st hst
    refine cov_map _ _ _ _ P (cov_sub _ _ P (epoch_cov t st.1 P hst.1)) ?_
    intro P' r ⟨hsub, hr1, hr2⟩
    refine ⟨hr1, fun y hy => ?_⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact hsub y (hst.2 y hy)
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hr1
      · exact hr2 y hy

end Epoch

end

end LongTails.Proofs.ComparisonTrustVisits
