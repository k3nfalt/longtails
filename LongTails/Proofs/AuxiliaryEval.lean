import LongTails.Algorithms.AuxiliarySimilarity
import LongTails.Proofs.AuxiliaryPlan

namespace LongTails.Proofs.AuxiliaryEval

open scoped RealInnerProductSpace
open LongTails.Algorithms.AuxiliaryPlan LongTails.Algorithms.AuxiliarySimilarity
open LongTails.Algorithms.AuxiliaryPlan.TwoPlan LongTails.Proofs.AuxiliaryPlan.TwoPlan
open LongTails.Algorithms.GuardedMetricAcceleration

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def orc (F H : E → ℝ × E) : Fin 2 → E → ℝ × E := fun i x => if i = 0 then F x else H x

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] lemma orc_zero (F H : E → ℝ × E) (x : E) : orc F H 0 x = F x := by simp [orc]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] lemma orc_one (F H : E → ℝ × E) (x : E) : orc F H 1 x = H x := by simp [orc]

lemma firstBad_congr {n : ℕ} {b b' : ℕ → Prop} (h : ∀ i < n, (b i ↔ b' i)) :
    firstBad n b = firstBad n b' := by
  classical
  have hex : (∃ i, i < n ∧ b i) ↔ (∃ i, i < n ∧ b' i) :=
    ⟨fun ⟨i, hi, hb⟩ => ⟨i, hi, (h i hi).1 hb⟩, fun ⟨i, hi, hb⟩ => ⟨i, hi, (h i hi).2 hb⟩⟩
  unfold firstBad
  split_ifs with h1 h2 h2
  · congr 1
    exact Nat.find_congr' (fun {i} => ⟨fun ⟨hi, hbi⟩ => ⟨hi, (h i hi).1 hbi⟩,
      fun ⟨hi, hbi⟩ => ⟨hi, (h i hi).2 hbi⟩⟩)
  · exact absurd (hex.1 h1) h2
  · exact absurd (hex.2 h2) h1
  · rfl

lemma firstBad_none {n : ℕ} {b : ℕ → Prop} (h : firstBad n b = none) : ∀ i < n, ¬ b i := by
  intro i hi hbi
  unfold firstBad at h
  split_ifs at h with h1
  exact h1 ⟨i, hi, hbi⟩

lemma firstBad_some {n i : ℕ} {b : ℕ → Prop} (h : firstBad n b = some i) : i < n ∧ b i := by
  classical
  unfold firstBad at h
  split_ifs at h with h1
  cases h
  convert Nat.find_spec h1

section Cheap

variable (t : Tuning) (y v : E) (F H : E → ℝ × E)

noncomputable def cheapZ (xbar b : E) : ℕ → E
  | 0 => xbar
  | i + 1 => cheapZ xbar b i - (1 / t.M) • (b + (psiRec t y v (cheapZ xbar b i)
      (H (cheapZ xbar b i))).2.2 - (psiRec t y v xbar (H xbar)).2.2)

noncomputable def cheapRun (xbar b : E) (k : ℕ) : CheapState E :=
  (fun s => eval (orc F H) (cheapStep t y v b (psiRec t y v xbar (H xbar)) s))^[k]
    ⟨0, fun _ => psiRec t y v xbar (H xbar)⟩

lemma cheapRun_spec (xbar b : E) (k : ℕ) :
    (cheapRun t y v F H xbar b k).k = k ∧ ∀ i ≤ k, (cheapRun t y v F H xbar b k).recs i =
      psiRec t y v (cheapZ t y v H xbar b i) (H (cheapZ t y v H xbar b i)) := by
  induction k with
  | zero =>
      refine ⟨rfl, fun i hi => ?_⟩
      obtain rfl : i = 0 := by omega
      rfl
  | succ k ih =>
      obtain ⟨hk, hr⟩ := ih
      have hs : cheapRun t y v F H xbar b (k + 1) =
          eval (orc F H) (cheapStep t y v b (psiRec t y v xbar (H xbar))
            (cheapRun t y v F H xbar b k)) :=
        Function.iterate_succ_apply' _ _ _
      rw [hs]
      simp only [cheapStep, eval_bind', eval_call, eval_pure, orc_one]
      refine ⟨by rw [hk], fun i hi => ?_⟩
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · rw [Function.update_of_ne (by omega)]
        exact hr i (by omega)
      · obtain rfl : i = k + 1 := by omega
        rw [hk, Function.update_self, hr k le_rfl]
        rfl

lemma firstBad_map_congr {α : Type*} {n : ℕ} {b b' : ℕ → Prop} {f f' : ℕ → α}
    (hb : ∀ i < n, (b i ↔ b' i)) (hf : ∀ i < n, f i = f' i) :
    (firstBad n b).map f = (firstBad n b').map f' := by
  rw [firstBad_congr hb]
  cases h : firstBad n b' with
  | none => rfl
  | some i => simp [hf i (firstBad_some h).1]

lemma eval_cheapGD (xbar b : E) :
    eval (orc F H) (cheapGD t y v xbar b) =
      (cheapZ t y v H xbar b (t.N - 1),
        (firstBad t.N (fun i => recBreg
            (psiRec t y v (cheapZ t y v H xbar b t.N) (H (cheapZ t y v H xbar b t.N)))
            (psiRec t y v (cheapZ t y v H xbar b i) (H (cheapZ t y v H xbar b i))) <
          3 * t.db / 2 * ‖cheapZ t y v H xbar b t.N - cheapZ t y v H xbar b i‖ ^ 2)).map
          (fun i => (cheapZ t y v H xbar b t.N, cheapZ t y v H xbar b i)),
        psiRec t y v xbar (H xbar)) := by
  obtain ⟨_, hr⟩ := cheapRun_spec t y v F H xbar b t.N
  have he : eval (orc F H) (cheapGD t y v xbar b) =
      (((cheapRun t y v F H xbar b t.N).recs (t.N - 1)).1,
        (firstBad t.N (fun i => recBreg ((cheapRun t y v F H xbar b t.N).recs t.N)
            ((cheapRun t y v F H xbar b t.N).recs i) <
          3 * t.db / 2 * ‖((cheapRun t y v F H xbar b t.N).recs t.N).1 -
            ((cheapRun t y v F H xbar b t.N).recs i).1‖ ^ 2)).map
          (fun i => (((cheapRun t y v F H xbar b t.N).recs t.N).1,
            ((cheapRun t y v F H xbar b t.N).recs i).1)),
        psiRec t y v xbar (H xbar)) := by
    simp only [cheapGD, eval_bind', eval_call, eval_pure, orc_one, eval_loop]
    rfl
  rw [he, hr (t.N - 1) (Nat.sub_le _ _), hr t.N le_rfl]
  congr 2
  exact firstBad_map_congr (fun i hi => by rw [hr i hi.le]; try rfl)
    (fun i hi => by rw [hr i hi.le]; try rfl)

end Cheap


section Dane

variable (t : Tuning) (y v : E) (F H : E → ℝ × E)

noncomputable def cheapOut (x : E) : E × Option (E × E) × Rec E :=
  eval (orc F H) (cheapGD t y v x (tRec t y v x (F x)).2.2)

noncomputable def daneX (s : E) : ℕ → E
  | 0 => s
  | j + 1 => (cheapOut t y v F H (daneX s j)).1

noncomputable def daneBook (s : E) (bk : Book E) : ℕ → Book E
  | 0 => bk.note s (F s).1
  | j + 1 => ((daneBook s bk j).flag (cheapOut t y v F H (daneX t y v F H s j)).2.1).note
      (daneX t y v F H s (j + 1)) (F (daneX t y v F H s (j + 1))).1

noncomputable def daneRun (s : E) (bk : Book E) (k : ℕ) : DaneState E :=
  (fun st => eval (orc F H) (daneStep t y v st))^[k]
    ⟨0, fun _ => tRec t y v s (F s), fun _ => tRec t y v s (F s), bk.note s (F s).1⟩

lemma daneRun_spec (s : E) (bk : Book E) (k : ℕ) :
    (daneRun t y v F H s bk k).k = k ∧
      (∀ i ≤ k, (daneRun t y v F H s bk k).recs i =
        tRec t y v (daneX t y v F H s i) (F (daneX t y v F H s i))) ∧
      (∀ i < k, (daneRun t y v F H s bk k).prec i = (cheapOut t y v F H (daneX t y v F H s i)).2.2) ∧
      (daneRun t y v F H s bk k).book = daneBook t y v F H s bk k := by
  induction k with
  | zero =>
      refine ⟨rfl, fun i hi => ?_, fun i hi => absurd hi (Nat.not_lt_zero _), rfl⟩
      obtain rfl : i = 0 := by omega
      rfl
  | succ k ih =>
      obtain ⟨hk, hr, hp, hb⟩ := ih
      have hs : daneRun t y v F H s bk (k + 1) =
          eval (orc F H) (daneStep t y v (daneRun t y v F H s bk k)) :=
        Function.iterate_succ_apply' _ _ _
      have hcur : (daneRun t y v F H s bk k).recs (daneRun t y v F H s bk k).k =
          tRec t y v (daneX t y v F H s k) (F (daneX t y v F H s k)) := by rw [hk, hr k le_rfl]
      rw [hs]
      simp only [daneStep, eval_bind', eval_call, eval_pure, orc_zero, hcur]
      refine ⟨by rw [hk], fun i hi => ?_, fun i hi => ?_, ?_⟩
      · rcases Nat.lt_or_ge i (k + 1) with h | h
        · rw [Function.update_of_ne (by omega)]
          exact hr i (by omega)
        · obtain rfl : i = k + 1 := by omega
          rw [hk, Function.update_self]
          rfl
      · rcases Nat.lt_or_ge i k with h | h
        · rw [Function.update_of_ne (by omega)]
          exact hp i h
        · obtain rfl : i = k := by omega
          rw [hk, Function.update_self]
          rfl
      · rw [hb]
        rfl

noncomputable def daneCert (s : E) : Option (E × E) :=
  (firstBad (t.J + 1) (fun j => recBreg
      (tRec t y v (daneX t y v F H s (t.J + 1)) (F (daneX t y v F H s (t.J + 1))))
      (tRec t y v (daneX t y v F H s j) (F (daneX t y v F H s j))) <
    2 / 5 * recBreg (psiRec t y v (daneX t y v F H s (t.J + 1)) (H (daneX t y v F H s (t.J + 1))))
      (cheapOut t y v F H (daneX t y v F H s j)).2.2)).map
    (fun j => (daneX t y v F H s (t.J + 1), daneX t y v F H s j))

lemma eval_dane (s : E) (bk : Book E) :
    eval (orc F H) (dane t y v s bk) =
      (tRec t y v (daneX t y v F H s t.J) (F (daneX t y v F H s t.J)),
        (daneBook t y v F H s bk (t.J + 1)).flag (daneCert t y v F H s)) := by
  obtain ⟨_, hr, hp, hb⟩ := daneRun_spec t y v F H s bk (t.J + 1)
  have he : eval (orc F H) (dane t y v s bk) =
      ((daneRun t y v F H s bk (t.J + 1)).recs t.J,
        (daneRun t y v F H s bk (t.J + 1)).book.flag
          ((firstBad (t.J + 1) (fun j => recBreg ((daneRun t y v F H s bk (t.J + 1)).recs (t.J + 1))
              ((daneRun t y v F H s bk (t.J + 1)).recs j) <
            2 / 5 * recBreg (psiRec t y v ((daneRun t y v F H s bk (t.J + 1)).recs (t.J + 1)).1
                (H ((daneRun t y v F H s bk (t.J + 1)).recs (t.J + 1)).1))
              ((daneRun t y v F H s bk (t.J + 1)).prec j))).map
            (fun j => (((daneRun t y v F H s bk (t.J + 1)).recs (t.J + 1)).1,
              ((daneRun t y v F H s bk (t.J + 1)).recs j).1)))) := by
    simp only [dane, eval_bind', eval_call, eval_pure, orc_zero, orc_one, eval_loop]
    rfl
  rw [he, hr t.J (Nat.le_succ _), hb]
  congr 2
  unfold daneCert
  apply firstBad_map_congr
  · intro i hi
    rw [hr i hi.le, hr (t.J + 1) le_rfl, hp i hi]
    try rfl
  · intro i hi
    rw [hr i hi.le, hr (t.J + 1) le_rfl]
    try rfl

end Dane

section Appa

variable (t : Tuning) (y : E) (F H : E → ℝ × E)

noncomputable def gRecY (x : E) : Rec E :=
  (x, (F x).1 + t.α * ‖x - y‖ ^ 2, (F x).2 + (2 * t.α) • (x - y))

lemma gRec_tRec (v x : E) : gRec t v (tRec t y v x (F x)) = gRecY t y F x := by
  simp only [gRec, tRec, gRecY, Prod.mk.injEq, true_and]
  constructor
  · ring
  · abel

noncomputable def appaNext (p : E × E × Book E) : E × E × Book E :=
  let v := extrapolate t.a p.1 p.2.1
  let x' := daneX t y v F H p.1 t.J
  ( x', centerStep t.a (t.α / 2) v p.2.1 ((2 * t.db) • (v - x')),
    ((((daneBook t y v F H p.1 p.2.2 (t.J + 1)).flag (daneCert t y v F H p.1)).flag
      (guardPair t (gRecY t y F p.1) (gRecY t y F x'))).flag
      (guardPair t (gRecY t y F y) (gRecY t y F x'))))

noncomputable def appaP (bk0 : Book E) (k : ℕ) : E × E × Book E :=
  (appaNext t y F H)^[k] (y, y, bk0)

noncomputable def appaRun (bk0 : Book E) (k : ℕ) : EpochState E :=
  (fun st => eval (orc F H) (appaStep t y (y, (F y).1, (F y).2) st))^[k]
    ⟨0, y, y, fun _ => (y, (F y).1, (F y).2), bk0⟩

lemma gRecY_self : gRecY t y F y = (y, (F y).1, (F y).2) := by
  simp [gRecY]

lemma appaRun_spec (bk0 : Book E) (k : ℕ) :
    (appaRun t y F H bk0 k).k = k ∧ (appaRun t y F H bk0 k).x = (appaP t y F H bk0 k).1 ∧
      (appaRun t y F H bk0 k).z = (appaP t y F H bk0 k).2.1 ∧
      (appaRun t y F H bk0 k).book = (appaP t y F H bk0 k).2.2 ∧
      ∀ i ≤ k, (appaRun t y F H bk0 k).recs i = gRecY t y F (appaP t y F H bk0 i).1 := by
  induction k with
  | zero =>
      refine ⟨rfl, rfl, rfl, rfl, fun i hi => ?_⟩
      obtain rfl : i = 0 := by omega
      exact (gRecY_self t y F).symm
  | succ k ih =>
      obtain ⟨hk, hx, hz, hb, hr⟩ := ih
      have hs : appaRun t y F H bk0 (k + 1) =
          eval (orc F H) (appaStep t y (y, (F y).1, (F y).2) (appaRun t y F H bk0 k)) :=
        Function.iterate_succ_apply' _ _ _
      have hp : appaP t y F H bk0 (k + 1) = appaNext t y F H (appaP t y F H bk0 k) :=
        Function.iterate_succ_apply' _ _ _
      have hcur : (appaRun t y F H bk0 k).recs (appaRun t y F H bk0 k).k =
          gRecY t y F (appaP t y F H bk0 k).1 := by rw [hk, hr k le_rfl]
      rw [hs, hp]
      simp only [appaStep, eval_bind', eval_dane, eval_pure, hcur, hx, hz, hb, gRec_tRec,
        ← gRecY_self t y F]
      refine ⟨by rw [hk], rfl, rfl, rfl, fun i hi => ?_⟩
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · rw [Function.update_of_ne (by omega)]
        exact hr i (by omega)
      · obtain rfl : i = k + 1 := by omega
        rw [hk, Function.update_self, hp]
        rfl

end Appa

end LongTails.Proofs.AuxiliaryEval
