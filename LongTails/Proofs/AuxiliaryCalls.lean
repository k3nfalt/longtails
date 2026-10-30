import LongTails.Algorithms.AuxiliarySimilarity
import LongTails.Proofs.AuxiliaryPlan

namespace LongTails.Proofs.AuxiliaryCalls

open LongTails.Algorithms.AuxiliaryPlan LongTails.Algorithms.AuxiliarySimilarity
open LongTails.Algorithms.AuxiliaryPlan.TwoPlan LongTails.Proofs.AuxiliaryPlan.TwoPlan

section General

variable {Q R α β : Type} (g : Fin 2 → Q → R) (j : Fin 2)

lemma calls_bind_le {p : TwoPlan Q R α} {k : α → TwoPlan Q R β} {B1 B2 : ℕ}
    (h1 : calls g j p ≤ B1) (h2 : ∀ a, calls g j (k a) ≤ B2) : calls g j (p >>= k) ≤ B1 + B2 := by
  rw [calls_bind']
  exact Nat.add_le_add h1 (h2 _)

lemma calls_ite_le {c : Prop} [Decidable c] {p q : TwoPlan Q R α} {B : ℕ}
    (hp : calls g j p ≤ B) (hq : calls g j q ≤ B) : calls g j (if c then p else q) ≤ B := by
  split_ifs
  · exact hp
  · exact hq

lemma calls_call_le (i : Fin 2) (q : Q) : calls g j (call i q : TwoPlan Q R R) ≤ if i = j then 1 else 0 :=
  (calls_call g i j q).le

lemma calls_pure_le (a : α) (B : ℕ) : calls g j (pure a : TwoPlan Q R α) ≤ B := by
  rw [calls_pure]; exact Nat.zero_le _

end General

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (g : Fin 2 → E → ℝ × E) (t : Tuning)

def cost (j : Fin 2) (a0 a1 : ℕ) : ℕ := if j = 1 then a1 else a0

lemma calls_cheapStep (j : Fin 2) (y v b : E) (r0 : Rec E) (st : CheapState E) :
    calls g j (cheapStep t y v b r0 st) ≤ cost j 0 1 := by
  unfold cheapStep cost
  dsimp only
  refine (calls_bind_le g j (calls_call_le g j 1 _) (fun _ => calls_pure_le g j _ 0)).trans ?_
  fin_cases j <;> simp

lemma calls_cheapGD (j : Fin 2) (y v xb b : E) :
    calls g j (cheapGD t y v xb b) ≤ cost j 0 (t.N + 1) := by
  unfold cheapGD cost
  dsimp only
  refine (calls_bind_le g j (calls_call_le g j 1 _) (fun _ => calls_bind_le g j
    (calls_loop_le g j _ _ (calls_cheapStep g t j y v b _) t.N _)
    (fun _ => calls_pure_le g j _ 0))).trans ?_
  fin_cases j <;> first | (simp [cost]; done) | (simp [cost]; omega)

lemma calls_daneStep (j : Fin 2) (y v : E) (st : DaneState E) :
    calls g j (daneStep t y v st) ≤ cost j 1 (t.N + 1) := by
  unfold daneStep cost
  dsimp only
  refine (calls_bind_le g j (calls_cheapGD g t j y v _ _) (fun _ => calls_bind_le g j
    (calls_call_le g j 0 _) (fun _ => calls_pure_le g j _ 0))).trans ?_
  fin_cases j <;> simp [cost]

lemma calls_dane (j : Fin 2) (y v s : E) (bk : Book E) :
    calls g j (dane t y v s bk) ≤ cost j (t.J + 2) ((t.J + 1) * (t.N + 1) + 1) := by
  unfold dane cost
  dsimp only
  refine (calls_bind_le g j (calls_call_le g j 0 _) (fun _ => calls_bind_le g j
    (calls_loop_le g j _ _ (calls_daneStep g t j y v) (t.J + 1) _)
    (fun _ => calls_bind_le g j (calls_call_le g j 1 _) (fun _ => calls_pure_le g j _ 0)))).trans ?_
  fin_cases j <;> first | (simp [cost]; done) | (simp [cost]; omega)

lemma calls_appaStep (j : Fin 2) (y : E) (gy : Rec E) (st : EpochState E) :
    calls g j (appaStep t y gy st) ≤ cost j (t.J + 2) ((t.J + 1) * (t.N + 1) + 1) := by
  unfold appaStep
  dsimp only
  exact (calls_bind_le g j (calls_dane g t j y _ _ _) (fun _ => calls_pure_le g j _ 0)).trans
    (by rw [add_zero])

lemma calls_exploit (j : Fin 2) (y : E) (bk : Book E) :
    calls g j (exploit t y bk) ≤ cost j 4 0 := by
  unfold exploit
  cases bk.cert with
  | none => exact calls_pure_le g j _ _
  | some p =>
      obtain ⟨u, w⟩ := p
      dsimp only
      refine (calls_bind_le g j (calls_call_le g j 0 _) (fun _ => calls_bind_le g j
        (calls_call_le g j 0 _) (fun _ => calls_bind_le g j (calls_call_le g j 0 _)
        (fun _ => calls_bind_le g j (calls_call_le g j 0 _) (fun _ => calls_pure_le g j _ 0))))).trans ?_
      fin_cases j <;> simp [cost]

lemma calls_epoch (j : Fin 2) (y : E) :
    calls g j (epoch t y) ≤
      cost j ((t.T + 1) * (t.J + 2) + 6) ((t.T + 1) * ((t.J + 1) * (t.N + 1) + 1)) := by
  unfold epoch
  dsimp only
  refine (calls_bind_le g j (calls_call_le g j 0 _) (fun _ => calls_ite_le g j
    (calls_pure_le g j _ (cost j (t.T * (t.J + 2) + (t.J + 2) + 1 + 4)
      (t.T * ((t.J + 1) * (t.N + 1) + 1) + ((t.J + 1) * (t.N + 1) + 1))))
    (calls_bind_le g j (calls_loop_le g j _ _ (calls_appaStep g t j y _) t.T _)
      (fun _ => calls_bind_le g j (calls_dane g t j y _ _ _)
        (fun _ => calls_bind_le g j (calls_call_le g j 0 _)
          (fun _ => calls_ite_le g j (calls_pure_le g j _ (cost j 4 0))
            (calls_bind_le g j (calls_exploit g t j y _) (fun _ => calls_pure_le g j _ 0)))))
      |>.trans ?_))).trans ?_
  · fin_cases j <;> first | (simp [cost]; done) | (simp [cost]; omega)
  · fin_cases j <;> first | (simp [cost]; done) | (simp [cost]; omega) | (simp [cost]; ring_nf; omega)

lemma calls_method (j : Fin 2) (x0 : E) :
    calls g j (method t x0) ≤
      t.K * cost j ((t.T + 1) * (t.J + 2) + 6) ((t.T + 1) * ((t.J + 1) * (t.N + 1) + 1)) :=
  calls_loop_le g j _ _ (calls_epoch g t j) t.K x0

end LongTails.Proofs.AuxiliaryCalls
