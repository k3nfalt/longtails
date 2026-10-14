import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.CohypomonotoneInclusion

structure MultiStepState (E : Type u) where
  k : ℕ
  j : ℕ
  back : Bool
  a : E
  t : E
  c : E
  v : E

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def target (s : ℝ) (k : ℕ) (a y g : E) : E :=
  (1 / ((k : ℝ) + 2)) • a + (1 - 1 / ((k : ℝ) + 2)) • (y - s • g)

noncomputable def predictor (η s : ℝ) (k : ℕ) (a y g : E) : E :=
  target s k a y g - (η * (1 - 1 / ((k : ℝ) + 2))) • g

noncomputable def multiStepAnchored (η s : ℝ) (m : ℕ) (x0 : E) :
    Algorithm (E ⊕ (ℝ × E)) E E where
  State := MultiStepState E
  initial := fun _ => ⟨0, 1, false, 0, x0, 0, x0⟩
  query :=  fun st => (0, if st.back then Sum.inr (η, st.c) else Sum.inl st.v)
  update := fun st r =>
    if st.back then ⟨st.k, st.j - 1, false, st.a, st.t, st.c, r⟩
    else if st.j = 0 then
      ⟨st.k + 1, m + 1, false, if st.k = 0 then st.c + η • r else st.a,
        target s st.k (if st.k = 0 then st.c + η • r else st.a) (st.c + η • r)
          (r + η⁻¹ • (st.c - st.v)),
        st.c,
        predictor η s st.k (if st.k = 0 then st.c + η • r else st.a) (st.c + η • r)
          (r + η⁻¹ • (st.c - st.v))⟩
    else ⟨st.k, st.j, true, st.a, st.t, st.t - η • r, st.v⟩
  output := fun st => st.v

end OracleTemplate.CohypomonotoneInclusion
