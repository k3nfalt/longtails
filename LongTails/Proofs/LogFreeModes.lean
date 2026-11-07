import LongTails.Algorithms.LogFreeProxNewton

namespace LongTails.Proofs.LogFreeModes

open LongTails.Setups.ThirdDerivativeSmoothNonconvex LongTails.Algorithms.LogFreeProxNewton
open scoped RealInnerProductSpace

variable (p : Params) (st : State p.E) (H : p.E →L[ℝ] p.E)

lemma mode_idle (h : st.done = true) : mode p st H = .idle := by
  unfold mode; simp [h]

lemma mode_stop (h0 : st.done = false) (h : ‖st.cur.grad‖ ≤ p.ε) : mode p st H = .stop := by
  unfold mode; simp [h0, h]

lemma mode_advance (h0 : st.done = false) (h : p.ε < ‖st.cur.grad‖) (ht : st.tail = true)
    (hs : stable (weight p) (tolerance st.level) st.cur H) : mode p st H = .advance := by
  unfold mode; simp [h0, not_le.mpr h, ht, hs]

lemma mode_magnify (h0 : st.done = false) (h : p.ε < ‖st.cur.grad‖) (ht : st.tail = true)
    (hs : ¬ stable (weight p) (tolerance st.level) st.cur H) : mode p st H = .magnify := by
  unfold mode; simp [h0, not_le.mpr h, ht, hs]

lemma mode_success (h0 : st.done = false) (h : p.ε < ‖st.cur.grad‖) (ht : st.tail = false)
    (hs : st.cur.value ≤ st.centerValue - threshold p) : mode p st H = .success := by
  unfold mode; simp [h0, not_le.mpr h, ht, hs]

lemma mode_escape (h0 : st.done = false) (h : p.ε < ‖st.cur.grad‖) (ht : st.tail = false)
    (hs : ¬ st.cur.value ≤ st.centerValue - threshold p)
    (hc : (curvature (weight p) st.cur).isSome = true) : mode p st H = .escape := by
  unfold mode; simp [h0, not_le.mpr h, ht, hs, hc]

lemma mode_enter (h0 : st.done = false) (h : p.ε < ‖st.cur.grad‖) (ht : st.tail = false)
    (hs : ¬ st.cur.value ≤ st.centerValue - threshold p)
    (hc : (curvature (weight p) st.cur).isSome = false)
    (hd : decrement (weight p) st.center st.cur ≤ tailLevel p) : mode p st H = .enter := by
  unfold mode; simp [h0, not_le.mpr h, ht, hs, hc, hd]

lemma mode_newton (h0 : st.done = false) (h : p.ε < ‖st.cur.grad‖) (ht : st.tail = false)
    (hs : ¬ st.cur.value ≤ st.centerValue - threshold p)
    (hc : (curvature (weight p) st.cur).isSome = false)
    (hd : ¬ decrement (weight p) st.center st.cur ≤ tailLevel p) : mode p st H = .newton := by
  unfold mode; simp [h0, not_le.mpr h, ht, hs, hc, hd]

end LongTails.Proofs.LogFreeModes
