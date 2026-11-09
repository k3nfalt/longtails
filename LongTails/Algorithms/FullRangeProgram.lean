import LongTails.Algorithms.FullRangeMlmc
import LongTails.Template
import LongTails.Algorithms.SafeguardedSimilarTriangles

namespace LongTails.Algorithms.FullRangeProgram

open LongTails.Algorithms.FullRangeMlmc
open OracleTemplate.LocalHiddenConvex (ballProj)

inductive Prog (Q R O : Type) where
  | done (o : O) : Prog Q R O
  | ask (q : Q) (k : R → Prog Q R O) : Prog Q R O

namespace Prog

variable {Q R O O' : Type}

def bind : Prog Q R O → (O → Prog Q R O') → Prog Q R O'
  | done o, f => f o
  | ask q k, f => ask q fun r => bind (k r) f

def eval (resp : ℕ → Q → R) : Prog Q R O → ℕ → O × ℕ
  | done o, c => (o, c)
  | ask q k, c => eval resp (k (resp c q)) (c + 1)

end Prog

variable {E S : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Q (E : Type) := E ⊕ (ℝ × E)

structure Cfg (E S : Type) where
  η : ℝ
  γ0 : ℝ
  a : ℝ
  r : ℝ
  n0 : ℕ
  top : ℕ
  B : ℕ
  limit : ℕ
  x0 : E
  init : S
  point : S → E
  update : S → E → S

noncomputable def stepProg (η γ : ℝ) (x z : E) : Prog (Q E) E E :=
  .ask (.inl z) fun r => .ask (.inr (γ * η, z - γ • (z - x + η • r))) .done

noncomputable def pathProg (η γ0 : ℝ) (n0 : ℕ) (x : E) : ℕ → Prog (Q E) E (ℕ → E)
  | 0 => .done fun _ => x
  | k + 1 => (pathProg η γ0 n0 x k).bind fun h =>
      (stepProg η (stepAt γ0 n0 k) x (h k)).bind fun z => .done (Function.update h (k + 1) z)

noncomputable def histEstimate (n0 top l : ℕ) (h : ℕ → E) : E :=
  if l = 0 then h n0
  else h n0 + (levelWeight top l)⁻¹ • (h (levelTime n0 l) - h (levelTime n0 (l - 1)))

noncomputable def callProg (c : Cfg E S) (x : E) (l : ℕ) : Prog (Q E) E E :=
  let y := ballProj c.x0 c.r x
  (pathProg c.η c.γ0 c.n0 y (levelTime c.n0 l)).bind fun h =>
    .done ((1 - c.a) • y + c.a • histEstimate c.n0 c.top l h)

noncomputable def loopProg (c : Cfg E S) : List ℕ → S → Prog (Q E) E S
  | [], s => .done s
  | l :: t, s => (callProg c (c.point s) l).bind fun r => loopProg c t (c.update s r)

noncomputable def batchProg (z : E) : ℕ → E → Prog (Q E) E E
  | 0, acc => .done acc
  | m + 1, acc => .ask (.inl z) fun r => .ask (.inr (1, z)) fun _ => batchProg z m (acc + r)

noncomputable def certProg (c : Cfg E S) (y : E) : Prog (Q E) E (E × E) :=
  (pathProg c.η c.γ0 c.n0 y (levelTime c.n0 c.top)).bind fun h =>
    (batchProg (h (levelTime c.n0 c.top)) c.B 0).bind fun acc =>
      let p := y - c.η • ((c.B : ℝ)⁻¹ • acc)
      .ask (.inr (c.η, p)) fun xb => .done (xb, c.η⁻¹ • (p - xb))

noncomputable def levelCost (n0 : ℕ) (l : ℕ) : ℕ := 2 * levelTime n0 l

noncomputable def seedCost {K top : ℕ} (n0 : ℕ) (ℓ : Fin K → Fin (top + 1)) : ℕ :=
  ∑ i, levelCost n0 (ℓ i)

noncomputable def fullProg (c : Cfg E S) {K : ℕ} (ℓ : Fin K → Fin (c.top + 1)) :
    Prog (Q E) E (E × E) :=
  if seedCost c.n0 ℓ ≤ c.limit then
    (loopProg c (List.ofFn fun i => ((ℓ i : ℕ))) c.init).bind fun s =>
      certProg c (ballProj c.x0 c.r (c.point s))
  else certProg c c.x0

noncomputable def stateQuery (x0 : E) : Prog (Q E) E (E × E) → Fin 1 × Q E
  | .done _ => (0, .inl x0)
  | .ask q _ => (0, q)

noncomputable def stateUpdate : Prog (Q E) E (E × E) → E → Prog (Q E) E (E × E)
  | .done o, _ => .done o
  | .ask _ k, r => k r

noncomputable def stateOutput (x0 : E) : Prog (Q E) E (E × E) → E × E
  | .done o => o
  | .ask _ _ => (x0, 0)

end LongTails.Algorithms.FullRangeProgram
