import LongTails.Setups.DiagonalSmoothStronglyConvexBlackBox
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open scoped BigOperators

namespace OracleTemplate.BlackBoxDiagonal

open LongTails.Setups.DiagonalSmoothStronglyConvexBlackBox

abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

noncomputable def dot (g v : Vec d) : ℝ := ∑ i, g i * v i

structure Cut (d : ℕ) where
  a : Fin d → ℝ
  b : Fin d → ℝ
  c : ℝ

noncomputable def Cut.val (C : Cut d) (θ : Fin d → ℝ) : ℝ :=
  ∑ k, C.a k * Real.exp (-θ k) + ∑ k, C.b k * Real.exp (θ k) - C.c

noncomputable def Cut.grad (C : Cut d) (θ : Fin d → ℝ) (k : Fin d) : ℝ :=
  -(C.a k * Real.exp (-θ k)) + C.b k * Real.exp (θ k)

noncomputable def sqn (v : Fin d → ℝ) : ℝ := ∑ k, v k ^ 2

noncomputable def clampBox (lo hi θ : Fin d → ℝ) : Fin d → ℝ :=
  fun k => max (lo k) (min (hi k) (θ k))

noncomputable def cutStep (lo hi : Fin d → ℝ) (r : ℝ) (C : Cut d) (θ : Fin d → ℝ) :
    Fin d → ℝ :=
  clampBox lo hi (fun k => θ k - r * C.grad θ k / Real.sqrt (sqn (C.grad θ)))

noncomputable def cutCoco (fy fx : ℝ) (y x gy gx : Vec d) : Cut d :=
  ⟨fun i => (gx i - gy i) ^ 2 / 2, fun _ => 0, fy - fx - dot gx (y - x)⟩

noncomputable def cutSc (μ fy fx : ℝ) (y x gx : Vec d) : Cut d :=
  ⟨fun _ => 0, fun i => μ / 2 * (y i - x i) ^ 2, fy - fx - dot gx (y - x)⟩

noncomputable def cutMono (μ : ℝ) (x y gx gy : Vec d) : Cut d :=
  ⟨fun _ => 0, fun i => μ * (x i - y i) ^ 2, dot (gx - gy) (x - y)⟩

noncomputable def cutCocoMono (x y gx gy : Vec d) : Cut d :=
  ⟨fun i => (gx i - gy i) ^ 2, fun _ => 0, dot (gx - gy) (x - y)⟩

noncomputable def muh (j : ℕ) : ℝ := 1 / (4 * 2 ^ j)

noncomputable def alph (j : ℕ) : ℝ := 1 / (2 * Real.sqrt (2 ^ j))

noncomputable def len (j : ℕ) : ℕ := ⌈2 * Real.sqrt (2 ^ j) * Real.log (512 * (2 ^ j) ^ 3)⌉₊

def cap (d j : ℕ) : ℕ := d * j ^ 2 / 4 + 1

noncomputable def lo (J : Fin d → ℝ) : Fin d → ℝ := fun k => Real.log (J k)

noncomputable def hi (J : Fin d → ℝ) (j : ℕ) : Fin d → ℝ :=
  fun k => Real.log (J k) + Real.log 4 + j * Real.log 2

noncomputable def th0 (J : Fin d → ℝ) (j : ℕ) : Fin d → ℝ :=
  fun k => Real.log (J k) + Real.log 2 + j * Real.log 2 / 2

noncomputable def metric (θ : Fin d → ℝ) : Fin d → ℝ := fun k => Real.exp (θ k)

noncomputable def ystep (α : ℝ) (x v : Vec d) : Vec d :=
  WithLp.toLp 2 (fun i => (α * v i + x i) / (1 + α))

noncomputable def xstep (m : Fin d → ℝ) (y g : Vec d) : Vec d :=
  WithLp.toLp 2 (fun i => y i - g i / m i)

noncomputable def vstep (m : Fin d → ℝ) (α μ : ℝ) (v y g : Vec d) : Vec d :=
  WithLp.toLp 2 (fun i => (1 - α) * v i + α * y i - α / μ * (g i / m i))

noncomputable def xv (m : Fin d → ℝ) (α μ : ℝ) (base : Vec d) (H : ℕ → ℝ × Vec d) :
    ℕ → Vec d × Vec d
  | 0 => (base, base)
  | k + 1 =>
      let p := xv m α μ base H k
      let y := ystep α p.1 p.2
      (xstep m y (H (2 * k)).2, vstep m α μ p.2 y (H (2 * k)).2)

noncomputable def yAt (m : Fin d → ℝ) (α μ : ℝ) (base : Vec d) (H : ℕ → ℝ × Vec d)
    (k : ℕ) : Vec d :=
  ystep α (xv m α μ base H k).1 (xv m α μ base H k).2

noncomputable def zAt (m : Fin d → ℝ) (α μ : ℝ) (base : Vec d) (H : ℕ → ℝ × Vec d)
    (N : ℕ) : Vec d :=
  xstep m (xv m α μ base H N).1 (H (2 * N - 1)).2

noncomputable def phaseQuery (m : Fin d → ℝ) (α μ : ℝ) (N : ℕ) (base : Vec d)
    (H : ℕ → ℝ × Vec d) (s : ℕ) : Vec d :=
  if s = 2 * N then zAt m α μ base H N
  else if s % 2 = 0 then yAt m α μ base H (s / 2)
  else (xv m α μ base H (s / 2 + 1)).1

noncomputable def phaseCuts (m : Fin d → ℝ) (α μ : ℝ) (N : ℕ) (base : Vec d)
    (H : ℕ → ℝ × Vec d) : List (Cut d) :=
  let Y := yAt m α μ base H
  let X := fun k => (xv m α μ base H k).1
  let z := zAt m α μ base H N
  (List.range N).map (fun k => cutCoco (H (2 * k)).1 (H (2 * k + 1)).1 (Y k) (X (k + 1))
      (H (2 * k)).2 (H (2 * k + 1)).2) ++
    [cutCoco (H (2 * N - 1)).1 (H (2 * N)).1 (X N) z (H (2 * N - 1)).2 (H (2 * N)).2] ++
    (List.range N).map (fun k => cutSc μ (H (2 * N)).1 (H (2 * k)).1 z (Y k) (H (2 * k)).2) ++
    [cutSc μ (H (2 * N - 1)).1 (H 0).1 (X N) base (H 0).2,
      cutMono μ z base (H (2 * N)).2 (H 0).2,
      cutCocoMono z (X N) (H (2 * N)).2 (H (2 * N - 1)).2]

noncomputable def firstViolated (θ : Fin d → ℝ) (cs : List (Cut d)) : Option (Cut d) :=
  cs.find? fun C => decide (0 < C.val θ)

structure St (d : ℕ) where
  probing : Bool
  pidx : ℕ
  g0 : Vec d
  J : Fin d → ℝ
  lvl : ℕ
  fails : ℕ
  θ : Fin d → ℝ
  base : Vec d
  s : ℕ
  H : ℕ → ℝ × Vec d

noncomputable def St.N (st : St d) : ℕ := len st.lvl

noncomputable def St.m (st : St d) : Fin d → ℝ := metric st.θ

noncomputable def initial (x0 : Vec d) : St d :=
  ⟨true, 0, 0, fun _ => 1, 0, 0, fun _ => 0, x0, 0, fun _ => (0, 0)⟩

noncomputable def queryOf (x0 : Vec d) (st : St d) : Vec d :=
  if st.probing then
    (if h : st.pidx - 1 < d then
      (if st.pidx = 0 then x0 else x0 + EuclideanSpace.single (⟨st.pidx - 1, h⟩ : Fin d) 1)
    else x0)
  else phaseQuery st.m (alph st.lvl) (muh st.lvl) st.N st.base st.H st.s

noncomputable def endPhase (st : St d) (H : ℕ → ℝ × Vec d) : St d :=
  match firstViolated st.θ
      (phaseCuts st.m (alph st.lvl) (muh st.lvl) st.N st.base H) with
  | none =>
      { st with base := (xv st.m (alph st.lvl) (muh st.lvl) st.base H st.N).1, s := 0, H := H }
  | some C =>
      if st.fails + 1 = cap d st.lvl then
        { st with lvl := st.lvl + 1, fails := 0, θ := th0 st.J (st.lvl + 1), s := 0, H := H }
      else
        let θ' := cutStep (lo st.J) (hi st.J st.lvl) (Real.log 2) C st.θ
        { st with fails := st.fails + 1, θ := θ', s := 0, H := H }

noncomputable def updateOf (st : St d) (r : ℝ × Vec d) : St d :=
  if st.probing then
    if st.pidx = 0 then { st with g0 := r.2, pidx := 1 }
    else if h : st.pidx - 1 < d then
      let J' := Function.update st.J ⟨st.pidx - 1, h⟩ (r.2 ⟨st.pidx - 1, h⟩ - st.g0 ⟨st.pidx - 1, h⟩)
      if st.pidx = d then
        { st with probing := false, J := J', θ := th0 J' 0, pidx := st.pidx + 1, s := 0 }
      else { st with J := J', pidx := st.pidx + 1 }
    else st
  else
    let H' := Function.update st.H st.s r
    if st.s = 2 * st.N then endPhase st H' else { st with H := H', s := st.s + 1 }

noncomputable def algorithm (p : Public) : Algorithm (spec.Query p) (spec.Reply p) (spec.Output p) where
  State := St p.d
  initial _ := initial p.x0
  query st := (0, queryOf p.x0 st)
  update := updateOf
  output st := st.base

end OracleTemplate.BlackBoxDiagonal
