import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.LapCount
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.ParcelBill
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.TiltAccount

/-!
# Chain alphabet on blocks with cost coupons

Keep ordered intermediate vertices even after combining color; different
from moving through an arbitrary sequence of metric balls. Eᵗ order in
full script matters. Use det via a *single* real flow parameter ν, exact
also on winding paths. Scalar exponent bill paired flat and sector
terms within a given ordered tuple. For covariance correction trace use
similar tuples (last factor 1); combine these and the quadratic ratio
into one factor. This is fine for pure hit/derivative prices on the same
marginal; if wanting valuation by rescaling in E's continuation refine
types again. Linear letters assigned separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Chains
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps 
open Centered Centered.Till 
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

-- include both endpoint indices in history; even scalar case evaluates
-- only when equal. k trailing remaining beyond first step. 80B uniform
-- visit enlargement (within choice per inventory).
abbrev Season (_S : StepData c f) (k : ℕ) := Laps.History (Bond f) (k+1)
abbrev Year (_S : StepData c f) := Σ k, Season _S k

def allot (S : StepData c f) (b : ℕ) (p : Year S) := sector (home S) (80*b) _ p.2.1 p.2.2.1 p.2.2.2





section receipt
variable (S : StepData c f) (x : ℝ) (M : Matrix (Vars G f) (Vars G f) ℝ)

-- elementary chain pay, cyclic order for trace regrouping

def confluence (p : Year S) (t : ℝ) :=
    let W := eyes S G (radiusB x)
    if p.2.1=p.2.2.2 then
      trace (routeF (-W.error (flows M t)) ((M-1)*W.within (flows M t)) _ p.2.1 p.2.2.1 p.2.2.2) else 0

def crosses (p : Year S) (t : ℝ) :=
    let W := eyes S G (radiusB x)
    if p.2.1=p.2.2.2 then
      (-t)^p.1*trace (routeF (W.untuned M) 1 _ p.2.1 p.2.2.1 p.2.2.2) else 0

def excise (p : Year S) (z : ArrayR G f) :=
    let W := eyes S G (radiusB x)
    amount (routeF (-W.untuned M) M _ p.2.1 p.2.2.1 p.2.2.2) z p.2.1 p.2.2.2
end receipt

def celebration (T : Tube G S) (F : Forest S.ratio) (x : ℝ) (M : Matrix (Vars G f) (Vars G f) ℝ) (p : Year S) (z : ArrayR G f) : ℝ :=
    (∫ t in (0:ℝ)..1, confluence S x (flatReference T x F) p t-confluence S x M p t+crosses S x M p t)/2 +
        excise S x M p z / 2

def chain (Y : Mint T F A x) (p : Year S) (z : ArrayR G f) : ℝ := Real.exp (celebration T F x Y.sheet p z)-1

-- Straightness purchase

section range
variable {v : Type*} {n : Type*} [Fintype v] [DecidableEq v] [Fintype n] [DecidableEq n] (d : v→Site c) (N M : Laps.Tile v n)

def horizon (b : ℕ) := ∀ i j, b < separation (d i.1) (d j.1) → N i j=0

omit [Fintype v] [DecidableEq v] [Fintype n] [DecidableEq n] in
lemma makes_narrow {b : ℕ} (h : horizon d N b) : Narrow d b N := by
  intro i j hi; by_contra! hq; exact hi (by ext r s; exact h (i,r) (j,s) hq)

omit [DecidableEq v] [DecidableEq n] in
lemma multiplies {p q} (hA : horizon d M p) (hN : horizon d N q) : horizon d (M*N) (p+q) := by
  intro i j he
  rw [Matrix.mul_apply]; apply Finset.sum_eq_zero
  intro k hk; by_cases h : p < separation (d i.1) (d k.1)
  · rw [hA _ _ h,zero_mul]
  rw [hN _ _ ?_,mul_zero]; have hi := separation_triangle (d i.1) (d k.1) (d j.1); omega
omit [Fintype v] [Fintype n] in
lemma horizon_sub {p : ℕ} (h : horizon d N p) : horizon d (N-1) p := by
  intro i j he
  have hh : i≠j := by intro H; rw [H] at he; simp at he
  simp [hh,h _ _ he]
omit [Fintype v] [DecidableEq v] [Fintype n] [DecidableEq n] in
lemma tail_range {p q} (he : p≤q) (hN : horizon d N p) : horizon d N q := fun i j hp => hN i j (he.trans_lt hp)
end range


end YM.AnalyticNext.ConnectedActivity.Chains
