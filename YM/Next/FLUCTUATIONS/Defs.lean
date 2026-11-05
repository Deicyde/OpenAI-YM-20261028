import YM.Work.F03.Transport


/-!
# The two defects in the price estimate. Physical coordinates.

E(drows) , EBare: cut exactly as in `Pressure.Rows`,
including adjoint after transport on the actual input. No analytic assumption
on indicators. We leave one input (`w` below) free; can substitute the
actual thinned coarse data even when they aren't differentiable. Contrast
`flatF`, `flatI`, `flatN`, `xLin`, `zLin` which carry only a *calculation*,
in full, uncut real counting matrix coordinates, compared to the actual
reads later. As in E-chain code, a bare expression (even
extensional identities like locality of that expression) doesn't
guarantee summability of e.g. unguarded ℓ terms! Use as estimates
with `Funds`: both `PathData.Bounds` and `Deep` give the absolute
receipts; later proofs include checks of these when using `tsum`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Fluctuations
open Filter Function Lattice RG Wilson Matrix Pressure Pressure.Tube Precision Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {n m c f : Side} {S : StepData c f}

/-- Vector contracted in the L row. -/
def lGap (T : Tube G S) (R : ℕ) (U : Config G f) (Q V : Config G c) (i : Twin c) : G.Color :=
  unzip (T.Φ R V) (T.Xf R U) i + unzip (T.Φ' R V) (Z S Q V) i - T.Xn R V i

/-- Vector contracted in the D row (price has also a factor of 1/2). -/
def dGap (T : Tube G S) (R : ℕ) (V : Config G c) (w : Twin c → G.Color) (i : Twin c) : G.Color :=
  w i - (unzip (T.Φ R V) (zip (T.Φ R V) w) i + unzip (T.Φ' R V) (zip (T.Φ' R V) w) i +
    unzip (T.N R V) (zip (T.N R V) w) i)

lemma workL_gap (T : Tube G S) (R : ℕ) (U : Config G f) (Q V : Config G c) (s : ℝ) (i : Cell c) :
    T.workL R U Q V s i = ∑ j : Bool,
      inner ℝ (T.vision R s V (i,j)) (lGap T R U Q V (i,j)) := rfl

lemma workD_gap (T : Tube G S) (R : ℕ) (V : Config G c) (s : ℝ) (i : Cell c) :
    T.workD R V s i = ∑ j : Bool,
      inner ℝ (T.vision R s V (i,j)) (dGap T R V (T.vision R s V) (i,j))/2 := rfl

abbrev LogField (G : Gauge) (n : Side) := fieldDir G n 1

/-- Full linear expression, first component ALSO in physical color. -/
def xLin (A : Clip) (P : PathData G) (a : LogField G n) (i : Twin n) : G.Color :=
  if i.2 then Work.F03.ellLine P i.1 a else Real.sqrt A.direct • Work.F03.faceCurl i.1 a

/-- This is from differentiating the actual prediction; note `probe`,
not `mean`, appears here. -/
def zLin (S : StepData c f) (a : LogField G f) (b : LogField G c) (i : Bond c) : G.Color :=
  Real.sqrt S.kernel.penalty • (b (pole i) - WithLp.toLp 2
    (fun j : G.ColorIndex => ((probe S)*ᵥ parts G 1 a j) (pole i)))

def scalar (G : Gauge) (x : ℝ) : Pay G := x • ContinuousLinearMap.id ℝ _

def flatF (T : Tube G S) (i : Twin f) (j : Twin c) : Pay G :=
  scalar G (installed S.ratio T.R.mf (mesh i) (mesh j))

def flatI (T : Tube G S) (i : Bond c) (j : Twin c) : Pay G :=
  scalar G (T.R.mn.acts c (pole i) (mesh j))

def flatN (T : Tube G S) (i : Co c Gain) (j : Twin c) : Pay G :=
  scalar G (T.R.o.acts c i (mesh j))

/-- The loss for kernel approximations; `h` bounds log norm, λ post-L.
     R = length cutoff in fine units. -/
def widen (R : ℕ) (h τ : ℝ) : ℝ := (1+R)*h + Real.exp (-τ*R)

lemma widen_nonneg (R : ℕ) {h τ : ℝ} (hh : 0 ≤ h) : 0 ≤ widen R h τ := by
  unfold widen; positivity

lemma le_widen (R : ℕ) {h τ : ℝ} (hh : 0 ≤ h) : h ≤ widen R h τ := by
  unfold widen
  exact (le_mul_of_one_le_left hh (by simp)).trans (le_add_of_nonneg_right (by positivity))

lemma widen_anti (R : ℕ) (h : ℝ) : Antitone (widen R h) := by
  intro x y hx
  unfold widen; gcongr

/-- Equality of the actual bonds tethered through radius D in coarse sites.
Guards both coarse (p identity) and fine (p parent). -/
def AgreeNear (p : Site n → Site m) (q : Site m) (D : ℕ) (U V : Config G n) :=
  ∀ e : Bond n, separation q (p e.1) ≤ D → U e = V e

lemma AgreeNear.shrink {p : Site n → Site m} {q q' : Site m} {D D' : ℕ} {U V : Config G n}
    (h : AgreeNear p q D U V) (he : separation q q' + D' ≤ D) : AgreeNear p q' D' U V := by
  intro i hi
  exact h i <| (separation_triangle ..).trans ((Nat.add_le_add_left hi _).trans he)

end YM.Next.Fluctuations
