import YM.PCalc.Chart

/-!
# Flat side syntax & algebra contracts

Particular cuts for the NEEDS of Wilson/Sector.

Use computed
arrays on the cover in the actual Ratio.

No hidden width from region or current period.

Costs MUST also be shown in assembly to have been chosen before L in its
uses across plateaus.

See WPs for Construction route.

These are **not** assertions that just these fields imply the vStep theorem,
and not trying to state the widest versions of estimate theorems: we're aiming
to construct `Recipe.Issues`, possibly using more about the actual choice of
kernel (cumulative, parity, sym paths etc). Clear seam definitions for proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Precision
open Lattice Wilson RG Matrix Exterior Finset Tree Function Bloch Laurent
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

abbrev Layers2 := TypeFace 2 ⊕ TypeFace 2
abbrev Gain := Layers2 ⊕ TypeFace 3

variable {c f n : Side} {G : Gauge}

/-- Fourier ℓ row and BOTH metrics H & H tilde. -/
structure Bed where
  diagonal : Row (TypeFace 2) (TypeFace 2)
  dual_diag : Row (TypeFace 2) (TypeFace 2)
  metric : Row (TypeFace 2) (TypeFace 2)
  inverse : Row (TypeFace 2) (TypeFace 2)
  roots : Row (TypeFace 2) (TypeFace 2)

/-- Need recover actual path entries of `R.ell` through these roots.
The R.Bounds carries own width/norm of full path length. -/
structure Attached (M : Bed) (R : PathData G) : Prop where
  layout (b p : PlaqAxes) (y : Cover) : HasSum (fun i => if (R.row b i).2.plaq=p ∧ (R.row b i).2.offset=y
        then (R.row b i).1 else 0) (M.roots (plaquette b) (plaquette p) y)

/-- Stack lifted metric; don't average channels separately in canonical action. -/
def Bed.full (M : Bed) (p : Clip) (n : Side) : Matrix (Co n Layers2) (Body 2 n) ℝ :=
    of fun x b => Sum.elim (fun i => Real.sqrt p.direct * (1 : Matrix (Body 2 n) (Body 2 n) ℝ) (x.1,i) b)
      (fun i => M.roots.acts n (x.1,i) b) x.2

def Bed.covered (M : Bed) (width price : ℝ) :=
    M.diagonal.strip width price ∧ M.metric.strip width price ∧ M.inverse.strip width price ∧ M.roots.strip width price ∧ M.dual_diag.strip width price

/-- counting bounds on REAL physical coordinates, no normalization by number
of sites. -/
def Numeric {m : Type*} [Fintype m] (H : Matrix m m ℝ) (η A : ℝ) := ∀ v : m → ℝ,
    η*dotProduct v v ≤ dotProduct v (H *ᵥ v) ∧ dotProduct v (H *ᵥ v) ≤ A*dotProduct v v

structure Floor (M : Bed) (p : Clip) (n : Side) (η A : ℝ) : Prop where
  diagonalInv : M.diagonal.acts n * M.dual_diag.acts n=1
  inverse : M.metric.acts n * M.inverse.acts n=1
  roots : (M.full p n).transpose*M.full p n=M.metric.acts n
  starts : M.metric.read 0=1
  same : M.metric.acts n*d 1 n=M.diagonal.acts n*d 1 n
  symmetric : (M.metric.acts n).transpose=M.metric.acts n ∧ (M.diagonal.acts n).transpose=M.diagonal.acts n
  uniform : Numeric (M.metric.acts n) η A ∧ Numeric (M.diagonal.acts n) η A

structure Towers (L : Side) where
  A0 : Cross L (TypeFace 1) (TypeFace 1)
  T : Cross L (TypeFace 2) (TypeFace 2)
  mf : Cross L Layers2 Layers2
  mn : Row (TypeFace 1) Layers2
  o : Row Gain Layers2

namespace Towers

variable (S : StepData c f) (H H' : Bed) (K : Towers S.patch.L)

/-- pointwise real matrix identities, not pinned-only. -/
structure Diagonal (S : StepData c f) (H H' : Bed) (K : Towers S.patch.L) : Prop where
  /-- T/H route still uses the unmodified H. -/
  trial : Inputs S (installed S.ratio K.A0) (H.metric.acts f) (H'.metric.acts c)
  transport : (installed S.ratio K.T).transpose * d 1 f=d 1 c*mean S
  stays : installed S.ratio K.T * H'.diagonal.acts c * d 1 c=H.diagonal.acts f*d 1 f*installed S.ratio K.A0

structure Roll (S : StepData c f) (H H' : Bed) (K : Towers S.patch.L) (p p' : Clip) : Prop where
  m : (installed S.ratio K.mf).transpose*installed S.ratio K.mf +
    (K.mn.acts c).transpose*K.mn.acts c + (K.o.acts c).transpose*K.o.acts c=1
  n : Real.sqrt S.kernel.penalty • (K.mn.acts c).transpose=H'.full p' c*d 1 c
  fPart : installed S.ratio K.mf * H'.full p' c*d 1 c=H.full p f*d 1 f*installed S.ratio K.A0
  nPart : K.mn.acts c*H'.full p' c*d 1 c=(Real.sqrt S.kernel.penalty)⁻¹ • Precision.K (H'.metric.acts c)
  oPart : K.o.acts c*H'.full p' c*d 1 c=0
  orthogonal : (installed S.ratio K.mf).transpose * (H.full p f*d 1 f)+
    (K.mn.acts c).transpose * (- Real.sqrt S.kernel.penalty • mean S)=0
end Towers

/-- Difference stencil on a cross row, incrementing FINE x in the
Cover. Need only odd L. True path costs can use separate path assignment.
-/
def forwardC (L : Side) {α β : Type*} (K : Cross L α β) (i : Axis) : Cross L α β := fun a b x =>
    let q := a.1+step i
    let Δ := if lift a.1 i=((L.val/2:ℕ):ℤ) then step i else 0
    K (q,a.2) b (x-Δ)-K a b x

def advanceC (L : Side) {α β : Type*} (K : Cross L α β) : List Axis → Cross L α β
  | [] => K
  | i::l => forwardC L (advanceC L K l) i

def Towers.Deep {L : Side} (K : Towers L) (α C : ℝ) (X : ℕ) : Prop :=
    K.mn.strip α C ∧ K.o.strip α C ∧ K.mf.strip α (C/(L.val:ℝ)^2) ∧ ∀ l : List Axis,
      l.length ≤ X → (advanceC L K.A0 l).strip α (C/(L.val:ℝ)^(1+l.length)) ∧
      (advanceC L K.T l).strip α (C/(L.val:ℝ)^(2+l.length))

/-- Compute knot over every N,m then use `MapPrices` depending only j
and actual prechoices; can test both transitions, all sizes/directions jointly.
The filtering quantities on c,f matrices are not dimension-free by defeq. -/
structure Horizon (a : Levels G) where
  H (N m : ℕ) : Bed
  towers (N m : ℕ) : Towers (a.S.block m)

structure MapPrices where
  α : ℕ → ℝ
  Ω : ℕ → ℝ
  η : ℕ → ℝ
  alpha_pos i : 0 < α i
  eta_pos i : 0 < η i

namespace Horizon
variable {a : Levels G}
structure Suffices (M : Horizon a) (P : MapPrices) : Prop where
  rows N m : m ≤ N → (M.H N m).covered (P.α (a.clock.J m)) (P.Ω (a.clock.J m))
  /-- Require every torus here; binit constructs UNIVERSAL. -/
  all N m : m ≤ N → ∀ n, Floor (M.H N m) (a.params m).clip n (P.η (a.clock.J m)) (P.Ω (a.clock.J m))
  costs N m : m < N → (M.towers N m).Deep (P.α (a.clock.J (m+1))) (P.Ω (a.clock.J (m+1))) (a.clock.J (m+1)-2)
  crossings N m p : m < N → Towers.Diagonal (a.clock.op m p) (M.H N (m+1)) (M.H N m) (M.towers N m)
  stack N m p : m < N → Towers.Roll (a.clock.op m p) (M.H N (m+1)) (M.H N m) (M.towers N m) (a.params (m+1)).clip (a.params m).clip
  top N : ∀ n, (M.H N N).diagonal.acts n=1
end Horizon
end YM.Precision
