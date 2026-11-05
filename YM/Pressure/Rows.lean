import YM.PCalc.Band
import YM.Pressure.Cost


/-!
# drows , fixed orientation

Unclamped quadratic through clipped path counts, R in absolute fine units.
Cross kernel installed by root cover routes here; choose these paths even
on winding overlaps. No random choice of cuts. Contributions charged with
ALL ancillary halo/mask reads. Adjoint M,N are physical adjoints at real
actual V even after cutoff. Do NOT assert M,M* exact at V! Formula proof
retains defects. Uncut base keeps tails per priority.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pressure
open Filter Function Lattice RG RG.Patch Axial Wilson Finset Precision Exterior Bloch Laurent
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal ComplexOrder

abbrev Cell (n : Side) := Face (Per n)
abbrev Twin (n : Side) := Cell n × Bool
abbrev Bond (n : Side) := Edge (Site n)
def mesh {n} (x : Twin n) : Co n Layers2 := (x.1.1, if x.2 then .inr (plaquette x.1.2) else .inl (plaquette x.1.2))
def pole {n} (e : Bond n) : Co n (TypeFace 1) := (e.1, coord e.2)

variable {G : Gauge} {c f n : Side}
-- choices on \\bar V uses gauge rotations constant on blocks; equivalent to desired transported kernels. Unlike test ell always applied cut.
abbrev Pay (G : Gauge) := G.Color →L[ℝ] G.Color

def rated (U : Config G n) (x : Site n) (w : Walk) (c : ℝ) : Pay G := c • (G.adjoint (travel U x w)).toContinuousLinearMap

def priced {α β : Type*} (R d : ℕ) (U : Config G n) (K : Row α β) (p : Co n α) (q : Co n β) (i : Cover) : Pay G :=
    if (route 0 i 1).length*d ≤ R ∧ q.1=p.1+wrap n i then rated U p.1 (route 0 i 1) (K p.2 q.2 i) else 0

def lane {α β : Type*} (R d : ℕ) (U : Config G n) (K : Row α β) (p : Co n α) (q : Co n β) :=
    ∑' i, priced R d U K p q i

variable (S : StepData c f) (M : Towers S.patch.L)

def casted (R : ℕ) (V : Config G c) (x : Co f Layers2) (y : Co c Layers2) (i : Cover) : Pay G :=
    let r := S.ratio.residue x.1
    let w := route (lift r) (S.patch.L.val • i) 1
    if w.length ≤ R ∧ y.1=S.ratio.parent x.1+wrap c i then rated (replica S.ratio V) x.1 w (M.mf (r,x.2) y.2 i) else 0

def leap (R : ℕ) (V : Config G c) (x : Twin f) (y : Twin c) : Pay G :=
    ∑' i, casted S M R V (mesh x) (mesh y) i

def kick (R : ℕ) (V : Config G c) (x : Bond c) (y : Twin c) := lane R S.patch.L.val V M.mn (pole x) (mesh y)

def gk (R : ℕ) (V : Config G c) (x : Co c Gain) (y : Twin c) := lane R S.patch.L.val V M.o x (mesh y)

section terms
variable (S : PathData G)
def toll (U : Config G n) (x : Cell n) := G.chord (faceValue U x)

def shoot (A : Clip) (U : Config G n) (x : Cell n) := Real.sqrt A.direct • G.curvature (faceValue U x)

def shortenTerm (R d : ℕ) (U : Config G n) (x : Cell n) (i : ℕ) := if (S.row x.2 i).2.length*d ≤ R then S.ellTerms x i U else 0

def shorten (R d : ℕ) (U : Config G n) (x : Cell n) := ∑' i, shortenTerm S R d U x i

def plotted (A : Clip) (R d : ℕ) (U : Config G n) (x : Twin n) := if x.2 then shorten S R d U x.1 else shoot A U x.1

open scoped Classical in
def trunk (A : Clip) (R d : ℕ) (t : ℝ) (U : Config G n) (x : Cell n) := if PathData.kept A t x.1 U then ‖shorten S R d U x‖^2/2 else 0

def crown (A : Clip) (R d : ℕ) (t : ℝ) (U : Config G n) (x : Cell n) := trunk S A R d t U x+PathData.clipped A t (G.chord (faceValue U x))

open scoped Classical in
def thinned (A : Clip) (t : ℝ) (d R : ℕ) (U : Config G n) (x : Twin n) : G.Color :=
    if x.2 then if PathData.kept A t x.1.1 U then shorten S R d U x.1 else 0 else
        (if toll U x.1=0 then 1 else min 1 (t/toll U x.1)) • shoot A U x.1

def cuff (A : Clip) (m : BudgetPoint) (d R : ℕ) (U : Config G n) (x : Cell n) :=
    S.baseTerm A m U x-crown S A R d m.threshold U x
end terms

section
variable {α β : Type*} [Fintype α] [Fintype β] (g : α→β→Pay G)

def zip (a : β→G.Color) (x : α) := ∑ y, g x y (a y)

def unzip (a : α→G.Color) (x : β) := ∑ y, (g y x).adjoint (a y)

lemma arity (p : α → G.Color) (q : β→G.Color) :
    ∑ i, inner ℝ (zip g q i) (p i)=∑ i, inner ℝ (q i) (unzip g p i) := by
  unfold zip unzip
  simp_rw [sum_inner,inner_sum,ContinuousLinearMap.adjoint_inner_right]; rw [sum_comm]
end

/-- Parameters e.g. from a single Movement. R measured fine, no
sup cardinal. `/100000` used below not here. -/
structure Tube (G : Gauge) {c f : Side} (S : StepData c f) where
  R : Towers S.patch.L
  up : PathData G
  high : Clip
  down : PathData G
  low : Clip

namespace Tube
variable {S : StepData c f} (T : Tube G S) (R : ℕ)

def vision (t' : ℝ) (V : Config G c) := thinned T.down T.low t' S.patch.L.val R V

def Xf (U : Config G f) := plotted T.up T.high R 1 U

def Xn (V : Config G c) := plotted T.down T.low R S.patch.L.val V

def Z (S : StepData c f) (Q V : Config G c) (b : Bond c) := Real.sqrt S.kernel.penalty • G.curvature (V b * (Q b)⁻¹)

def monetary (S : StepData c f) (Q V : Config G c) (x : Bond c) :=
    S.kernel.penalty*wire Q V x^2/2

abbrev Φ (V : Config G c) := leap S T.R R V
abbrev Φ' (V : Config G c) := kick S T.R R V
abbrev N (V : Config G c) := gk S T.R R V

def Mv (s : ℝ) (V : Config G c) := zip (T.Φ R V) (T.vision R s V)
def Mw (s : ℝ) (V : Config G c) := zip (T.Φ' R V) (T.vision R s V)

def workF (U : Config G f) (V : Config G c) (t s : ℝ) (x : Cell f) :=
    crown T.up T.high R 1 t U x + ∑ i : Bool,
      (‖T.Mv R s V (x,i)‖^2/2 - inner ℝ (T.Mv R s V (x,i)) (T.Xf R U (x,i)))

def workI (Q V : Config G c) (s : ℝ) (x : Bond c) :=
    monetary S Q V x + (‖T.Mw R s V x‖^2/2 - inner ℝ (T.Mw R s V x) (Z S Q V x))

def workC (V : Config G c) (s : ℝ) (x : Cell c) :=
    (∑ i : Bool, (inner ℝ (T.vision R s V (x,i)) (T.Xn R V (x,i)) - ‖T.vision R s V (x,i)‖^2/2)) -
      crown T.down T.low R S.patch.L.val s V x

def workL (U : Config G f) (Q V : Config G c) (s : ℝ) (x : Cell c) :=
    (∑ i : Bool, inner ℝ (T.vision R s V (x,i)) (unzip (T.Φ R V) (T.Xf R U) (x,i) + unzip (T.Φ' R V) (Z S Q V) (x,i) - T.Xn R V (x,i)))

def workN (V : Config G c) (s : ℝ) (x : Co c Gain) := ‖zip (T.N R V) (T.vision R s V) x‖^2/2

def workD (V : Config G c) (s : ℝ) (x : Cell c) :=
    ∑ i : Bool, inner ℝ (T.vision R s V (x,i)) (T.vision R s V (x,i) -
      (unzip (T.Φ R V) (T.Mv R s V) (x,i) + unzip (T.Φ' R V) (T.Mw R s V) (x,i) + unzip (T.N R V) (zip (T.N R V) (T.vision R s V)) (x,i)))/2

section globe
variable (U : Config G f) (Q V : Config G c) (t s : ℝ)

lemma locates : (∑ x, T.workF R U V t s x) + (∑ x,T.workI R Q V s x) + (∑ x,T.workC R V s x)+
      (∑ x,T.workN R V s x)+(∑ x,T.workL R U Q V s x)+(∑ x,T.workD R V s x) =
    (∑ x, crown T.up T.high R 1 t U x) + (∑ x, monetary S Q V x) - ∑ x,crown T.down T.low R S.patch.L.val s V x := by
  let w := T.vision R s V
  let e := T.Mv R s V
  let f := T.Mw R s V
  let g := zip (T.N R V) w
  have hn := arity (T.N R V) g w
  have hf := arity (T.Φ R V) e w
  have he := arity (T.Φ' R V) f w
  have h1 := arity (T.Φ R V) (T.Xf R U) w
  have h2 := arity (T.Φ' R V) (Z S Q V) w
  unfold g w e f Mv Mw at *
  simp_rw [workF,workI,workC,workN,workL,workD,Mw,Mv,inner_sub_right,inner_add_right, real_inner_self_eq_norm_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← sum_div]
  -- flatten
  unfold Twin at *
  simp_rw [Fintype.sum_prod_type, real_inner_self_eq_norm_sq] at *
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← sum_div]
  linarith only [hn,hf,he,h1,h2]
end globe
end Tube
end YM.Pressure
