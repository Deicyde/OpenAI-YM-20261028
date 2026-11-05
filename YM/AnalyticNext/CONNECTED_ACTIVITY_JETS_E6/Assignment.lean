import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Coat


/-!
# Coercive block assignments

Orientation-local Cut. Individually F or I can pay a square. All
accounting happens on the **actual** drows, recombine exactly at halo
and its complement. Signs on `debit`: still energy before -β.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

/-- Coarse L/D at same physical anchor/color as C; bundle with it; N
rows separate. -/
abbrev Spot (c f : Side) := Cell f ⊕ Bond c ⊕ Cell c ⊕ Co c Gain

def lead (S : StepData c f) : Spot c f → Site c := Sum.elim (fun i => S.ratio.parent i.1)
    (Sum.elim Prod.fst (Sum.elim Prod.fst Prod.fst))

def parents (X : Spot c f) : Finset (Rod c f) :=
    match X with
    | .inl i => {.inl (i,true),.inl (i,false)}
    | .inr (.inl b) => {.inr b}
    | _ => ∅

def spot (_S : StepData c f) (p : Rod c f) : Spot c f := p.elim (fun i => .inl i.1) (fun b => .inr (.inl b))



lemma cost_is_here (i : Rod c f) : focus S i=lead S (spot S i) := by rcases i with i|b <;> rfl

lemma spots_sum (_S : StepData c f) (G : Rod c f → ℝ) :
    (∑ i, ∑ p∈parents i, G p)=∑ p,G p := by
  unfold Spot Rod Bond Cell Twin; simp only [Fintype.sum_sum_type];
  simp [parents, Fintype.sum_prod_type,Finset.sum_add_distrib]

def principal (T : Tube G S) (x : ℝ) (U : Config G f) (V Q : Config G c) : Spot c f → ℝ :=
    let R := till x; let t := Pressure.fiery G x S.patch.L; let y := Pressure.temp x
    Sum.elim (T.workF R U V t y) (Sum.elim (T.workI R Q V y) (Sum.elim (fun p => T.workC R V y p+
      (T.workL R U Q V y p+T.workD R V y p)) (T.workN R V y)))

/-- Keep V switches actual (can override later when checking derivatives
with flags frozen good throughout the stencil; value estimates do not
cover derivative obligations by themselves). F switch extension. -/
def yielding (T : Tube G S) (x : ℝ) (U : Config G f) (V : Config G c) (k : S.Choices) : Spot c f → ℝ :=
    Sum.elim (soft T x U V k) (fun i => principal T x U V (S.prediction U k) (.inr i))

/-- Look-up at one oriented lattice. -/
def posted (A : Stores S) (d : ℕ) := univ.filter fun i : Spot c f => Inside (lead S i) A d

theorem posted_charge (A : Stores S) (U : Config G f) (V Q : Config G c) (x : ℝ) :
    A.assessed T x U Q V = ∑ i∈posted A (2*radiusB x), principal T x U V Q i := by
  let d := 2*radiusB x; let t := Pressure.temp x; let R := till x
  have h : (∑ p : Cell c, (if p.1∈A.dome d then T.workC R V t p+(T.workL R U Q V t p+T.workD R V t p) else 0)) =
      (∑ p : Cell c, (if p.1∈A.dome d then T.workC R V t p else 0))+
      ∑ p : Cell c, (if p.1∈A.dome d then T.workL R U Q V t p+T.workD R V t p else 0) := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun p _ => ?_; split <;> simp_all
  unfold assessed tally talli tallc talll talln
  simp_rw [limit,intern,outs,coordN,posted, sum_filter]
  unfold Spot; simp only [Fintype.sum_sum_type]
  change _ = (∑ p : Cell f, if S.ratio.parent p.1∈A.dome d then T.workF R U V (Pressure.fiery G x S.patch.L) t p else 0) +
    ((∑ p : Bond c, if p.1∈A.dome d then T.workI R Q V t p else 0) +
      ((∑ p : Cell c, if p.1∈A.dome d then T.workC R V t p+(T.workL R U Q V t p+T.workD R V t p) else 0) +
       (∑ p : Co c Gain, if p.1∈A.dome d then T.workN R V t p else 0)))
  rw [h]; unfold d R t; abel

variable (X : Coat T F)
def addr (_X : Coat T F) (s : Signed) (i : Spot c f) : Site c := s.act (lead S i)

/-- Use all rows out of H6 of X (in each orientation), even where linear
coefficient zero. No actual core/seed supplies Gaussian Hessian. -/
def selected (s : Signed) (p : Spot c f) := ¬ Inside (X.addr s p) X.seeds (6*X.B)

def energy (u : Directions G f) (s : Signed) (p : Spot c f) :=
    let k := choice s X.k; let U := pull s 0 (X.input u)
    principal T X.x U (pull s 0 X.V) (S.prediction U k) p

def surcharge (s : Signed) (p : Rod c f) (u : Directions G f) :=
    if X.selected s (spot S p) then ‖X.realPath s p u‖^2/2 else 0

def extracted (u : Directions G f) (s : Signed) (p : Spot c f) :=
    ∑ i∈parents p, X.surcharge s i u

lemma surcharge_nn (u : Directions G f) (s : Signed) (p : Rod c f) : 0≤X.surcharge s p u := by
  unfold surcharge; split <;> positivity

lemma extracted_nn (u : Directions G f) (s : Signed) (p : Spot c f) : 0 ≤ X.extracted u s p :=
  sum_nonneg fun _ _ => X.surcharge_nn ..

lemma parent_iff (i : Rod c f) (p : Spot c f) : i∈parents p ↔ spot S i=p := by
  rcases i with ⟨i,b | b⟩|i <;> rcases p with i|(i|(i|i)) <;> simp [parents,spot]

lemma uncaptured (u : Directions G f) (s : Signed) (p : Spot c f) (h : ¬ X.selected s p) : X.extracted u s p=0 := by
  unfold extracted; apply sum_eq_zero
  intro i hi; unfold surcharge; rw [(parent_iff i p).1 hi, if_neg h]

def debit (u : Directions G f) (s : Signed) (p : Spot c f) := X.energy u s p - X.extracted u s p

def light (u : Directions G f) (s : Signed) (p : Spot c f) :=
    yielding T X.x (pull s 0 (X.input u)) (pull s 0 X.V) (choice s X.k) p-X.extracted u s p

def assigned (A : Stores S) (u : Directions G f) (s : Signed) :=
    ∑ i∈posted (turnStore s A) (200*X.B), X.debit u s i

def quoteNear (A : Stores S) (u : Directions G f) := averaged (X.assigned A u)

def liftSq (u : Directions G f) := averaged fun s => ∑ p, X.extracted u s p

/-- full cut recombination, no subtraction of determinant here. -/
lemma covers_paths (h : P.Funds S T) (u : Directions G f) :
    wholeGap T X.x (X.input u) X.V + (∑ i, monetary S (S.prediction (X.input u) X.k) X.V i) =
      (averaged fun s => ∑ p, X.debit u s p)+ X.liftSq u := by
  let Q := S.prediction (X.input u) X.k
  let m := ∑ i, monetary S Q X.V i
  rw [liftSq, ← av_const (∑ i, monetary S (S.prediction (X.input u) X.k) X.V i)]
  unfold wholeGap; rw [← av_add, ← av_add]; apply congr_arg averaged; funext s
  let U := pull s 0 (X.input u); let k := Oriented.choice s X.k; let Z := S.prediction U k; let V := pull s 0 X.V
  have hg := T.locates X.R U Z V X.t (Pressure.temp X.x)
  have hv : (∑ i, monetary S Z V i)=m := by
    rw [show Z=_ from (Oriented.carry s (SectorMeasure.funds_branch h) X.k (X.input u)).2]; unfold monetary V; simp_rw [wire_pulled]
    exact Equiv.sum_comp (StepData.sendBonds s 0) (monetary S Q X.V)
  simp_rw [debit,sum_sub_distrib,sub_add_cancel]
  simp only [Spot,Fintype.sum_sum_type]
  change ((∑ i, crown T.up T.high _ _ _ U i) - (∑ i,crown T.down T.low _ _ _ V i))+m = _
  simp only [energy,principal,Sum.elim,sum_add_distrib];
  rw [hv] at hg; unfold Z U V k Coat.R Coat.t at hg; unfold V U; linarith only [hg]

lemma core (A : Stores S) (hi : A.place ⊆ X.seeds.place) (s : Signed) (u : Directions G f) :
    (∑ p∈posted (turnStore s A) (2*X.B),X.debit u s p) =
      (turnStore s A).assessed T X.x (pull s 0 (X.input u)) (S.prediction (pull s 0 (X.input u)) (choice s X.k)) (pull s 0 X.V) := by
  rw [posted_charge]; apply sum_congr rfl; intro i hi'
  have hp : Inside (X.addr s i) A (2*X.B) := (rotates_dome ..).1 (mem_filter.mp hi').2
  have he : Inside (X.addr s i) X.seeds (6*X.B) := Corona.halo_mono (by omega) hi hp
  rw [debit,X.uncaptured u s i (fun hw => hw he),sub_zero]; rfl
end YM.ConnectedActivityE6.Coat
