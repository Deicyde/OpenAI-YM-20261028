import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.IssuePlan

/-!
# Calendar consumer on an actual β band test

Good buys through E,F/I, incl normalized γ/likelihood; shows W and a
concrete possible extension in deadlines. No asserting existence of a
complete Directed or that choosing a fresh Buy after a schedule suffices. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees    PriceCompiler
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} 

lemma aim_budget {Ñ : ChartRatio G} (h : LocalRatio Ñ) (P : Teller G) (p e : ℝ) (m : ℕ) (l : ℕ)
    (hl : 500≤l) (hp : 0 ≤ p) (he : -(1/2:ℝ)<e) (he' : e<0) : ∃ (Q : Target G P)
    (v : Target.Expense Q), Q.table=Ñ ∧ v.degrees=m ∧ v.earn=p ∧ v.wanting=e ∧ Q.halo=l := by
  let a := min P.top.supportExponent (min P.top.width P.below.width)
  obtain ⟨r,hr,hR⟩ := exists_between he
  have ha : 0 < a := lt_min P.top.price_pos (lt_min P.top.width_pos P.below.width_pos)
  let Q : Target G P := ⟨a/10,p+2,1,r,l,hl,Ñ,h,(by positivity),zero_lt_one,(by linarith),hr,hR.trans he',by
      have hx : a≤ P.top.supportExponent := min_le_left ..
      have ht : a ≤ min P.top.width P.below.width := min_le_right ..; obtain ⟨ht,hi⟩:= le_min_iff.mp ht
      constructor
      · linarith
      constructor <;> linarith⟩
  refine ⟨Q, ⟨m,p,1,1,e,hp,zero_lt_one,zero_lt_one,?_ ,hR,he'⟩,rfl,rfl,rfl,rfl,rfl⟩
  change p+1+1 ≤ p+2; linarith

open RG.Supply Pressure.Testing
namespace Planning



open Input Shoot
variable {C : Sheet G} {M : MapPrices} {Q : ∀ j i,Target G (Pressure.Testing.query C M j i)}
variable {p : ∀ j i,Target.Expense (Q j i)} {D : Supply.Rolls C}
variable {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
variable {O : ChartRatio G} {K : PostCost D} (D' : Directed G I O M K)
variable {w : ℕ→ℕ→ℝ} {A : ℕ→ℝ} (L : Purchase C M Q p D w A) (he : A≤W.betaEntry)
variable (h : ∀ N m n,m≤N→ Sworn (D'.M.H N m) n G)
include L he



lemma testing (N m n : ℕ) (hm : m<N) :
    let j:= D'.a.clock.J (m+1); let i:= D'.a.clock.J m; let P:= query C M j i
    let S:=D'.a.clock.op m n; let T := ships D' N m n; let x :=D'.a.clock.hatBeta m
    let _a:= A j; let _Q:= Q j i
    0<w j i ∧ 0<L.μ j i ∧ Works P (D.L j) x S T ∧ Target.Ledgered (p j i) (D.L j) (w j i) (L.μ j i) (L.c j i) (L.o j i) x := by
  intro j i P S T x a q
  have hx := L.consumes j i (step_paid D'.a m)
  have hs : 100*(1+radiusB x) ≤ (D'.a.S.side m n).val := by rw [add_comm 1]; exact D'.a.fits.sizeT m n
  refine ⟨hx.1,hx.2.1,⟨Pressure.Testing.proceeds D' N m n hm,block_eq D'.valid m,hs⟩, hx.2.2.2 x ((he _).trans (D'.valid.pays m))⟩

include h
lemma walls (N m n : ℕ) (hm : m<N) (R : Rep G (D'.a.S.side (m+1) n)) (hR : Lives D'.bake N (m+1) n R) (hx : R.beta∈band D'.a (m+1)) :
    let j:= D'.a.clock.J (m+1); let i:= D'.a.clock.J m; let T:= ships D' N m n; let x:= D'.a.clock.hatBeta m; let P:=p j i
    ∃ (H : Cash (w j i) x (L.μ j i) (D.L j) (Q j i) (L.o j i) (L.c j i) T R), Cash.Renewed P.degrees P.earn P.one P.two H ∧
      (Q j i).mergeScale (D.L j) (L.μ j i) x P.degrees ≤ D'.a.clock.hatBeta (m+1)^P.wanting := by
  intro j i T x P
  have ⟨h1,h2,h3,h4⟩:= testing D' L he N m n hm
  have hv : SliceRows.Stamp T := ⟨D'.M.H N (m+1),D'.M.H N m,D'.plan.crossings N m n hm,D'.plan.stack N m n hm,h N _ _ hm,
    h N _ _ hm.le,D'.support.links _ _ hm,D'.support.links _ _ hm.le,_,_, D'.plan.all N _ hm _,_,_,D'.plan.all _ m hm.le _⟩
  obtain ⟨H,hH⟩:= (h4.2 _ _ _ _ h3).2 hv R (Application.intake_at D' N m n hm R hR hx)
  rw [PriceCompiler.beta_eq D'.valid]; exact ⟨H,hH,h4.1⟩
end Planning
end YM.ConnectedActivityE6
