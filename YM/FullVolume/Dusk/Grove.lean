import YM.FullVolume.Mark.Vega
/-! Transport local receipts only; don't ask for an equality of mark polys if the path isn't equal here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.GuardedAtom.Guard
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Push.Local Next.Foundations Extra.Histories
open Progress.DirectedRecipe
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge}{n : Side}{d:ℕ} (F:Labels.Frame G d) (B:SectionData F)
private def grape (A : Activities G n) := { A with forced := fun i => {A.forced i with extraTest := fun _=>True} }
private def plank (R:Rep G n): Rep G n := {R with activities:=grape R.activities}
private def fjords {A : Activities G n}{P:BudgetPoint} {K:Keeper P A}(h:∀ s,A.K (K.code s)=0) : Shelf (grape A):= ⟨K.code,K.support,K.inventory,fun _ _=> trivial,h⟩
def toper (R: Rep G n)(K : Keeper R.p R.activities)(h:∀ s,R.activities.K (K.code s)=0)(q:ℕ):= born B (plank R) (0:Site n) (fjords h) q
lemma upstreams (H:History G)(N p:ℕ) (K: Keeper (H.rep N p N).p (H.rep N p N).activities) (h:∀ s,(H.rep N p N).activities.K (K.code s)=0)(q:ℕ): (summit F B H N p K h q).plays=toper F B (H.rep N p N) K h q:=rfl
end YM.Planned.GuardedAtom.Guard
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{a b:Side}{L:Rep G a}{R:Rep G b}(P:Plate F a b)(K: Keeper L.p L.activities)
def collectP (A:∀ v:Motion,R.activities.Moves v.1 0)(Y:F.Index→File G a): F.Coeff→ Coefficient F b:= pencil (code (Tally F)) (fun i:Tally F=> audition (A i.1) (gather P K (book (Size.axis F i.2) (Y i.2)) i.2)) (chips F)
variable {B:SectionData F}{H:History G}{V0:Hol G}{N p m:ℕ}{D:Desk G (H.S.side (m+1) p)}(hw:Well (H.rep N p (m+1)) D (Real.sqrt (H.levels.clock.forcedAllowance (m+1))))
lemma venture (T: Tool F H N p m) (V: Voice F H p (m+1))(h:Heard B H N p V0 (m+1) V): Gram.point T (measure h T.up hw)= collectP T.plate T.up T.whirl (fun i=>capture (V.plays (V.index.symm (Size.axis F i))) T.up):=rfl
-- explicit M.P.P.Field.Open Real Branch to ded.fin.Proof.
end YM.MergeProof.Matric
#print axioms YM.MergeProof.Matric.venture
#print axioms YM.Planned.GuardedAtom.Guard.upstreams
