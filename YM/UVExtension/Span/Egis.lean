import YM.UVExtension.Span.Clocked
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Span
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}

structure Kept (R : ι→ Rep G n):Prop where
    chan : ∀ i j,(R i).p=(R j).p
    labels : ∀ i j,(R i).activities.forced=(R j).activities.forced ∧(R i).activities.reg=(R j).activities.reg
structure StableR (v:Filter ι)(R:ι→ Rep G n): Prop extends Kept R where
    beta : ∃ t,Tendsto (fun i=>(R i).beta) v (𝓝 t)
    alongK : ∃ K, Swift v K∧ ∀ᶠ i in v,∀ z X, |(R i).activities.K z X|≤ K i z
    alongE : ∃ K, Swift v K∧ ∀ᶠ i in v,∀ z X, |(R i).activities.regularOccurrence (R i).p z X| ≤ K i z
    right (j:ℕ)(ε:ℝ)(h:0<ε): ∀ᶠ n in v ×ˢ v,∀ X, dist ((R n.1).activities.K j X) ((R n.2).activities.K j X) ≤ ε ∧ dist ((R n.1).activities.regularOccurrence (R n.1).p j X) ((R n.2).activities.regularOccurrence (R n.2).p j X)≤ ε
namespace Kept
variable {R:ι→ Rep G f}
lemma chores (p:Kept R) (i j:ι)(A:Support f)(L:Finset ℕ): Contract.order (R i) L A= Contract.order (R j) L A :=by unfold Contract.order Contract.charges Contract.covered; simp_rw [(p.labels i j).1,p.chan i j]
lemma charged (p:Kept R)(i j:ι)(L:Finset ℕ)(Z:Config G f): Contract.charges (R i) L Z= Contract.charges (R j) L Z:=by unfold Contract.charges Contract.covered; rw [(p.labels i j).1,p.chan i j]
lemma phalanx (p:Kept R)(T:ι→Tube G S)(u v:ℕ) (i j) : Matter.troupe (T i) (R i) u v= Matter.troupe (T j) (R j) u v:=by unfold Matter.troupe Contract.sealed Contract.incidence; rw [(p.labels i j).1]
end Kept
namespace StableR
open Concerted
variable (YV:StableR v R) 
variable {Y:κ→ Config G f}
variable {t:κ→ Bool→ι}(h:∀ b,Tendsto (fun n=>t n b) qq v)
include h YV
lemma pricesBet : Together qq (fun n b=> (R (t n b)).beta):=by obtain ⟨k,hk⟩:= YV.beta; exact pairsHere _ k (fun i=> hk.comp (h i))
lemma real_arrays (i:ℕ)(Y:κ→ Config G f) : Together qq (fun n b=> (R (t n b)).activities.K i (Y n)) ∧ Together qq (fun n b=> (R (t n b)).activities.regularOccurrence (R (t n b)).p i (Y n)):=by
   obtain ⟨W,hW,hV⟩:= YV.alongK; obtain ⟨F,hF,hY⟩:=YV.alongE; obtain ⟨r,hr⟩:=hW.books; obtain ⟨s,hs⟩:=hF.books
   have ht (ε:ℝ)(hp:0<ε): ∀ᶠ n in qq, ∀ X, dist ((R (t n true)).activities.K i X) ((R (t n false)).activities.K i X) ≤ ε ∧ dist ((R (t n true)).activities.regularOccurrence (R (t n true)).p i X) ((R (t n false)).activities.regularOccurrence (R (t n false)).p i X) ≤ ε:= ((h true).prodMk (h false)).eventually (YV.right i ε hp)
   have hK := eventually_all.mpr (fun i=> (h i).eventually (hV.and (hr.and (hY.and hs))))
   constructor
   · refine Together.of_cap _ ⟨r,hK.mono fun n hn i'=> ((hn i').1 i _).trans (budget_single (hn i').2.1 _)⟩ (fun ε he=>(ht ε he).mono fun n hn=>?_)
     exact (hn _).1
   refine Together.of_cap _ ⟨s,hK.mono fun n hn i'=> ((hn i').2.2.1 i _).trans (budget_single (hn i').2.2.2 _)⟩ (fun ε he=>(ht ε he).mono fun n hn=>?_)
   exact (hn _).2
end StableR
namespace Score
open Oriented Vine Concerted Raw
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Score v T H k l χ A b u B N r d f' V Z) (J:Kept R)
include p
lemma upR (i) : (R i).path=(T i).up∧(R i).clip=(T i).high:= ⟨(H i).laws.intake.received.1,(H i).laws.intake.received.2⟩
omit p in
lemma lands {j:ℕ}{A C: ℕ→ Atom G j}(p:∀ i,(A i).leg=(C i).leg) (g:Lattice.Ratio c f)(L B:ℕ) : Raw.atomFoot g L B A= Raw.atomFoot g L B C ∧ Raw.atomCharge (f:=f) A= Raw.atomCharge C:=by
    unfold atomFoot Atom.footprint Atom.stencil atomCharge Atom.length; simp_rw [p]; exact ⟨trivial,trivial⟩
omit p in
lemma edges {A B:PathData G}(h:∀ i j,(A.row i j).2=(B.row i j).2)(v:Ratio c f) (k n:ℕ): bothFoot v k n A=bothFoot v k n B∧ bothCharge (f:=f) A=bothCharge B:=by
   unfold bothFoot bothCharge pairFoot Paths.duplex; simp_rw [h]; exact ⟨trivial,trivial⟩
include J
lemma core (i j:ι)(V l:ℕ): Raw.forcedFoot S.ratio l V (R i)=Raw.forcedFoot S.ratio l V (R j) ∧ Raw.regularFoot S.ratio l V (R i)=Raw.regularFoot S.ratio l V (R j) := by
    unfold Raw.forcedFoot Raw.regularFoot; rw [(J.labels i j).1,(J.labels i j).2]; exact ⟨rfl,rfl⟩
lemma receipts (i j:ι)(B y:ℕ): Raw.space (T i) y B (R i)= Raw.space (T j) y B (R j)∧ Raw.extra (T i) (R i)=Raw.extra (T j) (R j) := by
    obtain ⟨s,A,h⟩:=p.views.cap; obtain ⟨t,C,hC⟩:=p.views.cap'; obtain ⟨h₁,h₂,h₃⟩:= h.layout i; obtain ⟨h₄,h₅,h₆⟩:= h.layout j
    obtain ⟨u,hv⟩:= edges (fun d z=> (h.slots i d z).trans (h.slots j d z|>.symm)) S.ratio y B
    obtain ⟨hx,hq⟩:= edges (fun d z=> (hC.slots i d z).trans (hC.slots j d z|>.symm)) (Raw.atOne c) y B
    obtain ⟨he,hE⟩:= lands (fun x=> (h₁ x).trans (h₄ x|>.symm)) S.ratio y B
    obtain ⟨ha,hA⟩:= lands (fun x=>(h₂ x).trans (h₅ x|>.symm)) S.ratio y B
    obtain ⟨hl,hL⟩:= lands (fun x=> (h₃ x).trans (h₆ x|>.symm)) S.ratio y B
    have hh:regularExtra (R i)=regularExtra (R j):= by unfold regularExtra; rw [(J.labels i j).2,J.chan i j]
    unfold Raw.space extra; dsimp only; rw [(core p J i j B y).2, (p.upR i).1,(p.upR j).1,hh,u,hx,he,ha,hl,hE,hA,hL,hq,hv]; exact ⟨rfl,rfl⟩
lemma zones (i j:ι)(b d:ℕ): Matter.areas (R i) (T i) b d=Matter.areas (R j) (T j) b d := by unfold Matter.areas footprints; rw [(p.core J i j d b).1]; unfold roadway; rw [(p.receipts J i j d b).1]
lemma riders (i j:ι) (F:Molecule S): (H i).unionP F=(H j).unionP F:= congr_arg (F.biUnion ·) (zones p J _ _ _ _)
lemma chairs (P:Molecule S) {F:Forest S.ratio} (i j)(M: Hat G F) : Matter.standsIn (M.order (T i) s χ U.K) (R i) Q.halo P=Matter.standsIn (M.order (T j) s χ U.K) (R j) Q.halo P:=by
    unfold Matter.standsIn Matter.claimed Matter.ground Hat.order; dsimp only [Coat.B]; rw [zones p J i j, J.phalanx T]
end Score
end YM.UVExtension.Span
