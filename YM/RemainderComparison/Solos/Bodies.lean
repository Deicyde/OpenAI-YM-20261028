import YM.RemainderComparison.Solos.Pub
/-!
# Loyalty to test address markings
 Needed only for uniform integrability near equality F.B.Flags. For all other uses
 preserve the real rendered leaves. `weight` is before probe restriction.
 Honors support, gauges and flags. Don't require a cost summable over tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Solos
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {θ ι : Type} {R₀ : θ→Type*} [∀ i, NormedAddCommGroup (R₀ i)] [∀ i,NormedSpace ℝ (R₀ i)]
variable {α:Type*}{G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Sleet Serif Typeface
variable (M:ι→Portrait R α) (y:α)
-- place : all tags of leaf (empty if dormant)
variable (M:ι→Portrait R (Audited R₀)) (place :ι→ Finset θ)(Hpc: ∀ (U:Config G f) i, LinearP (place i) (fun a=> ((brand M a i).ingredient U)))
local notation "V'" z:max=> brand M z
open scoped Classical

def mapWord (place :ι→ Finset θ) : Multiset ι →+ Multiset θ where
   toFun x:= x.bind (fun i=> (place i).val)
   map_add' := by intro a b; simp
   map_zero' := by simp
variable (y:Audited R₀)(X:Coat T F)(i:Drums (brand M y) S)
local notation "t" => mapWord place
local notation "q"=> t i.val.val
lemma notes (M :ι→ Leaf R) (v:Drums M S): t v.val.val=∑ i∈v.val,(place i).val:= rfl -- test
lemma shape (M:ι→ Leaf R)(p:Drums M S)(f:Leaf R→ℝ) : (∏ j∈ (team M p).own,f j)=∏ j∈p.val,f (M j):= by unfold team; dsimp only; rw [prod_image]; exact fun i hi j hj he=> p.prop hi hj (show sign M S i=sign M S j from by unfold sign; rw [he])
include Hpc
lemma syllabic (U:Config G f) : PaperP q (fun a=> (team (brand M a) i).ingredients U):=by
    unfold Team.ingredients; have hx(z:Audited R₀): (∏ j∈(team (brand M z) i).own,j.ingredient U)= ∏ j∈i.val,(brand M z j).ingredient U:= shape _ _ _
    simp_rw [hx,notes place]
    apply PaperP.stack
    intro k _ h; simpa only [mapWord,Finset.val_toFinset] using Hpc U k -- wrong simp
lemma words (p:Directions G f) (v:ℝ) : PaperP q (fun u=> (team (brand M u) i).paidU X v p):=by
    unfold Team.paidU; have hx(z:Audited R₀): (∏ j∈(team (brand M z) i).own,j.paidU X v p)= ∏ j∈i.val,(brand M z j).paidU X v p:= shape _ _ _
    simp_rw [hx,notes place]; apply PaperP.stack
    intro j _ hv; unfold Leaf.paidU Leaf.fond; let c':= X.enforce (2*v) p (X.plaza (areas R T 0 X.B ((brand M y j).turn.badge S)))
    have hz(z:Audited R₀): (brand M z j).turn=(brand M y j).turn:=rfl
    change LinearP (place j).val.toFinset (fun z=> (brand M z j).ingredient (X.input p)*c')
    simpa only [Finset.val_toFinset, mul_comm] using (LinearP.pitch c' (Hpc (X.input p) j))
lemma solar (V: Config G c)(p:Molecule S)(I':Finset (Bond f))(b:F.Slice G×Air f G) : PaperP q (fun a=> (team (brand M a) i).carat I' X V v Ñ p W r m b):=by
    let Y:= vary (X.wrapY b.1) V
    intro h; apply LinearP.pitch; unfold Team.floret
    -- rw common reach in lambda
    have he (z:Audited R₀): (team (V' z) i).signs S=i.reach:= Palette.label _ _
    simp_rw [he]; split_ifs; next he=>
      let c':= floating Y r R W Ñ (course (X.wrapY b.1) v R.beta b.2 V) (Matter.own p) m (p\i.reach)
      simp_rw [mul_comm _ (floating (vary _ _) _ _ _ _ _ _ _ (p\i.reach))]; exact LinearP.pitch _ (words M place Hpc y Y i _ _ h)
    next=> exact LinearP.nil _

lemma heat(X:Coat T F) (H:Cash W X.x μ L Q o C T R) (hr:X.width=o.K)(hp:X.manifest)(K: Finset ℕ) (p:Molecule S): PaperP q (fun a=> (team (brand M a) i).tithe X K W o.a Q.table Q.halo p):=by
    intro hv; apply LinearP.meal (F:=fun (v:F.Slice G × Air f G) a=> (team (brand M a) i).into X W o.a Q.table K Q.halo p v)
    · intro v
      unfold Team.into Team.premium
      have he (z:Audited R₀): (team (V' z) i).signs S=i.reach:= Palette.label _ _
      simp_rw [he]; split_ifs
      next h=> simp_rw [mul_comm _ ((X.wrapY v.1).term R Q.table W o.a K Q.halo v.2 (p\i.reach))] -- edit
               exact LinearP.pitch _ (words M place Hpc y _ _ _ _ hv)
      exact LinearP.nil _
    intro V; exact ((team (V' V) _).tip X K H hr hp p).2.1

set_option maxHeartbeats 500000 in
lemma act_h (p: Molecule S) (V: Config G c): PaperP q (fun a=> Palette.act (brand M a) H χ V p i):=by
    let X (r:Greenbelt.Reserve S):= prism T x χ o.K V (allot r)
    intro h; unfold Palette.act Team.lotus likely; apply LinearP.pitch; apply LinearP.seats (F:=fun r a=> (team (V' a) i).bloom (X r) W o.a Q.table Q.halo p)
    intro r _; unfold Team.bloom; split_ifs
    next=>
      unfold Team.steep likely; apply LinearP.pitch; apply LinearP.seats (F:=fun z a=> (team (V' a) i).tithe (((planted (X r) p)).taggedL z) (Matter.own p) W o.a Q.table Q.halo p); intro j _
      exact heat M place Hpc y i (((planted (X r) p)).taggedL j) H rfl (planted_valid (X r) p) (Matter.own p) p h
    next=> exact LinearP.nil _
end YM.RemainderComparison.Solos
