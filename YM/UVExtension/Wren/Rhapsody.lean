import YM.UVExtension.Wren.Fables
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wren
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze March Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι} {P:BudgetPoint}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Matrix MeasureTheory WithLp Shield
open Span Oriented Vine PhysicalNext.Repeat PhysicalNext.Repeat.Match PhysicalNext.Repeat.Greenbelt Wick
open Polar Silica Shield Score Flux Matter Ursell Gas Trees Multiple Refrain

-- Captain leases come together with Score width for all L large and at any calendar.
-- regular-sector language for fixed-volume observability along the profile
structure Notes (v:Filter ι)(P:BudgetPoint)(A:κ→ RegularAddress c)(U:ι→κ→ Config G c→ℝ):Prop where
    available : ∀ i j,P.Regular (A j).support (U i j)
    invests : Transit v (fun n m (x:Choir.onstage P A m G)=>x.read (U n m))
namespace Choir
variable {H:∀ i:ι,Cash w s q L Q U C (T i) (R i)} (p:Choir v T H k χ)(h:StableR v R)
open Badge Song Strata Gala Concert Graph
variable (j:ι)(D:(H j).fragrances→ RegularAddress c) (hd:∀ m,(D m).support=perf (H j) m) (P:BudgetPoint)(hp:P.threshold=temp s)(hu:P.order ≤ k)
variable [NeBot v] [v.IsCountablyGenerated]

def wagtail (a:ι×ι) (b:Bool):ι:= if b then a.1 else a.2
lemma wig (b:Bool): Tendsto (fun i=> wagtail i b) (v ×ˢ v) v:=by cases b; exact tendsto_snd; exact tendsto_fst

def pathD (Y:κ→ Config G c) (i: Greenbelt.Reserve S)(t:κ): Hat G (Greenbelt.allot i):=⟨⟨∅,∅,∅⟩,Y t,Classical.arbitrary _,1⟩
include p h
lemma fable {X:ι×ι→ Config G c} (m:(H j).fragrances)(hx:∀ n, Healthy (temp s) (perf (H j) m) (X n)):
    Baton (v ×ˢ v) (fun n b=> rings p h j (wagtail n b) m) X p.u k:=by
    obtain ⟨V,Y,ht⟩:= Polish.entrance p.laws (p.sails j).position.le h
    intro E _ _ _ W t hW he
    let f l n b r:= tables p h j (wagtail n b) (m.2 l) (W n r)
    have hh i : Walt (v×ˢv) t k (f i) :=by
       letI :=Tree.select S.ratio S.patch.odd_side
       let g (l:Greenbelt.Reserve S) n b y:= Stained.fringe (vary (prism (T (wagtail n b)) s χ U.K (X n) (Greenbelt.allot (S:=S) l)) (W n y)) w U.a (m.2 i).val (R (wagtail n b)) Q.table Q.halo
       have ht' n b : Healthy (temp s) ((H (wagtail n b)).unionP (m.2 i).val) (W n (t n)):= p.laws.riders h.toKept j (wagtail n b) (m.2 i).val ▸ Finset.disjoint_of_subset_left (subset_biUnion_of_mem ((H j).smallAt ∘ m.2) (mem_univ i)) (hW n ▸ hx n)
       have hD (l : Greenbelt.Reserve S): Walt (v×ˢv) t k (g l):= Polish.tightR p.laws wig (pathD X l) he h (p.sails j).position.le V Y ht (m.2 i).val (m.2 i).property.2 ht' hW
       apply ((Walt.ready (Fintype.card (Greenbelt.Reserve S):ℝ)⁻¹).times (Walt.schedule Finset.univ g (fun i _=>hD i))).same
       filter_upwards with n b; filter_upwards with r; exact p.coins h j _ (X n) (W n r) (m.2 i)
    have hf(S:Finset _): Walt (v×ˢv) t k (fun n b y=>∏ i∈S, f i n b y):=by
       induction S using Finset.induction_on with
       | empty=> simpa using (Walt.ready (x:=t) (k:=k) (v:=v×ˢv) (1:ℝ))
       | insert i S hx h=> simp_rw [prod_insert hx]; exact (hh i).times h
    refine ((Walt.ready (sailsW (H:=H) j m)).times (hf Finset.univ)).same ?_
    filter_upwards with n b; filter_upwards with y; exact p.bridges h j m _ _
include hd hp hu
lemma sonnets : Notes v P D (p.rings h j):=by
    obtain ⟨C,hC,ht⟩:= p.harvest h j D hd P hp hu
    obtain ⟨B,hB⟩:=hC.books; refine ⟨fun i z=> by rw [hd]; exact p.smoothB h j P hp hu z i,⟨C,hC,ht⟩,fun m=> ?_⟩
    refine ⟨⟨B,(ht.and hB).mono fun n hn x=> (hn.1 _ _).trans (budget_single hn.2 _)⟩, podium (v:=v) (Z:=(D m).support) (o:=(D m).site) (f':=fun i=> rings p h j i m) (p.sails j).income (p.sails j).near (show Sailor G P.threshold p.q' k from ?_) (fun i=> fable p h j m ?_) hu⟩
    · rw [hp]; exact ⟨fun M _ h=> (p.sails j).weigh.stroke M _ (h.trans (p.sails j).talent)⟩
    intro n; exact (hp.trans rfl) ▸ hd m ▸ ((i n).live)
end Choir
end YM.UVExtension.Wren
#print axioms YM.UVExtension.Wren.Choir.sonnets
