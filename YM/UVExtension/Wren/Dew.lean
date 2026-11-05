import YM.UVExtension.Wren.Flys
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
open AnalyticBridge VerifiedReset Collection Quotes WilsonStartup Extra.Iteration Next.Scheduling
open Song Strata Gala Concert Geo
open Badge Chains Marlin Trio Slide Animals
namespace Gold
variable {A:ι→ Config G c→ℝ}(h:∀ i,P.Regular univ (A i))(hp:Tune v (fun n (x:Fly G c P)=> x.reel (A n)))
include h hp
lemma lenses : Tune v (fun n (x:Fly G c P)=> x.reel (Boulevard.stillA (A n))) :=by
   let f i (x:Fly G c P):= x.reel (fun _=> A i 1); have he: Tune v f:=by
       apply ((hp.cues (fun _=>Fly.star G P c)).mask (fun x:Fly G c P=> x.ls=[])).switch; filter_upwards with i; funext x
       unfold f Fly.reel; rw [Work.G07.left_const]; split <;> rfl
   refine (hp.sub he).switch (Eventually.of_forall fun i=> funext fun x=>?_)
   let z: RegularAddress c:=⟨0,univ,mem_univ _⟩; exact Eq.symm (VerifiedReset.left_sub (f:=A i) (g:=fun _=>A i 1) ((h i).smooth _ (x.taps z).live) contDiffAt_const x.lengthC)
lemma pins {κ w:ℕ}(p:κ+1≤w) (o:Site f)(K:2*κ ≤ c.val) : Tune v (fun n (x:Tap P G o (neighbors w o))=> x.read (Boulevard.stillA (A n) ∘ Slide.shape (Slide.cognac K) o)):=by
   let Z:=Slide.cognac K; let U:=Slide.shape Z o (K:=G.El); let F i:=Boulevard.stillA (A i); have hT i : P.Regular Finset.univ (F i):= CouplingShape.reg_sub (h i) (CouplingShape.reg_const _)
   let t:= Trio.tilt P w; have ht:0<t:= by unfold t Trio.tilt; positivity
   let D: RegularAddress c:= ⟨0,univ,mem_univ _⟩; have hz i: separation o (Slide.sites Z o i) ≤ w:= (Slide.village K o i).trans (by omega)
   obtain ⟨⟨r,hr⟩,hL⟩:= lenses h hp
   let V:= Tap P G o (neighbors w o)
   have hc (q: Config G c → ℝ)(b:ℝ)(hQ:P.Regular Finset.univ q)(hh:∀ x:Fly G c P,‖x.reel q‖ ≤ b)(x:V): ‖x.read (q ∘ U)‖ ≤ t*b:=by
       have he:flags P.threshold (U x.view)=∅:= Slide.allFlag Z o x.view _ (fun i=>(neighbors_mem ..).2 (hz i)) _ P.threshold_pos.le x.live
       exact Slide.stalled Z o q hz x.poll x.view x.card x.innerP (hQ.smooth _ (by unfold Healthy; rw [he]; simp)) (fun l hl hi=> hh ⟨U x.view,he,l,hl,hi⟩)
   have hM (n): P.Regular (neighbors w o) (F n ∘ U):= Slide.regular Z o (hT n) (fun i=> (neighbors_mem ..).2 (hz i))
   refine ⟨⟨t*r,hr.mono fun n hn x=>hc _ _ (hT n) hn x⟩,fun ε he=>?_⟩
   filter_upwards [hL (ε/t) (by positivity)] with n hn x
   have hF:=hc _ (ε/t) (CouplingShape.reg_sub (hT n.1) (hT n.2)) (fun r=> ?_) x; swap
   · refine (le_of_eq (b:=‖Fly.reel r (Boulevard.stillA (A n.1))-Fly.reel r (Boulevard.stillA (A n.2))‖) ?_).trans (hn r); apply congr_arg; exact VerifiedReset.left_sub (f:=F n.1) (g:=F n.2) ((hT n.1).smooth _ (show Healthy P.threshold _ _ from (r.taps D).live)) ((hT n.2).smooth _ (r.taps D).live) r.lengthC
   refine le_trans ?_ (le_of_eq (show t*(ε/t)=ε by field_simp)); refine (le_of_eq ?_).trans hF; apply congr_arg; exact (VerifiedReset.left_sub (f:=F n.1∘ U) (g:=F n.2 ∘ U) ((hM n.1).smooth _ x.live) ((hM n.2).smooth _ x.live) x.card).symm

omit h hp
variable {Qp:Stars→Side} {κ w:ℕ} (hq:∀ i:Stars,(Qp i).val=2*(κ+i.val))(hw:κ+5≤ w)(g:ι→ ∀ i:Stars,Trio.Offer G (Qp i))(hh:∀ i, Aside.Stars v P (fun n=> g n i))
include hq hh hw
-- Each UNIT sing on reborn lexicon
lemma standing (i:Stars) (x:Site (Qp i)) (u:Site c): Tune v (fun n (q:Tap P G u (neighbors w u))=> q.read (Trio.unit hq (Trio.rip (g n)) i x u)):= by exact pins (fun n=> (hh i).regular n x) ((hh i).small x) (by have hk:=i.isLt; omega) u (hq i).ge
lemma slides (i x) : Notes v P (Marlin.leap w (c:=c)) (fun n u=> Trio.unit hq (Trio.rip (g n)) i x u) :=⟨fun n u=>Trio.unit_m (B:=P) hq _ _ (fun i j=> (hh i).regular n j) (by omega) u i x, Transit.ready (fun u=> standing hq hw g hh _ _ u)⟩
lemma mirrored (o:Site c): Tune v (fun n w'=> Trio.unearned P hq w (Trio.rip (g n)) o w'):=by
   apply Tune.term; intro i hi; apply (Tune.constant _ (Slide.ray i) tendsto_const_nhds).mul; apply Tune.term; intro j hj
   exact (TransitM.under (slides hq hw g hh i j)).meters (emerge hq i j o)
lemma august : Notes v P (Marlin.leap w (c:=c)) (fun n u=> Trio.ornament hq (g n) u):=by
    let f i n (o:Site c):= ∑ j,Trio.unit hq (Trio.rip (g n)) i j o; have hf i n (o:Site c): P.Regular (neighbors w o) (f i n o):= Meadow.regularA _ (fun j _=> (slides hq hw g hh i j).available n o)
    have ht n (o:Site c): Trio.ornament hq (g n) o=∑ i:Stars,ray i • f i n o:=by ext; simp [Trio.ornament,Trio.beacon,f]
    simp_rw [ht]; refine ⟨fun i j=> Meadow.regularA _ fun z _=> CouplingShape.reg_scale _ (hf z i j), Transit.ready fun o=>?_⟩
    have hp(n)(x:Choir.onstage P (leap w) o G): x.read (∑ i:Stars,ray i • f i n o)=∑ i:Stars,ray i*x.read (f i n o):= x.staves _ _ _ fun i _=> hf i n o
    simp_rw [hp]; apply Tune.term; intro i hi; apply (Tune.constant _ (ray i) tendsto_const_nhds).mul
    have hZ (n)(x:Choir.onstage P (leap w) o G): Tap.read x (f i n o) = ∑ j,x.read (Trio.unit hq (Trio.rip (g n)) i j o):= Push.Local.left_sum _ _ _ _ (fun j _=> ((slides hq hw g hh i j).available n o).smooth _ x.live) x.card
    simp_rw [hZ]; exact Tune.term Finset.univ (fun j n q=> Tap.read q (Trio.unit hq (Trio.rip (g n)) i j o)) (fun j _=> standing hq hw g hh i j o)
end Gold
end YM.UVExtension.Wren
