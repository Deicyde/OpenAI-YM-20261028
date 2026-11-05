import YM.FullVolume.Renew.Reset
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
namespace Ledgers
open Geo WilsonStartup
variable {K H: ℕ→ Cad G} {σ C A:ℝ}{p:BudgetPoint}{b:Clip}{α κ v v':ℕ→ℝ} {X : Listing G c}{F T:ℕ→ Collection.Source G c}
lemma Twin.couple {a b c d:ℕ→ℝ}(h:Twin a b)(he:Twin c d) : Twin (a+c) (b+d):=by
    obtain ⟨r,ha,hb⟩:=h.bound; obtain ⟨s,hc,hd⟩:=he.bound; refine ⟨⟨_,fun i=>(abs_add_le ..).trans (add_le_add (ha i) (hc i)),fun i=> (abs_add_le ..).trans (add_le_add (hb i) (hd i))⟩,?_⟩; refine (zero_add (0:ℝ) ▸ h.goes.add he.goes).congr' (Eventually.of_forall fun _=>?_); dsimp only [Pi.add_apply]; ring
lemma Twin.prank {a b:ℕ→ℝ}(h:Twin a b)(c:ℝ) :Twin (fun i=>c*a i) (fun i=>c*b i):=by
    obtain ⟨v,hv,V⟩:= h.bound; refine ⟨⟨|c| *v,fun i=>?_,fun i=>?_⟩,?_⟩
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv _) (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (V _) (abs_nonneg _)
    simp_rw [←mul_sub]; simpa only [mul_zero] using h.goes.const_mul c
open Ovens Residual
variable (h:G.Simple)(h1:∀ n,(K n).path.Bounds b σ C A)(h2:∀ n,(H n).path.Bounds b σ C A)(hv:Soul atTop K H)(hk:Geo.Width p b σ)(hd: Decent b p) (he: Twin α κ)
variable (hE: Canopy p X.reg (fun i=>(F i).logRead) (fun i=>(T i).logRead))(hK: Angel (fun i=> (F i).hardRead) (fun i=>(T i).hardRead))
include h h1 h2 hd hv he hE
private lemma refunds : Canopy p (enlarges ∘ X.reg) (fun n i=> rebate (X.reg i) ((F n).logRead i)) (fun n i=> rebate (X.reg i) ((T n).logRead i)):=by
    have hm{F:ℕ→ Collection.Source G c}(hv:PulseWise p X.reg (fun i=> (F i).logRead)): PulseWise p (enlarges ∘ X.reg) (fun n i=> rebate (X.reg i) ((F n).logRead i)) :=by obtain ⟨v,hw,V⟩:=hv.sup; exact ⟨fun n i=>rebate_regular _ (hv.chart n i),_,hw.climb (loss_pos G p).le,fun n i=>rebate_sup _ h (hv.chart n i) (V n i)⟩
    refine ⟨hm hE.a,hm hE.b,fun i t ht=>(hE.sails i _ (div_pos ht (loss_pos G p))).mono fun n hn=>?_⟩
    let f:= hE.a.chart n i; let P:= hE.b.chart n i; have hp := rebate_sup (X.reg i) (f:= (F n|>.logRead i)-(T n|>.logRead i)) h (VerifiedReset.reg_sub f P) hn
    have hx : resetLoss G p*(t/resetLoss G p)≤ t:=by have hx:=loss_pos G p; field_simp; norm_num
    apply VerifiedReset.sup_le _ hx; rw [← (label_sub _ _ p.threshold _ p f P).1]; exact hp
set_option quotPrecheck false
local notation "χ"=> VerifiedReset.factor
private lemma surfaces (hp:Twin v v') : Canopy p (Collection.incoming X (K 0).path p) (fun n=> archive X (K n).path b (F n) (α n) (v n)) (fun n=>archive X (H n).path b (T n) (κ n) (v' n)):=by
    refine Canopy.splices (refunds h h1 h2 hv hd he hE) (Canopy.splices ?_ ?_)
    · have hh:=hp.prank χ; let W(n:ℕ):= χ*v n; let V(n:ℕ):= χ*v' n; obtain ⟨C,hv',hu⟩:=hh.bound; have hF:= (loch (c:=c) hd h1 h2 hv).repel hv' hu hh.goes
      have hx (d:ℝ)(R: PathData G)(i : Faces c): i.2.fresh R b 0 d ∘ Seat.view (G:=G) i.1=d • (i.2.fresh R b 0 1 ∘ Seat.view (G:=G) i.1):=by ext X; unfold Low.fresh; simp [Function.comp_apply,mul_assoc]
      change Canopy _ _ (fun n (i:Faces c)=> i.2.fresh ((K _).path) b 0 (W n) ∘ i.1.view) (fun n (i:Faces c)=> i.2.fresh ((H _).path) b 0 (V n) ∘ i.1.view); rw [show (fun n (i: Faces c)=>_)=_ from funext (fun n:ℕ=>funext (fun i:Faces c=> hx (W n) (K n).path i)), show (fun n (i:Faces c)=> _) = _ from funext (fun n:ℕ=>funext (fun i:Faces c=> hx (V n) (H n).path i))]; exact hF
    let F:=highEntry G (K 0).path (n:=c)
    let t n (i:Spikes c):= High.fresh (K n).path i.2 0 (χ*α n) (χ*v n) ∘ i.1.view; let w n (i:Spikes c):= High.fresh (H n).path i.2 0 (χ*κ n) (χ*v' n) ∘ i.1.view
    let x:=Equiv.prodSumDistrib (Seat c) ℕ ℕ
    have hx(y:Spikes c): x.symm (x y)=y:= x.symm_apply_apply y
    suffices hs:Canopy p (F ∘ x.symm) (fun i=>t i ∘ x.symm) (fun i=>w i ∘ x.symm) by
        have h':= hs.transI x.toEmbedding; simp_rw [Equiv.toEmbedding_apply,Function.comp_apply,hx] at h'; exact h'
    have hS:= (he.couple hp).prank (-1); let f n:= -(α n+v n); let f' n:= -(κ n+v' n); have hS:Twin f f':=by simpa [f,f'] using hS
    obtain ⟨B',hF,hB'⟩:=hS.bound
    have hg (a b:ℝ) {j:ℕ}(v : ℕ→Atom G j)(i:Stave (n:=c)): (fun U=> -(χ*a+χ*b)*(v i.2).unmasked (i.1.view U) 0)= (-(a+b)) • tuneAtom v 1 i:=by ext U; unfold tuneAtom; simp only [Pi.smul_apply,smul_eq_mul,mul_one]; ring
    refine Canopy.splices ?_ ?_
    · have hh:= (Cad.herd (c:=c) (p:=p) (A:=fun n=> (K n).d3) (B':=fun n=> (H n).d3) (fun i=> (h1 i).three) (fun i=>(h2 i).three) (h1 0|>.width) (fun i j=> (h1 i|>.invariant j).2.1) (fun i j=> (h2 i|>.invariant j).2.1) hv.2.2.1).repel hF hB' hS.goes
      convert! hh using 1
      · exact funext fun i=>funext fun j=> hg _ _ (K i).path.cubic j
      exact funext fun i=>funext fun j=> hg _ _ (H i).path.cubic j
    have hh:= (Cad.herd (c:=c) (p:=p) (A:=fun n=> (K n).d4) (B':=fun n=> (H n).d4) (fun i=> (h1 i).four) (fun i=>(h2 i).four) (h1 0|>.width) (fun i j=> (h1 i|>.invariant j).2.2) (fun i j=> (h2 i|>.invariant j).2.2) hv.2.2.2).repel hF hB' hS.goes
    convert! hh using 1
    · exact funext fun i=>funext fun j=> hg _ _ (K i).path.quartic j
    exact funext fun i=>funext fun j=> hg _ _ (H i).path.quartic j
include hk
private lemma maxima (hp:Twin v v'): Angel (fun i=> loses X (K i).path b p (F i) (α i) (v i)) (fun i=> loses X (H i).path b p (T i) (κ i) (v' i)):=by
    refine Angel.both ?_ (disused h1 h2 hv hk (he.prank χ) (hp.prank χ))
    have hx{F :ℕ→ Collection.Source G c}(hE:PulseWise p X.reg fun i=>(F i).logRead):Vented fun i j=>fault (X.reg j) ((F i).logRead j) p.threshold:=by
         obtain ⟨v,hv,V⟩:=hE.sup; exact ⟨_, hv.climb (loss_pos G p).le,fun n U k=> fault_sup _ h (hE.chart n k) (V n k) U⟩
    refine ⟨hx hE.a,hx hE.b,fun i b' hb=>(hE.sails i _ (div_pos hb (loss_pos G p))).mono fun n hn U=>?_⟩
    let F:= hE.a.chart n i; let H:=hE.b.chart n i
    apply le_trans (b:=resetLoss G p*(b'/resetLoss G p)); swap; · exact le_of_eq (by have hh:=loss_pos G p; field_simp)
    have h := fault_sup _ h (VerifiedReset.reg_sub F H) hn U; rw [(label_sub _ _ p.threshold _ p F H).2] at h; exact h
include hK
lemma tapu : let D:= shelves X (K 0).path p;
         let P n:= branch X (K n|>.path) b p (F n) (α n)
         let N n:= branch X (H n|>.path) b p (T n) (κ n)
         Canopy p D.reg (fun i=> (P i).regular) (fun i=> (N i).regular)∧ Angel (fun n=> (P n).logarithm) (fun n=> (N n).logarithm):=by
   intro A W J; let f n:= Averaging.delta (X.read (F n)); let g n:= Averaging.delta (X.read (T n)); have hp:Twin f g:= incomes h hE hK
   exact ⟨(surfaces h h1 h2 hv hd he hE hp).transI (numbering (EKey c)).toEmbedding,(maxima h h1 h2 hv hk hd he hE hp).forms (numbering (LKey c)).toEmbedding⟩
end Ledgers
end YM.ConnectedActivityE6.Lim
