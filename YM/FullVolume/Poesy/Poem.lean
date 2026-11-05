import YM.FullVolume.Poesy.Dice
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
lemma treasury {a b:ℕ→ℝ}(h:Glints atTop a b) : ∃ v:ℝ,(∀ i,|a i| ≤ v)∧∀ i,|b i| ≤ v:=by
    obtain ⟨u,hA,hB⟩:=h; obtain ⟨C,hC⟩:=hA.abs.bddAbove_range; obtain ⟨D,hD⟩:=hB.abs.bddAbove_range; exact ⟨max C D,fun i=>(hC ⟨i,rfl⟩).trans (le_max_left ..),fun i=>(hD ⟨i,rfl⟩).trans (le_max_right ..)⟩
open Geo WilsonStartup
variable {M:Bank}(I:Depot Q o x μ L C₀ K)(T:Depot Q o x μ L C₀ H){χ:Chi}(R:∀ n,Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)
    {B: BudgetPoint}{v v':ℕ→ℝ}
structure Accord (K H:ℕ→ Epoch Λ) (B:BudgetPoint)(v v':ℕ→ℝ):Prop where
    fore:Sweep K
    tail:Sweep H
    mirror:Mirror K H
    tread:∃ a b' t,(∀ n,(K n).down.path.Bounds Λ.low a b' t)∧∀ n,(H n).down.path.Bounds Λ.low a b' t
    read: Soul atTop (fun i=>(K i).down) (fun i=>(H i).down)
    granted: Decent Λ.low B
    tends:Glints atTop v v'
    curve:Glints atTop (fun n=>(K n).beta) (fun n=>(H n).beta)
variable (h:Accord K H B v v')
lemma trep {ι:Type}[Fintype ι]{κ:Type}{f:ℕ→κ→ℝ}(h:Sparse f) :Sparse fun n(p:ι×κ)=> f n p.2:= sparking h
lemma tuneCue {D D' :ℕ→ℕ→ Atom G j} {g:Stave (n:=c)→RegularAddress c}{A A':ℕ→ℝ}(hp:Glints atTop A A')(h:Canopy B g (fun n=> tuneAtom (D n) 1) (fun n=> tuneAtom (D' n) 1)): Canopy B g (fun n=> tuneAtom (D n) (A n)) (fun n=>tuneAtom (D' n) (A' n)):=by
    obtain ⟨x,hx,hg⟩:=treasury hp; have hh:= h.repel hx hg hp.shrank
    have ht (g:ℕ→Atom G j) (p:Stave (n:=c)) (a:ℝ): tuneAtom g a p=a • tuneAtom g 1 p:=by ext U; unfold tuneAtom; dsimp only [Pi.smul_apply,smul_eq_mul]; ring
    simp_rw [show ∀ j, tuneAtom (D j) (A j)=_ from fun i=> funext fun p=> ht _ p _,show ∀ j, tuneAtom (D' j) (A' j)=_ from fun i=>funext fun p=> ht _ p _]; exact hh
include h in
lemma pathCue (n:Side): Canopy B (Song.strings (K 0).tubes.down B (n:=n)) (fun n=> Song.sounding (K n).down.path Λ.low (K n).beta (v n)) (fun n=> Song.sounding (H n).down.path Λ.low (H n).beta (v' n)) :=by
    obtain ⟨a,b,t,ha,hb⟩:=h.tread; let X:=h.granted; let Hn:=(h.curve.bin (Q:=fun i:ℝ=> -i) (fun _ _ => continuous_neg.continuousAt))
    refine Canopy.splices ?_ (Canopy.splices ?_ (Canopy.splices ?_ ?_));
    · have hp:=h.tends.bin (Q:=fun i:ℝ=> -i) (fun _ _ => continuous_neg.continuousAt); obtain ⟨x,hx,hS⟩:= treasury hp; have ht:= (Cad.lyric (c:=n) X ha hb h.read).repel hx hS hp.shrank
      have he (P: PathData G)(i:Tally n)(a:ℝ): tuneLow P Λ.low a i=a • tuneLow P Λ.low 1 i:=by ext U; unfold tuneLow; dsimp only [Pi.smul_apply,smul_eq_mul]; ring
      change Canopy _ _ (fun n i=> tuneLow _ Λ.low (-(v n)) i) (fun n i=>tuneLow _ Λ.low (-(v' n)) i); simp_rw [show ∀ n i, tuneLow _ _ _ _ = _ from fun (k:ℕ) (i:Tally n)=> he (K k).down.path i (-v k), show ∀ n i, _= _ from fun (k:ℕ) (i:Tally n)=> he (H k).down.path i (-v' k)]; exact ht
    · exact tuneCue (j:=3) (c:=n) Hn (Cad.herd (A:=fun n=> (K n).down.d3) (B':=fun n=>(H n).down.d3) (p:=B) (fun i=>(ha i).three) (fun i=>(hb i).three) (ha 0|>.width) (fun i j=> (ha i|>.invariant j).2.1) (fun i j=> (hb i|>.invariant j).2.1) h.read.2.2.1)
    · exact tuneCue (j:=4) (c:=n) Hn (Cad.herd (A:=fun n=> (K n).down.d4) (B':=fun n=>(H n).down.d4) (p:=B) (fun i=>(ha i).four) (fun i=>(hb i).four) (ha 0|>.width) (fun i j=> (ha i|>.invariant j).2.2) (fun i j=> (hb i|>.invariant j).2.2) h.read.2.2.2)
    exact tuneCue (j:=2) (c:=n) (g:=fun i=> pitch ((K 0).down.path.loop) i) (show Glints atTop (fun _=> (-1:ℝ)) (fun _=> -1) from ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩) (Cad.herd (A:=fun n=> (K n).down.d2) (B':=fun n=>(H n).down.d2) (p:=B) (fun i=>(ha i).two) (fun i=>(hb i).two) (ha 0|>.width) (fun i j=> (ha i|>.invariant j).1) (fun i j=> (hb i|>.invariant j).1) h.read.2.1)
lemma laurels {ι:Type}{A:ι→ RegularAddress c}{F K:ℕ→ι→ Config G c→ℝ}(h:Canopy B A F K) : Canopy B (revolve A) (fun i=> choir (F i)) (fun i=>choir (K i)):=by
    let v:= Song.Rim c*turnFee B; have hv : 0<v:=mul_pos (by unfold Song.Rim; positivity) (turnFee_pos _)
    have hg {F:ℕ→ι→ Config G c→ℝ}(a:PulseWise B A F):PulseWise B (revolve A) (fun i=> choir (F i)):=by
       obtain ⟨w,hw,h⟩:= a.sup
       refine ⟨fun n p=>CouplingShape.reg_scale _ (p.1.regular (a.chart n p.2)), _,(trep (ι:=Seat c) hw).climb hv.le, fun n p=>?_⟩
       refine CouplingShape.sup_larger (CouplingShape.sup_scale (Song.Rim c) (Song.transSup p.1 (a.chart n p.2) (h n p.2))) ?_
       rw [abs_of_nonneg (rim_nn _),←mul_assoc]
    -- generalize hg
    refine ⟨hg h.a,hg h.b,fun ⟨x,i⟩ e he=>?_⟩
    filter_upwards [h.sails i (e/v) (div_pos he hv)] with j hj
    have hh : choir (F j) (x,i)- choir (K j) (x,i)= Song.Rim c • ((F j i-K j i) ∘ x.view):=by unfold choir; rw [← smul_sub]; rfl
    change B.supBounds _ _ (choir (F j) (x,i)- choir (K j) (x,i)) e; rw [hh]; apply CouplingShape.sup_larger (CouplingShape.sup_scale (Song.Rim c) (Song.transSup x (CouplingShape.reg_sub (h.a.chart j i) (h.b.chart j i)) hj))
    rw [abs_of_nonneg (rim_nn _), ← mul_assoc]; change v*(e/v)≤e; field_simp; norm_num
end YM.ConnectedActivityE6.Lim
