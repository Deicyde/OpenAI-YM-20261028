import YM.UVExtension.Wet.Tunes
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wet
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady PhysicalNext.Repeat Lotus
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a ag u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Strata Strata.Polish Matrix MeasureTheory WithLp Shield
open Span Oriented Vine
open Polar Silica Shield Score Flux Matter
open Wren Wren.Choir Gala Badge Next.Foundations Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March Daisy Charity
variable [NeBot v][v.IsCountablyGenerated]{H:∀ i:ι,Cash w s q L Q U C (T i) (R i)}
variable {D:(i:ι)→ Lotus.Leaf (R i)}(p:Choir v T H k χ) (h:StableR v R)(g:Constant (v:=v) D)(j:ι)
local notation "P"=> H j
local notation "T!"=> p.sails j
local notation "X0"=> p.laws
variable (B':BudgetPoint)(hu:B'.order=k) (hp:B'.threshold=temp s)
local notation "P!"=> U
open Concert
-- receipts.Amnesty mined. from calendar.
structure Cooling (a:ℝ) : Prop where
   covers :0≤ a
   firm:foam Q L
   knows i: ∃ (A b q' t v Y r B g e:ℝ)(n:ℕ), Bikes Q L q s a e B k n∧ Daisy.tailCost L Q q s B e k n B'.power ≤ Daisy.poster Q L s∧ ∃ N:Captain (H i) k q' t v Y A b r B g n χ,Herd (H i) N.conduit A B n
variable (hs: Cooling (H:=H) (χ:=χ) (k:=k) B' a)(o:Site c)(hy:∀ i,o∈ (D i).crest.image S.ratio.parent)
local notation "Q0"=> froth p h j D
local notation "Y!"=> locus (D j) (H j) o
include hy p h g j hu hp hs
lemma reconciled (n:ι)(m:(H j).fragrances) : B'.Regular (locus (D j) (H j) o m) (froth p h j D m n):=by obtain ⟨A,b,q',t,v,Y,r,B,g',e,n',_,_,N,hN⟩:=hs.knows n; rw [← heights p h g j o m n]; exact scops (D n) (H n) N hN B' (hy n) hp hu.le (p.casts h j n m)
lemma untilM (o:Site c): ∃ w:ℕ→ℝ,Tendsto w atTop (𝓝 0)∧∀ (o:Site c),(∀ i,o∈ (D i).crest.image S.ratio.parent) →∀ Z:ℕ,∀ i:ι, ∃ f : (H j).fragrances→ℝ, SumBudget (fun x=> if Z < Sigma.fst x then f x else 0) (w Z) ∧ ∀ x,B'.supBounds o (locus (D j) (H j) o x) (froth p h j D x i) (f x):=by
    let p':=(R j).p; have hx i:(R i).p=p':=h.toKept.chan i j
    obtain ⟨W,hW⟩:= g.weightsC; let g'(i):= R i; let fW (x:Support f) := p'.mass x |W| * Real.exp (-Q.ε*coverNumber p'.B x)
    let v:= ∑ x:Support f, |fW x|; let k:=Daisy.poster Q L s
    have hv:0≤v:=sum_nonneg (fun i _=> abs_nonneg _)
    have hz i : (R i).p.mass (D i).crest (D i).weight*Real.exp (-Q.ε*coverNumber (R i).p.B (D i).crest)*k ≤ v*|k|:= by
       rw [hx]; let M:= (D i).crest; apply le_trans (mul_le_mul_of_nonneg_left (le_abs_self k) (mul_nonneg (mul_nonneg (Real.exp_pos _).le ((D i).profit)) (Real.exp_pos _).le)); apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); apply le_trans _ ((le_abs_self (fW M)).trans (Finset.single_le_sum (f:=fun x=>|fW x|) (fun _ _=> abs_nonneg _) (mem_univ M)))
       exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((hW i).trans (le_abs_self _)) (Real.exp_pos _).le) (Real.exp_pos _).le
    refine ⟨fun Z=> (1/2:ℝ)^Z*(v*|k|), ?_,?_⟩
    · simpa only [zero_mul] using! ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (show (1/2:ℝ)<1 by norm_num)).mul_const (v*|k|))
    intro o hy Z i; obtain ⟨A,b,p',t,u,Y,r,B,g',e,n',hB,hx,N,hN⟩:= hs.knows i
    obtain ⟨f,hf,hC⟩:= captors _ (H i) N hN B' o (hy i) hp hu hs.covers hB hs.firm hx Z; -- hu maybe n
    refine ⟨fun m=> f (Choir.casts p h j i m), mapsV (Choir.casts p h j i) _ _ _ ?_ (budget_loosen hC (mul_le_mul_of_nonneg_left (hz i) (by positivity))),fun m=>?_⟩ -- p syntax
    · intro m; rw [show (Choir.casts p h j i m).fst=m.fst from Choir.grassK ..]
    rw [← heights p h g j o m i]; exact (hf _).2
lemma lowP (Z:ℕ): ∃ f:ι→(H j).fragrances→ℝ,Swift v f ∧ ∀ᶠ i in v,∀ m:(H j).fragrances,m.fst ≤ Z → B'.supBounds o (locus (D j) (H j) o m) (froth p h j D m i) (f i m):=by
    obtain ⟨b,hb,hf⟩:= choirO p h g j o
    let t:=∑ x:Site c,∑ y:Site c,(separation x y:ℝ); have he: ∀ x y:Site c, (separation x y:ℝ)≤t:=by
        intro x y; refine le_trans (single_le_sum (f:=fun y=> (separation x y:ℝ)) ?_ (s:=Finset.univ) (mem_univ y)) (single_le_sum (f:=fun x=> ∑ y:Site c,(separation x y:ℝ)) (fun z _=> by positivity) (mem_univ x)); exact fun _ _=>Nat.cast_nonneg _
    let c':=1+t; have ht : 1≤c':= le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=> by positivity))
    have hS:Sailor G B'.threshold p.q' k:= by rw [hp]; exact ⟨fun C _ h=> (p.sails j).weigh.stroke C _ (h.trans (p.sails j).talent)⟩
    let C:=c'^(B'.power*k); have hC:0<C:=pow_pos (zero_lt_one.trans_le ht) _
    obtain ⟨B,hB⟩:=hb.books; refine ⟨_,(smallW p h j b hb Z).scales C hC.le,?_⟩
    filter_upwards [hf,hB] with i hi hb m hm; rw [if_pos hm]; refine ⟨mul_nonneg hC.le ?_,fun V hv l hl hx=> costsD (reconciled p h g j B' hu hp hs o hy i m).sites hS (p.sails j).income o _ (p.sails j).near (hi _ V (hp ▸ hv)) (Y:=c') (fun i _=> add_le_add_right (he i _) _) ht l (hu ▸ hl) hx⟩
    exact mul_nonneg (by positivity) (mul_nonneg (abs_nonneg _) (mul_nonneg (Finset.prod_nonneg fun i _=> hb.1 _) (by positivity)))
set_option quotPrecheck false
-- form minimal.P.L.Slots. no positivity wrapping assumption ever.K finite.
lemma choirC : Notes v B' (fun (i:(H j).fragrances)=> ⟨o,locus (D j) (H j) o i,seatY (D j) (H j) o (hy j) i⟩) (fun n m=> froth p h j D m n) :=by
    obtain ⟨w,hw,hf⟩:= untilM p h g j B' hu hp hs o hy o; let D' (i:(H j).fragrances):= Tap B' G o (locus (D j) (H j) o i)
    let X'(n)(m)(x:D' m):= x.read (froth p h j D m n); have hl ε(he:0 < ε): ∃ S:ℕ,∀ i:ι,∃ f:(H j).fragrances→ℝ, SumBudget (fun m=> if S < Sigma.fst m then f m else 0) ε ∧ ∀ m x, ‖X' i m x‖ ≤ f m:=by
       obtain ⟨x,hx⟩:=(hw.eventually_le_const he).exists; refine ⟨x,fun i=>?_⟩; obtain ⟨f,hf,hg⟩:= hf o hy x i; exact ⟨f,budget_loosen hf hx,fun m=>(tap_bound.mp (hg m)).2⟩
    -- Swift exact minimal.X bucket read.Cah.Nonempty D_i unneeded
    let f i m:= sSup (Set.range (fun u:Option (D' m)=> u.elim 0 (fun X=> ‖X' i m X‖)))
    have hr(i m):0≤ f i m∧ (∀ x, ‖X' i m x‖ ≤ f i m) ∧∀ a:ℝ, 0 ≤ a→ (∀ x,‖X' i m x‖≤ a)→ f i m ≤ a:=by
       obtain ⟨v,hv,ht⟩:= hf o hy 0 i; let g' (u:Option (D' m)):= u.elim 0 (fun X=> ‖X' i m X‖)
       have he: BddAbove (range g') := ⟨v m, forall_mem_range.mpr (fun i=> by cases i; exact (ht _).1; exact (tap_bound.mp (ht _)).2 _)⟩
       exact ⟨(show g' none ≤ f i m from le_csSup he ⟨_,rfl⟩),fun x=> le_csSup he ⟨some x,rfl⟩,fun a ha hb=> csSup_le (range_nonempty g') (forall_mem_range.mpr fun i=>by cases i; exact ha; exact hb _)⟩
    have hM(Z):∀ i, SumBudget (fun m:(H j).fragrances=> if Z < m.fst then f i m else 0) (w Z):=fun i=>by
       obtain ⟨a,hv,h⟩:= hf o hy Z i; refine budget_mono hv (fun j=>?_) (fun m=>?_); split; exact (hr ..).1; exact le_rfl
       split_ifs with hp; exact (hr i m).2.2 _ (h m).1 (tap_bound.mp (h m)).2; exact le_rfl
    have hL(Z):Swift v (fun i (m:(H j).fragrances)=> if m.fst ≤ Z then f i m else 0):=by
       obtain ⟨p,hp,hT⟩:= lowP p h g j B' hu hp hs o hy Z; apply hp.le; obtain ⟨b,hb⟩:= hp.books
       filter_upwards [hb,hT] with i hi h m; split; next hk=> exact ⟨(hr ..).1,(hr i m).2.2 _ (hi.1 _) (tap_bound.mp (h _ hk)).2⟩
       next hx=> exact ⟨le_rfl,hi.1 _⟩
    have hx : Swift v f:=by
       obtain ⟨c,hc⟩:= (hL 0).books; refine Swift.absorbs ⟨c+w 0, hc.mono fun i hi=> ?_⟩ ?_
       · have ht:=(budget_plus hi (hM 0 i)); convert! ht using 1; ext x; split_ifs <;> first |omega|simp_all only [add_zero,zero_add]
       intro ε hε; obtain ⟨Z,hZ⟩:= (hw.eventually_le_const hε).exists; refine ⟨_,_,hL Z, Eventually.of_forall (fun i=> budget_loosen (hM Z i) hZ), Eventually.of_forall (fun i m=>?_)⟩; split_ifs <;> first|omega|simp_all only [add_zero, zero_add, le_refl]
    obtain ⟨V,hV⟩:= hx.books; constructor; exact fun n m=> reconciled p h g j B' hu hp hs o hy n m
    refine ⟨⟨f,hx,Eventually.of_forall (fun n i=> (hr n i).2.1)⟩,fun m=> ⟨⟨V,hV.mono fun n hn x=> ((hr n m).2.1 x).trans (budget_single hn m)⟩,podium (p.sails j).income (p.sails j).near (show Sailor G B'.threshold p.q' k from ?_) (fun i=> fanfare p h g j m o ?_) hu.le⟩⟩
    · rw [hp]; exact ⟨fun C _ h=> (p.sails j).weigh.stroke C _ (h.trans (p.sails j).talent)⟩
    intro n; exact hp ▸ ((i n).live)
end YM.UVExtension.Wet
