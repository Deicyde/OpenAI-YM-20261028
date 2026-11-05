import YM.UVExtension.Wren.Pilfer
import YM.UVExtension.Wren.Oars
/-!
 Capped price+tightness at fixed volume. Real Slice earns; Armada only
 for tails of high-degree; for seats among each degree harvest by analytic
 on each first-stage occurrence, from Spin.Strata. Use this even if estimates
 Finance ledgers Reload vary wildly.
 -/
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
structure Choir (v:Filter ι) (T:ι→Tube G S)(H:∀ i,Cash w s q L Q U C (T i) (R i)) (k:ℕ) (χ:Chi) : Type where
   u : ℝ
   A : ℝ
   l : ℕ
   B : ℝ
   d : ℝ
   r : ℝ
   Z : ℝ
   Y : ℝ
   b : ℝ
   V : ℝ
   E : ℝ
   C' : ℝ
   d' : ℝ
   B' : ℝ
   t' : ℝ
   A' : ℝ
   a : ℝ
   q' : ℝ
   r' : ℝ
   k' : ℕ
   i : ℝ
   w' : ℝ
   laws : Score v T H k l χ A b u B Z r d Y V E
   sails : ∀ n, Captain (H n) k C' d' u t' A' a r' B' q' k' χ
   amasses : Armada Q L q w' s i B' k k'
namespace Choir
variable {H:∀ i:ι,Cash w s q L Q U C (T i) (R i)} (p:Choir v T H k χ)(h:StableR v R)
open Badge Song Strata
variable (j:ι)
include h p in
lemma stirs (t:ι):(H j).unionP=(H t).unionP:=funext (p.laws.riders h.toKept j t)
def casts (t:ι) := grass _ _ (p.stirs h j t)
def ice (t:ι):= dahlia _ _ (p.stirs h j t)
lemma via_ice (u z:Molecule S→Support c)(h:u=z)(x): (dahlia u z h x).val=x.val:= rfl
lemma ice_all (i:ι)(j':(H j).ThinP): (p.ice h j i j').val=j'.val:= via_ice _ _ (p.stirs h j i) j'
def tables (t:ι)(m:(H j).ThinP)(V:Config G c):= leaflet (H t) χ V (p.ice h j t m)
def rings (t:ι)(m:(H j).fragrances) (V:Config G c):= stream (H t) χ V (p.casts h j t m)
lemma landscapes (m:(H j).fragrances) (i:ι): perf (H i) (p.casts h j i m)=perf (H j) m:= perfed (p.stirs h j i) m
lemma tariffs (m:(H j).fragrances)(i:ι): coefficient (H i).seam (p.casts h j i m).2= coefficient (H j).seam m.2:= (costants (p.stirs h j i) m).symm

def sailsW (m:(H j).fragrances):= coefficient (H j).seam m.2/((m.1+1).factorial:ℝ)
lemma bridges (m:(H j).fragrances)(i:ι)(V:Config G c): rings p h j i m V=sailsW (H:=H) j m*∏ l, tables p h j i (m.2 l) V:=by
    rcases m with ⟨m,x⟩; unfold rings stream Gas.term; rw [p.tariffs h j ⟨m,x⟩]; unfold sailsW; -- batches repr fst
    have hz : (casts p h j i ⟨m,x⟩).fst=m:=rfl
    -- avoid dependent rewriting here
    let A (x:(H i).ThinP):= leaflet (H i) χ V x; let b:= coefficient (H j).seam x; let Z := ∏ l,p.tables h j i (x l) V; let P:= (p.casts h j i ⟨m,x⟩); have hV:(∏ l,A (P.snd l))=Z:=rfl
    change b*(∏ l,A (P.snd l))/(↑((P.fst+1).factorial):ℝ)= (b/((m+1).factorial:ℝ))*Z
    rw [hV,show P.fst=m from hz]; ring

variable (L':ι→Molecule S→ℝ) [NeBot v] (hr: Polish.Defines (v:=v) (H:=H) (χ:=χ) (k:=k) (u:=p.u) L')
def charm (i:ι)(m:(H j).fragrances):= |sailsW (H:=H) j m| * ( (∏ l,L' i (m.2 l).val) * (1+((m.fst+1:ℕ):ℝ))^(k)) -- `(1+...).-. notation nat/real fix with casts
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
-- direct low bound, arity power k. not used for high tails. use full V all for fixed S.
omit [FiniteDimensional ℝ E] [NeBot v] in
lemma herald (i:ι)(V V':Config G c)(b:(H i).ThinP): leaflet (H i) χ V b=Pond.likely (fun v:Greenbelt.Reserve S=> Stained.fringe (vary (prism (T i) s χ U.K V' (Greenbelt.allot (S:=S) v)) V) w U.a b.val (R i) Q.table Q.halo):=by
    unfold leaflet; refine congr_arg Pond.likely (funext fun v=> ?_); rw [show vary _ V=prism (T i) s χ U.K V (Greenbelt.allot (S:=S) v) from rfl]
-- avoid reducibility bills between type-indexing and dependent masks
omit [FiniteDimensional ℝ E] [NeBot v] in
lemma songB (Y:Molecule S)(i:ι)(z:(H i).ThinP)(he:z.val=Y)(P':Config G c)(V':Config G c): leaflet (H i) χ V' z=Pond.likely (fun v:Greenbelt.Reserve S=> Stained.fringe (vary (prism (T i) s χ U.K P' (Greenbelt.allot (S:=S) v)) V') w U.a Y (R i) Q.table Q.halo):= he ▸ herald i V' P' z
omit [FiniteDimensional ℝ E] [NeBot v] in
lemma coins (i:ι)(V V':Config G c)(b:(H j).ThinP): tables p h j i b V'=Pond.likely (fun v:Greenbelt.Reserve S=> Stained.fringe (vary (prism (T i) s χ U.K V (Greenbelt.allot (S:=S) v)) V') w U.a b.val (R i) Q.table Q.halo):=by
   unfold tables; exact songB (H:=H) (χ:=χ) b.val i (p.ice h j i b) (p.ice_all h j i b) V V'
include h p hr
set_option maxHeartbeats 200000 in
omit [NeBot v] in
lemma resonance : ∀ᶠ i in v,∀ (m:(H j).fragrances) (V:Config G c), Healthy (temp s) (perf (H j) m) V→ Ore V (rings p h j i m) p.u (charm (H:=H) (k:=k) j L' i m) k:=by
   filter_upwards [hr.laws] with i hi m V hv E _ _ _ X τ ht hT
   let J:(Option (Fin m.fst))→ℝ:=fun l=> L' i (m.2 l).val; let b l z:= tables p h j i (m.2 l) (X z)
   have hLi l : Brush k (J l) 1 (b l) τ:=by
      letI : Nonempty (Tree.Forest S.ratio) := Tree.select S.ratio S.patch.odd_side
      let y v:= prism (T i) s χ U.K V (Greenbelt.allot (S:=S) v); let K:= (m.2 l).val
      have hh: Healthy (temp s) ((H i).unionP K) V := p.laws.riders h.toKept j i K ▸ Finset.disjoint_of_subset_left (Finset.subset_biUnion_of_mem ((H j).smallAt ∘ m.2) (mem_univ l)) hv
      let U' v r:= Stained.fringe (vary (y v) (X r)) w U.a K (R i) Q.table Q.halo
      have hs: b l=(fun r=> Pond.likely (fun v:Greenbelt.Reserve S=> U' v r)):=funext fun r=> p.coins h j i V (X r) (m.2 l)
      rw [hs]; refine Captain.avgBrush (fun v z=> Stained.fringe (vary (y v) (X z)) w U.a K (R i) Q.table Q.halo) _ _ (fun o=> (hi K _ (y o) rfl rfl rfl).2 E X τ (m.2 l).prop.2 hh ht hT)
   let f:= fun y=>∏ l, b l y; have hp := ((Brush.all_prod Finset.univ b J (fun _=>1) (fun _ _=> hLi _)).trim).smul (sailsW (H:=H) j m)
   apply Brush.shimmy (hp.climb ?_ le_rfl)
   · filter_upwards with t'; exact p.bridges h j m i _
   unfold charm; simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_option,Fintype.card_fin,mul_one]; exact le_rfl
omit hr in
lemma smoothB (P:BudgetPoint) (hp:P.threshold=temp s)(hf:P.order≤k) (m:(H j).fragrances)(i:ι): P.Regular (perf (H j) m) (rings p h j i m) :=by
   have hx:= ((p.sails i).gloryBudget (p.casts h j i m) P hp hf).2.1; rw [← p.landscapes h j m i]; exact hx
lemma hymns (D:(H j).fragrances→ RegularAddress c) (hd:∀ m,(D m).support=perf (H j) m) (P:BudgetPoint)(hp:P.threshold=temp s)(hu:P.order ≤ k) : ∃ C>0, ∀ᶠ i in v,∀ (m:(H j).fragrances), P.supBounds (D m).site (D m).support (rings p h j i m) (C*charm (H:=H) (k:=k) j L' i m) :=by
    let t:=∑ x:Site c,∑ y:Site c,(separation x y:ℝ); have he: ∀ x y:Site c, (separation x y:ℝ)≤t:=by
        intro x y; refine le_trans (single_le_sum (f:=fun y=> (separation x y:ℝ)) ?_ (s:=Finset.univ) (mem_univ y)) (single_le_sum (f:=fun x=> ∑ y:Site c,(separation x y:ℝ)) (fun z _=> by positivity) (mem_univ x)); exact fun _ _=>Nat.cast_nonneg _
    let c':=1+t; have ht : 1≤c':= le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=> by positivity))
    have hS:Sailor G P.threshold p.q' k:= by rw [hp]; exact ⟨fun C _ h=> (p.sails j).weigh.stroke C _ (h.trans (p.sails j).talent)⟩
    let C:=c'^(P.power*k); have hC:0<C:=pow_pos (zero_lt_one.trans_le ht) _
    obtain ⟨B,hB⟩:= hr.swift.books; refine ⟨C,hC,?_⟩
    filter_upwards [hB,p.resonance h j L' hr] with i hx hg m
    rw [hd]; refine ⟨mul_nonneg hC.le ?_,fun Y hy=>?_⟩
    · unfold charm; apply mul_nonneg (abs_nonneg _); refine mul_nonneg (Finset.prod_nonneg (fun i _=> hx.1 _)) (by positivity)
    intro l hl hq; exact costsD (p.smoothB h j P hp hu m i).sites hS (p.sails j).income _ _ (p.sails j).near (hg m Y (hp ▸ hy)) (fun i hi=>add_le_add_right (he i _) _) ht l (hl.trans hu) hq
end Choir
end YM.UVExtension.Wren
