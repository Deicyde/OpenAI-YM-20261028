import YM.RG08.Yamen.Starter

/-! # kfalt transfer to Pair.turnstile. Coaf beds differ but chart is SAME. !-/
noncomputable section
namespace YM.RG08.Yamen
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Filter
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {O:Type}{G:Gauge}{a:Levels G}{F:Horizon a}{P X:MapPrices}(hg:G.Simple){Z:ChartRatio G}{W:Rate.Stair O}{E e r:ℕ}
variable (K:Wheelhouse a E W ) (L:Supplies F P Z ) (hM:Bill G P X a ) (hE:Yamen.Funds P X Z a W)
variable {N:O→ℕ}(hi:∀ i:O,W.top i ≤ N i)
local notation "TT"=>Yamen.charter P X Z K
local notation "R"=>Yamen.caliph F X hg Z K

def Earn (F:Horizon a ) (W:Rate.Stair O ) (X:MapPrices ) (N:O→ℕ):=∃ p,(kiosk W).cheap p ∧∀ i:Haven W,
 let x:=a.clock.J i.m;RowCost (Flat.curve X x) 1 (Cell.changeK (F.H (N i.x) i.m) (F.H (W.top i.x) i.m)) (p i)

-- all ingredient receipts. V and V' Vows elsewhere, differences here.
include hM hE
lemma billings (h:W.Admits ) (ht:Earn F W X N ) (he:e ≤ E ) (hr:Live r e ) (hn:0<e):
 let S0:=(R W.top (fun _=>le_rfl) L).side; let S1:=(R N hi L).side
 ; let v:=needs (TT).warp e r
 ; ∃ d,(turnstile W).cheap d ∧ FairT (D:=turnstile W ) (G:=G ) (Γ:=(TT).patch) (K:=a.clock.kernel) S0.fine S1.fine v d:=by
 intro S0 S1 v;obtain ⟨p,hp,hx⟩:=ht;let d(i:Run W):=p i.high
 have hd:(turnstile W).cheap d:= (highString h).glow _ hp
 let k:=a.clock.kernel;let f:=Yamen.seniors a (W:=W)
 have hT (N:O→ℕ ) (hs:∀ i,W.top i ≤ N i):∀ i:Run W,Cell.Warm G k ((TT).patch i) (F.H (N i.x) (i.m+1)) (RG08.Supplies.PlanCurve G k P (f i)) (RG08.Supplies.planSupply G k P (f i) (((TT).patch i).L)):=fun i=> warms L.housed _ _ (shoulders N hs i)
 have h0 (N:O→ℕ ) (hs:∀ i,W.top i ≤ N i ) (i:Run W): (∃ u: Clip,∀ n,Floor (F.H (N i.x) (i.m+1)) u n (P.η (f i)) (P.Ω (f i)))∧ (F.H (N i.x) (i.m+1)).metric.strip (P.α (f i)) (P.Ω (f i)):=⟨⟨_,L.housed.all _ _ (shoulders N hs i)⟩,(L.housed.rows _ _ (shoulders N hs i)).2.1⟩
 refine ⟨d,hd,?_⟩
 apply arms (P:=P ) (Q:=X) Z (p:=pay P X Z a) (lowString.golf _ hE) (fun i=>postpaid ..)
    (hT W.top (fun _=>le_rfl)) (hT N hi) (fun i=> (h0 W.top (fun _=>le_rfl) i).1) (fun i=>(h0 N hi i).1) (fun i=>(h0 W.top (fun _=>le_rfl) i).2) (fun i=>(h0 N hi i).2) (fun i=>Flat.Ω_pos L.housed (i.m+1))
    (fun i=> ((commerce (e:=e) (r:=r) K hM hE he hr hn ).roof i|>.1)) -- need fun
    ?_ (tiny _ hd) (fun i=>hx i.high)
 intro i
 exact (honesty_small G P X k (a.clock.J i.m) e).trans (warmth (i:=a.clock.J i.m) (j:=a.clock.J (i.m+1)) (stepN i.m))

-- rotation origin differences cheaper. Needed any level for top edge. Compare BOTH via root paid. Reuse seats_diff (uses strip & Floor). Need control Ω used and d receipt; endpoint explicit any side including n=N. -/
omit hM hE in
include L in
lemma basis_update {w:ℝ}{i:ℕ}{n m:ℕ}(ht:i ≤ n ) (hv:i ≤ m ) (he:RowCost (Flat.curve X (a.clock.J i)) 1 (Cell.changeK (F.H m i) (F.H n i)) w ) (hd:0≤w):
 let H:=lamp P X a i; let A:=base P X a i (F.H n i);let B:=base P X a i (F.H m i)
 ; Held (carpet _) (H.coats 0 0) (H.cash 0 0*(Cast.tax G 1*w)) (A-B):=by
 intro H A B
 let j:=a.clock.J i
 have hσ: H.need 0 0 ≤ P.α j:= (zeal (P:=P ) (X:=X ) (a:=a) i).2.trans (min_le_right ..)
 have hz: H.need 0 0 ≤ Flat.curve X j:=by apply (honesty_small G P X a.clock.kernel j 0).trans;exact (min_le_right ..).trans ((min_le_left ..).trans (min_le_right ..))
 have hx (N ) (hi:i ≤ N): (F.H N i).metric.strip (H.need 0 0) (P.Ω j):=fun p q=> ((L.housed.rows _ _ hi).2.1 p q).mono hσ le_rfl
 let D:=F.H n i;let D':=F.H m i
 have hH:= Cast.seats_diff D' D (G:=G) (hx _ ht) (hx _ hv) (L.housed.all _ _ ht) (L.housed.all _ _ hv) (fun b=>L.herald _ _ _ ht) (fun b=>L.herald _ _ _ hv) (H.tall 0 0) ((zeal (P:=P) (X:=X) (a:=a) i).2.trans (min_le_left ..)) (Flat.Ω_pos L.housed i) (H.tag 0 0) (he.mono hz) hd
 unfold A B base initial
 rw [←neg_sub] -- neg_sub gives? 
 exact hH.neg

omit hM in
private lemma heroic : (kiosk W).Good fun i=>(lamp P X a i.m).cash 0 0:= (kiosk W).hale _ _ hE (fun i=> ((lamp P X a i.m).tag 0 0).2.2.1) fun i=> (stamped G P X a.clock.kernel Z (RG08.Supplies.stone a i.m)).brew _ (a.fits.mono (by omega:i.m ≤ i.m+1)) 0 (by omega) 0 le_rfl
include L hi
omit hM in
lemma adjustC (ht:Earn F W X N): Wave (r:=0) (turnstile W) (coats (TT).warp 0 0) (fun i=>base P X a i.m (F.H (W.top i.x) i.m)) (fun i=>base P X a i.m (F.H (N i.x) i.m)):=by
 obtain ⟨v,hv,H⟩:=ht
 let D:=turnstile W
 have hU:D.cheap (fun x=>v x.low):=lowString.glow _ hv
 refine ⟨_, D.awe _ _ (D.moreover _ _ (lowString.golf _ (heroic (X:=X) hE)) (D.steady (Cast.tax G 1) (Nat.cast_nonneg _))) hU,fun i=> ?_⟩
 have he:= basis_update (X:=X) L i.admit.1.2 (i.admit.1.2.trans (hi _)) (H i.low) (tiny _ hv _)
 rw [mul_assoc]; exact he

omit hi L hM hE in
lemma zeroAngle {f:Haven W→ℝ}(h: (kiosk W).Good f)(hg:∀ i,f i=0∨i.m=W.top i.x) : (kiosk W).cheap f:=by
 change W.Fade (wide f)
 apply Rate.Stair.Fade.of_top h
 intro x i hi hj;rw [wide,dif_pos hi]; exact (hg _).resolve_right (Nat.ne_of_lt hj)
-- difference level-zero cost with exceptional N boundary polynomial from absolute. Wider aperture fresh. -/
omit hM in
lemma brace (ht:Earn F W X N):
 let C:=R W.top (fun _=>le_rfl) L;let C':=R N hi L
 ; Wave (r:=0) (kiosk W) (fun i=>apron (TT).yard 0 0 i.x i.m) (fun i=>C.current i.x i.m 0 0) (fun i=>C'.current i.x i.m 0 0):=by
 let c:=R W.top (fun _=>le_rfl) L;let t:=R N hi L
 obtain ⟨A,ha,H⟩:= realism hg K (X:=X) L (N:=W.top) (fun _=>le_rfl) hE;obtain ⟨B,hb,Tq⟩:=realism hg K (X:=X) L (N:=N) hi hE
 let D:= kiosk W;let f(i:Haven W):=if i.m=W.top i.x then A i+B i else 0
 have hG:D.Good f:= D.hale _ _ (D.hear A B ha hb) ?f1 ?f2
 case f1=>intro i;unfold f;split;exact add_nonneg (D.safe _ ha i) (D.safe _ hb i);exact le_rfl
 case f2=>intro i;unfold f; have hz:=D.safe _ ha i;have hf:=D.safe _ hb i;split<;>first|exact le_rfl|exact add_nonneg hz hf
 have hN:D.cheap f:=zeroAngle hG (fun i=>by unfold f;split<;>simp_all)
 obtain ⟨p,hp,hP⟩:=ht
 let g(i:Haven W):=(lamp P X a i.m).cash 0 0*(Cast.tax G 1 *p i)+f i
 have hf:D.cheap g:=D.lasts _ _ (D.awe _ _ (heroic (X:=X) hE) (D.awe _ _ (D.steady (Cast.tax G 1) (Nat.cast_nonneg _)) hp) ) hN -- multiplies order! heroic good * cheap inner; no nope
 intro c₀ c₁;refine ⟨g,hf,fun i=>?_⟩
 have ht:0 ≤ (lamp P X a i.m).cash 0 0*(Cast.tax G 1 *p i):= mul_nonneg ((lamp P X a i.m).tag 0 0).2.2.1 (mul_nonneg (Nat.cast_nonneg _) (tiny _ hp i))
 change Held _ ((lamp P X a i.m).coats 0 0) (g i) (fed F P X hg _ (W.top i.x) i.m 0 0 -fed F P X hg _ (N i.x) i.m 0 0) -- hg shadow
 rcases eq_or_lt_of_le i.admit.2 with he|he
 · unfold g f;rw [if_pos he];exact ((H i).sub (Tq i) (D.safe _ ha i) (D.safe _ hb i)).mono le_rfl (le_add_of_nonneg_left ht) (fun _=>le_rfl)
 unfold g f;rw [if_neg (Nat.ne_of_lt he),add_zero,cargo hg he, cargo hg (lt_of_lt_of_le he (hi _))]; exact basis_update L he.le (he.le.trans (hi _)) (hP i) (tiny _ hp i)
end YM.RG08.Yamen
