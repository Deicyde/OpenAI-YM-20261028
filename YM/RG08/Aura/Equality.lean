import YM.RG08.Aura.Publisher
import YM.RG08.Yamen.Knot

/-! # Literal equality of curl transport, on cover from schedule signals and common tree invoice.
 Does NOT presume second precision profile agrees, gauge-only variation proved later from this.
-/
noncomputable section
namespace YM.RG08.Aura
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason Yamen Rows Filter Flat
open YM.Next.Free YM.Planned.PrimaryIntegral295 YM.RG08.Line Matrix
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}{I J:Type}

lemma coloring {S:Kernel I J}{σ p:ℝ}{L:Side}(h:RowCost σ L S p): RowCost σ L (prism G.ColorIndex S) p:=fun x j=> by
 rcases x with ⟨x,i,t⟩;rcases j with ⟨y,u⟩;by_cases hx:t=u
 · simpa only [prism,hx,if_true] using! h (x,i) y
 unfold prism;simp [bill,hx]

lemma smiling {S:Kernel I J}{σ p:ℝ}{L:Side}(h:ColCost σ L S p): ColCost σ L (prism G.ColorIndex S) p:=fun i j=> by
 rcases j with ⟨x,j,u⟩;rcases i with ⟨y,t⟩;by_cases hx:t=u
 · simpa only [prism,hx,if_true] using! h y (x,j)
 unfold prism;simp [bill,hx]

variable {σ p:ℝ}
-- forward pricing for independent one-form, t differences up to j-2.
lemma price (k:KernelChoices) (G:Gauge){i j :ℕ}(hi:4 ≤ i)(hj:4 ≤ j):∃ σ p,0<σ∧0<p∧∀ (W:Flight i j)(w:List Axis),w.length ≤ i-2→
 RowCost σ W.L (prism G.ColorIndex (install (advanceC W.L (Carrier.linesOf W k.penalty) w))) (Real.exp (4*σ)*p/(W.L.val:ℝ)^(1+w.length)):=by
 obtain ⟨x,v,hx,hv,H⟩:= Carrier.priced k.penalty k.penalty_pos hi hj
 refine ⟨x,v,hx,hv,fun i w hh=>?_⟩
 convert coloring (G:=G) (cross_row (H i w hh) hx.le le_rfl) using 1;ring
-- complete cover curl, colored identity, witnessed on actual cofinal period using extracted for the independent tower.
variable {a:Levels G}{H:Horizon a}{P:MapPrices}(hH:H.Suffices P)(h:licensed a H){N m:ℕ}(hM:m<N){J:Type}

def heat (G:Gauge):= prism G.ColorIndex (plain (cobound 1))
def oracle (G:Gauge)(a:Levels G)(N m:ℕ):Kernel (Loc G 1) (Loc G 1):=prism G.ColorIndex (install (Carrier.linesOf (destination a N m) a.clock.kernel.penalty))
abbrev rootK(G:Gauge)(a:Levels G)(H:Horizon a)(N m:ℕ):Kernel (Loc G 1) (Loc G 1):=Cell.plotted (RG08.Supplies.stone a m) a.clock.kernel G (H.H N (m+1))

private lemma price_left {σ C:ℝ}{L:Side}{K: Kernel (Loc G 1) (Loc G 1)}(he:RowCost σ L K C)(hc:0≤C)(hσ:0<σ):∃ p:ℝ, RowCost 0 L (Pert.Bulk.bind (heat G) K) p := by
 have H {σ p:ℝ}(h:(cobound 1).strip σ p)(he:0≤σ)(hp:0≤p):∃ t:ℝ, RowCost 0 1 (heat G) t ∧ 0 ≤ t:=⟨p,coloring (G:=G) (RowCost.mono (plain0 h le_rfl).1 he),hp⟩
 obtain ⟨p,hp,hP⟩:= H Flat.lineA_props.2 zero_le_one Flat.lineA_props.1
 exact ⟨_,row_block hP hc hp he (fun x y z=> by simp only [zero_mul,zero_add]; exact mul_nonneg hσ.le (delta_nonneg ..))⟩
private lemma arch {r s:ℕ}{K:Kernel (TypeFace r) (TypeFace s)}{f t:Side}{A:Matrix (Body r f) (Body s t) ℝ}(h:Matches K A): Matches (prism G.ColorIndex K) (patron G A):=by
 intro ⟨x,n,t⟩ ⟨a,b,u⟩
 have he:= prism_match (T:=K) G.ColorIndex h (x,n,t) (a,b,u); have ht:=Line.patron_cell G A (wrap f x,n) (a,b) t u; dsimp only; rw [show patron G A _ (a,b,u)=_ from ht]
 by_cases htu : t = u <;> simpa [htu] using he
-- lens defines H.Suffices -> Warm p k n earlier
include hM h hH
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 450000 in
lemma equality: Pert.Bulk.bind (heat G) (rootK G a H N m) = Pert.Bulk.bind (heat G) (oracle G a N m):=by
 let L:=a.S.block m;let γ:=a.clock.kernel;let j:=a.clock.J (m+1)
 let B:= H.H N (m+1);let p:=RG08.Supplies.stone a m
 have hW:=Yamen.warms hH N m hM
 let σ:=RG08.Supplies.PlanCurve G γ P j;have ht:0<σ:= (RG08.Supplies.plan_hr G γ P j).1;have hσ:σ≤1:= (RG08.Supplies.plan_hr G γ P j).2.1
 let q:= RG08.Supplies.planSupply G γ P j L
 have hp:Cell.Warm G γ p B σ q:=hW
 have he:= RG08.Supplies.outbound hp (θ:=σ) ht.le le_rfl hσ
 obtain ⟨u,c,hu,hc,Hc⟩:=price γ G (a.clock.adm (m+1)) (a.clock.adm m)
 let D:=destination a N m;let x:=oracle G a N m;let y:=rootK G a H N m
 have hx : RowCost u L x ((Real.exp (4*u)*c)/(L.val:ℝ)^1) := Hc D [] (Nat.zero_le ..)
 have hy : RowCost σ L y (Cell.laneTax L*(q*Cell.key G p γ)):=he.2.row -- name
 have hp0:0 ≤ Cell.laneTax L*(q*Cell.key G p γ) :=by
    have hv:0≤q*Cell.key G p γ:= (Cell.predictor_price p γ G B hp ht.le hσ).pos
    unfold Cell.laneTax; positivity
 obtain ⟨X,hX⟩:=price_left hx (by have hL:=L.property;positivity) hu
 obtain ⟨Y,hY⟩:=price_left hy hp0 ht
 let s (t):=a.S.side m t;let f(t):= a.S.side (m+1) t
 let T (t):=a.clock.op m t
 let K (t):=Bloch.installed (T t).ratio (Carrier.linesOf D γ.penalty)
 let M (t:ℕ):Matrix (Lines G (f t) 2) (Lines G (s t) 1) ℝ:= patron G (((cobound 1).acts (f t))* (extracted (T t) (Line.green (T t)) (K t)))
 let hA(t):Matrix (Lines G (f t) 1) (Lines G (s t) 1) ℝ:= patron G (K t)
 have hK t:Matches (oracle G a N m) (hA t):=arch (matches_install (g:=(T t).ratio) (Carrier.linesOf D γ.penalty))
 have hE t:Matches (heat G) (shaded (f t) (f t) G.ColorIndex ((cobound 1).acts (f t))):=by rw [Spar.pigment (G:=G)]; exact arch (matches_plain (c:=f t) (cobound 1))
 have hhB:∃ p:ℝ,RowCost 0 (1:Side) (heat G) p:=⟨_,coloring (RowCost.mono (plain0 (Flat.lineA_props.2) le_rfl).1 zero_le_one)⟩ -- bind
 obtain ⟨p',hB⟩:=hhB
 apply readahead (t:=f) (s:=s) (L:=L) (M:=M) (Flat.mesh_sides a.S m) hY hX le_rfl le_rfl
 · intro i
   have hx(i) : Matches y (Cell.RootField γ G (T i) B):=(Cell.viewed hp ht.le hσ ((T i).sizes)).2
   have hr := applies_bind hB hy (le_refl _) ht.le (hE i) (hx i)
   have hh {c f:Side}(S:StepData c f)(hW:Cell.Warm G S.kernel S.patch B σ q) (K:Matrix (Body 1 f) (Body 1 c) ℝ)(ht:Inputs S K (B.metric.acts f) ((H.H N m).metric.acts c)): Cell.RootField S.kernel G S B=patron G (extracted S (Line.green S) K):=by
      obtain ⟨P,k,hs⟩:=S; have ht':f=c*P.L:=Subtype.ext hs;subst f
      exact Cell.tree_station _ G rfl _ _ (hW.invert _|>.2.1) ht
   change Matches (Pert.Bulk.bind (heat G) y) (M i)
   unfold M;rw [patron_mul,← hh (T i) hp (K i) (h N m i hM), ← Spar.pigment];exact hr
 · intro i;unfold M;rw [extracted,Matrix.mul_add, ← Matrix.mul_assoc]
   have he : (cobound 1).acts (f i)*d 0 (f i)=0:=d_d_vac
   rw [he,Matrix.zero_mul,add_zero,patron_mul,←Spar.pigment]; exact applies_bind hB hx le_rfl hu.le (hE i) (hK i)
end YM.RG08.Aura
