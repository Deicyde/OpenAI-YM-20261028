import YM.RG08.Yamen.Fabric
import YM.RG08.Yamen.Rune
import YM.RG08.Packets.Limit

/-! # Rooted coefficient completeness & emission. -/
noncomputable section
namespace YM.RG08.Orison
open Filter Function Lattice Laurent Pert.Bulk Forms Packets Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Ducat Mason Yamen
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {I:Type}{n:ℕ}{F V:ℕ→Flake n (Market I)}
-- collar selection limit on real functions. General grades & kernels.
def hope {I:Type}(F:ℕ→I→ℝ)(x:I):ℝ:=limUnder atTop (fun i=>F i x) -- limUnder of ?? ℝ condition limUnder?
lemma receipt (f:ℕ→I→ℝ){x:I}(r:ℝ)(h:Tendsto (fun i=>f i x) atTop (𝓝 r)):hope f x=r:=h.limUnder_eq

def Sums {I:Type}(σ:ℝ)(F:ℕ→Flake n (Market I))(A:ℕ→ℝ)(p:ℝ)(m:ℕ):Prop:=(∀ t:Tape n (Market I), Tendsto (fun i=>F i t) atTop (𝓝 (hope F t))) ∧ Held (carpet _) σ p (hope F) ∧ ∀ N,m ≤ N → Held (carpet _) σ (A N) (F N-hope F)
lemma smart (n m:ℕ)(hn:0<n)(σ:ℝ)(hσ:0≤σ)(F:ℕ→Flake n (Market I))(A:ℕ→ℝ)(h:Tendsto A atTop (𝓝 0))(hA:∀ i,m ≤ i→0 ≤ A i)(p:ℝ)(hs:∀ i j,m ≤ i→i ≤ j→ Held (carpet _) σ (A i) (F i-F j))(hp:∀ i,m ≤ i→ Held (carpet _) σ p (F i)):Sums σ F A p m:=by
 let f(i:ℕ):=hung (F i)
 have hh:∀ i j,m ≤ i→i ≤ j→ Ticket (Forms.hike (carpet _) n σ) (fun x t=>f i x t-f j x t) (A i):=by
    intro i j he ht;rw [show (fun x t=>f i x t-f j x t)=hung (F i-F j) from by funext x t; unfold f hung;split<;>simp]; exact hs i j he ht
 obtain ⟨V,hV,hB,hP⟩:= solvent (K:=f) (e:=Forms.hike (carpet _) n σ) m (fun _ x=>mul_nonneg hσ (Ground.radius_nn (carpet _) x)) h hh hA p ((eventually_ge_atTop m).mono fun _ he=> hp _ he)
 let o:Fin n:=⟨0,hn⟩
 have H(t:Tape n (Market I)):Tendsto (fun i=>F i t) atTop (𝓝 (V (o,t o) t)):=by simpa [f,hung] using hV (o,t o) t
 have ht(t:Tape n (Market I)): V (o,t o) t=hope F t:= (receipt F _ (H t)).symm
 have hx:V=hung (hope F):=by
    funext x t; apply tendsto_nhds_unique (hV x t);unfold f hung;split
    exact ht t ▸ H t
    exact tendsto_const_nhds
 rw [hx] at hB hP
 refine ⟨fun t=> ht t ▸ H t,hP,fun i hi=> ?_⟩; unfold Held;rw [show hung (F i-hope F)=(fun x t=> f i x t-hung (hope F) x t) from by funext x t; unfold f hung;split<;>simp];exact hB i hi

variable {G:Gauge}{a:Levels G}{F0:Horizon a}{P X:MapPrices}(hg:G.Simple){Z:ChartRatio G}{U:ℕ→Kernel Flat.Links Flat.Links}{A B c:ℝ}{d k:ℕ}{E e r:ℕ}
variable (L: Yamen.Supplies F0 P Z) (hM:Bill G P X a)(hh:Payment G P X Z a)

def retreat (F0:Horizon a)(P X:MapPrices)(hg:G.Simple)(Z:ChartRatio G)(i:ℕ) :Castle G:=fun r e=>Orison.hope (fun N=>fed F0 P X hg Z N i r e)
lemma rate0 {c:ℝ}(h:0<c)(x:ℝ)(i:ℕ): Tendsto (fun N=> x*((a.S.a N/a.S.a i)^c)) atTop (𝓝 0):=by
 convert tendsto_const_nhds (x:=x) |>.mul (Filter.Tendsto.rpow_const (a.S.shrinks.div_const (a.S.a i)) (Or.inr h.le)) using 1;simp [Real.zero_rpow h.ne']

include L hM hh
lemma levels (he:e ≤ E)(hr:Live r e): ∃ (B:ℝ)(d:ℕ),0 ≤ B ∧ ∀ (i N k:ℕ),i ≤ N→E ≤ a.clock.J i→ Held (carpet _) ((lamp P X a i).coats e r) (B*Flat.clock a.S (Flat.Lambda' a) k i^d) (fed F0 P X hg Z N i r e):=by
 let W:= Yamen.small a E;let K₀:= Yamen.listed (a:=a) (E:=E) Audience.coarse;let J:=Yamen.caliph F0 X hg Z K₀ W.top (fun _=>le_rfl) L
 obtain ⟨C,hC,H⟩:= (Mason.delivers (R:=J) hg (admission hg Audience.coarse hh) (Yamen.starter hg K₀ L (Yamen.nutrient hg _ hh) hM) he hr).1
 obtain ⟨A,d,hA,hb⟩:=(show W.Poly (Mason.wide C) from hC)
 refine ⟨A,d,hA,fun i N k hi hk=>?_⟩
 let x : Haven W:= ⟨⟨i,N,N,le_rfl,k,hk⟩,i,le_rfl,hi⟩
 have ht:= (hb x.x x.m x.admit).2;rw [Mason.wide,dif_pos x.admit,show (⟨x.x,x.m,x.admit⟩:Haven W)=x from rfl] at ht; exact (H x).mono le_rfl ht (fun _=>le_rfl)

lemma vanishing (hA: Flat.Quorum (Flat.curve X) U 0 F0 A B d k c)(he:e ≤ E)(hr:Live r e) :
    ∃ (B' A':ℝ)(b d':ℕ)(c':ℝ),0 ≤ B' ∧ 0 ≤ A' ∧ 0<c'∧∀ (i u:ℕ),E ≤ a.clock.J i→ let T:=Flat.clock a.S (Flat.Lambda' a) u i
    ; Sums ((lamp P X a i).coats e r) (fun N=>fed F0 P X hg Z N i r e) (fun N=>A'*T^d'*((a.S.a N/a.S.a i)^c')) (B'*T^b) i:=by
 obtain ⟨p,n,hs,hS⟩:=levels hg L hM hh he hr;obtain ⟨q,m,c,hq,hc,H⟩:=Yamen.stones hg L hM hh hA he hr
 refine ⟨p,q,n,m,c,hs,hq,hc,fun i u hi=>?_⟩
 let t:=Flat.clock a.S (Flat.Lambda' a) u i
 apply smart (RG08.Mount.rank r) i (Nat.zero_lt_succ _) _ ((lamp P X a i).tag e r).1.le _ _ (rate0 hc _ i) _ _ (fun _ _ hi' hj=>H i _ _ u hi hi' hj) (fun x hj=>hS i x u hj hi)
 intro N _;change 0 ≤ q*t^m*((a.S.a N / a.S.a i)^c); have h:=a.S.a_pos i;have ht:=a.S.a_pos N
 have he:2 ≤ t:=(small a E).age_big (⟨i,i,i,le_rfl,u,hi⟩:Audience a E) i
 positivity
end YM.RG08.Orison
