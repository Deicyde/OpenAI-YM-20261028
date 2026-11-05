import YM.RG08.Orison.Vale
/-! # Rates on rebased turret (catalog in fine coupling), its kinetic reading & reset,
 at any working horizon. -/
noncomputable section
namespace YM.RG08.Orison
open Filter Function Lattice Laurent Pert.Bulk Forms Packets Carrel Steam Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Ducat Mason Yamen
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}{a:Levels G}{F:Horizon a}{P X:MapPrices}(hg:G.Simple){Z:ChartRatio G}{U:ℕ→Kernel Flat.Links Flat.Links}{A B c:ℝ}{d k:ℕ}{E e r:ℕ}
variable (L: Yamen.Supplies F P Z) (hM:Bill G P X a)(hh:Payment G P X Z a) (h:Flat.Quorum (Flat.curve X) U 0 F A B d k c)

-- wood assembly V, full formal outputs comparison even if N top stencil. Turf meaningful only i<N. !-/
variable (F P X Z) in
def wings(N i:ℕ):Castle G:= Ducat.wild (lamp P X a i) (Yamen.base P X a i (F.H N i)) (fed F P X hg Z N (i+1)) Z (Yamen.branches (a:=a) i) (F.H N (i+1)) (F.H N i)
variable (F P X Z) in
def anchor (i:ℕ):Castle G:=fun r e=>Orison.hope (fun N=>wings F P X hg Z N i r e)
include L hM hh h
local notation "W"=>small a E
local notation "K₀"=> Yamen.listed (a:=a) (E:=E) Audience.coarse
local notation "Jx"=>Yamen.caliph F X hg Z K₀
-- Woken variance costs at slot. U absolute. embrace rates at any p.
lemma scores (he:e ≤ E)(hr:Live r e) : ∃ (A B:ℝ)(d k:ℕ)(c:ℝ),0≤A∧ 0 ≤ B∧ 0<c ∧ ∀ (i N M u:ℕ), E ≤ a.clock.J i→ i<N→ N ≤ M → let C:=Flat.clock a.S (Flat.Lambda' a) u i; let q (N) := wings F P X hg Z N i r e;let v:= (lamp P X a i).coats e r
 ; Held (carpet _) v (A*C^d) (q N) ∧ Held (carpet _) v (B*C^k*((a.S.a N/a.S.a i)^c)) (q N-q M):=by
 let Q: Mason.Pair hg E (Jx Audience.coarse (fun _=>le_rfl) L) (Jx Audience.fine (fun x=>x.cover) L):= Yamen.solves hg L hM hh h
 have ha:=admission (E:=E) hg Audience.coarse hh
 obtain ⟨p,hp,hP⟩:= (Mason.delivers hg _ ha Q.one he hr).2
 obtain ⟨q,hq,Hq⟩:= (Mason.pellets (R:=Jx Audience.coarse (fun _=>le_rfl) L) hg (P:=Jx Audience.fine _ L) ha Q he hr).2
 obtain ⟨x,j,xg,hx⟩:= (show (W).Poly (wide p) from hp)
 obtain ⟨y,l,hY,ht,h0,H⟩:= (show (W).Fade (wide q) from hq).cap
 refine ⟨x,y,j,l,hY,xg,ht,h0,?_⟩
 intro i n m u hz hi ht C z θ
 let t : Audience a E:= ⟨i,n,m,ht,u,hz⟩;let o:Run W:=⟨t,i,⟨le_rfl,hi.le⟩,hi⟩
 have hf(i:Run W)(f:Run W→ℝ):wide f i.x i.m=f i:=dif_pos i.admit
 have hu:= (hx o.x o.m o.admit.1).2; rw [hf] at hu -- not rewrite lemma hf? maybe
 have hw:=(H o.x o.m o.admit.1).2;rw [hf] at hw
 exact ⟨(hP o).mono le_rfl hu (fun _=>le_rfl),(Hq o).mono le_rfl hw (fun _=>le_rfl)⟩
lemma fresh (he:e ≤ E)(hr:Live r e):
 ∃ (B' A':ℝ)(b d':ℕ)(c':ℝ),0 ≤ B' ∧ 0 ≤ A' ∧ 0<c' ∧∀ (i u:ℕ),E ≤ a.clock.J i→ let t:=Flat.clock a.S (Flat.Lambda' a) u i; Sums ((lamp P X a i).coats e r) (fun N=>wings F P X hg Z N i r e) (fun N=>A'*t^d'*((a.S.a N /a.S.a i)^c')) (B'*t^b) (i+1):=by
 obtain ⟨x,y,q,l,c,hx,hy,hc,H⟩:= scores hg L hM hh h he hr
 refine ⟨x,y,q,l,c,hx,hy,hc,?_⟩; intro i u hi
 let t:=Flat.clock a.S (Flat.Lambda' a) u i
 apply smart (RG08.Mount.rank r) _ (Nat.zero_lt_succ _) _ ((lamp P X a i).tag e r).1.le _ _ (rate0 hc _ i) _ _ (fun j m hj hm=>(H i j m u hi hj hm).2) (fun j hj=>(H i j j u hi hj le_rfl).1)
 intro j _;change 0 ≤ y*t^l*((a.S.a j / a.S.a i)^c); have h:=a.S.a_pos i;have ht:=a.S.a_pos j
 have he:2 ≤ t:=(small a E).age_big (⟨i,i,i,le_rfl,u,hi⟩:Audience a E) i
 positivity
end YM.RG08.Orison
