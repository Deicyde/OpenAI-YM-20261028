import YM.RG08.April.Consumes
/-! # Manufacturer plate. Supply with stage choices, output & compile stencil recursion
 from boundary value (permits even high-led variant on overlap/continuation). -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.April
open Function Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Rate.Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Camera Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Jetty Precision Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks Sideshow
open scoped Classical Matrix BigOperators PowerSeries Topology
variable {X:Type}{G:Gauge}{D d p l e n k r j t:ℕ}{σ τ μ U η:ℝ}{K:KernelChoices}
local notation "Δ"=> stance (Loc G 1)
local notation "E"=> Ed G Cover
variable (F:Labels.Frame G d)(W:Rate.Stair X)(H:Housing F W D k)
local notation "I₀"=> Accent F
local notation "B₀"=>Bouquet F
local notation "V₀"=>Haven W
local notation "R₀"=>Mason.Run W
local notation "D0"=> Mason.kiosk W
local notation "D1"=> Mason.turnstile W

-- density stage data on every Run. all costs at specific k knee. 
structure Dials (G:Gauge)(W:Rate.Stair X)(D d k:ℕ) where
 κ:KernelChoices
 P:Mason.Run W→ Patch
 lengths(x):((P x).L.val:ℝ)= W.length x.x x.m
 older:Mason.Run W→ℕ -- Athena fine smoothing
 horizon:Mason.Run W→ℕ
 filter: Haven W→ℝ
 paid:∀ i,0<filter i
 shift: Mason.Run W→ℝ -- before Ω, row and costs
 orth:Mason.Run W→ℝ
 norm:Mason.Run W→ℝ
 fee(x:Mason.Run W): Sideshow.Font d D k (older x) (horizon x) (filter (past W x)) (shift x) (filter (old W x)) (orth x) (norm x)
 Q:∀ i:Mason.Run W,Crew G (P i) κ
 Q':∀ i:Mason.Run W,Crew G (P i) κ
 power: Mason.Run W→ℝ -- W
 score: Mason.Run W→ℝ
 can:(Mason.turnstile W).Good power
 hit: (Mason.turnstile W).cheap score
 warm i:0<score i
 foil (i:Mason.Run W)(r:ℝ):score i≤r→Race (filter (past W i)) (shift i) (filter (old W i)) (orth i) (norm i) (power i) r D d k (d+k) (older i) (horizon i) (Q i) (Q' i)
 slots i:1 ≤ power i

-- pre numbers & post adjacency constants given before lengths. CHOSEN from implementation @harbor. carry for consumer. 
def cap (F:Labels.Frame G d)(D k j t l e n:ℕ)(A:Hol G)(K:KernelChoices)(σ η τ μ U:ℝ)(h:Font d D k j t σ τ η μ U)(hl:l≤d)(he:e≤k)(hn:n≤l+e):ℝ:= (harbor F D k j t l e n A K σ η τ μ U h hl he hn).choose
def post (F:Labels.Frame G d)(D k j t l e n:ℕ)(A:Hol G)(K:KernelChoices)(σ η τ μ U:ℝ)(h:Font d D k j t σ τ η μ U)(hl:l≤d)(he:e≤k)(hn:n≤l+e):ℝ→ℝ:=(harbor F D k j t l e n A K σ η τ μ U h hl he hn).choose_spec.choose
lemma ledger (A:Hol G)(H:Font d D k j t σ τ η μ U)(hl:l≤d)(he:e≤k)(hn:n≤l+e):
 let C:=cap F _ _ _ _ _ _ _ A K _ _ _ _ _ H hl he hn;let V:= post F _ _ _ _ _ _ _ A K _ _ _ _ _ H hl he hn
 ; 1≤C ∧ Week (transitR n e l d k) V∧(∀ p≥1,1≤V p)∧∀ {P:Patch}{Q R:Crew G P K}{w δ:ℝ},Race σ τ η μ U w δ D d k (d+k) j t Q R→0<δ→∀ {S S':Bouquet F},Silo F D k H.fine S → Silo F D k H.fine S' →
 let Y:=sing F Q S; let Y':=sing F R S';let M:=Sideshow.deposit F Q S;let N:=Sideshow.deposit F R S';let g:ℝ:=P.L.val
 ; ∀ {B B0 B1 T:ℝ},Stamps F D e n l B δ H.fine H.coarse S S' Y Y' M N → 0≤B0→0≤B1→0≤T→(∀ i∈Sideshow.booth F l,Sings Δ D H.fine (S i e n) B0∧ Sings Δ D H.fine (S' i e n) B1 ∧ Sings Δ D H.fine (S i e n-S' i e n) T) →
 Replies F D e n l C (V w*B^2) (V w*(B+B1)^4) B0 B1 g δ T H.coarse Y Y' M N:= (harbor F D k j t l e n A K σ η τ μ U H hl he hn).choose_spec.choose_spec
namespace Dials
variable (P:Dials G W D d k)(A:Hol G)
def shell (x:R₀)(hl:l≤d)(he:e≤k)(hn:n≤l+e):= cap F _ _ _ _ _ _ _ A P.κ _ _ _ _ _ (P.fee x) hl he hn
def echo (x:R₀)(hl:l≤d)(he:e≤k)(hn:n≤l+e):= April.post F _ _ _ _ _ _ _ A P.κ _ _ _ _ _ (P.fee x) hl he hn (P.power x)
end Dials
structure Paid {W:Rate.Stair X}(P:Dials G W D d k)(A:Hol G):Prop where
 shell(e l n:ℕ)(he:e≤k)(hl:l≤d)(hn:n≤l+e):(Mason.turnstile W).Good (fun x=>P.shell F W A x hl he hn)
 post_(e l n:ℕ)(he:e≤k)(hl:l≤d)(hn:n≤l+e):(Mason.turnstile W).Good fun x=>P.echo F W A x hl he hn
 floor(e l n:ℕ)(he:e≤k)(hl:l≤d)(hn:n≤l+e):∀ x,(P.shell F W A x hl he hn)^2≤ ((P.P x).L.val:ℝ)
structure Boundary (F:Labels.Frame G d)(W:Rate.Stair X)(D k:ℕ)(strip:Haven W→ℝ)(paid:∀ i,0<strip i) where
 map: (x:X)→Bouquet F
 call: ∀ i:Haven W,i.m=W.top i.x → Silo F D k (paid i) (map i.x)
 pay (e n:ℕ)(_he:e≤k):∃ p:Haven W→ℝ,(Mason.kiosk W).Good p∧∀ i:Haven W,i.m=W.top i.x→∀ j:Accent F,Sings (stance (Loc G 1)) D (paid i) (map i.x j e n) (p i)

-- independent full historical formulas (may read backwards as linear recurrence)
def template (Q:(Mason.Run W )→ Bouquet F→Bouquet F)(T:X→Bouquet F)(x:X):ℕ→Bouquet F
 | 0=> T x
 | n+1=> if h: Mason.active W x (W.top x - (n+1)) then Q ⟨x,_,h⟩ (template Q T x n) else 0
-- `template` implicit recursion with parameters F W maybe need explicit.
def rise (Q:(Mason.Run W)→Bouquet F→Bouquet F)(T:X→Bouquet F)(y:Haven W):Bouquet F:=template F W Q T y.x (W.top y.x-y.m)
lemma rise_top (Q:R₀→B₀→B₀)(T:X→B₀)(i:V₀)(hi:i.m=W.top i.x):April.rise F W Q T i=T i.x:=by unfold April.rise;rw [hi,Nat.sub_self,template]
lemma rise_step (Q:R₀→B₀→B₀)(T:X→B₀)(i:R₀):April.rise F W Q T (old W i)=Q i (April.rise F W Q T (past W i)):=by
 have hi:i.m < W.top i.x:=i.admit.2;unfold April.rise;change template F W Q T i.x (W.top i.x-i.m)=Q _ (template _ _ _ _ i.x (W.top i.x-(i.m+1)));nth_rw 1 [show W.top i.x-i.m=W.top i.x-(i.m+1)+1 by omega,template];have he:W.top i.x-(W.top i.x-(i.m+1)+1)=i.m:=by omega
 rw [dif_pos (he.symm ▸ i.admit)]  
 congr 2
lemma downcorner {Q:V₀→Prop}(hh:∀ i:V₀,i.m=W.top i.x→Q i)(ht:∀ i:R₀,Q (past W i)→Q (old W i))(i:V₀):Q i:=by
 generalize he:W.top i.x-i.m=n;induction n generalizing i with
 | zero =>
   apply hh
   have hi : i.m ≤ W.top i.x := i.admit.2
   omega
 | succ n ih=>
    let j:R₀:=⟨i.x,i.m,i.admit,by omega⟩; exact ht j (ih (past W j) (by change W.top i.x-(i.m+1)=n;omega))

namespace Dials
variable (T:Dials G W D d k)(A:Hol G)
def shoot (Q:Boundary F W D k T.filter T.paid)(i:Haven W): Bouquet F := April.rise F W (fun j=>Sideshow.sing F (T.Q j)) Q.map i -- remove C
abbrev shoot2 (C:Boundary F W D k T.filter T.paid):= April.rise F W (fun j=>Sideshow.sing F (T.Q' j)) C.map
include A in
lemma shoot_valid (Y Y':Boundary F W D k T.filter T.paid)(i:Haven W):Silo F D k (T.paid i) (T.shoot F W Y i) ∧ Silo F D k (T.paid i) (T.shoot2 F W Y' i):=by
 let V(i:Haven W):Prop:=Silo F D k (T.paid i) (T.shoot F W Y i) ∧ Silo F D k (T.paid i) (T.shoot2 F W Y' i)
 apply downcorner W (Q:=V) (fun i hi=>?_ ) _ i;swap
 · unfold V shoot shoot2;rw [rise_top F W _ _ i hi,rise_top F W _ _ i hi];exact ⟨Y.call i hi,Y'.call i hi⟩
 intro i hi
 let x:=T.shoot F W Y (past W i);let y:=T.shoot2 F W Y' (past W i)
 obtain ⟨C,hC,Hc⟩:= Sideshow.oneWing F D k _ _ T.κ _ _ _ _ _ A (T.fee i)
 obtain ⟨hx,hy⟩:= Hc (T.foil i (T.score i) le_rfl) (T.warm i) (S:=x) (S':=y) hi.1 hi.2
 unfold V shoot shoot2;rw [rise_step,rise_step]; exact ⟨hx.rises,hy.rises⟩
def plot (Y Y':Boundary F W D k T.filter T.paid)(he:Paid F T A): Housing F W D k where
 strip:=T.filter
 stand:=T.paid
 S:=T.shoot F W Y
 S':=T.shoot2 F W Y'
 P i:= Sideshow.deposit F (T.Q i) (T.shoot F W Y (past W i))
 P' i:=Sideshow.deposit F (T.Q' i) (T.shoot2 F W Y' (past W i))
 wish i:= T.shoot_valid F W A Y Y' i
 score :=fun i=>let h:=T.shoot_valid F W A Y Y' (past W i);⟨(Sideshow.overjoy F (T.Q i) _ h.1.unbound).2,(Sideshow.overjoy F (T.Q' i) _ h.2.unbound).2⟩
 debt:=T.score
 tiny:=T.hit
 never:=T.warm
 afford:=by
    intro e l n hx hr hn
    refine ⟨_,_,he.shell e _ _ hx hr hn, he.post_ e _ _ hx hr hn,fun i=>?_⟩
    obtain ⟨hA,hC,hU,H⟩:= April.ledger (l:=l) (e:=e) (n:=n) (K:=T.κ) F A (T.fee i) hr hx hn
    have hk:(cap F _ _ _ _ _ _ _ A T.κ _ _ _ _ _ (T.fee i) hr hx hn)^2≤W.length i.x i.m:= (he.floor e _ _ hx hr hn i).trans_eq (T.lengths i)
    refine ⟨hA,hU _ (T.slots i),hk,?_⟩
    let x:=T.shoot F W Y (past W i);let y:=T.shoot2 F W Y' (past W i)
    intro B δ B0 B1 t ht hs
    have hL:T.shoot F W Y (old W i)=Sideshow.sing F (T.Q i) x:=rise_step F W _ _ i
    have hQ:T.shoot2 F W Y' (old W i)=Sideshow.sing F (T.Q' i) y:=rise_step F W _ _ i
    rw [hL,hQ] at hs ⊢ -- expensive. change selectively
    obtain ⟨h₁,h₂⟩:=T.shoot_valid F W A Y Y' (past W i)
    intro hb hG hD hi
    rw [←T.lengths]
    exact H (T.foil i δ ht) ((T.warm i).trans_le ht) h₁ h₂ hs hb hG hD hi
 vault:=by
    intro e n he
    obtain ⟨p,hp,hq⟩:=Y.pay e n he
    obtain ⟨a,hA,ha⟩:=Y'.pay e n he
    refine ⟨fun i=>p i+a i, (Mason.kiosk W).hear _ _ hp hA,fun i hi j=>?_ ⟩; dsimp only [shoot,shoot2];rw [rise_top _ _ _ _ _ hi,rise_top _ _ _ _ _ hi]
    exact ⟨(hq i hi j).mono le_rfl le_rfl (fun _=>le_rfl) (le_add_of_nonneg_right ((Mason.kiosk W).safe _ hA _)),(ha i hi j).mono le_rfl le_rfl (fun _=>le_rfl) (le_add_of_nonneg_left ((Mason.kiosk W).safe _ hp _))⟩

end Dials
end YM.RG08.April
