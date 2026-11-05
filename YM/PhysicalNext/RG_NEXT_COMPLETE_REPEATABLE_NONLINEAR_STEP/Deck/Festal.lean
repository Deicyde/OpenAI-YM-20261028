import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Vale
/-!
 # motion/form linear bits. Tube true narrowing. Deck world met at ANY Skin pair.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Coat
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f C F:Side} {P : Patch} {M : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} (hC : C.val=c.val*M) (he:2 ≤ c.val)
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ}
open Pressure.Tube
local notation "x'" => Pressure.Stores.till p
variable {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio} (X: Coat T E) (X': Coat T' E')

def bleached (Z: Coat T E):= Z.seeds= ⟨∅,∅,∅⟩
structure Stellar (hC : C.val=c.val*M) (he:2 ≤ c.val) (K : Teller G) (p : ℝ) (X:Coat T E) (X':Coat T' E') : Prop where
  snow : bleached X
  dawn : bleached X'
  equal : X.x=p
  reached : X'.x=p
  clips : X.χ=X'.χ
  wit : X.width=X'.width
  views : X'.V= (Lace.project (h:=h) (H:=H) hC he).low.links X.V
  tree : (Lace.project (h:=h) (H:=H) hC he).Fitted E E'
  reach : X'.k= (Lace.project (h:=h) (H:=H) hC he).pullTag Q X.k
  old : Room K (stepped Q h) T p
  wall : Room K (stepped Q H) T' p
  tall : T'=re T
  news : 10*(radiusB p)+10<c.val
lemma clean_c (hk : bleached X) (i: Bond f): X.Hot i ↔ i∉E.trunks:= by unfold Coat.Hot Shell.active; rw [show X.seeds= _ from hk]; simp [Shell.frozen,Pressure.Stores.dome,Pressure.Stores.place,halo]
lemma selected_s (hk : bleached X) (s : Signed) (p : Spot c f): X.selected s p:= by unfold Coat.selected Inside; rw [show X.seeds= _ from hk]; simp [Pressure.Stores.dome,Pressure.Stores.place,halo]
namespace Stellar
variable {hC he X X'} (A : Stellar hC he K p X X')
include A
lemma D: X'.B=radiusB p ∧ X.B=radiusB p:= ⟨congr_arg _ A.reached,congr_arg _ A.equal⟩
lemma optics : 2*((x')+predReach P+4)<c.val:= by
  have hp:=A.old.frame; have hr:= A.news
  unfold Pressure.Stores.till; change 10000*(predReach P+macroR P+P.L.val+10) ≤ _ at hp -- inspect
  omega
lemma rank : 2*(x')< c.val:= by have h:= A.optics; omega
lemma glassU (u : Directions G f): X'.lens (Deck.light (L).high.cut u)=Deck.light (L).high.cut (X.lens u) ∧ X'.signal (Deck.light (L).high.cut u)=Deck.light (L).high.cut (X.signal u) ∧ X'.input (Deck.light (L).high.cut u)=(L).high.links (X.input u):= by
  let l:= L; let f := curr l.high.cut (X:=Axis); let w:= Deck.light l.high.cut u
  have ht i: i∈ E'.trunks↔ f i∈ E.trunks:= A.tree.pines i
  have hp i : X'.Hot i ↔ X.Hot (f i):=(clean_c X' A.dawn i).trans ((ht i).not.trans (clean_c X A.snow ..).symm)
  have hh : X'.lens w=Deck.light l.high.cut (X.lens u):= by ext1 i; unfold Coat.lens; rw [hp]; rfl
  refine ⟨hh,funext fun i=>?_,funext fun i=>?_⟩
  · by_cases h:i∈E'.trunks
    · rw [X'.on_trunk ..]; change 0=X.signal u (f i); rw [X.on_trunk _ _ ((ht _).1 h)]; exact h
    have he := (clean_c X' A.dawn _).2 h; rw [X'.at_hot _ i he]; exact Eq.symm (X.at_hot _ _ ((hp i).1 he))
  by_cases h:i∈E'.trunks
  · exact (X'.sliced _ _ h).trans (X.sliced u (f i) ((ht i).1 h)).symm
  have he:=(clean_c X' A.dawn _).2 h; rw [X'.viewing _ i he]; change increment (replica (Y).ratio _) w i=X.input u (f i); rw [X.viewing _ _ ((hp i).1 he),A.views, show replica (Y).ratio (l.low.links X.V)=_ from Lace.Fitted.replicate l X.V]; rfl

lemma lays (s:Signed) (t:Rod C F) (u : Directions G f) : X'.realPath s t (Deck.light (L).high.cut u)=X.realPath s (Deck.rod (L) t) u:= by
  unfold realPath; rw [A.views,A.reach]; unfold Coat.R; rw [A.reached,A.equal,req hC he A.tall A.old A.wall X.V A.rank,(A.glassU u).2.1]; exact congr_arg _ (Deck.wing hC he (hT:=SectorMeasure.funds_branch A.old.accepted) A.tall (x') t A.optics (X.signal u) X.V s) -- args
abbrev men (V : Lace h H M) : Mention C F → Mention c f:= Prod.map id (Deck.rod V)
lemma motionB (u : Directions G f) (z:Mention C F): X'.motion (Deck.light (L).high.cut u) z=X.motion u (men (L) z):= by
  unfold motion; rw [if_pos (selected_s X A.snow _ _),if_pos (selected_s X' A.dawn _ _)]; unfold Coat.R; rw [(A.glassU u).1,A.views,A.reached,A.equal]; exact Deck.wing hC he (hT:=SectorMeasure.funds_branch A.old.accepted) A.tall (x') z.2 A.optics ..
lemma priceB (z:Mention C F): X'.priced 0 z=X.priced 0 (men (L) z):= by unfold Coat.priced; rw [if_pos (selected_s X' A.dawn z.1 (spot (Y) z.2)),if_pos (selected_s X A.snow (men (L) z).1 (spot (S) (men (L) z).2))]; exact congr_arg _ (A.lays z.1 z.2 0)
end Stellar
end YM.PhysicalNext.Repeat.Deck
