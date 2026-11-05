import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Cobble
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Nibs
/-! # Ember's price U.Path physical align on bare. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck.Stellar
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Mint
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Stellar hC he K p X X') {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p
include hC he
lemma birthS : Nest (Deck.divides hC) (Deck.spo (L)) (lead (Y)) (lead (S)):= by
  have hx:=onfloor (h:=h) (H:=H) hC he
  have ht := (Deck.footing (h:=h) (H:=H) hC he); exact ht.pr.sum (hx.pr.sum (hx.pr.sum hx.pr))
omit he in
lemma fonts {X Y':Type} (q : X→Site C) (r:Y'→ Site c) (p:X→ Y') (h : Nest (Deck.divides hC) p q r) :
    Nest (Deck.divides hC) (Prod.map (id:Signed→Signed) p) (fun i=>i.1.act (q i.2)) (fun i=>i.1.act (r i.2)):= by
  refine ⟨fun i=>?_,fun x i hi=>?_,fun i j hh hj=>?_⟩
  · simp only [← usual,Prod.map_fst, Prod.map_snd,h.footing, id_eq]
  · obtain ⟨s,i⟩:=i; obtain ⟨j,hp,hT⟩:= h.extend (s⁻¹.act x) i (by change s.act (r i)=_ at hi; rw [← usual,← hi,s.inv_act]); exact ⟨(s,j),Prod.ext rfl hp,(congr_arg s.act hT).trans (by rw [← Signed.act_mul,mul_inv_cancel,Signed.act_one])⟩
  have ht : i.1=j.1:=congr_arg (fun z : Signed × Y'=>z.1) hh; refine Prod.ext ht (h.firm _ _ (congr_arg (fun z:Signed×Y'=>z.2) hh) (j.1.act_injective ?_)); simpa only [ht] using hj
lemma swans : Nest (Deck.divides hC) (minnow (L)) (caption (Y)) (caption (S)):= by
  have hs:= fonts (hC:=hC) _ _ _ (birthS (hC:=hC) (he:=he) (h:=h) (H:=H) (Q:=Q)); have hv:= Deck.footing (h:=h) (H:=H) hC he|>.pr (E:=Axis); exact hs.sum (hv.sum hv)
lemma nest_mint : Nest (Deck.divides hC) (verse_down (L)) (pace (Y)) (pace (S)):= by
  have h:= fonts (hC:=hC) _ _ _ (Deck.footing (h:=h) (H:=H) hC he|>.pr (E:=ℕ)); exact h.sum (h.sum (h.sum swans))

lemma voy {T:Tube G (stepped Q h)} {T':Tube G (stepped Q H)} (p:Music C F) (n l:ℕ) (hp:R'.path=R.path) (ht:4 < f.val) :
    verse R'.path p=verse R.path (verse_down (L) p) ∧ areas R T n l (disc (S) (verse_down (L) p))=(areas R' T' n l (disc (Y) p)).image (L).low.cut:= by
  let O:= L
  have he {D':ℕ} (A: ℕ→ Atom G D') (V:Trans F): atomFoot (S).ratio n l A (turn_down O V) = (atomFoot (Y).ratio n l A V).image O.low.cut:= projectionA (h:=h) (H:=H) hC ‹2 ≤ _› n l A V ht
  constructor; · rw [hp]; rcases p with p|p|p|p<;> rfl
  rcases p with p|p|p|p
  · change atomFoot _ n l R.path.cubic (turn_down O p) = (atomFoot _ n l R'.path.cubic p).image _; rw [hp]; exact he ..
  · change atomFoot _ n l R.path.quartic (turn_down O p) = (atomFoot _ n l R'.path.quartic p).image _; rw [hp]; exact he ..
  · change atomFoot _ n l R.path.loop (turn_down O p) = (atomFoot _ n l R'.path.loop p).image _; rw [hp]; exact he ..
  change Coat.sleeve (S) l n (minnow O p)= (Coat.sleeve (Y) l n p).image _
  have hy:= (swans (hC:=hC) (he:=(by assumption)) (Q:=Q) (h:=h) (H:=H)).footing p
  have hf (p:Bond F) : Itinerary.town (S) l n (curr O.high.cut p)=(Itinerary.town (Y) l n p).image O.low.cut:= by unfold Itinerary.town; rw [show ends _ _= _ from finish_point (hC:=hC) (Q:=Q) (he:=(by assumption)) p,show ∀ y,halo (n*l) (y.image O.low.cut)=_ from fun y=>ringed hC y _]; rfl
  rcases p with p|p|p
  · change neighbors (n*l) (caption (S) (minnow (L) (Sum.inl p)))=(neighbors (n*l) _).image _; rw [← hy]; exact inclined hC (n*l) _
  all_goals exact hf _
include A
lemma naryL (t : Miniature C F) (β a:ℝ) (u: Directions G f) (v : ChartRatio G) : X'.Short (Deck.light (L).high.cut u) v β a t=X.Short u v β a (minnow (L) t) := by
  let W:= L
  have he := (swans (Q:=Q) (hC:=hC) (H:=H) (h:=h) (he:=he)).footing t
  rcases t with ⟨s,i⟩|i|i
  · let z:=rowSite (Y) (s,i); let J:= neighbors B z
    have hl:2*((B)+3)<c.val:= by have hh:=A.news; omega
    change X'.speck _ _ _ (s,i)=X.speck u β a (s,Deck.spo (L) i)
    have hA : X'.enforce (2*a) (Deck.light W.high.cut u) (X'.booth z)=X.enforce (2*a) u (X.booth (rowSite (S) (s,Deck.spo W i))):= by
      unfold booth; rw [A.D.1,A.D.2,← (show W.low.cut z=rowSite (S) (s,Deck.spo W i) from he),show neighbors B (W.low.cut z)= _ from inclined hC B z]; exact A.porter J B hl z (Subset.refl J) _ u
    have hz (X:Coat T E) (hx:bleached X) (x) : ¬Inside x X.seeds (200* X.B):= by rw [show X.seeds=_ from hx]; simp [Inside, Pressure.Stores.dome, Pressure.Stores.place, halo]
    have hk : ¬Inside z X'.seeds (200*X'.B):= by rw [show X'.seeds=_ from A.dawn]; simp [Inside, Pressure.Stores.dome,Pressure.Stores.place, halo]
    rw [speck,speck,if_neg hk,if_neg (hz X A.snow _),hA,A.flight,A.mus,A.vexed]
  · have hz (p:Bond f): ¬ voyage X.seeds (200*X.B) p:= by rw [show X.seeds= _ from A.snow]; simp [voyage, Pressure.Stores.dome, Pressure.Stores.place, halo]
    have hk: ¬ voyage X'.seeds (200*X'.B) i:= by rw [show X'.seeds= _ from A.dawn]; simp [voyage,Pressure.Stores.dome,Pressure.Stores.place,halo]
    change undercurrent X' i= undercurrent X _; rw [undercurrent,undercurrent,if_neg hk,if_neg (hz _), A.crowns]
  · have hk:i∉ X'.plaza (X'.seeds.dome (304*X'.B)):=by rw [show X'.seeds=_ from A.dawn]; simp [Pressure.Stores.dome,Pressure.Stores.place,halo,plaza]
    have ht (i:Bond f): i∉ X.plaza (X.seeds.dome (304*X.B)):=by rw [show X.seeds=_ from A.snow]; simp [Pressure.Stores.dome,Pressure.Stores.place,halo,plaza]
    change solo X' _ _ _ i= solo X _ _ _ (curr W.high.cut i); unfold solo; simp only [A.hotnext,hk,ht,not_false_eq_true, true_and]; split
    · unfold gentry; rw [A.sig]; rfl
    rfl
end YM.PhysicalNext.Repeat.Deck.Stellar
