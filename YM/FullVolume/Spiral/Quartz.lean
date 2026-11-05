import YM.FullVolume.Spiral.Walt
/- prepare matrix stage. No extra requirements on Y(t) choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Tower
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations Rank
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n m:Side}{Y:Hol G}
open MergeProof MergeProof.Matric FullVolume.Ray Jams Luna
variable {i:ℕ}{F:Labels.Frame G i}{B:BudgetPoint}{q t v a b s c u:ℝ}{p:sun→ Coefficient F n}{P:Desk G n}{y:F.Coeff}
local notation "A_"=> P.orient
set_option maxHeartbeats 350000
open Forum
open Extra.Histories.InputColumn
open UniformSpace
local notation "I"=> Extra.Histories.InputColumn.Listing
variable {Z:Plate F m n}{P:Desk G n}{Q:Desk G m}{R:Rep G n}{S:Rep G m}
variable (K:Keeper Q.orient.p Q.orient.activities)
variable (L:Keeper P.orient.p P.orient.activities)
-- Full- Completion Crop
variable (B:SectionData F)(V:∀ z:Motion,P.orient.activities.Moves z.1 0)
structure Seer (Z:Plate F m n)(K:Keeper Q.orient.p Q.orient.activities)(V:∀ z:Motion,P.orient.activities.Moves z.1 0)(Y:Hol G)(x:F.Coeff):Prop where
    stage : ∀ j:F.Index,∀ f:Coin F Y Q,∃ a b: Extra.Histories.InputColumn.Listing→ℝ, Summable a ∧ Summable b ∧ ∀ i,let u:=Matric.tell (dots Z K j f i); Hein u Y P ∧ u.remBound 0 P.orient P.k (a i) ∧ F.coeffSize u.x ≤ b i
    region : ∀ f:F.Index→ Coin F Y Q,Hein (pagesS Z K V f x) Y P
    atolls : Hein (pagesP Z V x) Y P
section
variable (hf:Along Q.orient S)(he:Along P.orient R)
variable (h: Elastic Z Y R S) (x:F.Coeff) (hS:Seer (P:=P) (Q:=Q) Z K V Y x)
variable (hs:B.Sound Y)(hn:2 ≤ n.val)
include hf he h hS hs hn
lemma portal (f f':F.Index→ Coin F Y Q): let g u':= pagesS Z K V u' x
   let l(u'):Completion (Coin F Y P):=↑(alb (g u') Y P L)
   (g f).x-(g f').x=(g (f-f')).x∧l f-l f'=l (f-f'):=by
   intro g l; let y:=breakP (g f) (g f')
   have hu:= penn hf he h K hS.stage _ V hs hn f f' x; let t:= hu.axes
   have he': (g f).support=(g f').support:=sharedP K V f f' x
   obtain ⟨ha,v,hv⟩:= breakH (g f) (g f') he' (hS.region f) (hS.region f'); let z:= f-f'; obtain ⟨hp,u,h'⟩:= hS.region z
   refine ⟨hu.axes,Eq.trans (b:=((alb y Y P L):Completion (Coin F Y P))) ?_ (hu.warmth L hu.old ha hv hp h')⟩ -- order check
   have hQ:alb (g f) Y P L-alb (g f') Y P L= alb y Y P L:=by
       obtain ⟨h,b,hT⟩:= hS.region f; obtain ⟨hf,c,hg⟩:= hS.region f'; apply Coin.noted; rw [map_sub,alb_read _ _ _ h hT,alb_read _ _ _ hf hg,alb_read _ _ _ ha hv]; exact (collected _ _ L he' hT hg).symm
   rw [← hQ]; exact (Completion.coe_sub ..).symm
omit hf he hs hn h
lemma stripes (f : F.Index→ Coin F Y Q) (X:Coin F Y P)(hx: Coin.uses X= capture (fullF Z K V f x) L)(hd:Hein (fullF Z K V f x) Y P):
   let g:= pagesS Z K V f x; let p:=pagesP Z V x; (fullF Z K V f x).x=g.x+p.x ∧ X= alb g Y P L+alb p Y P L:=by
     intro g p; have h:=splitS K hS.stage V f x; let y:=fullF Z K V f x
     refine ⟨?_,eq_add_of_sub_eq' ?_⟩
     · have hu:y.x-g.x=p.x:= congr_arg Coefficient.x h; change y.x=_; rw [← hu]; abel
     have hp : breakP y g=p:=h
     obtain ⟨hQ,b,hb⟩:= hS.region f; obtain ⟨hf,c,hc⟩:= hS.atolls; obtain ⟨hE,a,ht⟩:=hd; apply Coin.noted; rw [map_sub,alb_read _ _ _ hQ hb,hx,alb_read _ _ _ hf hc]; rw [← collected _ _ _ (sharedF K V f x) ht hb]; exact congr_arg (fun u=> capture u L) hp
end
section book
-- uniforms Skew.
variable {Z:sun→ Plate F m n}
variable {U:sun→Rep G n}{R:sun→Rep G m}
variable {T:Tableau q 300} {E:Heading F}{W:Side}
variable {Y':sun→F.Index→ Response G n}{Yr Yk:sun→ℕ→ (Config G m→ℂ)→ Response G n}
variable {η χ :ℝ}
local notation "e"=> ((T.price+1)+(3+2*T.price))
variable (hU:∀ s,Along P.orient (U s))(hK:∀ s,Along Q.orient (R s))(h:Epics Z U R E W Y T P.k Q.k η χ Y' Yr Yk) (hQ:4≤q) (hF :∀ s,Scan (Z s) Y (U s) (R s))
variable (hα:0≤η)(hχ:0≤χ) (hs:B.Sound Y)(hn:2 ≤ n.val)
include hU hK h hQ hF hα hχ hs hn
lemma termsW (x:F.Coeff)(s:sun): Seer (Z s) K V Y x:=by
    refine ⟨fun j f=>?_,fun a=>?_,?_⟩
    · obtain ⟨a,b,hB,hV,h'⟩:= balms hU hK h hQ hF hα K j f
      have he i:= (h' i).play s
      refine ⟨b,a,hV.2.1,hB.2.1,fun i=>?_⟩; intro u; have t:=he i|>.1; rw [sub_zero] at t
      exact ⟨⟨(he i).2.1,b i,(he i).2.2⟩,(he i).2.2,t⟩
    · have hp:= Forum.play (moonts hU hK h hQ hF hα K V B hs hn x a) s; exact ⟨hp.2.1,_,hp.2.2⟩
    have hp:=Forum.play (archwork hU h hQ hF hα hχ V B hs hn x) s; exact ⟨hp.2.1,_,hp.2.2⟩
end book
end YM.FullVolume.Paint.Tower
