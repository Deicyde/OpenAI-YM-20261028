import YM.FullVolume.Reel.Goals
import YM.FullVolume.Reel.Balsa
/-! Joint payment. Up and down dictionaries fixed across state arrays.ALL Ƶ Echo reads. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Legato.Bandage.Boutique
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
open YM.FullVolume Ray Paint Tower
variable {G:Gauge}{n:Side}{d:ℕ} (F:Labels.Frame G d)(Y:Hol G) (Q:Desk G n)(K:Keeper Q.orient.p Q.orient.activities)
namespace Stamp
local notation "A_"=>Q.orient
abbrev pollen (i:F.Index) (x:Coin F Y Q):=book (Size.axis F i) (Coin.uses x)
abbrev packY (i:F.Index)(x:Coin F Y Q):= rack K (pollen F Y Q i x)
local notation "Pℓ"=> pollen F Y Q
local notation "Vℓ"=> packY F Y Q K
variable (i:F.Index)
lemma ware (x:Coin F Y Q)(hr:K=K) : let X:=Vℓ i x; (Pℓ i x).Format 0 Y Q.orient ∧ (Pℓ i x).remBound 0 Q.orient Q.k ‖x‖∧ X.Format 0 Y Q.orient ∧ X.remBound 0 Q.orient Q.k ‖x‖:=by
    intro X; have hx:= granted (show Well (Q.orient) Q Q.k from ⟨⟨rfl,rfl⟩,rfl⟩) Y (Size.axis _ i) x; exact ⟨hx.1,hx.2,rack_format K _ hx.1,keeps K _ hx.2⟩
local notation "A"=> Q.orient
structure Relief (P:Desk G n)(X: Coefficient F n)(s:ℝ)(a b:ℕ→ℝ):Prop where
   suit : X.Format 0 Y P.orient
   sharp j: P.orient.p.supBounds 0 (X.support j) (X.regular j) (a j)
   stock j :0≤b j∧ ∀ W,‖X.forced j W‖≤b j
   totalsE :Summable (fun i=> P.orient.p.mass (X.support i) (a i))
   totalsK : Summable (fun i=> P.orient.p.mass (Local.patch P.orient.activities i) (b i)/P.k)
   price :(∑' i,P.orient.p.mass (X.support i) (a i))+(∑' i,P.orient.p.mass (Local.patch P.orient.activities i) (b i)/P.k)≤ s
lemma minted (x:Coin F Y Q): ∃ a b, Relief F Y Q (packY F Y Q K i x) ‖x‖ a b:=by
   let X:=packY F Y Q K i x; obtain ⟨_,_,hu,hv⟩:= ware F Y Q K i x rfl; obtain ⟨c,v,h₁,h₂,h,ha,⟨u,hp,hE⟩,k,hs,hK⟩:= hv
   refine ⟨_,_, hu,hE,hK,hp.2.1,hs.2.1.div_const _,?_⟩; rw [tsum_div_const]; apply le_trans _ h; exact add_le_add hp.2.2 ((div_le_iff₀ ha).mpr (hs.2.2.trans_eq (mul_comm ..)))
lemma solvent (x y:Coin F Y Q): let P:=packY F Y Q K i (x-y);let T:= packY F Y Q K i x;let X:=packY F Y Q K i y
    P.regular=T.regular-X.regular ∧ P.forced=T.forced-X.forced:=by
     intro Xp T V'; constructor
     · change (Coin.uses (x-y)).1= (Coin.uses x).1-(Coin.uses y).1; rw [map_sub]; rfl
     change stowK K (Pℓ i (x-y))= _; change _=stowK K (Pℓ i x)-stowK K (Pℓ i y); rw [← cogent (Pℓ i x) (Pℓ i y) K (ware F Y Q K i x rfl).2.1 (ware F Y Q K i y rfl).2.1]; unfold pollen; rw [map_sub]; rfl
variable {R:RG.Rep G n}(h:Along Q.orient R)
include h
lemma bank (X:Coefficient F n){t a}(hr: X.remBound 0 Q.orient t a) (Y:Keeper R.p R.activities)(hp:cart K=cart Y): stowK K X=stowK Y X:=by
    have hz:= h.force; unfold stowK; rw [hp, Rank.Hue.projector h X hr] -- param order
-- supports at startup. choice dictionary.Move across Π.Actual labels fixed by operations. Note gas licensed under any co history. Real.E dummy.
end Stamp
end YM.MergeProof.Matric
