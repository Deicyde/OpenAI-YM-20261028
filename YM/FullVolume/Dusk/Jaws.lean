import YM.FullVolume.Mark.Sanctum
import YM.MergeProof.Ravine
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H:History G) (N p m:ℕ)(Y:Hol G)
local notation "κ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "U"=> H.rep N p (m+1)
local notation "O"=> H.rep N p m
namespace Tool
variable {W:Worth}{u ζ v:ℝ}{D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}{T:Heading F}{X:Set Wing}
variable (P:Tool F H N p m)(h:Cap P B Y W D T u ζ v X)
include h
lemma fade : Stampede B H N p m Y D u ζ v T X:= by
    refine ⟨fun i hi=>?_, fun f S t=> ?_,fun f j x=> ?_, h.copies.heading⟩
    · intro a Z; obtain ⟨hs,hw⟩:= h.copies.main i
      rw [show Size.axis F i 0=0 from by simp [Size.axis,hi]] at hw
      exact ⟨_,hs,hw⟩
    · intro x hV hp; obtain ⟨i,he⟩:= (code (Support (H.S.side (m+1) p))).surjective (S,0)
      have hz:mapSeat i=S:=by rw [mapSeat,he,Finset.insert_eq_of_mem hV.anchor]
      have hP:=h.copies.regular i f t; dsimp only at hP
      rw [hz] at hP; obtain ⟨hR,hQ⟩:= hP hV hp; exact ⟨_,hR,hQ⟩
    intro a he hx hp ht hc; obtain ⟨hr,hq⟩:=h.copies.forced j f x he hx hp ht hc; exact ⟨_,hr,hq⟩
lemma tuneR (hP:(1+2*(H.levels.params m).columns)*ζ ≤ Bid.barunit (H.S.block m)) : Relay.Tones B H N p Y v m ζ D:=by
    have hz:=h.budget.epsilon; refine ⟨⟨hP,h.dish,h.toll,hz⟩,X,h.tote, fun Q t hp hu ht => asideP B H N p m Y P.up Q X _ h.shines h.late hu ht hp h.dish hz (fade B H N p m Y P h) h.hv h.cart⟩
end Tool
end YM.MergeProof.Matric
#print axioms YM.MergeProof.Matric.Tool.tuneR
