import YM.RG08.Yamen.Crown

/-! # Construct independent unmarked Fk on this exact H with all stages announcing
 lengths/pre curves. No derivatives of the actual reports. No assumptions carrying packets
 or stable lines. -/
noncomputable section
namespace YM.RG08.Yamen
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason Supplies Flat Filter
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable {G:Gauge}{a:Levels G}(F:Horizon a)(P X:MapPrices)(hg:G.Simple)(Z:ChartRatio G)

theorem branches (i:ℕ): (stone a i).Branches a.clock.kernel G:= (a.blocks i 0).branches
-- stamp convention hp0 branches at θ actual geometry. T depends on N path H N i!
def mint (N i:ℕ)(C:Castle G):Castle G:=Nacre.send (wild (lamp P X a i) (Yamen.base P X a i (F.H N i)) C Z (branches (a:=a) i) (F.H N (i+1)) (F.H N i)) hg
def shed (N:ℕ):ℕ→Castle G
| 0=>Yamen.top G
| j+1=>mint F P X hg Z N (N-(j+1)) (shed N j)
def fed (N i:ℕ):Castle G:=shed F P X hg Z N (N-i)

variable {F P X hg Z}
lemma top_eq (N:ℕ):fed F P X hg Z N N=Yamen.top G:=by unfold fed;rw [Nat.sub_self,shed]
lemma mint_step {N i:ℕ}(h:i<N): fed F P X hg Z N i=mint F P X hg Z N i (fed F P X hg Z N (i+1)):=by unfold fed; nth_rw 1 [show N-i=N-(i+1)+1 by omega];rw [shed,show N-(N-(i+1)+1)=i by omega]

structure Supplies (F:Horizon a)(P:MapPrices)(Z:ChartRatio G):Prop where
 housed : F.Suffices P
 herald : ∀ N i c,i ≤ N → Bid.Sworn (F.H N i) c G
 lodged : LocalRatio Z
variable (X)(hg)
lemma ship (h:Supplies F P Z){N i:ℕ}(ht:i ≤ N): Tires (F.H N i) (fed F P X hg Z N i):=by
 generalize he:N-i=j
 induction j generalizing i with
 | zero=>have heq:i=N:=by omega
         subst i;rw [top_eq];exact trial _ h.housed
 | succ n ih=>
   have hi:i<N:=by omega
   have hp:=ih (i:=i+1) hi (by omega)
   let C:=fed F P X hg Z N (i+1); let k:=a.clock.kernel; let T:=stone a i
   let B:=Yamen.base P X a i (F.H N i); let w:= (F.H N (i+1));let v:=F.H N i
   obtain ⟨⟨H⟩,hT⟩:= studio (X:=X) h.housed N i hg hi (fun _=>h.herald _ _ _ hi.le) h.lodged C hp
   have h:= (Nacre.proceeds (Y:=Z) C hg T k H B hT (branches (a:=a) i) (lamp P X a i)).1
   rw [mint_step hi];exact h
end YM.RG08.Yamen
