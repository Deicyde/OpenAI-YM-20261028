import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.RemainderComparison.Lobby.Gas
import YM.RemainderComparison.Flues.Finance

/-!
# Rotating packed address book without losing orientation in chosen rep

Transport as in PROJECTOR_EQUIVARIANCE. We keep the old test exactly;
no replacing test by the claim that all flagged outputs are zero.
Rotating the NULL portion, not all marks (retain source locations);
where the vacuum payload is zero we can add empty lecterns.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Jolt
open Function Filter Finset Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Push Push.AbsoluteSums PhysicalNext.Repeat
open Merge Mosaic Mosaic.Verse Marker
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PhysicalNext.Repeat AnalyticBridge VerifiedReset Collection Quotes
open Flues ProjectorNext.Equivariance
variable {G : Gauge} {c : Side} {ι θ Ω : Type*}{V:Config G c}

def standing (c:Side): Seat c:= (1,0)
lemma stun (p:Support c) : Seat.spread (standing c) p=p:= by
   unfold Seat.spread standing; rw [show (affine (Prod.fst _) (Prod.snd _))= (id : Site c→Site c) from ?_]; exact image_id
   funext; simp [affine]
lemma stamp (V:Config G c) : Seat.view (standing c) V=V:= by change pull 1 0 V= _; rw [pull_one]; funext; simp [Lattice.translate]

def spring (A:ForcedAddress G c)(s:Seat c):ForcedAddress G c:= ⟨s.spread A.support,s.spread A.inventory,A.inventory_ne.image _, image_subset_image A.inventory_sup,A.extraTest ∘ s.view⟩
lemma lock (A:ForcedAddress G c) : spring A (standing c)=A:=by
   obtain ⟨a,b,h,h',w⟩:=A; simp only [spring, stun]; congr; funext; rw [stamp]
lemma movement (A:ForcedAddress G c)(s: Signed)(b:Site c)(i:Seat c) : spring A (Seat.move s b i)= Jolt.spring (spring A i) (s,b):=by
    simp only [spring,i.spread_move, i.view_move]; rfl
-- Full support includes A's inspected.H#.
structure Placed (A:ForcedAddress G c) (t:ℝ):Prop where
     orientation : GaugeInvariant A.extraTest
     measurable : MeasurableSet {x| A.extraTest x}
     reads : UsesFinal t A.support A.extraTest

variable {A:Activities G c}{f:Ω→ ForcedAddress G c}{t:ℝ}
lemma situated {A:ForcedAddress G c} (h: Placed A t) (p: Seat c): Placed (spring A p) t:=by
   refine ⟨fun s U=> ?_, (show Measurable (pull p.1 p.2 : Config G c → Config G c) from (continuous_pull ..).measurable) h.measurable, final_pull p.1 p.2 A.support h.reads⟩
   change A.extraTest (pull p.1 p.2 (Lattice.gauge s U))= _; rw [pull_gauge, h.orientation]; rfl
-- readiness probes
variable {F : ForcedAddress G c}
lemma valids (s: Signed) (b:Site c) (A B:ForcedAddress G c) : spring A (s,b)=B↔ B.support= A.support.image (affine s b)∧ B.inventory=A.inventory.image (affine s b) ∧ ∀ V, B.extraTest V ↔ A.extraTest (pull s b V):=by
    constructor
    · rintro rfl; exact ⟨rfl,rfl,fun _=>Iff.rfl⟩
    rintro ⟨h,h',w⟩; have he : B.extraTest=A.extraTest ∘ pull s b:=funext fun i=>propext (w i)
    obtain ⟨i,j,k,hκ,l⟩:=B; dsimp only at *; subst_vars; rfl
lemma eligible (s:Seat c) (A: ForcedAddress G c) (V:Config G c) : (spring A s).eligible t V ↔ A.eligible t (s.view V) := by
    refine and_congr ?_ Iff.rfl
    let f:=affine s.1 s.2; have ht : Injective f:= affine_injective ..
    have hx:(RG.flags t (s.view V)).image f=RG.flags t V:=Work.H03.flags_send _ _ _ V
    rw [← hx]; change A.support.image f∩ _= A.inventory.image f↔ _; rw [← Finset.image_inter _ _ ht]; exact ((Finset.image_injective ht).eq_iff)

-- condition on Yard for closure. ExtraTest includes dummy entries for Ω large; keep orientations of same real values.
variable {α:Type*} {ι δ:Type}
variable (H:Yard ι α G c) (S:Scone ι α G c)(u:Set ι)

def phase (i:ℕ):= Verse.load u (H.score i)=0
def dawn (i:ℕ):= Verse.load u (S.glyph i)=0

structure Orbit : Prop where
    quiet i : phase H u i→∀ (a b:α),H.glow a i=H.glow b i
    spins (s:Signed)(b:Site c): ∃ p:Equiv.Perm ℕ, ∀ i, (phase H u (p i)↔phase H u i)∧ H.more (p i)=spring (H.more i) (s,b)∧ (phase H u i → ∀ (V:Config G c) a, H.glow a (p i) V= H.glow a i (pull s b V))
structure Whirls : Prop where
    quiet i : dawn S u i→∀ (a b:α),S.glow a i=S.glow b i
    spins (s:Signed)(b:Site c): ∃ p:Equiv.Perm ℕ, ∀ i, (dawn S u (p i)↔dawn S u i)∧ S.leg (p i)=(S.leg i).image (affine s b)∧ (dawn S u i→ ∀ (V:Config G c) a, S.glow a (p i) V= S.glow a i (pull s b V))
end YM.RemainderComparison.Jolt
