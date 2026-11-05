import YM.AnalyticNext.GRID_STOP_ATTENUATION.Coarrival.Core
import YM.MergeProof.North.Dolphin
import YM.MergeProof.North.Prax
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
variable {G:Gauge} {n:Side} (C:Family G) (J p N j d:ℕ){k:ℕ}
local notation "H"=> C.path
variable (a:Site (C.side j p))(hj:j≤N) (hJ:J ≤ N) (f:Bool→ Config G (C.side N p)→ℂ)
local notation "ε"=> C.S.a J
local notation "y"=> (C.S.place a)
local notation "T"=> center C.S p hJ 0
local notation "v"=> Site (C.side J p)
local notation "P"=> hands C p J
local notation "ξ"=> Mix.camp C p J
variable (hf :∀ i,Continuous (f i))
def capped (x:Name (Site (C.side J p))):Config G (C.side N p)→ℂ:= (center C.S p hJ 0).copy x.1 (f x.2)
local notation "r"=> capped C J p N hJ f
include hJ
lemma canned (i : v)(b) : r (i,b)= stepUp (hands C p J i) (ξ N i) (f b):= (handmove C N p J hJ ..).symm
lemma cappid (i): r (0,i)=f i:=by rw [canned,zeroMama C J p N hJ,P_on,stepid]
lemma cappedC (i:Name v)(hc:Continuous (f i.2)):Continuous (r i):=by unfold capped; unfold Tiling.copy; split <;> first| exact (hc.comp (continuous_pull ..)).star| exact hc.comp (continuous_pull ..)
lemma cap_mul (i:v) (c): r (i,false) c *r (i,true) c=(T).copy i ((f false)*(f true)) c:=by unfold capped Tiling.copy; split <;> simp
omit hJ
lemma ratio_same {c n:Side}(z : Ratio c n)(x:Ratio c n) : x=z:=by
   obtain ⟨x,hx⟩:=x; rcases z with ⟨z,hz⟩; suffices h': x=z by cases h'; rfl
   exact Subtype.ext ((Nat.eq_of_mul_eq_mul_left c.property) (hx.symm.trans hz))
end
-- Official interface (constructed carrier)
section
variable {G:Gauge}(C:Family G)(N p d k J:ℕ)
open Next.Foundations
structure Created (C:Family G):Prop where
    uses : ∃ (H:History G) (t:ℕ→ℕ) (S:∀ d N p:ℕ,TransferData ((Labels.frames G).level d) H N p), C= Family.mk H (hol G) (Labels.frames G) (localSection G) t S
local notation "R"=> C.path.rep N p
variable {u:Type}[Fintype u][DecidableEq u](v:u→Motion)(f:u→Site (C.side k p))(w:u→ℝ)(p':Config G (C.side k p)→Poly (Bud u))
lemma Created.bridge (h:Created C){x:ℝ}(hp:∃ Q:Coefficient ((Labels.frames G).level d) (C.side k p), Q.Format 0 (Next.Foundations.hol G) (R k) ∧ Q.remBound 0 (R k) (kappa C.path k) x∧ ((Labels.frames G).level d).coeffSize Q.x ≤ x ∧ Served (R k) (fun i=> radiant (alto C.path k d) (v i) (f i) (Q.exponentialEntry 0 (Next.Foundations.localSection G d) (R k))) (fun i=> sunny (R k) Q.forced (v i) (f i) (alto C.path k d)) p' f w (C.path.levels.budget k).supportExponent 1): ∃ Q:Coefficient (C.labels.level d) (C.side k p), Q.Format 0 C.params (R k) ∧ Q.remBound 0 (R k) (kappa C.path k) x ∧ (C.labels.level d).coeffSize Q.x ≤ x ∧ Served (R k) (fun i=>radiant (alto C.path k d) (v i) (f i) (Q.exponentialEntry 0 (C.localSection d) (R k))) (fun i=>sunny (R k) Q.forced (v i) (f i) (alto C.path k d)) p' f w (C.path.levels.budget k).supportExponent 1 :=by obtain ⟨H,t,S,h⟩:= h.uses; subst C; exact hp
end
end YM.MergeProof.Ribbons
