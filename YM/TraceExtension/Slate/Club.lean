import YM.TraceExtension.Slate.Ven
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Slate
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Perfect Turret Margin
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
variable (P:C.Makes) (h:G.Simple) (θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W) (hT:supportQ C.path.levels)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} (hb:(𝓛:Filter (ℕ×ℕ))≤F.fuse)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "V!"=> C.path
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
local notation "H!"=> C.path.levels.clock.hatBeta
variable {t:Tickets C} (hu:Grant C (𝓛:Filter (ℕ×ℕ)) t)
open Zn
variable {d:ℕ}{Z:Arch C}(hz:steep 𝓛 Z)
open Finset StressFlux
lemma core_acts {d:ℕ}(F':Frame G d)(s:Motion)(v:F'.Coeff): F'.core (Prism F' s v)= Prism F' s (F'.core v):=by
    unfold Prism Motion.patch; simp only[LinearMap.coe_mk,AddHom.coe_mk,apply_ite]; split; · rw[Push.Local.core_star,← Push.Local.core_act]
    rw[← Push.Local.core_act]
def OrbitR(Y:Frame G 5): (Axis→ Y.Coeff)→L[ℝ] Bowl Y:= LinearMap.toContinuousLinearMap ((Reed (Prism Y)).codRestrict (Bowl Y) (blade Y))
def OrbitT(Y:Frame G 4): (Axis→ Axis→ Y.Coeff)→L[ℝ] (Axis → Axis→ Y.Coeff) := LinearMap.toContinuousLinearMap (Plot (Prism Y))
lemma orbit_core (F':Frame G 5)(v:Axis→ F'.Coeff): OrbitR F' (fun i=>F'.core (v i))=OrbitR F' v:=by
   let U:=OrbitR F'; have he(a):F'.core ((U v).val a)= (U v).val a:=nights F' (frames_night F' (U v) a); refine Subtype.ext (funext fun a=>?_)
   change _=(U v).val a; rw [← he]; change Reed (Prism F') _ _ = F'.core (Reed (Prism F') v a); let L:= F'.core.restrictScalars ℝ
   rw[reedEq,reedEq]; change _=L _;rw[map_sum L]; refine sum_congr rfl fun i _=>?_ ; rw [map_smul L]; exact congr_arg ( (rent*hued i a) • · ) (core_acts F' i (v (prev i a))).symm
lemma MintR_eq (F':Frame G 5)(h:G.Simple): MintR F' h=(Lease F' h).comp (OrbitR F'):=rfl
include hb hz P ht
lemma stomp (i:ℕ)(hj:C.ref d ≤ i)(s:Motion)(v:C.label d): swale Z d i (Prism (C.labels.level d) s v)=Prism (C.labels.level d) s (swale Z d i v):=by
   let F':= C.labels.level d; rw [land,land,map_smul,←core_acts]
   have he:Z.M d i (Prism F' s v)=Prism F' s (Z.M d i v):=by
      change _= Motion.patch _ _ _; unfold Prism Motion.patch; simp only[apply_ite,LinearMap.coe_mk,AddHom.coe_mk]; split
      · rw [move_anchor_star hz P hb ht hj,move_anchor hz P hb ht hj]
      rw [move_anchor hz P hb ht hj]
   rw[he]
lemma stroke (i:ℕ)(hj:C.ref 5≤ i)(x:Axis→ C.label 5)(a:Axis): swale Z 5 i ((OrbitR (C.labels.level 5) x).val a)=(OrbitR (C.labels.level 5) (fun a=> swale Z 5 i (x a))).val a:=by
    let L:= (swale Z 5 i).restrictScalars ℝ; change L (Reed _ x a)= Reed _ _ a; rw[reedEq,reedEq,map_sum L]; exact sum_congr rfl (fun j _=> (L.map_smul _ _).trans (congr_arg ( (rent*hued j a) • · ) (stomp P ht hb hz i hj j (x (prev j a)))))
lemma strikes (i:ℕ)(hj:C.ref 4≤ i)(x:Axis→Axis→ C.label 4)(a b:Axis): swale Z 4 i (OrbitT (C.labels.level 4) x a b)= OrbitT (C.labels.level 4) (fun a b=> swale Z 4 i (x a b)) a b:=by
    let L:=(swale Z 4 i).restrictScalars ℝ;change L (Plot _ x a b)= Plot _ _ a b; rw[plotEq,plotEq,map_sum L];exact sum_congr rfl (fun j _=> (L.map_smul _ _).trans (congr_arg ( (rent*hued j a*hued j b) • · ) (stomp P ht hb hz i hj j _)))
end YM.Trace.Slate
