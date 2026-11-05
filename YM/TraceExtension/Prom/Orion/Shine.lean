import YM.MergeProof.East.Shine
import YM.TraceExtension.Prom.Orion.Plume
import YM.TraceExtension.Prom.Orion.Reach
import YM.TraceExtension.Prom.Front.West.Lys
import YM.TraceExtension.Prom.Front.West.Tael
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Incoming
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ} {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ℕ→ ι → Tapes.Panel D) (Z:ArcSky P) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels

variable (z:ℝ) (hZ : ∀ i≤D,Accent.generator G i≤ z)
open Analysis Next.UVStress Climb Ward
include H h hZ hp Z
lemma soleSky (F:Extraction.Order)(hn:2 ≤ n)(x:ι)(d:Fin (D+1))(v:C.label d) :∃ Q:ℝ,0 ≤ Q ∧ ∀ᶠ k:ℕ in atTop, ∀ Y,PoisedSky (P k) B H O J n z k Y→
     ∀ᶠ i in F.fuse, centeredBudget C ⟨d,ladd C (mag A (P k x).arc k) k i.1 i.2 d (Y i.1 i.2 d) v⟩ Q (Next.Rank.Station.widthSky A (P k x).arc k) i.1 i.2:=by
   let V : Fin (0+1) → Fin (D+1):= fun _=>d
   let w : (i:Fin (0+1))→C.label (V i):= fun _=>v
   let o : Points (0+1):=0; let u:=jointX w;let x0:modes (Fin (0+1)):=slot 0; let r:ℂ:= (Read.maxProfile C o u).part x0
   have he:o∈generic _:= fun _=> (Function.injective_of_subsingleton (α:=Fin 1) _); let T:= (singleton o:Set _)
   refine ⟨1+‖r‖,by positivity,?_⟩
   filter_upwards [lava_vSky P Z B H h hp O J z hZ w x (t:=V) isCompact_singleton (Set.singleton_subset_iff.mpr (generic_conf _ he)) hn (by omega), (Ship.diminishes A n h (show 0<n by omega)).eventually (ge_mem_nhds (zero_lt_one' ℝ))] with k hi hz Y hY
   let b:=(P k x).arc
   obtain ⟨l,j,a,h⟩:=hY.supply x
   have hA:AllowedSky A b k:=by unfold b; rw [← (P k x).factor (C.path.levels.clock.J k)]; exact a.age.allot.permitted
   have ht0: Next.Rank.Station.choose A b k o=0:=by ext;simp [Next.Rank.Station.choose,address,o]
   have ht:Next.Rank.Station.tested A b k o=o:=by rw [Station.tested,Station.key,ht0]; change _ • tag _ _= _; ext;simp [Extraction.tag,points,o]
   have hv0 : Next.Rank.Station.key A b k o=0:= by unfold Next.Rank.Station.key; rw [ht0]; ext;simp [Extraction.tag,points]
   have hF: FitSky A b k o:= ⟨hv0.symm ▸ he, fun i j=>by rw [hv0]; change |(0:ℝ)| ≤ _; rw [abs_zero]; exact div_nonneg ((A).S.a_pos _).le (by norm_num)⟩
   let s:=widthSky A b k
   filter_upwards [large_mesh F (k+1), (show ∀ᶠ i : ℕ × ℕ in F.fuse, ∀ (h : s ≤ i.1), ∀ x:Site (C.side i.1 i.2),∀ v:C.label d, Interior ((Cells.center C.S i.2 h x).chamber 0) (C.O i.1 i.2 v x) from by
       rw [Extraction.Order.fused]; unfold Extraction.Order.late; refine Eventually.of_forall fun p=> (F.mesh.cofinal.eventually (Stock.clear_interior C H s d)).mono fun i h _=>h.choose_spec _)] with i hu hI
   let y:=ladd C (mag A b k) k i.1 i.2 d (Y i.1 i.2 d) v;let a:= C.O i.1 i.2 y 0
   have hj : k< i.1:= hu; have hk : s ≤ i.1:= (widerSky ..).trans ((beforeSky ..).trans hj.le)
   let W:=Ship.yardSky C b hj.le i.2; let β:= C.beta i.1 i.2
   have hP:= hi Y hY i.1 i.2 hj o (show _ ∈ ({o} : Set _) by rw [ht]; simp) hF x0 (show ({0} : Finset (Fin (0+1))).Nonempty from Finset.singleton_nonempty _)
   let t:= fun _ : Fin (0+1)=> (⟨d,y⟩:C.book.Token); let q:=Read.probes C i.1 i.2 k (Next.Rank.Station.choose A b k o) t
   have hS:q 0=a:=by unfold q Read.probes; rw [ht0]; change C.O _ _ _ (Cells.location C.S k _ _ 0)= _; rw [location_origin]
   let x:Config G (C.side i.1 i.2)→ℂ:= fun U=> (Ship.invoiceSky u t hF i.1 i.2 U).part x0
   have hπ: x=a-r • (1 : Config G (C.side i.1 i.2) → ℂ):=by
       funext U; change (Read.cylinder (Read.cumulants C _ u _) q U).part (slot 0)=_
       rw [Read.cylinder_single (Read.cumulative ..),hS,show (Read.maxProfile C _ u).part x0=r from congr_arg (fun i=> (Read.maxProfile C i u).part x0) ht]
       change _=a U-r*1; rw [mul_one]
   have hv: Interior (W.chamber 0) a:= hI hk 0 y
   have hx: Interior (W.chamber 0) x:= Read.raw_in W q (fun i=>by rw [(Subsingleton.elim (α:=Fin 1) i 0),hS]; exact hv) (Read.cumulants C _ u _) x0
   refine ⟨hk,(hY.early _ (Nat.le_of_lt_succ d.isLt)).trans hj.le,fun i' => ⟨hI _ _ _,?_⟩⟩
   change (center C.S i.2 hk i').rootTest β (C.O i.1 i.2 y i')≤1+‖r‖
   rw [show (center C.S i.2 hk i').rootTest β _= W.rootTest β a from Stock.translate_s hk i' ⟨d,y⟩ hv,show a=x+r • 1 by rw [hπ,sub_add_cancel]]
   refine ((seamless H i.1 i.2).semi W x _ hx ((show Interior (W.chamber 0) (1:Config G _ → ℂ) from Interior.constant _ (1:ℂ)).scale r)).trans ?_
   change W.rootTest β x+ W.rootTest β (r•(1:Config G (C.side i.1 i.2)→ℂ)) ≤ _; rw [Next.Extract.root_smul,Tiling.root_one,mul_one]; exact add_le_add_left ((show W.rootTest β x≤ _ from hP).trans hz) _
end YM.MergeProof.East
