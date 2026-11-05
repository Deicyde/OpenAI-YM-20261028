import YM.MergeProof.Canopy
import YM.MergeProof.East.Ladle
import YM.MergeProof.East.Plume

/-! Endpoint in stamping coordinates and uniform over fit x -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ} {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ι → Tapes.Panel D) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "S"=> standard C
variable (z:ℝ) (hZ : ∀ i≤D,Accent.generator G i≤ z)
variable {R : Set (Points (m+1))} {t :Fin (m+1)→Fin (D+1)} (y: (i:Fin (m+1))→ C.label (t i)) (x:ι)
set_option quotPrecheck false
local notation "a" => (P x).arc
-- conversion putting arc equal. spectral posterior used to READ using actual purchase.
-- pb proof assistant small
include H h hp hZ
lemma lava_v (hR:IsCompact R)(hi:R ⊆ conf _) (hn:2≤n)(hn':m+1 ≤ n) : ∀ᶠ k:ℕ in atTop,
    ∀ T,Poised P B H O J n z k T→ ∀ N p (he:k<N),
     let v(i):= ladd C (mag A a k) k N p _ (T N p (t i)) (y i)
     ∀ (w : Points (m+1)), (tested A a k w)∈R →∀ h:Fit A a k w,∀ s : modes (Fin (m+1)),s.val.Nonempty →
       (Ship.yard C a he.le p).rootTest (C.beta N p) (fun U=> (Ship.invoice (jointX y) (q_asked (C:=C) (d:=fun i=> (t i).val) v) h N p U).part s) ≤ Ship.budget C.path.levels n k:=by
   filter_upwards [earnings B H h hp O J (P x) hZ (d0:=fun i=>(t i).val) y hn' hn (fun i=>Nat.le_of_lt_succ (t i).isLt) hR hi] with k hu T he N p hN
   intro v w hw hs s hv
   let K (x:ℝ)(h:Fit A x k w):=(Ship.yard C x hN.le p).rootTest (C.beta N p) (fun U=> (Ship.invoice (jointX y) (q_asked (C:=C) (d:=fun i=>(t i).val) v) h N p U).part s)
   obtain ⟨l,r,F,hF⟩:=he.supply x; obtain ⟨V,hV,hx⟩:= hF N p hN
   choose Y hy using hx
   let θ := (P x).bag ((A).clock.J k);have ha:θ.band=a:= (P x).factor _
   have hf:Fit A θ.band k w:=ha.symm ▸ hs
   have hg(i): Price.Solves C (mag A θ.band k) _ k N p (Y (t i)).T (y i) (v i):= by
      rw [ha,hy]; exact poured H (he.early _ (Nat.le_of_lt_succ (t i).isLt)) hN.le _ _ (he.charts N p hN (t i)).1 _
   have hQ : K θ.band hf ≤ Ship.budget C.path.levels n k:= hu l r F N p hN V hV w (ha.symm ▸ hw) hf (fun i=> Y (t i)) v hg s hv
   change K a hs ≤ _; suffices hh:∀ (h:Fit (A) a k w), K a h ≤ Ship.budget (A) n k from hh hs; rw [← ha]; intro h; exact hQ
end YM.MergeProof.East
