import YM.MergeProof.East.Largo
import YM.TraceExtension.Prom.Orion.Medal
import YM.TraceExtension.Prom.Orion.Pint
import YM.TraceExtension.Prom.Orion.Plume
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ} {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ℕ → ι → Tapes.Panel D) (Z:ArcSky P) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels

variable (z:ℝ) (hZ : ∀ i≤D,Accent.generator G i≤ z)
variable {x y w:ι}{c:ℝ}
-- pricing bands and purchasing
-- declarations
include H h hZ hp Z
lemma podiumSky (F:Extraction.Order)(hn:2≤n)(R:ℝ)(hr:0<R)(hs:(standard C).Smooth)(H':(standard C).RealSpin) (q:ι→ℝ) (Lz:ℕ→ℝ) (hL:∀ k,0≤ Lz k) (hh:∀ k i,(P k i).arc=q i+Lz k) (g:Checks (q x) (q y) (q w) c n D)
    (f:ℕ→ℕ)(hf:Tendsto f atTop atTop)(Y:ℕ→ℕ→ℕ→TableL C D)(hY:∀ i,PoisedSky (P (f i)) B H O J n z (f i) (Y i)) : Granular (D:=D) (fun i=>wok C D (f i) (P (f i) x).arc c (Y i)) F H' n R:=by
   let K:= fun i=>wok C D (f i) (P (f i) x).arc c (Y i); have hx(i):= w_rightSky c F H' (P (f i) x).arc (hY i)
   obtain ⟨η,u,hD,hp'⟩:=Z.wave
   have he : Tendsto (fun i=>(K i).r) atTop (𝓝 0):= by
      apply squeeze_zero (fun i=>(K i).rad.le) _ ((Station.gap_rate A h (η x+1)).comp hf)
      intro i; change Station.gap _ _ _ ≤ Station.gap _ _ _; unfold Station.gap; exact mul_le_mul_of_nonneg_left (Wall.mag_rank A ((hp' x (f i)).trans_le (add_le_add_right (hD _).2 _)) _) ((A).S.a_pos _).le
   refine ⟨⟨Eventually.of_forall (fun i=>(hx i).1),?_,?_,?_⟩,he,fun m hm t ht w=> aspectSky P Z B H h hp O J z hZ F hn R hr hs H' q Lz hL hh g t ht (depthWord t w) hm hf Y hY ⟩
   · exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.1
   · exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.2.1
   exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.2.2

-- procurement market
end YM.MergeProof.East
