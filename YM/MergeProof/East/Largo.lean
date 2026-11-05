import YM.MergeProof.East.Medal
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
variable (P:ι → Tapes.Panel D) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "S"=> standard C
variable (z:ℝ) (hZ : ∀ i≤D,Accent.generator G i≤ z)
variable {x y w:ι}{c:ℝ}
-- pricing bands and purchasing
-- declarations
include H h hZ hp
lemma podium (F:Extraction.Order)(hn:2≤n)(R:ℝ)(hr:0<R)(hs:(S).Smooth)(H':(S).RealSpin) (g:Checks (P x).arc (P y).arc (P w).arc c n D)
   (hw:∃ᶠ k in atTop,∃ Y,Poised P B H O J n z k Y) : ∃ W', Granular (D:=D) W' F H' n R:=by
   obtain ⟨f,hf,hh⟩:= extraction_of_frequently_atTop hw; choose Y hY using hh
   let a:= (P x).arc;let K:= fun i=>wok C D (f i) a c (Y i); have hx(i):= w_right c F H' a (hY i)
   have he := hf.tendsto_atTop
   refine ⟨K,⟨Eventually.of_forall (fun i=>(hx i).1),?_,?_,?_⟩,(Station.gap_rate A h a).comp he,fun m hm t ht w=> aspect P B H h hp O J z hZ F hn R hr hs H' g t ht (depthWord t w) hm he Y hY ⟩
   · exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.1
   · exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.2.1
   exact Eventually.of_forall fun i=> (hx i).2.mono fun j h=> h.mono fun k hk=> hk.2.2
omit H h hZ hp in
lemma reduce_wave {D M k' k:ℕ} {R:ℝ} (W:ℕ→Wheel C D) (H:(S).RealSpin)(F:Extraction.Order)(h:Granular W F H k R)(hd:M≤D)(hk:k' ≤ k): ∃ V, Granular (D:=M) V F H k' R:=by
    let f(x : Fin (M+1)):Fin (D+1):=⟨x,(Nat.lt_of_lt_of_le x.isLt (Nat.add_le_add_right hd 1))⟩; let V:ℕ→ Wheel C M:= fun i=> {r:=(W i).r,rad:=(W i).rad, grid:=(W i).grid, σ:=(W i).σ,stripe:=(W i).stripe,atCut:=fun z x=>(W i).atCut z (f x)}
    refine ⟨V, ⟨h.grants.mono (fun i hk=> ?_), h.central,h.real.mono (fun i hi=> hi.mono fun j hj=>hj.mono fun k hk u=> hk (f u)),h.h_symm.mono (fun i hi=> hi.mono fun j hj=>hj.mono fun k hk u=> hk (f u))⟩,h.small,?_⟩
    · obtain ⟨a,hA⟩:= hk; refine ⟨max a 0,hA.mono fun i hi=>hi.mono fun j hj=> (pi_norm_le_iff_of_nonneg (le_max_right ..)).2 (fun k=> (norm_le_pi_norm (W _|>.atCut _) (f k)).trans (hj.trans (le_max_left ..)))⟩
    intro n hn t hu x
    obtain ⟨e,a,b,hB⟩:= h.proof_ n (hn.trans hk) t (fun i=>(hu i).trans hd) x
    refine ⟨e,a,b,hB.goes,hB.stripe,hB.room,hB.pos,hB.off,hB.on_,hB.costs.mono fun i hi=>?_⟩
    exact ⟨hi.compare,hi.crude,hi.slab⟩
-- procurement market
end YM.MergeProof.East
