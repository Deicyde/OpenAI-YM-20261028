import YM.WilsonBulk.Trees.Identity
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Tiling

/-! Boost a common tree model to the periods. For bulk Fourier use the SAME
map from fine links and directions in every lifted coarse cell, inexhaustibly.
Exporter over any chosen reference (feed in coordinate tree once). -/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open RG Finset Precision Exterior Stationary Audience Matrix FreeResolvent Tree
open Work.F08 Lifted Primitives.TwoWave
open Primitives.TwoWave.RealSlice (three)
open Progress.ClassicalKin Progress.ClassicalKin.Tent
open scoped Topology BigOperators Matrix

variable {c f : Side} {G : Gauge} (P : Patch) (K : KernelChoices)
abbrev Model := Forest (dock P K three).ratio
variable {P K} (T : Model P K)
abbrev master : Ratio three (three*P.L) := (dock P K three).ratio -- check

variable (v : f.val=c.val*P.L.val)
def spreadForest : Forest (data v K).ratio := rebuild (K:=K) (P:=P) T (fun _=>0) (h':=v) (hh:=le_refl 3) -- check

lemma copied_hike (o : Site f) : (spreadForest T v).hike o =
    T.hike ((dock P K three).ratio.assemble (0,(data v K).ratio.residue o)) := by
  let g:= (data v K).ratio; let g':=(dock P K three).ratio
  let x (o : Site f) := g'.assemble (0,g.residue o)
  let X := spreadForest T v
  have ht (o): X.up o=T.up (x o) := rfl
  have hh (o): leaf g o ↔ leaf g' (x o) := by
    have hv : g'.residue (x o) = g.residue o := g'.assemble_res _
    simp only [Tree.leaf, ne_eq,g'.root_id,g.root_id]; rw [hv]; rfl
  change X.hike o=T.hike (x o)
  induction o using Forest.hike.induct X with
  | case1 i hi ih =>
    have hP := T.stays _ ((hh i).1 hi)
    have he : x (i+(X.up i).vec)=x i+(X.up i).vec := by
      have hj : carry (g.residue i) (X.up i).vec=0 := by
        erw [ht i,← show g'.residue (x i)=g.residue i from g'.assemble_res _]; exact tiny _ _ _ (le_refl 3) hP
      rw [← wrap_vec (below P three),Work.F08.moves_site g', show g'.residue (x i)=g.residue i from g'.assemble_res _]
      unfold x; rw [← wrap_vec f,Work.F08.moves_residue]
      congr 2
      erw [Ratio.assemble_parent,hj]; simp
    conv_rhs => rw [Forest.hike,dif_pos ((hh i).1 hi)]
    rw [Forest.hike,dif_pos hi,ih,he,ht]
  | case2 i hi => rw [Forest.hike,dif_neg hi,Forest.hike,dif_neg ((hh i).not.mp hi)]

end YM.WilsonBulk
