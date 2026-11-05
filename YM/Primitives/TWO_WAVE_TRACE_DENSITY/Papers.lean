import YM.AnalyticNext.CALENDAR_SCENE_ADAPTER.ThermalRule
import YM.Next.EXTRACTION.Use
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Heating
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Migrations

/-!
# All coherent jets with cover-width estimates
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave.RealSlice
open Set Filter Lattice RG Precision Tree Bid Matrix Laurent
open Progress.ClassicalKin Progress.ClassicalKin.Tent Function Wilson
open Push.Uniform
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge}(P:Patch)(K:KernelChoices) {n:Side}
local notation "T[" n "]" => trees P K n
local notation "μ[" n "]" => dock P K n
-- Varies only P through L and J, with Before's real chart purchases
-- universal. Receipt for values on that *same* family post-L.
variable {μ C : ℝ} (p:Clip) (A: Before G μ C P.J K 4)







abbrev ActiveLeaf (P:Patch)(K:KernelChoices)(n:Side)(G:Gauge):=Leaf n (Vertical G P K)

-- pure period family before publishing

def house (R:PathData G)(n:Side) : Invoices (Coarse G) (Vertical G P K) n ℝ:=
    let seed := extractF (titles P K p R n 2)
    let U : Matrix (ActiveLeaf P K n G) (ActiveLeaf P K n G) ℝ:= (base seed).submatrix (TwoWave.peg _) (TwoWave.peg _)
    ⟨seed,extractF (titles P K p R n 3),extractF (titles P K p R n 4),U⁻¹,0,0⟩
-- separate tail selection O common

def estates (O:ChartRatio G)(R:PathData G)(n:Side):Invoices (Coarse G) (Vertical G P K) n ℝ:={house P K p R n with
    nonLoop₁:=extractF (outro P K O R n 1)
    nonLoop₂:=extractF (outro P K O R n 2) }

def outline (R:PathData G)(n:Side):Matrix (ActiveLeaf P K n G) (ActiveLeaf P K n G) ℝ:=
    (base (house P K p R n).seed).submatrix (TwoWave.peg _) (TwoWave.peg _)
lemma outline_frame (R:PathData G)(hn:Ad G P K n)(Λ:ℝ)(hb:R.Bounds p μ C Λ):
    let h:=enough P K hn
    let X:=hessian T[n] (label μ[n]) p R 0 0
    outline P K p R n=(X.submatrix (insider P K G h) (insider P K G h)):=by
  have he:ContDiffAt ℝ ω (uncurry (tested T[n] (label μ[n]) p R)) (0:Bid.Dir G n×AxisChart G T[n]) := (price_identity _ _ hb hn.1).1
  intro h X; let S:= value P K p R h
  unfold outline house; dsimp only
  rw [← value_glue P K p R h 1]
  let f := uncurry (tested T[n] (label μ[n]) p R)
  let L:=(equip G P K h).toContinuousLinearMap
  have ht : ContDiffAt ℝ ω S 0:= (show ContDiffAt ℝ ω f (L 0) from by rw [map_zero]; exact he).comp (f:=equip G P K h) _ (equip G P K h).contDiff.contDiffAt
  rw [vertical_flat ht]
  ext i j
  change iteratedFDeriv ℝ 2 (f ∘ L) 0 _=X _ _
  rw [Next.Foundations.jets_linear L (he.of_le le_top),ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hh s : L (0,spot s)=(0,frame T[n] (insider P K G h s)):=Prod.ext (map_zero (surfaceIn G n)) (surface_frame ..)
  let e:= insider P K G h
  rw [show (fun i' : Fin 2=> (fun (_:Fin 2)=>L) i' (![((0:Board (Coarse G) n ℝ),spot i),(0,spot j)] i'))= ![((0:Bid.Dir G n),frame T[n] (e i)),(0,frame T[n] (e j))] by ext1 k; fin_cases k <;> exact hh _]
  exact (AnalyticNext.CalendarScene.adjacents (show ContDiffAt ℝ ω f ((0:Bid.Dir G n),0) from he) (frame T[n] (e i)) (frame T[n] (e j))).symm


end YM.Primitives.TwoWave.RealSlice
