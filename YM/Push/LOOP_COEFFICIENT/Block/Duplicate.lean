import Mathlib.Analysis.PSeries
import YM.Push.LOOP_COEFFICIENT.Block.Portal
import YM.Push.LOOP_COEFFICIENT.Fine.Operators

/-!
# Replicating a site vertex while keeping spatial counting
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Matrix Set Filter Metric Lattice Laurent RG Wilson Bloch Complex Portal Fine
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {L c f : Side} {g : Ratio c f} {G : Gauge} {η C : ℝ}

abbrev ScalarBlock (G : Gauge) (L : Side) := Co L G.ColorIndex
abbrev VectorBlock (G : Gauge) (L : Side) := Co L (Axes G)

def install (G : Gauge) (L : Side) : Matrix (ScalarBlock G L) (ScalarBlock G L) ℂ →ₗ[ℂ] Matrix (VectorBlock G L) (VectorBlock G L) ℂ where
  toFun M := of fun i j => if i.2.1=j.2.1 then M (i.1,i.2.2) (j.1,j.2.2) else 0
  map_add' _ _ := by ext ⟨i,k,a⟩ ⟨j,l,b⟩; by_cases k=l <;> simp [*]
  map_smul' _ _ := by ext ⟨i,k,a⟩ ⟨j,l,b⟩; by_cases k=l <;> simp [*]

def duplicate (V : Vertex (Axes G) (ScalarBlock G L) (ScalarBlock G L)) : Vertex (Axes G) (VectorBlock G L) (VectorBlock G L) := ⟨fun q => install G L (V.base q), fun q p => (install G L).comp (V.one q p), fun q p s => (V.two q p s).compr₂ (install G L)⟩
lemma install_eval (V) (v : CSpace (VectorBlock G L)) (x i j) : (install G L V *ᵥ v) (x,i,j) = (V *ᵥ fun y : ScalarBlock G L => v (y.1,i,y.2)) (x,j) := by simp [install,mulVec,dotProduct,Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel]
lemma cab_routed {q p M V} (h : Routed (coarseNodes G g) (coarseNodes G g) q p M V) : Routed (coarseLinks G g) (coarseLinks G g) q p (parallel M) (install G g.count V) := by
  refine Routed.of_vector fun v => funext fun ⟨⟨x,i⟩,a⟩ => ?_
  have hW (x i a) (p : Site c) (w) : (plane (coarseLinks G g) p *ᵥ w) ((x,i),a) = cell p (g.parent x) * w (g.residue x,i,a) := by simp [plane_apply,coarseLinks,linksGrid,split_co]
  rw [hW,install_eval, show (parallel M *ᵥ _) ((x,i),a) = _ from Fine.parallel_eval M _ (x,a) i, show (fun s : SiteKey G f => (plane (coarseLinks G g) p *ᵥ v) ((s.1,i),s.2)) = plane (coarseNodes G g) p *ᵥ (fun y => v (y.1,i,y.2)) from funext fun j => by rw [hW,plane_apply]; simp [coarseNodes,nodesGrid,split_co],h.vector,plane_apply]; simp [coarseNodes,nodesGrid,split_co]
open scoped Matrix.Norms.Frobenius in
lemma duplicate_models {X V} (h : Models (linksGrid G c) (coarseNodes G g) (coarseNodes G g) X V) : Models (linksGrid G c) (coarseLinks G g) (coarseLinks G g) (fun z => parallel (X z)) (duplicate V) := by
  let T := (parallelMap G f ℝ).toContinuousLinearMap
  refine ⟨T.contDiff.contDiffAt.comp (f:=X) 0 h.smooth,?_⟩
  change Synced _ _ _ (actual cmat (T ∘ X)) _; erw [actual_push cmat cmat T (parallelMap G f ℂ) h.smooth (fun x => Matrix.ext fun i j => by change ((parallel x i j:ℝ):ℂ) = parallel (cmat x) i j; by_cases i.1.2=j.1.2 <;> simp [parallel, *,cmat_apply,Bloch.approached])]
  exact ⟨fun hq => cab_routed (h.sync.base hq),fun hq hp v => cab_routed (h.sync.one hq hp v),fun hq hp hs v w => cab_routed (h.sync.two hq hp hs v w)⟩













end YM.Push.Loops.Block
