import YM.Push.LOOP_COEFFICIENT.Continuum.Orbit
import YM.Push.LOOP_COEFFICIENT.Fine.Algebra


/-!
# Interpreted fine vertices, with regulator corrections explicit
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Fine
open Function Filter Set Matrix Lattice Laurent Exterior Bloch RG Precision Wilson Paths Continuum Complex
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

abbrev VectorRoot (G : Gauge) := Vertex (Axes G) (Axes G) (Axes G)
abbrev GhostRoot (G : Gauge) := Vertex (Axes G) G.ColorIndex G.ColorIndex

def parallelMap (G : Gauge) (n : Side) (R : Type) [Field R] : Matrix (SiteKey G n) (SiteKey G n) R →ₗ[R] Matrix (BondKey G n) (BondKey G n) R where
  toFun := parallel
  map_add' a b := Matrix.ext fun i j => by by_cases i.1.2=j.1.2 <;> simp [parallel, *]
  map_smul' c a := Matrix.ext fun i j => by by_cases i.1.2=j.1.2 <;> simp [parallel, *]

def onAxis (G : Gauge) : Matrix G.ColorIndex G.ColorIndex ℂ →ₗ[ℂ] Matrix (Axes G) (Axes G) ℂ where
  toFun M := of fun i j => if i.1=j.1 then M i.2 j.2 else 0
  map_add' a b := Matrix.ext fun i j => by by_cases i.1=j.1 <;> simp [*]
  map_smul' c a := Matrix.ext fun i j => by by_cases i.1=j.1 <;> simp [*]
lemma parallel_eval (M : Matrix (SiteKey G n) (SiteKey G n) ℂ) (v : CSpace (BondKey G n)) (i : SiteKey G n) (j : Axis) : (parallel M *ᵥ v) ((i.1,j),i.2) = (M *ᵥ fun s : SiteKey G n => v ((s.1,j),s.2)) i := by simp [parallel,mulVec,dotProduct,Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel]
lemma onAxis_eval (M : Matrix G.ColorIndex G.ColorIndex ℂ) (v : Polarization G) (j : Axis) (i) : (onAxis G M *ᵥ v) (j,i) = (M *ᵥ shaft j v) i := by simp [onAxis,mulVec,dotProduct,Fintype.sum_prod_type,ite_mul,Finset.sum_ite_irrel,shaft]
lemma parallel_routed (k l : Site n) {M : Matrix (SiteKey G n) (SiteKey G n) ℂ} {U} (h : Routed (nodesGrid G n) (nodesGrid G n) k l M U) : Routed (linksGrid G n) (linksGrid G n) k l (parallel M) (onAxis G U) := by
  refine Routed.of_vector fun v => funext fun ⟨⟨x,i⟩,a⟩ => ?_
  rw [plane_apply,show (parallel M *ᵥ _) ((x,i),a) = _ from parallel_eval M _ (x,a) i,show (fun s : SiteKey G n => (plane (linksGrid G n) l *ᵥ v) ((s.1,i),s.2)) = plane (nodesGrid G n) l *ᵥ shaft i v from funext fun j => by rw [plane_apply,plane_apply]; rfl,h.vector,plane_apply,onAxis_eval]; rfl

def lift (V : GhostRoot G) : VectorRoot G := ⟨fun k => onAxis G (V.base k),fun k p => (onAxis G).comp (V.one k p),fun k p s => (V.two k p s).compr₂ (onAxis G)⟩
lemma lift_models {X V} (h : Models (linksGrid G n) (nodesGrid G n) (nodesGrid G n) X V) : Models (linksGrid G n) (linksGrid G n) (linksGrid G n) (fun z => parallel (X z)) (lift V) := by
  let L := (parallelMap G n ℝ).toContinuousLinearMap
  refine ⟨L.contDiff.contDiffAt.comp (f:=X) 0 h.smooth,?_⟩
  change Synced _ _ _ (actual cmat (L ∘ X)) _; erw [actual_push cmat cmat L (parallelMap G n ℂ) h.smooth (fun x => Matrix.ext fun i j => by change ((parallel x i j:ℝ):ℂ) = parallel (cmat x) i j; by_cases i.1.2=j.1.2 <;> simp [parallel, *,cmat_apply,Bloch.approached])]
  exact ⟨fun hq => parallel_routed _ _ (h.sync.base hq),fun hq hp v => parallel_routed _ _ (h.sync.one hq hp v),fun hq hp hs v w => parallel_routed _ _ (h.sync.two hq hp hs v w)⟩

variable {σ C Λ μ : ℝ} {W : PathData G} {p : Clip}

def gauged (G : Gauge) (μ : ℝ) : GhostRoot G := (ghostFree G).add (Vertex.id.smul ((μ^2:ℝ):ℂ))
def factor (G : Gauge) (μ : ℝ) : GhostRoot G := (gauged G μ).inv.smul ((μ^2:ℝ):ℂ)
def massive (G : Gauge) (μ : ℝ) := (((lift (factor G μ)).pow depth).smul ((μ^2:ℝ):ℂ))
def surfeit (G : Gauge) (μ : ℝ) := (((root G).mul ((factor G μ).excess)).mul (root G).transpose).add (massive G μ)
def complete (W : PathData G) (p : Clip) (μ : ℝ) := (vectorFree G W p).add (surfeit G μ)

abbrev SiteModel (n : Side) (X : Loops.Links G n → Matrix (SiteKey G n) (SiteKey G n) ℝ) := Models (linksGrid G n) (nodesGrid G n) (nodesGrid G n) X
abbrev LinkModel (n : Side) (X : Loops.Links G n → Matrix (BondKey G n) (BondKey G n) ℝ) := Models (linksGrid G n) (linksGrid G n) (linksGrid G n) X
lemma root_models (G : Gauge) (n : Side) : Models (linksGrid G n) (linksGrid G n) (nodesGrid G n) (onGradient G n) (root G) := ⟨onGradient_diff G,root_sync G⟩
lemma ghost_models (G : Gauge) (μ : ℝ) (n : Side) : SiteModel n (fun z => ghost μ (vary 1 z)) (gauged G μ) := ((root_models G n).transpose.mul (root_models G n)).add (Models.identity.smul _)
lemma routed_invertible {a E : Type} [Fintype a] [DecidableEq a] [Fintype E] [DecidableEq E] {A : Grid n E a} {X U k} (h : Routed A A k k X U) (hX : IsUnit X) : IsUnit U := by
  refine Matrix.mulVec_injective_iff_isUnit.mp fun v w he => ?_
  have hv := Matrix.mulVec_injective_of_isUnit hX (show X *ᵥ plane A k *ᵥ v = X *ᵥ plane A k *ᵥ w by rw [h.vector,h.vector,he])
  simpa only [mulVec_mulVec, pick_plane,if_true, Matrix.one_mulVec] using! congr_arg (pick A k *ᵥ ·) hv
lemma dressing_models (G : Gauge) (n : Side) (hμ : 0<μ) : SiteModel n (fun z => dressing μ (vary 1 z)) (factor G μ) := ((ghost_models G μ n).inv (fun _ _ hp => routed_invertible ((ghost_models G μ n).sync.base hp) (cmat_unit (ghost_pos _ μ hμ |>.isUnit)))).smul (μ^2)

lemma complete_models (h : W.Bounds p σ C Λ) (hμ : 0<μ) (n : Side) : LinkModel n (fun z => reference μ p W (vary 1 z)) (complete W p μ) := by
  have hs : LinkModel n (cost (mainTerm p W) ∘ vary 1) (localVertex W p) := ⟨smooth_cost (U:=vary 1) (f:=fun _ => mainTerm p W) (Work.F02.mainTerm_contDiffAt h ((vary_diff.comp contDiffAt_fst).vary contDiffAt_snd)), local_synced h⟩
  have hg := root_models G n
  have ht := dressing_models G n hμ
  convert! (hs.add (hg.mul hg.transpose)).add (((hg.mul (ht.excess)).mul hg.transpose).add (((lift_models ht).pow depth).smul (μ^2))) using 1
  funext t
  dsimp only [reference,regulation,onGradient, Function.comp_apply]; rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one]; abel
end YM.Push.Loops.Fine
