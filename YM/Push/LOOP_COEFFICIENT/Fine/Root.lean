import YM.Push.LOOP_COEFFICIENT.Continuum.Curls
import YM.Push.LOOP_COEFFICIENT.Fine.Spin
import YM.Push.LOOP_COEFFICIENT.PlaneRules

/-!
# Fine gauge-root vertex and mesh interpretation
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Fine
open Function Set Filter Matrix Lattice Laurent Bloch RG Precision Wilson Work.F02 Complex Continuum Paths
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {n : Side}
abbrev RootVertex (G : Gauge) := Vertex (Axes G) (Axes G) G.ColorIndex

def rootOne (G : Gauge) (k : Momentum) : Polarization G →ₗ[ℂ] Matrix (Axes G) G.ColorIndex ℂ where
  toFun v := of fun i j => cexp (Continuum.freq k i.1) * ((coupling G).lin (shaft i.1 v)) i.2 j
  map_add' _ _ := by ext; simp [mul_add]
  map_smul' _ _ := by ext; simp [mul_left_comm]

def matrix₂ {a b d : Type} (Q : a → b → CSpace d →ₗ[ℂ] CSpace d →ₗ[ℂ] ℂ) := LinearMap.mk₂ ℂ (fun v w => Matrix.of fun i j => Q i j v w) (fun v w x => by ext; simp) (fun c v w => by ext; simp) (fun x v w => by ext; simp) (fun c x v => by ext; simp)

def rootTwo (G : Gauge) (k : Momentum) := matrix₂ fun (i : Axes G) (j : G.ColorIndex) =>
    cexp (Continuum.freq k i.1) • (((coupling G).quad.compl₁₂ (shaft i.1) (shaft i.1)).compr₂ (entryLinearMap ℂ ℂ i.2 j))

def root (G : Gauge) : RootVertex G := ⟨longitudinal G,fun q _ => rootOne G q,fun q _ _ => rootTwo G q⟩

open scoped Matrix.Norms.Frobenius in
lemma gradient_one (v : CSpace (BondKey G n)) (i : Edge (Site n)) (j : Site n) (a b : G.ColorIndex) : (actualMatrix (onGradient G n)).lin v (i,a) (j,b) = if i.1+step i.2=j then (coupling G).lin (readSite i v) a b else 0 := by
  have he := congr_arg (fun z => z.lin v) (gradient_jet_entry i j a b)
  split <;> simpa [*,Jet.push,Jet.add,Jet.const,Jet.pre] using he
open scoped Matrix.Norms.Frobenius in
lemma gradient_two (v w : CSpace (BondKey G n)) (i : Edge (Site n)) (j : Site n) (a b : G.ColorIndex) : (actualMatrix (onGradient G n)).quad v w (i,a) (j,b) = if i.1+step i.2=j then (coupling G).quad (readSite i v) (readSite i w) a b else 0 := by
  have he := congr_arg (fun z => z.quad v w) (gradient_jet_entry i j a b)
  split <;> simpa [*,Jet.push,Jet.add,Jet.const,Jet.pre] using he

lemma routed_wave {k : Momentum} {a b : Site n} {X : Axis → Matrix G.ColorIndex G.ColorIndex ℂ} {M : Matrix (BondKey G n) (SiteKey G n) ℂ}
    (ha : Matches k a) (h : ∀ i j s t, M (i,s) (j,t) = if i.1+step i.2=j then cell b i.1 * X i.2 s t else 0) : Routed (linksGrid G n) (nodesGrid G n) (a+b) a M (of fun (i : Axes G) j => cexp (Continuum.freq k i.1) * X i.1 i.2 j) := by
  refine Routed.of_vector fun v => funext fun ⟨⟨x,i⟩,r⟩ => ?_; rw [plane_apply]
  change _ = cell (a+b) x * _; rw [cell_duality,cell_add,cell_duality x a, cell_duality x b]; simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,h]
  simp [plane, linksGrid,nodesGrid,ite_mul, Finset.mul_sum,cell_add,ha.step]; unfold Continuum.freq; apply Finset.sum_congr rfl fun j _ => by ring
lemma read_plane (x : Edge (Site n)) (k : Site n) (v : Polarization G) : readSite x (plane (linksGrid G n) k *ᵥ v) = cell k x.1 • shaft x.2 v := funext fun i => plane_apply (linksGrid G n) k v (x,i)

open scoped Matrix.Norms.Frobenius in
lemma root_sync (G : Gauge) : Synced (linksGrid G n) (linksGrid G n) (nodesGrid G n) (actualMatrix (onGradient G n)) (root G) := by
  refine ⟨fun h => by simpa [actualMatrix,actual,root,onGradient] using R_zero_routed (G:=G) h,fun h h' v => routed_wave (X:=fun i => (coupling G).lin (shaft i v)) h (fun i j s t => ?_),fun h h' h'' v w => ?_⟩
  · rw [gradient_one,read_plane,map_smul,Matrix.smul_apply,smul_eq_mul]
  rename_i k p q a b c
  rw [add_assoc]; refine routed_wave (X:=fun i => (coupling G).quad (shaft i v) (shaft i w)) h (fun i j s t => ?_); rw [gradient_two, read_plane,read_plane,cell_duality (b+c),cell_add,cell_duality _ b,cell_duality _ c]; simp only [map_smul,LinearMap.smul_apply,Matrix.smul_apply,smul_eq_mul,mul_assoc]; rw [mul_left_comm (cell b _) (cell c _) _]
end YM.Push.Loops.Fine
