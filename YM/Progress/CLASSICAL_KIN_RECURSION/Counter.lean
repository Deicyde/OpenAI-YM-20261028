import YM.Progress.CLASSICAL_KIN_RECURSION.Hall

set_option warningAsError false

/-!
# Centered joint quadratic form (real)

Do not substitute probe as mean, nor treat frame Hessian as pinned to
site 0. Uses Towers rather than another inversion witness from a later call.
No lower estimate on a representative until N is built.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin.Tent
open Lattice RG Exterior Wilson Precision Tree Bid Bloch Matrix
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f} {r v : ℕ}

-- conjunct color dims even if 0
lemma bits_add (a b : fieldDir G n r) (i : G.ColorIndex) : parts G r (a+b) i=parts G r a i+parts G r b i:=rfl

lemma bits_scale (x : ℝ) (a : fieldDir G n r) (i : G.ColorIndex) : parts G r (x • a) i=x • parts G r a i:=rfl


def paint (G : Gauge) (A : Matrix (Body r c) (Body v f) ℝ) : fieldDir G f v →ₗ[ℝ] fieldDir G c r where
  toFun x:=fun j=>WithLp.toLp 2 (fun i:G.ColorIndex=>(A *ᵥ parts _ _ x i) j)
  map_add' x y:=by ext j i; simp only [bits_add,mulVec_add,Pi.add_apply]; rfl
  map_smul' y x:=by ext j i; simp only [bits_scale,mulVec_smul,Pi.smul_apply]; rfl




def counts (G : Gauge) (r : ℕ) (n : Side) : fieldDir G n r →ₗ[ℝ] fieldDir G n r →ₗ[ℝ] ℝ where
  toFun x:= { toFun y:=∑ i,parts _ _ x i ⬝ᵥ parts _ _ y i
              map_add' y z:=by simp only [bits_add,dotProduct_add,Finset.sum_add_distrib]
              map_smul' t y:=by simp only [bits_scale,dotProduct_smul, ← Finset.smul_sum]; rfl }
  map_add' x y:=by apply LinearMap.ext; intro z; change (∑ i:G.ColorIndex, parts G r (x+y) i ⬝ᵥ parts G r z i)= (∑ i:G.ColorIndex, _)+∑ i:G.ColorIndex, _; simp only [bits_add,add_dotProduct,Finset.sum_add_distrib]
  map_smul' t x:=by apply LinearMap.ext; intro z; change (∑ i:G.ColorIndex, parts G r (t • x) i ⬝ᵥ parts G r z i)= t • ∑ i:G.ColorIndex, _; simp only [bits_scale,smul_dotProduct,← Finset.smul_sum]






def avgBox (S : StepData c f) : form 0 f →ₗ[ℝ] form 0 c := LinearMap.pi (fun i : Body 0 c=>
    ∑ j, S.patch.weight j • LinearMap.proj (atPoint S i.1 j,vac))
def plaque (S : StepData c f) : Matrix (Body 0 c) (Body 0 f) ℝ:= LinearMap.toMatrix' (avgBox S)



/-- defect B-mean A+d' C. -/
def issue (S : StepData c f) (G : Gauge) : Tower G c f→ₗ[ℝ] Dir G c:=
    LinearMap.fst _ _ _-((paint G (mean S)).comp (LinearMap.fst _ _ _)).comp (LinearMap.snd _ _ _) +
      ((paint G (d 0 c)).comp (LinearMap.snd _ _ _)).comp (LinearMap.snd _ _ _)


def counter (S : StepData c f) (M : Bed) (G : Gauge) : Tower G c f→ₗ[ℝ] Tower G c f→ₗ[ℝ] ℝ:=
  let J : Tower G c f→ₗ[ℝ] Dir G f:= (LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _)
  (counts G 1 f).compl₁₂ J ((paint G (Precision.K (M.metric.acts f))).comp J) +
    S.kernel.penalty • (counts G 1 c).compl₁₂ (issue S G) (issue S G)




/-- extend to Towers for partial derivatives. -/
abbrev room (G : Gauge) (c f : Side) : Hall G c f→ₗ[ℝ] Tower G c f:=LinearMap.inr _ _ _
def mainCounter (S : StepData c f) (M : Bed) (G : Gauge) : Hall G c f→ₗ[ℝ] Hall G c f→ₗ[ℝ] ℝ:= (counter S M G).compl₁₂ (room G c f) (room G c f)










end YM.Progress.ClassicalKin.Tent
