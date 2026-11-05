import YM.Extra.FREE_DETECTOR_ALGEBRA.Corridors


set_option warningAsError false

/-! Scanners for Collinear derivative calibration. Uses actual `Scene`,
axis differs by component, concrete integer-lattice line though derivatives
in arbitrary direction. Constructs a Select.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Pair Labels SphereTest Residue OPE Ward Climb
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder Matrix

variable {G : Gauge} (F : Frames G) {d e n j : ℕ} {x : Points n}
local notation "W" => Table.Field (freeTable F)
local notation "T" => freeTable F

lemma diagramDiff (v : Fin n → W d) (P : Climb.Matrix d e T) (m : ℕ) (hx : x∈conf n) : ContDiffAt ℝ (↑m) (diagram v P) x := by
  obtain ⟨A⟩ := EnhDiagram F P v; exact (foreground A hx).of_le le_top

def watching (p : Scene T d) : Climb.Vector d T→ₗ[ℝ] ℂ where
  toFun A := p.lens A
  map_add' A B := by
    have he : diagram p.v ((A+B) p.b)=diagram p.v (A p.b)+diagram p.v (B p.b) := by
      ext1 x; rw [Pi.add_apply,Pi.add_apply,← observation,← observation,← observation]; exact map_add ..
    unfold Scene.lens; rw [he, iteratedFDeriv_add_apply (diagramDiff F _ _ p.m p.strict) (diagramDiff F _ _ p.m p.strict)]; rfl
  map_smul' t A := by
    let g := diagram p.v (A p.b)
    have he : diagram p.v ((t • A : Climb.Vector d T) p.b)=t • g := by
      funext x; unfold g; rw [Pi.smul_apply,Pi.smul_apply,← observation,← observation]; exact ((Climb.observed p.v x (d+1)).restrictScalars ℝ).map_smul ..
    unfold Scene.lens; rw [he, iteratedFDeriv_const_smul_apply (show ContDiffAt ℝ (↑p.m) g p.x from diagramDiff F _ _ _ p.strict)]; rfl

def auxiliaryI (b : Axis) : Axis := if b=0 then 1 else 0
lemma offI (b : Axis) : b≠auxiliaryI b := by unfold auxiliaryI; split_ifs with h; simp [h]; exact h

def spine (b : Axis) (n : ℕ) : Points n := points fun i => (i.val:ℝ) • basis (auxiliaryI b)
lemma spine_conf (b : Axis) (n : ℕ) : spine b n∈conf n := by
  let j := auxiliaryI b
  intro i t hi
  have he := congr_arg (fun a : E4 => a j) hi; change (i.val:ℝ)*basis j j=(t.val:ℝ)*basis j j at he
  apply Fin.ext; simpa using he

structure Tube (F : Frames G) (d : ℕ) where
  n : ℕ
  v : Fin n→ (freeTable F).Field d
  b : Axis
  m : ℕ
  shift : Fin m→ Points n

def Tubed (s : Tube F d) : Scene T d :=
  ⟨s.n,s.v,auxiliaryI s.b,s.b,offI s.b,spine s.b s.n,spine_conf s.b s.n,(fun _ => ⟨_,rfl⟩),s.m,s.shift⟩



-- finite row extraction retaining EXACT whole kernel, adapting A07


lemma dimensionsV (d : ℕ) : FiniteDimensional ℝ (Climb.Vector d T) := by
  letI : FiniteDimensional ℝ (Climb.Matrix d (d+1) T) := Module.Finite.trans ℂ _
  infer_instance

theorem sbuild (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E := inferInstance
def spying (m : ℕ) (p : Fin m → Tube F d) : Climb.Vector d T→L[ℝ] (Fin m → ℂ) := by
  letI : ContinuousSMul ℝ (Climb.Vector d T) := sbuild (Climb.Vector d T)
  letI := dimensionsV F d; exact LinearMap.toContinuousLinearMap (LinearMap.pi fun i => watching F (Tubed F (p i)))


variable (M : Register G) (d : ℕ)

def periscope (p : Fin n→ Tube M.grid d) : Climb.Select M d where
  m := n
  rows i := Tubed M.grid (p i)
  reads := spying M.grid n p
  stimulated _ _ := rfl



-- adequacy extends through all sufficiently high d on same DiffPlan

end YM.Extra.FD
