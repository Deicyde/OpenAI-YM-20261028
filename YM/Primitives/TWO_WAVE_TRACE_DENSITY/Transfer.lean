import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Fans
import YM.Progress.CLASSICAL_KIN_RECURSION.Dock


/-!
# A scalar jet invoice transfers to all output entries

Compare scalars on integer PERIOD covers, not block ratios. Verified
translation coherence of the whole functional suffices; no evaluating
nearby wave frequencies, holding a singular projection across grids, or
assuming normalization of an inverse determinant itself on lifted fields.
Important: this lemma to be used on e.g. action NOT its traced loop.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave
open Lattice Laurent Bloch Matrix Complex RG
open Progress.ClassicalKin Progress.ClassicalKin.Tent Function
open scoped BigOperators Topology Classical

variable {ι α : Type*} {n m : Side} {k : ℕ}

def spot (i : ι) : ι→ℝ := Pi.single i 1


variable [Fintype ι] [Fintype α]
abbrev Page (ι : Type*) [Fintype ι] (k : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin k => ι → ℝ) ℝ

/-- first (query) slot indexed separately. -/
def extractF (T : Page ι (k+1)) : FrameCoeffs ι ι k ℝ :=
    fun i t=> T (spot ∘ (Fin.cons i t))









/-- change of period and placement. -/
def tele (h : divides n m) (p : Site n) (x : Leaf m α) : Leaf n α := (lieBy h p x.1,x.2)
def teleport (h : divides n m) (p : Site n) : (Leaf n α → ℝ) →L[ℝ] Leaf m α → ℝ :=
    ContinuousLinearMap.pi fun x : Leaf m α=> ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Leaf n α=>ℝ) (tele h p x)
omit [Fintype α] in
lemma teleport_at (h : divides n m) (p : Site n) (u : Leaf n α→ℝ) (x : Leaf m α): teleport h p u x = u (tele h p x):=rfl





variable {Ad : Side → Prop}

omit [Fintype α] in
lemma teleport_self (p : Site n) (i : Leaf n α) : tele (dvd_refl _) p i = (i.1+p,i.2) := by rw [tele,lies_self]



omit [Fintype α] in
lemma tele_onto (h : divides n m) (o : Site n) : Surjective (tele h o (α:=α)) := by
  rintro ⟨x,i⟩; refine ⟨(wrap m (lift (x-o)),i),?_⟩; rw [tele,lieBy]; dsimp only; rw [shrinkWrap,wrap_lift,sub_add_cancel]


end YM.Primitives.TwoWave
