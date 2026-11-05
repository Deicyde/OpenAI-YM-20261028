import YM.Push.FREE_RESOLVENT.Tags

/-!
# Include a tagged response in the inverse prices

Absolute point budgets (read from drawn projections). TT-compatible tags
pay while including path-length and window changes (consequences
for ). These are at actual identity-completed matrices, on *both*
sets of real slots. Roots of the nonlinear phase etc. not obtained by this
estimate. This proof doesn't vary any RG.Story or path/gauge minimizer
empirically. Marked estimates refer only to changing that one tree. Domains
of steps, radii, W, h etc. the SAME across all components. For symbol
norms with summed higher indices see tensor lemmas.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice Wilson RG Precision Tree Matrix Lever Filter Function Set Shell Mark TestD
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {τ E ι X : Type*}
namespace Lever
variable [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Tag Δ is SECOND minus FIRST. `Here` pays entrywise on both leg anchors.
Extra location mark (no volume factor). -/
structure Here (v : τ → E) (D : Cost X) (a : ι → X) (p : τ → X) (d γ : ℝ) (x : X) (l : List τ) (M : ℝ)
    (A B : E → Matrix ι ι ℝ) : Prop where
  test (i j : ι) :
    let y := a i; let z := a j
    let t := |(jet v B l 0-jet v A l 0) i j|
    D.weight d y x*(positions D p d).pay l y*(D.weight γ y z*t) ≤ M ∧
      D.weight d z x*(positions D p d).pay l z*(D.weight γ z y*t) ≤ M

lemma paid {v : τ → E} {p : τ → X} {D : Cost X} {d γ : ℝ} {F H : E → Matrix ι ι ℝ}
    {G : E × ℝ → Matrix ι ι ℝ} (hG : ∀ x, G (x,0)=F x) (hH : ∀ x, G (x,1)=H x)
    {w : X} {k : ℕ} {l : List τ} {a : ι → X} {M : ℝ} (hx : l.length < k)
    (ht : ∀ t ∈ Icc (0:ℝ) 1, Bundle (guides v) (park D p d w) D a a G (0,t) k γ M) : Here v D a p d γ w l M F H := by
  constructor
  intro i j; have he := recovers (v:=v) (γ:=γ) (x:=w) (a:=a) (p:=p) l
    (fun t h => smooth_of_le (ht t h).smooth (Nat.succ_le_of_lt hx))
    (fun t h => (ht t h).bound (none::l.map some) (by rw [List.length_cons,List.length_map]; omega)) i j
  simp_rw [hG,hH] at he; exact he
end Lever

namespace Affine
variable {G : Gauge} {c f : Side} {S : StepData c f} {v : Site c}
variable (T U : Forest S.ratio) (k : S.Choices) (p : Clip) {W : PathData G} {u σ A : ℝ}
variable (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (hp : Bid.Larger (G:=G) S) (hu : 0 ≤ u)

-- Every big theta and the powers independent of u in these costs except for the given drain factors.
def earnings (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (k : ℕ) (M σ : ℝ) :=
  meter k k (nuts G P K p k M σ) 1 (rise (locker G P K p k M σ) (gum G P K p))

lemma now (R : Admit) (x : Vec G c 1) : crest S k (W:=W) (T:=T) (U:=U) (p:=p) R (x,0)=whole S T k p W R x := by
  simp [crest,mixture, castLift,stir]
lemma thenAt (R : Admit) (x : Vec G c 1) : crest S k (W:=W) (T:=T) (U:=U) (p:=p) R (x,1)=whole S U k p W R x := by
  simp [crest,mixture, castLift,stir]

include hs ha hW hp hu








end Affine
end YM.FreeResolvent
