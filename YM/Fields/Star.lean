import YM.Boundary.Contour
import YM.Mink.Boost
import YM.Euclid.Stress
import YM.Analysis.Nonnegative

/-!
# The analytically-continued labels and the star Gram element

Label actions must be integrated, no hidden Lie theory. Rotation action in the
polynomial basis not assumed continuous Lorentz on bare labels. J_E is the
specific one induced by S. Sums of words may be represented by finite family
positions + coefficients (arbitrary constants, repetitions allowed).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open MeasureTheory Filter Complex Function Set Analysis Mink
open scoped Topology BigOperators InnerProductSpace ComplexOrder Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L}

structure Spins (S : Table L) where
  rail : Lorentz → S.Union ≃ₗ[ℂ] S.Union
  shell : (n : ℕ) → Lorentz → S.Field n ≃ₗ[ℂ] S.Field n

structure Spins.Descends (X : Spins S) (R : S.Rotation) (h : S.RealSpin) : Prop where
  ties (p : Lorentz) (d : ℕ) (v : S.Field d) : X.rail p (S.pin d v) = S.pin d (X.shell d p v)
  identity a : X.rail 1 a=a
  representation a b v : X.rail (a*b) v=X.rail a (X.rail b v)
  spin (n : ℕ) (v : S.Field n) : Continuous (fun x => X.shell n x v)
  boosts (n : ℕ) (i : SpaceAxis) (p : S.Field n) : HasDerivAt
    (fun t => X.shell n ((Ray.fromAxis i).boost t) p) ((-I) • R.lie n (Ortho.plane timeAxis i.castSucc) p) (0 : ℝ)
  spatial (K : Ortho) (hq : Lorentz.spatialTurn K) (d : ℕ) (p : S.Field d) :
    X.shell d (Lorentz.room K hq) p=R.act d K p
  commutes (g : Lorentz) (d : ℕ) (v : S.Field d) : S.adj h d timeAxis (X.shell d g v)=X.shell d g (S.adj h d timeAxis v)

abbrev StarOp (S : Table L) := S.Union →ₛₗ[starRingEnd ℂ] S.Union
abbrev Letter (S : Table L) := S.Union × Test4
abbrev Sentence (S : Table L) := List (Letter S)

/-- This proof port pins J to the actual induced map. -/
def starRead (j : StarOp S) (h : S.RealSpin) : Prop := ∀ d v,
    j (S.pin d v) = S.pin d (S.adj h d timeAxis v)

theorem calibrate {P : DiffPlan S} (hp : S.Symmetric) (he : P.Inclusions S) (h : S.RealSpin) (hy : P.Orientation h) :
    starRead (P.unionAdj hp he timeAxis h hy) h := fun d v => P.through_adjoint hp he timeAxis h hy d v

theorem invol {P : DiffPlan S} (hp : S.Symmetric) (he : P.Inclusions S) {h : S.RealSpin}
    {J} (hw : starRead J h) : Involutive J := by
  intro i; obtain ⟨y,p,rfl⟩ := P.covered hp he i
  rw [hw,hw, S.reflect_twice]

namespace Letter
def op (J : StarOp S) (p : Letter S) : Letter S := (J p.1, Probe.bar p.2)
def read (V : Spins S) (g : Poincare) (p : Letter S) : Letter S := (V.rail g.Λ p.1,Joint.push g p.2)
@[simp] lemma twice (J : StarOp S) (h : Involutive J) (p : Letter S) : op J (op J p)=p := by simp [op,h p.1]
lemma stays_read (V : Spins S) (p : Letter S) {R h} (ht : V.Descends R h) : read V 1 p=p := by
  refine Prod.ext ?_ ?_
  · simp [read,ht.identity]
  change Joint.push 1 p.2 = _; ext1; rw [Joint.push_at,inv_one,Poincare.sends_one]
lemma travels (V : Spins S) {R h} (ht : V.Descends R h) (p q : Poincare) (s : Letter S) :
    read V (p*q) s = read V p (read V q s) := by
  refine Prod.ext ?_ ?_
  · simp [read,ht.representation]
  change Joint.push (p*q) s.2 = Joint.push p _; ext1; rw [Joint.push_at,Joint.push_at]
  change s.2 _ = Joint.push q s.2 _
  rw [Joint.push_at,mul_inv_rev,Poincare.sends_mul]
lemma rewrites {P : DiffPlan S} (H : S.Symmetric) (he : P.Inclusions S) {J h} (hw : @starRead _ _ S J h) (V : Spins S)
    {R} (ht : V.Descends R h) (p : Letter S) (g) : op J (read V g p) = read V g (op J p) := by
  rcases p with ⟨x,f⟩
  obtain ⟨d,v,rfl⟩ := P.covered H he x
  refine Prod.ext ?_ ?_
  · simp [op,read,ht.ties,show ∀ d v, J (S.pin d v) = _ from hw,ht.commutes]
  change Probe.bar _ = Joint.push _ _
  ext1; simp [op,read]
end Letter

namespace Sentence
variable (J : StarOp S)

def rev (b : Sentence S) : Sentence S := List.reverse (b.map (Letter.op J))
@[simp] theorem rev_append (b c : Sentence S) : rev J (b++c)=rev J c ++ rev J b := by simp [rev]
@[simp] theorem rev_rev (h : Involutive J) (b : Sentence S) : rev J (rev J b) = b := by
  induction b with
  | nil => rfl
  | cons p b ih => simp [rev,List.map_append,Letter.twice J h] at ih ⊢
                   -- reduce
                   simp_all
end Sentence

namespace Surface
variable (W : Surface S) (J : StarOp S)

/-- Test the field in this Minkowski boundary. No compact-support requirement. -/
def expect (b : Sentence S) := W.W b.length (fun i => (b.get i).1)
    (Joint.materialize b.length (fun i => (b.get i).2))
def kernel (b c : Sentence S) := W.expect (Sentence.rev J b ++ c)

def wordsPositive := Analysis.NNKernel (W.kernel J)

lemma barrier {ι : Type*} [Fintype ι] (hp : W.wordsPositive J)
    (Wor : ι → Sentence S) (c : ι → ℂ) : 0 ≤ ∑ i, ∑ j,
    star (c i)*W.expect (Sentence.rev J (Wor i) ++ Wor j)*c j := hp.positivity Wor c
end Surface
end YM.Boundary
