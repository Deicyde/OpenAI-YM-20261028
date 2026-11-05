import YM.Euclid.Register
import YM.Euclid.Test

/-!
# Candidate continuum hierarchy (no existence claim)

Smoothness on configuration space only. Junk off Conf never compared.
Positional derivative bounds here total order operator norm on Points n with Euclidean
volume, capped separation in cubedist; equivalent to e.g. all positional multi-indices
by finite dimensions at fixed arity/order. No replicated-product bound hidden here.
-/
set_option autoImplicit false
noncomputable section
namespace YM
open Function Set Filter
open MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators

abbrev Caps (n : ℕ) := Fin n → ℕ
abbrev Register.Vector {G : Gauge} (L : Register G) {n} (d : Caps n) := (i : Fin n) → L.Ref (d i)

namespace Points
variable {n : ℕ}

def move (s : Ortho) (x : Points n) := points fun i => Ortho.move s (x i)
def across (a : E4) (x : Points n) := points fun i => x i + a
def rearrange (r : Equiv.Perm (Fin n)) (x : Points n) := points (WithLp.ofLp x ∘ r)

def allAbove (a : Axis) (t : ℝ) (x : Points n) := ∀ i, t < x i a

@[simp] theorem move_coord (s : Ortho) (x : Points n) (i) : move s x i = Ortho.move s (x i) := rfl
@[simp] theorem across_coord (s : E4) (x : Points n) (i) : across s x i = x i + s := rfl
@[simp] theorem rearrange_at (r : Equiv.Perm (Fin n)) (x : Points n) (i) : rearrange r x i = x (r i) := rfl

theorem move_in (s : Ortho) {x : Points n} (hx : x ∈ conf n) : move s x ∈ conf n :=
  (Ortho.move_injective s).comp (show Injective x.ofLp from hx)

theorem across_in (s : E4) {x : Points n} (hx : x ∈ conf n) : across s x ∈ conf n := fun _ _ he =>
  (show Injective x.ofLp from hx) (add_right_cancel (show _ + s = _ + s from he))

theorem rearrange_in (r : Equiv.Perm (Fin n)) {x : Points n} (hx : x ∈ conf n) :
    rearrange r x ∈ conf n :=
  (show Injective x.ofLp from hx).comp r.injective

theorem tail_in {x : Points (n+1)} (hx : x ∈ conf (n+1)) : tail x ∈ conf n :=
  (show Injective x.ofLp from hx).comp (Fin.succ_injective n)
end Points

variable {G : Gauge} (L : Register G)

abbrev Moment (n : ℕ) (d : Caps n) := MultilinearMap ℂ (fun i => L.Ref (d i)) ℂ

/-- Use unconditional table type for all-arity, junk at coincident points.
Includes dependence on labels by actual algebraic multilinear map. -/
structure Table where
  value {n : ℕ} (d : Caps n) (x : Points n) : Moment L n d

variable {L}
namespace Table
variable (S : Table L) {n m : ℕ}

/-- Heterogeneous read. -/
def read (x : Points n) (v : Fin n → L.Token) : ℂ := S.value (fun i => (v i).1) x (fun i => (v i).2)

theorem read_eq (x : Points n) (d : Caps n) (v : L.Vector d) :
    S.read x (fun i => ⟨d i,v i⟩) = S.value d x v := rfl

/-- Smeared with joint test. -/
def integralOn (d : Caps n) (v : L.Vector d) (f : Test n) := f.applyTo fun x => S.value d x v

structure Symmetric : Prop where
  same {n : ℕ} (r : Equiv.Perm (Fin n)) {x : Points n} (H : x ∈ conf n) (v : Fin n → L.Token) :
    S.read (Points.rearrange r x) (v ∘ r) = S.read x v

structure Basic : Prop extends Symmetric S where
  trivial (f : Fin 0 → L.Token) (x : Points 0) : S.read x f = 1
  unital {n : ℕ} {x : Points (n+1)} (h : x ∈ conf (n+1)) (d : ℕ) (v : Fin n → L.Token) :
    S.read x (Fin.cons (L.one d) v) = S.read (Points.tail x) v

structure RealSpin : Prop where
  mirror {n : ℕ} (s : Signed) {x : Points n} (h : x ∈ conf n) (v : Fin n → L.Token) :
    S.read (Points.move s.ortho x) (L.move s ∘ v) = S.read x v
  real {n : ℕ} {x : Points n} (h : x ∈ conf n) (v : Fin n → L.Token) :
    S.read x (L.conjugate ∘ v) = star (S.read x v)

def Homogeneous := ∀ n (x : Points n), x ∈ conf n → ∀ (s : E4) (v : Fin n → L.Token), S.read (Points.across s x) v = S.read x v

structure Smooth : Prop where
  on_conf {n : ℕ} (d : Caps n) (v : L.Vector d) : ContDiffOn ℝ ∞ (fun x => S.value d x v) (conf n)

theorem smooth_read (H : S.Smooth) (v : Fin n → L.Token) : ContDiffOn ℝ ∞ (fun x => S.read x v) (conf n) :=
  H.on_conf _ _

/-- Constants may depend on all labels and fixed arity. For rn test families
or training lengths labels can not float in this definition. `spaced r x`
uses sup/cube. No growth allowed in positions holding separation capped from below. -/
def Capped := ∀ n (d : Caps n) (v : L.Vector d) (j : ℕ), ∃ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧
  ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x : Points n, spaced r x →
    ‖iteratedFDeriv ℝ j (fun y => S.value d y v) x‖ ≤ C * r⁻¹ ^ A

def readDegrees {v : Fin n → L.Token} (d : ℕ) (i : Fin (n+1)) : ℕ := Fin.cons (α := fun _ : Fin (n+1) => ℕ) d (fun i => (v i).1) i
def headValue (v : Fin n → L.Token) {d} (A : L.Ref d) : L.Ref (readDegrees (v := v) d 0) := A
def vals (v : Fin n → L.Token) {d} (A : L.Ref d) : L.Vector (readDegrees (v := v) d) :=
  Fin.cons (α := fun i => L.Ref (readDegrees (v := v) d i)) (headValue v A) (fun i => (v i).2)
theorem update_front (v : Fin n → L.Token) {d} (A B : L.Ref d) :
    vals v B = update (vals v A) 0 (headValue v B) := by
  funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [vals]
theorem front_eq (v : Fin n → L.Token) (x) {d} (A : L.Ref d) :
    S.read x (Fin.cons ⟨d,A⟩ v) = S.value (readDegrees (v := v) d) x (vals v A) := by
  rw [← read_eq]
  congr 1
  funext i; refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cons_zero]; exact (show _ from (rfl))
  rw [Fin.cons_succ]; rfl
theorem head_add (v : Fin n → L.Token) {d} (A B : L.Ref d) :
    headValue v (A+B) = headValue v A + headValue v B := rfl
theorem head_scale (v : Fin n → L.Token) {d} (c : ℂ) (A : L.Ref d) :
    headValue v (c • A) = c • headValue v A := rfl

/-- Determines the first value; symmetry moves the slot before applying. -/
def injectFront (v : Fin n → L.Token) (x : Points (n+1)) (d : ℕ) : L.Ref d →ₗ[ℂ] ℂ where
  toFun A := read S x (Fin.cons ⟨d,A⟩ v)
  map_add' A B := by
    -- fix degree map
    let p := vals v A
    rw [front_eq,front_eq,front_eq]
    rw [show vals v (A+B) = update p 0 (headValue v (A+B)) from update_front v A _,
      head_add,MultilinearMap.map_update_add]
    rw [← update_front, ← update_front]
  map_smul' z A := by
    let p := vals v A
    rw [front_eq,front_eq, show vals v (z • A) = update p 0 (headValue v (z • A)) from update_front v A _,
      head_scale, MultilinearMap.map_update_smul, ← update_front]
    all_goals rfl

@[simp] theorem head_read (x : Points (n+1)) (v : Fin n → L.Token) (d) (p : L.Ref d) :
    S.injectFront v x d p = S.read x (Fin.cons ⟨d,p⟩ v) := rfl
end Table
end YM
