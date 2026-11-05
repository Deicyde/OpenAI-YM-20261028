import YM.Euclid.Table
import Mathlib.Analysis.Normed.Group.Quotient

/-!
# All-spectator local field quotients

Equality against *every* exterior word is used in the type. For symmetric,
smooth kernels, show point-null-at-head equals null at all slots in tests.
No cutoff condition/exterior weight cap. Distinguish the free comparison
example (the same construction of quotients on shell Wick kernels) from a
rank statement connecting it to a physical hierarchy. Use complex spaces
and store the real structure explicitly. Quotient norm on each weight
from sup reference norm. No isometry assumption on symmetries.
-/
set_option autoImplicit false
noncomputable section
namespace YM
open Function Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {L : Register G}

structure Exterior (L : Register G) where
  n : ℕ
  point : Points (n+1)
  letter : Fin n → L.Token
  clear : point ∈ conf _

namespace Table
variable (S : Table L)

def replies (d) : L.Ref d →ₗ[ℂ] Exterior L → ℂ :=
  LinearMap.pi fun v => S.injectFront v.letter v.point d

def null (d : ℕ) := LinearMap.ker (S.replies d)

protected theorem criterion (d : ℕ) (v : L.Ref d) : v ∈ S.null d ↔
    ∀ (n : ℕ) (B : Fin n → L.Token), ∀ x ∈ conf (n+1), S.read x (Fin.cons ⟨d,v⟩ B) = 0 := by
  constructor
  · intro h n B x hx
    exact congr_fun (show S.replies d v = 0 from h) ⟨n,x,B,hx⟩
  intro h; exact funext (fun (i : Exterior L) => h i.n i.letter i.point i.clear)

/-- Move any slot to the head, proof independent of continuity. -/
lemma same_place {n} (h : S.Symmetric) {x} (hx : x ∈ conf (n+1)) (p : Fin (n+1)) (w : Fin (n+1) → L.Token) :
    S.read x w = S.read (Points.rearrange (Equiv.swap 0 p) x)
      (Fin.cons (w p) (Fin.tail (w ∘ Equiv.swap 0 p))) := by
  rw [← h.same (Equiv.swap 0 p) hx]
  congr 1
  simpa using (Fin.cons_self_tail (w ∘ Equiv.swap 0 p)).symm

lemma each_place (h : S.Symmetric) {d} {v : L.Ref d} (H : v ∈ S.null d) {n} {x : Points n} (hx : x ∈ conf n)
    (w : Fin n → L.Token) (p : Fin n) (hp : w p = ⟨d,v⟩) : S.read x w = 0 := by
  cases n with
  | zero => exact Fin.elim0 p
  | succ n =>
    rw [same_place S h hx p, hp]
    exact ((S.criterion _ _).mp H) n _ _ (Points.rearrange_in _ hx)


def vanishes (d : ℕ) (v : L.Ref d) := ∀ (n : ℕ) (w : Fin n → L.Token) (i : Fin n), w i = ⟨d,v⟩ →
    ∀ f : Test n, f.applyTo (fun x => S.read x w) = 0

theorem equivalent (hs : S.Smooth) (hp : S.Symmetric) (d : ℕ) (v : L.Ref d) :
    v ∈ S.null d ↔ S.vanishes d v := by
  constructor
  · intro hv n w i hw
    exact (Test.weak_null (S.smooth_read hs w).continuousOn).mpr fun x hx => S.each_place hp hv hx w i hw
  intro h
  refine (S.criterion _ _).mpr ?_
  intro n B x hx
  let w := Fin.cons (α := fun _ => L.Token) ⟨d,v⟩ B
  exact (Test.weak_null (S.smooth_read hs w).continuousOn).mp (h (n+1) w 0 (by simp [w])) hx

abbrev Field (d : ℕ) := L.Ref d ⧸ S.null d
abbrev project (d : ℕ) := (S.null d).mkQ

instance (d : ℕ) : IsClosed ((S.null d : Submodule _ _) : Set (L.Ref d)) :=
  Submodule.closed_of_finiteDimensional _

example (d) : NormedAddCommGroup (S.Field d) := inferInstance
example (d) : NormedSpace ℂ (S.Field d) := inferInstance
example (d) : FiniteDimensional ℂ (S.Field d) := inferInstance

theorem onto d : Surjective (S.project d) := (S.null d).mkQ_surjective

/-- Any section used only for evaluation, see `Class` descent. -/
def representative (d) : S.Field d →ₗ[ℂ] L.Ref d :=
  ((S.project d).exists_rightInverse_of_surjective (S.null d).range_mkQ).choose

@[simp] theorem rep (d) (v : S.Field d) : S.project d (S.representative d v) = v :=
  LinearMap.congr_fun ((S.project d).exists_rightInverse_of_surjective (S.null d).range_mkQ).choose_spec v

def spectra (d : ℕ) : S.Field d →ₗ[ℂ] Exterior L → ℂ := (S.null d).liftQ (S.replies d) le_rfl

@[simp] theorem projected (d) v : S.spectra d (S.project d v) = S.replies d v := rfl

theorem faithfully d : Injective (S.spectra d) := LinearMap.ker_eq_bot.mp
  ((S.null d).ker_liftQ_eq_bot (S.replies d) le_rfl le_rfl)

def unit (d : ℕ) : S.Field d := S.project d (L.scalar d)

theorem alive (d : ℕ) (h : S.Basic) : S.unit d ≠ 0 := by
  intro hx
  have he : L.scalar d ∈ S.null d := (Submodule.Quotient.mk_eq_zero _).mp hx
  let u := (0 : Points (0+1))
  let B : Fin 0 → L.Token := Fin.elim0
  have hz : u ∈ conf _ := fun _ _ _ => @Subsingleton.elim (Fin 1) _ _ _
  have hw : S.read u (Fin.cons (L.one d) B) = 0 := (S.criterion d _).mp he 0 B u hz
  rw [h.unital hz, h.trivial] at hw; exact one_ne_zero hw

section RealSpin
variable (H : S.RealSpin)
include H

theorem move_null (s : Signed) (d) {p} (h : p ∈ S.null d) : L.mirrorGroup d s p ∈ S.null d := by
  rw [S.criterion]; intro n B x hx
  let y := Points.move s.ortho⁻¹ x
  have he : Points.move s.ortho y = x := by ext1 j; simp [y]
  let A := L.move s⁻¹ ∘ B
  have hw : L.move s ∘ (Fin.cons (α := fun _ => L.Token) ⟨d,p⟩ A) = Fin.cons ⟨d,L.mirrorGroup d s p⟩ B := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Function.comp_apply,Fin.cons_zero,Fin.cons_zero]; rfl
    simp only [A,Function.comp_apply,Fin.cons_succ]
    unfold Register.move; simp only [← Register.mirror_mul,mul_inv_cancel,L.mirror_one]
  rw [← hw, ← he, H.mirror s (Points.move_in _ hx)]
  exact (S.criterion d _).mp h _ _ _ (Points.move_in _ hx)

theorem real_null (d) {p} (h : p ∈ S.null d) : star p ∈ S.null d := by
  rw [S.criterion]; intro n B x hx
  let A := L.conjugate ∘ B
  have he : L.conjugate ∘ (Fin.cons (α := fun _ => L.Token) ⟨d,p⟩ A) = Fin.cons ⟨d,star p⟩ B := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i
    · rw [Function.comp_apply,Fin.cons_zero,Fin.cons_zero]; rfl
    simp only [A,Function.comp_apply,Fin.cons_succ]; unfold Register.conjugate; simp
  rw [← he,H.real hx,(S.criterion d _).mp h n A x hx,star_zero]

def mirror (d : ℕ) (s : Signed) : S.Field d →ₗ[ℂ] S.Field d :=
  (S.null d).liftQ ((S.project d).comp (L.mirrorGroup d s)) fun _ hx =>
    (Submodule.Quotient.mk_eq_zero _).mpr (S.move_null H s d hx)

def conj (d : ℕ) : S.Field d →ₛₗ[starRingEnd ℂ] S.Field d :=
  (S.null d).liftQ ((S.project d).comp (L.bar d)) fun _ hx =>
    (Submodule.Quotient.mk_eq_zero _).mpr (S.real_null H d hx)

@[simp] theorem mirror_project (d s) (p : L.Ref d) : S.mirror H d s (S.project d p) = S.project d (L.mirrorGroup d s p) := rfl
@[simp] theorem conj_project (d) (p : L.Ref d) : S.conj H d (S.project d p) = S.project d (star p) := rfl
@[simp] theorem mirror_unit d s : S.mirror H d s (S.unit d) = S.unit d := by rw [unit,mirror_project,L.mirror_scalar]
@[simp] theorem conj_unit d : S.conj H d (S.unit d) = S.unit d := by rw [unit,conj_project,L.bar_scalar]

@[simp] theorem mirror_mul d (s t : Signed) (p : S.Field d) :
    S.mirror H d (s*t) p = S.mirror H d s (S.mirror H d t p) := by
  obtain ⟨p,rfl⟩ := S.onto d p; rw [mirror_project,mirror_project,mirror_project,L.mirror_mul]

@[simp] theorem mirror_one d (p : S.Field d) : S.mirror H d 1 p = p := by
  obtain ⟨p,rfl⟩ := S.onto d p; rw [mirror_project,L.mirror_one]

@[simp] theorem mirror_star d (s : Signed) (p : S.Field d) :
    S.conj H d (S.mirror H d s p) = S.mirror H d s (S.conj H d p) := by
  obtain ⟨p,rfl⟩ := S.onto d p; rw [mirror_project,conj_project,conj_project,mirror_project,L.star_mirror]

@[simp] theorem reflect_star d (p : S.Field d) : S.conj H d (S.conj H d p) = p := by
  obtain ⟨p,rfl⟩ := S.onto d p; rw [conj_project,conj_project,star_star]

def adj (d : ℕ) (a : Axis) : S.Field d →ₛₗ[starRingEnd ℂ] S.Field d :=
  (S.mirror H d (Signed.mirror a)).comp (S.conj H d)

@[simp] theorem adj_project d a (p : L.Ref d) : S.adj H d a (S.project d p) = S.project d (L.adj d a p) := rfl

@[simp] theorem reflect_twice d a (p : S.Field d) : S.adj H d a (S.adj H d a p) = p := by
  obtain ⟨p,rfl⟩ := S.onto d p; rw [adj_project,adj_project,L.reflected]
end RealSpin
end Table
end YM
