import YM.Euclid.Lift
import Mathlib.Analysis.Complex.Order
import Mathlib.Data.List.FinRange

/-!
# Heterogeneous separated words and coordinate RP

Gram always antilinear in the FIRST variable. Reversal included even when symmetry permits ignoring.
All exterior unions involving test/Phase keep the same table.
-/
set_option autoImplicit false
noncomputable section
namespace YM
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ComplexOrder BigOperators

variable {G : Gauge}

namespace Register
abbrev Plant (L : Register G) := E4 × L.Token
abbrev Word (L : Register G) := List L.Plant
end Register

variable {L : Register G} {n : ℕ}

namespace Word
def positions (w : L.Word) := points fun i : Fin w.length => (w.get i).1
def tokens (w : L.Word) (i : Fin w.length) := (w.get i).2

def realize (v : Fin n → L.Token) (x : Points n) : L.Word := List.ofFn fun i => (x i,v i)

@[simp] theorem rebuilt (w : L.Word) : realize (tokens w) (positions w) = w := List.ofFn_get _

def distinct (w : L.Word) := positions w ∈ conf _

theorem plantInj {w : L.Word} (hx : distinct w) : Injective w.get := fun _ _ h =>
  (show Injective (positions w).ofLp from hx) (congr_arg Prod.fst h)

theorem locations {w : L.Word} : distinct w ↔ (w.map Prod.fst).Nodup := by
  let f := fun i => (w.get i).1
  have he : w.map Prod.fst = List.ofFn f := by
    rw [show f = Prod.fst ∘ w.get from rfl,← List.map_ofFn,List.ofFn_get]
  rw [he,List.nodup_ofFn]; rfl

@[simp] theorem realized (v : Fin n → L.Token) (x : Points n) : distinct (realize v x) ↔ x ∈ conf n := by
  rw [locations,realize,List.map_ofFn,List.nodup_ofFn]; rfl

/-- Translate all points. -/
def carry (v : L.Word) (x : E4) : L.Word := v.map fun p => (p.1+x,p.2)

theorem still {v : L.Word} (hv : distinct v) (x : E4) : distinct (carry v x) := by
  rw [locations]
  rw [show List.map Prod.fst (carry v x) = (v.map Prod.fst).map (fun y => y+x) by simp [carry,List.map_map]]
  exact (locations.mp hv).map (fun _ _ he => add_right_cancel he)

/-- Strictly past the common plane. Distinct within each summand, but
allow Gram against any other Positive there. -/
def Positive (w : L.Word) (a : Axis) := distinct w ∧ ∀ p ∈ w, 0 < p.1 a

def conjugate (w : L.Word) : L.Word := w.map fun p => (p.1,L.conjugate p.2)

def act (s : Signed) (w : L.Word) : L.Word := w.map fun p => (Ortho.move s.ortho p.1,L.move s p.2)

def reflect (w : L.Word) (a : Axis) : L.Word := act (Signed.mirror a) (conjugate w.reverse)

@[simp] theorem reflectedPoint (w : L.Word) (a : Axis) : reflect w a = w.reverse.map fun p =>
    (Ortho.move (Signed.reflect a) p.1,L.reflectedToken a p.2) := by
  rw [reflect,act,conjugate,List.map_map]; rfl

theorem strictly {w : L.Word} {a : Axis} (h : Positive w a) {p} (hp : p ∈ reflect w a) : p.1 a < 0 := by
  rw [reflectedPoint,List.mem_map] at hp
  obtain ⟨x,hx,rfl⟩ := hp
  simp [h.2 x (by simpa using hx)]

theorem reflects {w : L.Word} (a) (h : distinct w) : distinct (reflect w a) := by
  rw [locations, show (reflect w a).map Prod.fst = (w.map Prod.fst).reverse.map (Ortho.move (Signed.reflect a)) by
    simp only [reflectedPoint,List.map_map, ← List.map_reverse]; rfl]
  exact (List.nodup_reverse.mpr (locations.mp h)).map (Ortho.move_injective _)

theorem twoSides {w v : L.Word} {a} (H : Positive w a) (K : Positive v a) : distinct (reflect w a ++ v) := by
  rw [locations,List.map_append,List.nodup_append]
  refine ⟨locations.mp (reflects a H.1),locations.mp K.1,?_⟩
  intro x
  simp only [List.mem_map]
  rintro ⟨p,hp,rfl⟩ y ⟨q,hq,rfl⟩ he
  exact (strictly H hp).not_ge (he.symm ▸ (K.2 q hq).le)
end Word

namespace Table
open Word
variable (S : Table L)

def expect (w : L.Word) := S.read (positions w) (tokens w)

lemma readCast {s : ℕ} {w : L.Word} (h : s=w.length) (p : Fin s → L.Plant) (x : Points s) (v : Fin s → L.Token)
    (hp : ∀ i, w.get (Fin.cast h i) = p i) (he : ∀ i, p i = (x i,v i)) : S.expect w = S.read x v := by
  subst s
  have hv (i) : w.get i = (x i,v i) := (hp i).trans (he i)
  unfold expect; congr 1
  · exact PiLp.ext fun i => congr_arg Prod.fst (hv i)
  exact funext fun i => congr_arg Prod.snd (hv i)

@[simp] theorem readAt (v : Fin n → L.Token) (x : Points n) : S.expect (realize v x) = S.read x v := by
  refine S.readCast (by simp [realize]) (fun i => (x i,v i)) x v ?_ (fun _ => rfl)
  simp [realize]

theorem order {v w : L.Word} (h : S.Symmetric) (hx : distinct v) (hv : List.Perm v w) : S.expect w = S.expect v := by
  have hw : distinct w := locations.mpr ((hv.map Prod.fst).nodup (locations.mp hx))
  have he : ∀ i : Fin v.length, ∃ j : Fin v.length, v.get j = w.get (Fin.cast hv.length_eq i) := fun i =>
    List.mem_iff_get.mp (hv.mem_iff.mpr (List.get_mem ..))
  choose f hf using he
  have ht : Injective f := by
    intro i j he
    exact (finCongr hv.length_eq).injective (plantInj hw ((hf i).symm.trans (he ▸ hf j)))
  let p : Equiv.Perm (Fin v.length) := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp ht)
  rw [S.readCast hv.length_eq (v.get ∘ p) (Points.rearrange p (positions v)) (tokens v ∘ p)
    (fun i => (hf i).symm) (fun _ => rfl), h.same p hx]; rfl

def gram (a : Axis) (w v : L.Word) := S.expect (reflect w a ++ v)

/-- Coordinate axis seam through 0; all words including empty. Other axis
translation seams transport by translation invariance. -/
def RP := ∀ a : Axis, ∀ m : ℕ, ∀ w : Fin m → L.Word, (∀ i, Positive (w i) a) → ∀ c : Fin m → ℂ,
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, star (c i) * c j * S.gram a (w i) (w j)

/-- Separate tests in arbitrary arity, not only tensor products. -/
structure PastTest (L : Register G) (a : Axis) where
  n : ℕ
  v : Fin n → L.Token
  f : Test n
  past : ∀ x ∈ tsupport f, Points.allAbove a 0 x

def smeared (a : Axis) (f g : PastTest L a) :=
  fun z : Points f.n × Points g.n => star (f.f z.1) * g.f z.2 * S.gram a (realize f.v z.1) (realize g.v z.2)

def RPSmear : Prop := (∀ a : Axis, ∀ f g : PastTest L a, Integrable (S.smeared a f g)) ∧
  ∀ a : Axis, ∀ m : ℕ, ∀ w : Fin m → PastTest L a, ∀ c : Fin m → ℂ,
    0 ≤ ∑ i : Fin m, ∑ j : Fin m, star (c i) * c j * ∫ z, S.smeared a (w i) (w j) z

/-- Euclidean properties requested before continuous rotation. -/
structure Hierarchy : Prop where
  laws : S.Basic
  spin : S.RealSpin
  translations : S.Homogeneous
  positive : S.RP
  onTests : S.RPSmear
  smooth : S.Smooth
  order : S.Capped
end Table
end YM
