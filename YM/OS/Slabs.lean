import YM.OS.Core
import YM.Euclid.Differential

/-!
# Actual slab operators between separated clusters

Raw `place` op with *NNReal width*; masking to strict valid positions
required. Read on any quotient via lifts later. Continuity and all-arity multiplet
bound port at all widths, not one-slot estimates. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS
open Function Set Filter Analysis Word
open scoped Topology NNReal BigOperators ContDiff InnerProductSpace ComplexOrder
variable {G : Gauge} {L : Register G} {S : Table L}
variable (a : Axis)

def Slab (d : ℝ≥0) (w : L.Word) := 0<d ∧ Positive w a ∧ ∀ p ∈ w, p.1 a < (d:ℝ)

def buffer (r : ℝ) (d : ℝ≥0) (w : L.Word) := spaced r (positions w) ∧
  ∀ p ∈ w, r ≤ p.1 a ∧ p.1 a ≤ (d:ℝ)-r

def raised (d : ℝ≥0) (v : L.Word) := carry v ((d:ℝ) • basis a)

def linked (d : ℝ≥0) (v w : L.Word) : L.Word := v ++ raised a d w

def opposite (d : ℝ≥0) (v : L.Word) := raised a d (reflect v a)

/-- Bounded raw multiplets. (`d` integer degree, not width.) -/
def constrained (d : ℕ) (R : ℝ) (v : L.Word) : Prop := ∀ i ∈ v, i.2.1 ≤ d ∧ ‖i.2.2‖ ≤ R

variable {a}

lemma appendsFuture {v w : L.Word} {d} (h : Slab a d v) (hp : Positive w a) : Positive (linked a d v w) a := by
  have he := (travel (⟨w,hp⟩ : Future L a) d).property
  let F := raised a d w
  have ht : Positive F a := he
  refine ⟨?_, ?_⟩
  · unfold linked
    rw [locations,List.map_append,List.nodup_append]
    refine ⟨locations.mp h.2.1.1,locations.mp ht.1,?_⟩
    intro _ hx y hy; obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hy
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
    intro he; change p.1=s.1+_ at he
    have hv := h.2.2 p hp'
    rw [he] at hv; simp at hv
    exact hv.not_ge (hp.2 s hs).le
  intro p hu; exact (List.mem_append.mp hu).elim (fun hp => h.2.1.2 p hp) (fun hp => ht.2 p hp)

lemma mirrorsSlab {v : L.Word} {d} (hx : Slab a d v) : Slab a d (opposite a d v) := by
  have he p (hp : p∈opposite a d v) : 0<p.1 a ∧ p.1 a < (d:ℝ) := by
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hp
    rw [reflectedPoint,List.mem_map] at hu
    obtain ⟨w,hw,rfl⟩ := hu
    have hv := List.mem_reverse.mp hw
    have ht := hx.2.1.2 w hv
    have hh := hx.2.2 w hv
    simp [Signed.mirrored]; constructor <;> linarith
  exact ⟨hx.1,⟨still (reflects a hx.2.1.1) _, fun p hp => (he p hp).1⟩, fun p hp => (he p hp).2⟩

lemma connects {v w : L.Word} {d e} (h : Slab a d v) (hh : Slab a e w) : Slab a (d+e) (linked a d v w) := by
  refine ⟨add_pos h.1 hh.1,appendsFuture h hh.2.1,?_⟩
  intro i hI; cases List.mem_append.mp hI with
  | inl hv => exact (h.2.2 i hv).trans_le (by simp)
  | inr hw =>
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw
    have hp := hh.2.2 x hx; simp; linarith

lemma vacuum_width {d : ℝ≥0} (h : 0<d) : Slab (L := L) a d [] := ⟨h,(air (L := L) a).property,by simp⟩

@[simp] lemma invol (a) (u) (v : L.Word) : opposite a u (opposite a u v) = v := by
  unfold opposite raised
  rw [refl_over, reflect_twice, paths]
  rw [show Ortho.move (Signed.reflect a) ((u:ℝ) • basis a) = - ((u:ℝ) • basis a) by
    ext i; by_cases h : i=a <;> simp [Signed.mirrored,h], neg_add_cancel, rest]

def entering {d} {u : L.Word} (hx : Slab a d u) (v : Future L a) : Future L a :=
  ⟨linked a d u v.val, appendsFuture hx v.property⟩

@[simp] lemma when_empty {d} (h : Slab (L := L) a d []) (v : Future L a) : entering h v = travel v d := rfl

lemma connected {d e} {u v : L.Word} (hp : Slab a d u) (he : Slab a e v) (z : Future L a) :
    entering (connects hp he) z=entering hp (entering he z) := by
  apply Subtype.ext; simp [entering,linked,raised, add_smul,add_comm]

lemma realignment {u : L.Word} {d} (w : Slab a d u) (h : S.Homogeneous) (x y : Future L a) :
    S.gram a (entering w x).val y.val = S.gram a x.val (entering (mirrorsSlab w) y).val := by
  let t : E4 := (d:ℝ) • basis a
  unfold Table.gram
  rw [← invariance h (twoSides (entering w x).property y.property) t]
  congr 1
  have he (u v : L.Word) : reflect (u++v) a = reflect v a ++ reflect u a := by simp [reflectedPoint]
  change carry (reflect (u ++ carry x.val t) a ++ y.val) t = _
  rw [he,distribute,distribute,refl_over, paths, show Ortho.move (Signed.reflect a) t = -t by
    ext i; by_cases h : i=a <;> simp [Signed.mirrored,t,h], neg_add_cancel, rest,listEq]
  rfl
where listEq (u v z : L.Word) : (u++v)++z = u++(v++z) := List.append_assoc ..

structure Spread (V : Chamber S a) where
  place (d : ℝ≥0) (w : L.Word) : V.GNS.H.Op
  reads {d : ℝ≥0} {w : L.Word} (h : Slab a d w) (p : Future L a) :
    place d w (V.GNS.plant p) = V.GNS.plant (entering h p)

namespace Spread
variable {V : Chamber S a} (P : Spread V)

def radius (C : ℝ) (A : ℕ) (v : L.Word) (r : ℝ) := C^v.length * ((v.length:ℝ)/r)^(A*v.length)

def AllCopy := ∀ (D : ℕ) (R : ℝ), ∃ C : ℝ, ∃ A : ℕ, 0 < C ∧
    ∀ (w : L.Word) (d : ℝ≥0), constrained D R w → Slab a d w → ∀ r : ℝ,
    0 < r → r ≤ 1 → buffer a r d w → ‖P.place d w‖ ≤ radius C A w r

lemma blank {d} (h : 0 < d) : P.place d []=V.flow.E d :=
  V.GNS.by_bud fun i => (P.reads (vacuum_width h) _).trans (V.atBirth d i)

lemma concatenate {d e} {u v : L.Word} (h : Slab a d u) (he : Slab a e v) :
    P.place (d+e) (linked a d u v) = (P.place d u).comp (P.place e v) := by
  apply V.GNS.by_bud; intro i
  rw [ContinuousLinearMap.comp_apply,P.reads he,P.reads h, P.reads (connects h he),connected h he]

lemma adjoints {d} {u : L.Word} (h : Slab a d u) (hv : S.Homogeneous) :
    (P.place d u).adjoint = P.place d (opposite a d u) := by
  apply V.GNS.by_bud; intro x
  refine V.GNS.whole.eq_of_inner_left ℂ fun f => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add i j hi hj => simp only [map_add,inner_add_right,hi,hj]
  | single i c =>
    simp only [Kernel.Gram.stems,Finsupp.linearCombination_single,map_smul,
      inner_smul_right,P.reads h _,P.reads (mirrorsSlab h) _,V.GNS.measure]
    congr 1
    -- lhs input intermediate earlier than counterpart; use reflect twice
    rw [realignment (mirrorsSlab h) hv]; exact congr_arg (S.gram a _) (show _ from by simp [entering,linked])

lemma over_word (s : Cross a) {d} {u : L.Word} (h : Slab a d u) :
    Slab a d (carry u s.val) := by
  refine ⟨h.1,(over (⟨u,h.2.1⟩ : Future L a) s).property,?_⟩
  intro i hi; obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
  simpa [show s.val a=0 from s.property] using h.2.2 _ hw

lemma perpendicular {d} {u : L.Word} (h : Slab a d u) (s : Cross a) :
    (V.flow.U s).comp (P.place d u) = (P.place d (carry u s.val)).comp (V.flow.U s) := by
  apply V.GNS.by_bud; intro v
  simp only [ContinuousLinearMap.comp_apply,P.reads h _,← V.across s _, P.reads (over_word s h) _]
  apply congr_arg; apply Subtype.ext
  simp [over,entering,linked,raised, add_comm]

/-- Derivatives on any raw representative compatible with T quotient data.
Separate from `Reads` and requires same-C respect. -/
structure Laws {B : Table L} (R : DiffPlan B) : Prop where
  cap : P.AllCopy
  regular (d : ℝ≥0) (n : ℕ) (v : Fin n → L.Token) :
    ContDiffOn ℝ ∞ (fun x => P.place d (realize v x)) {x | Slab a d (realize v x)}
  positional (d : ℝ≥0) (n : ℕ) (v : Fin n → L.Token) (x : Points n) (p : Fin n)
      (h : Slab a d (realize v x)) (j : Axis) :
    let i := (v p).1
    Analysis.D (Points.direction p j) (fun y => P.place d (realize v y)) x =
    P.place d (realize (Function.update v p ⟨i+1,B.representative _
      (R.deriv i j (B.project i (v p).2))⟩) x)
end Spread
end YM.OS
