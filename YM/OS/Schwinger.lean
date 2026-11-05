import YM.Hilbert.Kolmogorov
import YM.Euclid.Words

/-!
# Coordinate reflection-positive spaces for the same hierarchy

Through positive half-space from position test convention. Time evolution acts
on *all* locations of a word. Descends because correlation bounds are global
away from collisions. Does not assume spectrum condition/PVM here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS
open Function Set Filter MeasureTheory
open Word Analysis
open scoped Topology ContDiff BigOperators InnerProductSpace NNReal ComplexOrder
variable {G : Gauge} {L : Register G} (a : Axis) {S : Table L}

def transverse (a : Axis) : Submodule ℝ E4 where
  carrier := {x | x a=0}
  add_mem' := fun {x y} h hp => by change x a+y a=0; rw [h,hp,add_zero]
  smul_mem' := fun t x h => by change t * x a=0; rw [h, mul_zero]
  zero_mem' := rfl
abbrev Cross := ↥(transverse a)

abbrev Future (L : Register G) (a) := {w : L.Word // Positive w a}

def air : Future L a := ⟨[], (show (distinct (L := L) []) from locations.mpr (by simp)),by simp⟩

variable {a}

lemma sign_act {v : L.Word} (s : Signed) : act s v = v.map (fun p => (Ortho.move s.ortho p.1,L.move s p.2)) := rfl

@[simp] lemma reflect_twice (a : Axis) (v : L.Word) : reflect (reflect v a) a=v := by
  simp only [reflectedPoint,← List.map_reverse,List.reverse_reverse,List.map_map]
  have he : (fun x : E4 => Ortho.move (Signed.reflect a) (Ortho.move (Signed.reflect a) x)) = id := by
    ext x i
    simp [Signed.mirrored]; split_ifs <;> simp
  have hv (p : L.Token) : L.reflectedToken a (L.reflectedToken a p) = p := by unfold Register.reflectedToken; simp
  -- unfold under lists safely
  convert! List.map_id v using 1
  congr 1; ext1 p; rcases p with ⟨t,p⟩
  exact Prod.ext (congr_fun he t) (hv _)

lemma refl_over (v : L.Word) (x : E4) (a : Axis) : reflect (carry v x) a =
    carry (reflect v a) (Ortho.move (Signed.reflect a) x) := by
  simp only [carry,reflectedPoint,← List.map_reverse,List.map_map]
  congr 1
  ext1 i
  exact Prod.ext ((Ortho.motion _).map_add _ _) rfl

lemma twice_expect (H : S.Basic) (h : S.RealSpin) (i : Axis) (v : L.Word) (he : distinct v) :
    S.expect (reflect v i) = star (S.expect v) := by
  have hv : List.Perm v v.reverse := (List.reverse_perm _).symm
  have hw : distinct v.reverse := by rw [locations, List.map_reverse]; exact List.nodup_reverse.mpr (locations.mp he)
  rw [← Table.order S H.toSymmetric he hv]
  have hh : reflect v i = realize (L.reflectedToken i ∘ tokens v.reverse) (Points.move (Signed.reflect i) (positions v.reverse)) := by
    rw [reflectedPoint,realize]
    let f := fun p : L.Plant => (Ortho.move (Signed.reflect i) p.1, L.reflectedToken i p.2)
    have ht : (List.ofFn v.reverse.get).map f = List.ofFn (f ∘ (v.reverse.get)) := List.map_ofFn
    rw [List.ofFn_get] at ht; exact ht
  rw [hh,S.readAt]
  let t := tokens (L := L) v.reverse
  change S.read _ _ = star (S.read (positions v.reverse) t)
  rw [show L.reflectedToken i ∘ tokens v.reverse = L.move (Signed.mirror i) ∘ (L.conjugate ∘ t) from rfl]
  exact (h.mirror (Signed.mirror i) hw _).trans (h.real hw _)

lemma nonnegative (H : S.Hierarchy) : NNKernel (fun (x y : Future L a) => S.gram a x.val y.val) := by
  apply NNKernel.criterion
  · intro x y
    have he : distinct (reflect y.val a ++ x.val) := twoSides y.property x.property
    have hv (w v : L.Word) : reflect (w++v) a = reflect v a ++ reflect w a := by simp [reflectedPoint]
    change star (S.expect _) = S.expect _
    rw [← twice_expect H.laws H.spin a _ he, hv, reflect_twice]
  intro m x c
  refine le_trans (H.positive a m (fun i => (x i).val) (fun i => (x i).property) c) (le_of_eq ?_)
  apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j hj; ring

/-- OS core. Plant vectors specified even when null. -/
abbrev Schwinger (S : Table L) (a : Axis) := Kernel.Gram fun (x y : Future L a) => S.gram a x.val y.val

theorem schwinger_ready (H : S.Hierarchy) : Nonempty (Schwinger S a) := Kernel.host (nonnegative H)

lemma nil_norm (X : Schwinger S a) (H : S.Basic) : ‖X.plant (air a)‖=1 := by
  have hx := X.measure (air a) (air a)
  rw [show S.gram a (air a).val (air a).val=1 from H.trivial _ _] at hx
  rw [@norm_eq_sqrt_re_inner ℂ, hx]; simp

def travel (v : Future L a) (t : ℝ≥0) : Future L a :=
  ⟨carry v.val ((t:ℝ) • basis a), still v.property.1 _, by
    intro p hp; obtain ⟨x,h,rfl⟩ := List.mem_map.mp hp
    change 0 < x.1 a + _
    exact add_pos_of_pos_of_nonneg (v.property.2 x h) (by simp)⟩

def over (v : Future L a) (u : Cross a) : Future L a :=
  ⟨carry v.val u.val, still v.property.1 _, by
    intro p hp; obtain ⟨x,h,rfl⟩ := List.mem_map.mp hp
    change 0 < x.1 a + u.val a; rw [u.property, add_zero]; exact v.property.2 _ h⟩

lemma invariance (Ht : S.Homogeneous) {x : L.Word} (hx : distinct x) (t : E4) :
    S.expect (carry x t) = S.expect x := by
  rw [show carry x t = realize (tokens x) (Points.across t (positions x)) from by
    unfold carry realize
    let f := fun p : L.Plant => (p.1+t,p.2)
    have he : (List.ofFn x.get).map f = List.ofFn (f ∘ x.get) := List.map_ofFn
    rw [List.ofFn_get] at he; exact he]
  rw [S.readAt]; exact Ht _ _ hx ..

@[simp] lemma paths (p : L.Word) (a b : E4) : carry (carry p a) b=carry p (a+b) := by
  unfold carry; rw [List.map_map]; congr 1; ext1 x; simp [add_assoc]

@[simp] lemma rest (p : L.Word) : carry p 0=p := by simp [carry]

@[simp] lemma distribute (p v : L.Word) (a : E4) : carry (p++v) a=carry p a++carry v a := by simp [carry]

lemma sym_time (h : S.Homogeneous) (a : Axis) (x y : Future L a) t :
    S.gram a (travel x t).val y.val = S.gram a x.val (travel y t).val := by
  unfold Table.gram
  let s : E4 := (t:ℝ) • basis a
  rw [← invariance h (twoSides (travel x t).property y.property) s]
  congr 1
  simp only [distribute, travel]
  rw [refl_over, paths, show Ortho.move (Signed.reflect a) s = -s by
    ext i; by_cases e : i=a <;> simp [s, Signed.mirrored,e], neg_add_cancel, rest]

lemma sym_space (h : S.Homogeneous) (a : Axis) (x y : Future L a) t :
    S.gram a (over x t).val (over y t).val = S.gram a x.val y.val := by
  unfold Table.gram over; simp only [refl_over]
  rw [show Ortho.move (Signed.reflect a) t.val=t.val from by
    ext i; by_cases hi : i=a <;> simp [Signed.mirrored,hi,show t.val a=0 from t.property], ← distribute]
  apply invariance h (twoSides x.property y.property)

@[simp] theorem done (w : Future L a) : travel w 0 = w := Subtype.ext (show _ from by simp [travel])
@[simp] theorem advances (w : Future L a) (t u) : travel (travel w t) u = travel w (t+u) := by
  apply Subtype.ext; simp [travel,add_smul]
@[simp] theorem inAir (t : ℝ≥0) : travel (air a (L := L)) t=air a := Subtype.ext rfl
@[simp] theorem pause (w : Future L a) : over w 0 = w := Subtype.ext (show _ from by simp [over])
@[simp] theorem parallel (w : Future L a) (t u) : over (over w t) u=over w (t+u) := by apply Subtype.ext; simp [over]
@[simp] theorem overAir (t) : over (air a (L := L)) t=air a := Subtype.ext rfl
@[simp] theorem switch (w : Future L a) (t u) : over (travel w t) u=travel (over w u) t := by apply Subtype.ext; simp [over,travel,add_comm]
end YM.OS
