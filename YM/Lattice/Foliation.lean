import YM.Lattice.Route

/-!
# Slice geometry on cover patches

Enumeration in faces is based at the minimal vertex. All complete support.
Grid patches foliated by one direction (`axes`,`other` proof often lists).
-/

set_option autoImplicit false
namespace YM.Lattice

open Finset Function

def layers (R : ℕ) : Finset ℤ := Finset.Icc (-(R : ℤ)) R

/-- pinned patch from box by fixing all unvisited axes to some coordinates. -/
def slab (R : ℕ) (x : Cover) (l : List Axis) : Finset Cover := (box R).filter fun y =>
    ∀ i ∉ l, y i=x i

lemma box_iff_layers (x : Cover) (r : ℕ) : x ∈ box r ↔ ∀ i, x i ∈ layers r := by simp [layers, forall_and]

lemma card_layers (R : ℕ) : (layers R).card = 2*R+1 := by rw [layers,Int.card_Icc]; omega

lemma slab_iff {x y : Cover} {l} {r} : y ∈ slab r x l ↔ y ∈ box r ∧ ∀ i ∉ l, y i=x i := mem_filter

lemma update_box {x : Cover} {r} (hx : x ∈ box r) {v} (hv : v ∈ layers r) (i : Axis) : update x i v ∈ box r := by
  rw [box_iff_layers] at *; intro j; by_cases h : j=i <;> simp [*, hx j]

lemma lower_pin {r : ℕ} {o : Cover} {l} {i z} (hi : i ∉ l) (x) : x ∈ slab r (update o i z) l ↔
    x ∈ slab r o (l++[i]) ∧ x i = z := by
  simp only [slab_iff,List.mem_append,List.mem_singleton,not_or]
  constructor
  · rintro ⟨hx,h⟩
    exact ⟨⟨hx,fun j ⟨h₁,h₂⟩ => by simpa [h₂] using h j h₁⟩, by simpa using h i hi⟩
  rintro ⟨⟨hx,h⟩,he⟩
  refine ⟨hx, fun j hj => ?_⟩
  by_cases H : j=i
  · simpa [H]
  simpa [H] using h j ⟨hj,H⟩

lemma step_between {r : ℕ} {o : Cover} {l} {i} (hi : i ∉ l) (z w : ℤ)
    (hz : w ∈ layers r) {x} (hx : x ∈ slab r (update o i z) l) :
    x+(w-z) • step i ∈ slab r (update o i w) l := by
  obtain ⟨h,h'⟩ := (lower_pin hi x).mp hx
  rw [show x+(w-z) • step i = update x i w by
    ext j; by_cases h0 : j=i <;> simp [*, Pi.smul_apply]]
  rw [lower_pin hi]
  refine ⟨slab_iff.mpr ⟨update_box (slab_iff.mp h).1 hz i, fun k hk => ?_⟩, by simp⟩
  rw [update_of_ne (show k ≠ i from fun he => hk (by simp [he]))]; exact (slab_iff.mp h).2 k hk

lemma slab_update_image {r : ℕ} {o : Cover} {l} {i} (hi : i ∉ l) (z w : ℤ)
    (hz : z ∈ layers r) (hw : w ∈ layers r) :
    (slab r (update o i z) l).image (·+(w-z) • step i) = slab r (update o i w) l := by
  ext x; rw [mem_image]
  constructor
  · rintro ⟨y,hy,rfl⟩; exact step_between hi z w hw hy
  intro hx
  refine ⟨_,step_between hi w z hz hx,?_⟩
  rw [add_assoc, ← add_smul]; simp

theorem slab_sum {M : Type*} [AddCommMonoid M] (r : ℕ) (o : Cover) {i} {l} (hi : i ∉ l) (f : Cover → M) :
    (∑ x ∈ slab r o (l++[i]), f x) = ∑ z ∈ layers r, ∑ x ∈ slab r (update o i z) l, f x := by
  have he : (layers r).biUnion (fun z => slab r (update o i z) l) = slab r o (l++[i]) := by
    ext x; rw [mem_biUnion]
    constructor
    · rintro ⟨z,-,hz⟩; exact ((lower_pin hi x).mp hz).1
    intro hx
    exact ⟨x i,(box_iff_layers ..).mp (slab_iff.mp hx).1 i, (lower_pin hi _).mpr ⟨hx,rfl⟩⟩
  rw [← he,sum_biUnion]; intro x hx y hy h
  exact disjoint_left.mpr fun i hi' hi'' ↦ h (((lower_pin hi i).mp hi').2.symm.trans ((lower_pin hi i).mp hi'').2)

lemma axis_orthogonal {l : List Axis} {o x y : Cover} {j r} {w : ℤ}
    (hx : x ∈ slab r (update o j w) l) (hy : y ∈ slab r (update o j w) l)
    (hj : j ∉ l) {i} (he : y=x+step i) : i ≠ j := by
  have h := ((lower_pin hj _).mp hx).2
  have h' := ((lower_pin hj _).mp hy).2
  subst y; rintro rfl; simp [h] at h'

theorem square_corners {A : Type*} [AddCommGroup A] [One A] (x : Four A) (a b : Axis) : visits x (square a b) = [x,x+step a,x+step a+step b,x+step b,x] := by
  simp [visits,square,add_right_comm (b := step b)]

section
variable {K : Type*} [Group K]

lemma axis_route_support (o x y : Cover) (l : List Axis) (h : ∀ i ∈ l, x i=y i) : axisRoute o x l = axisRoute o y l := by
  induction l with
  | nil => simp [axisRoute]
  | cons a p ih => rw [show axisRoute o x (a::p) = straight a (x a-o a) ++ axisRoute o x p from rfl, show axisRoute o y (a::p) = straight a (y a-o a) ++ axisRoute o y p from rfl,h a (by simp), ih (fun i hi => h i (by simp [hi]))]

theorem carry_succ (U : Links ℤ K) (x : Cover) (j : Axis) (d : ℤ) :
    travel U x (straight j (d+1)) = travel U x (straight j d) * U (x + d • step j,j) := by
  by_cases h : d < 0
  · have hh : straight j d = straight j (d+1) ++ [negDir j] := by
      by_cases hh : d+1=0
      · rw [show d = -1 by omega]; rfl
      unfold straight
      simp only [h, decide_true, show d+1<0 by omega]
      rw [show d.natAbs=(d+1).natAbs+1 by omega, ← List.replicate_append_replicate]; rfl
    rw [hh,travel_append,straight_stop,travel,travel,Step.neg_read]
    rw [show x+(d+1) • step j - step j = x + d • step j by rw [add_smul, one_smul]; abel]; group
  have hh : straight j (d+1)=straight j d ++ [posDir j] := by
    unfold straight
    rw [show (d+1).natAbs=d.natAbs+1 by omega]
    simp only [h, decide_false, show ¬ d+1<0 by omega]; rw [← List.replicate_append_replicate]; rfl
  rw [hh, travel_append,straight_stop]; simp [travel]
end
end YM.Lattice
