import YM.Slice.Levels

/-!
# Make circular expression for *actual* Wilson integrand. This is
not a Hamiltonian regulator. Helps point interpolation and reflected-cell RP.
Defines slice weights and one-step temporal interaction including all threads.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Slice
open Function Set MeasureTheory Lattice Wilson Cells
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {n : Side} {G : Gauge} (a : Axis)

abbrev Pair (a : Axis) := {p : Flat a × Flat a // p.1.val < p.2.val}
abbrev SmallFace (a : Axis) (n : Side) := Row a n × Pair a

def smallLoop (X : Leaf G a n) (f : SmallFace a n) :=
  let b := f.2.val.1
  let c := f.2.val.2
  X (f.1,b) * X (forward a f.1 b,c) * (X (forward a f.1 c,b))⁻¹ * (X (f.1,c))⁻¹

/-- First space then time. -/
def connect (X Y : Leaf G a n) (U : Thread G a n) (p : Tile a n) :=
  X p * U (forward a p.1 p.2) * (Y p)⁻¹ * (U p.1)⁻¹

@[fun_prop] lemma small_con (f : SmallFace a n) : Continuous (fun X : Leaf G a n => smallLoop a X f) := by
  unfold smallLoop; fun_prop

lemma square_val (U : Config G n) (x : Site n) (i j : Axis) :
    travel U x (square i j) = U (x,i) * U (x+step i,j) * (U (x+step j,i))⁻¹ * (U (x,j))⁻¹ := by
  simp [square,travel,sub_eq_add_neg,add_comm,add_assoc,add_left_comm,mul_assoc]

def spatialFace (z : Per n) (f : SmallFace a n) : Face (Per n) := (plane a z f.1, ⟨(f.2.val.1.1,f.2.val.2.1),f.2.2⟩)
def timely (z : Per n) (v : Tile a n) : Face (Per n) := (plane a z v.1,PlaqAxes.ordered v.2 a v.2.property)

theorem raw_cost (x : Circle G a n) (z : Per n) (f) : faceValue (chain a x) (spatialFace a z f) = smallLoop a (x z).1 f := by
  simp [smallLoop,spatialFace,faceValue,square_val]

theorem recurring (x : Circle G a n) (z : Per n) (v) : G.price (faceValue (chain a x) (timely a z v)) =
    G.price (connect a (x z).1 (x (z+1)).1 (x z).2 v) := by
  obtain ⟨u,b⟩ := v
  have he : travel (chain a x) (plane a z u) (square b.val a) =
      connect a (x z).1 (x (z+1)).1 (x z).2 (u,b) := by rw [square_val]; simp [connect]
  rcases lt_or_gt_of_ne b.property with h|h
  · simp only [timely, PlaqAxes.ordered, min_eq_left h.le, max_eq_right h.le, faceValue, he]
  simp only [timely, PlaqAxes.ordered, min_eq_right h.le, max_eq_left h.le, faceValue]
  rw [← he]
  change G.price (travel _ _ (oriented (posDir a) (posDir b))) = G.price (travel _ _ (oriented _ _))
  rw [oriented_swap]; simp

lemma calendar : Bijective (Sum.elim (fun p : Per n × SmallFace a n => spatialFace a p.1 p.2)
    (fun p : Per n × Tile a n => timely a p.1 p.2)) := by
  have he {b : Flat a} : a ∈ ({min b.val a, max b.val a} : Finset Axis) := by
    rcases lt_or_gt_of_ne b.property with h|h <;> simp [h.le]
  have hz {p : Pair a} : a ∉ ({p.val.1.val,p.val.2.val} : Finset Axis) := by simp [(Ne.symm p.val.1.property),Ne.symm p.val.2.property]
  have hb (p : Per n × SmallFace a n) (q : Per n × Tile a n) : spatialFace a p.1 p.2 ≠ timely a q.1 q.2 := by
    intro H; apply hz (p := p.2.2)
    change _ ∈ ({(spatialFace a p.1 p.2).2.val.1,(spatialFace a p.1 p.2).2.val.2} : Finset Axis)
    rw [H]; exact he
  constructor
  · rintro (⟨t,v,i⟩|⟨t,v,i⟩) (⟨u,w,j⟩|⟨u,w,j⟩) H
    · have hx := congr_arg (fun q : Face (Per n) => q.1) H
      change plane a t v = plane a u w at hx
      have ht : t=u := by simpa using congr_fun hx a
      have hv : v=w := by simpa using congr_arg (drop a) hx
      have hq : i=j := Subtype.ext (Prod.ext
        (Subtype.ext (congr_arg (fun q : Face (Per n) => q.2.val.1) H))
        (Subtype.ext (congr_arg (fun q : Face (Per n) => q.2.val.2) H)))
      rw [ht,hv,hq]
    · exact (hb _ _ H).elim
    · exact (hb _ _ H.symm).elim
    have hx := congr_arg (fun q : Face (Per n) => q.1) H
    change plane a t v = plane a u w at hx
    have ht : t=u := by simpa using congr_fun hx a
    have hv : v=w := by simpa using congr_arg (drop a) hx
    have hi : min i.val a = min j.val a := congr_arg (fun q : Face (Per n) => q.2.val.1) H
    have hj : max i.val a = max j.val a := congr_arg (fun q : Face (Per n) => q.2.val.2) H
    have hh : i=j := by
      have hm (x : Axis) : (min x a).val + (max x a).val = x.val+a.val := by
        rcases le_total x a with hx|hx
        · simp [hx]
        simp [hx,add_comm]
      apply Subtype.ext; apply Fin.ext
      have hg := hm i
      rw [hi,hj,hm] at hg
      omega
    rw [ht,hv,hh]
  rintro ⟨x,⟨b,c⟩,h⟩
  change b<c at h
  rcases eq_or_ne b a with e|e
  · subst b; exact ⟨Sum.inr (x a,drop a x,⟨c,h.ne'⟩),by simp [timely,PlaqAxes.ordered,h.le]⟩
  rcases eq_or_ne c a with e'|e'
  · subst c; exact ⟨Sum.inr (x a,drop a x,⟨b,h.ne⟩),by simp [timely,PlaqAxes.ordered,h.le]⟩
  exact ⟨Sum.inl (x a,drop a x,⟨(⟨b,e⟩,⟨c,e'⟩),h⟩),by simp [spatialFace]⟩

def potential (X : Leaf G a n) := ∑ i, G.price (smallLoop a X i)

def transition (X Y : Leaf G a n) (u : Thread G a n) := ∑ v, G.price (connect a X Y u v)

theorem total (x : Circle G a n) : energy (chain a x) =
    ∑ i : Per n, (potential a (x i).1 + transition a (x i).1 (x (i+1)).1 (x i).2) := by
  rw [energy, ← Equiv.sum_comp (Equiv.ofBijective _ (calendar (n := n) a)), Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, Equiv.ofBijective_apply,Sum.elim_inl,Sum.elim_inr,raw_cost,recurring]
  simp [potential,transition,Fintype.sum_prod_type,Finset.sum_add_distrib]

def evenPart (β : ℝ) (X : Leaf G a n) := Real.exp (-β*potential a X/2)

def weight (β : ℝ) (X Y : Leaf G a n) (u : Thread G a n) :=
  evenPart a β X * Real.exp (-β * transition a X Y u) * evenPart a β Y

@[fun_prop] lemma weight_cont (β : ℝ) : Continuous fun z : Leaf G a n × Leaf G a n × Thread G a n =>
    weight a β z.1 z.2.1 z.2.2 := by
  unfold weight evenPart transition connect potential
  fun_prop

theorem weight_pos (β : ℝ) (X Y : Leaf G a n) (u) : 0 < weight a β X Y u := by
  unfold weight evenPart; positivity

/-- Reversal temporal threads takes adjoint. -/
theorem transition_reflect (X Y : Leaf G a n) (u) : transition a Y X u⁻¹ = transition a X Y u := by
  unfold transition; apply Finset.sum_congr rfl; intro v _
  rw [show connect a Y X u⁻¹ v = (u v.1)⁻¹ * (connect a X Y u v)⁻¹ * (u v.1) by simp [connect,mul_assoc]]
  simpa using G.price_conj (u v.1)⁻¹ (connect a X Y u v)⁻¹

theorem weight_reflect (β : ℝ) (X Y : Leaf G a n) (u) : weight a β Y X u⁻¹ = weight a β X Y u := by
  unfold weight; rw [transition_reflect]; ring

theorem totalWeight (x : Circle G a n) (β) : bare β (chain a x) = ∏ i,
    weight a β (x i).1 (x (i+1)).1 (x i).2 := by
  unfold bare weight evenPart
  rw [total]
  simp_rw [← Real.exp_add, ← Real.exp_sum]
  congr 1
  have he : ∑ i : Per n, potential a (x (i+1)).1 = ∑ i, potential a (x i).1 :=
    Equiv.sum_comp (Equiv.addRight (1 : Per n)) fun i => potential a (x i).1
  simp only [Finset.sum_add_distrib,← Finset.sum_div,← Finset.mul_sum,he]; ring
end YM.Slice
