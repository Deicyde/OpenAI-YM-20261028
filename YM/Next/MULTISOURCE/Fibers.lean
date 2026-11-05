import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Pi.Interval
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.Star.Unitary
import YM.Space.Index

/-! Keep the sum over disjoint-address families when bucketing their activities
    by support and primary inventory. Algebraic finite version for repeated use. -/

set_option autoImplicit false
noncomputable section

namespace YM.Multi
open Finset
open scoped Classical BigOperators

lemma unique_fibers_prod {ι J X : Type*} [DecidableEq ι] [DecidableEq J] [CommSemiring X]
    (u : ι → J) (f : ι → X) (L : Finset ι) (S : Finset J) :
    (∏ q∈S, ∑ i∈ L with u i = q, f i) =
      ∑ b ∈ L.powerset.filter (fun b : Finset ι => b.image u = S ∧ Set.InjOn u b), ∏ i∈b, f i := by
  let C (q) := L.powerset.filter fun b : Finset ι => b.image u = q ∧ Set.InjOn u b
  change _ = ∑ b∈ C S, ∏ i ∈ b, f i
  induction S using Finset.induction with
  | empty =>
    rw [show C ∅={∅} by ext i; by_cases h : i=∅ <;> simp [h,C]]; simp
  | insert q S h ih =>
    rw [prod_insert h, ih, sum_mul, show
      (∑ i ∈ L with u i = q, f i * ∑ b∈ C S, ∏ j∈b, f j) =
      ∑ x ∈ (L.filter (fun i => u i=q)) ×ˢ C S, f x.1 * ∏ j ∈ x.2, f j by
        rw [Finset.sum_product]; simp_rw [Finset.mul_sum]]
    let r := L.filter (fun i => u i=q)
    have eq (b) (hb : b∈ C S) : b.image u = S := ((mem_filter.mp hb).2).1
    have nh {i : ι} {b : Finset ι} (hi : i∈ r) (hb : b∈ C S) : i ∉ b := by
      intro H
      apply h
      rw [← eq b hb]; exact mem_image.mpr ⟨_,H,(mem_filter.mp hi).2⟩
    refine Finset.sum_bij (fun x _ => insert x.1 x.2) ?_ ?_ ?_ ?_
    · rintro ⟨i,b⟩ hx
      obtain ⟨H,H'⟩ := Finset.mem_product.mp hx
      have he := (mem_filter.mp H).2
      have e := eq b H'
      obtain ⟨hb,hb'⟩ := mem_filter.mp H'
      refine Finset.mem_filter.mpr ⟨mem_powerset.mpr (insert_subset (mem_filter.mp H).1 (mem_powerset.mp hb)), ?_,?_⟩
      · rw [image_insert,e,he]
      rw [coe_insert,Set.injOn_insert (show i∉(b:Set ι) from nh H H')]
      rw [← coe_image,e,he]; exact ⟨hb'.2,h⟩
    · rintro ⟨i,b⟩ hx ⟨j,c⟩ hy H
      dsimp only at H
      obtain ⟨hi,hb⟩ := mem_product.mp hx
      obtain ⟨hj,hc⟩ := mem_product.mp hy
      have he : i=j := by
        have e : i∈insert j c := by rw [← H]; exact mem_insert_self ..
        exact (mem_insert.mp e).resolve_right (nh hi hc)
      subst j
      congr 1
      simpa only [erase_insert (nh hi hb), erase_insert (nh hj hc)] using congr_arg (fun b : Finset ι => b.erase i) H
    · intro b hb
      obtain ⟨hb,e,H⟩ := mem_filter.mp hb
      obtain ⟨i,hi,hi'⟩ := mem_image.mp (show q∈b.image u by rw [e]; exact mem_insert_self ..)
      have ht := insert_erase hi
      have hc : b.erase i ∈ C S := by
        refine mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset i b).trans (mem_powerset.mp hb)),?_, H.mono (erase_subset ..)⟩
        have hj : q ∉ (b.erase i).image u := by
          intro hw; obtain ⟨w,hw,hw'⟩ := mem_image.mp hw
          exact (mem_erase.mp hw).1 (H ((mem_erase.mp hw).2) hi (hw'.trans hi'.symm))
        have hv : insert q ((b.erase i).image u) = insert q S := by rw [← hi', ← image_insert, ht, e, hi']
        simpa only [erase_insert hj,erase_insert h] using congr_arg (fun D : Finset J => D.erase q) hv
      exact ⟨⟨i,b.erase i⟩, mem_product.mpr ⟨mem_filter.mpr ⟨mem_powerset.mp hb hi,hi'⟩,hc⟩, ht⟩
    · rintro ⟨i,b⟩ hx
      exact (prod_insert (nh (mem_product.mp hx).1 (mem_product.mp hx).2)).symm

lemma fiber_gather {ι J X : Type*} [DecidableEq ι] [DecidableEq J] [CommSemiring X]
    (u : ι → J) (f : ι → X) (L : Finset ι) (A : Finset (Finset J)) :
    (∑ q∈ A, ∏ j∈q, ∑ i∈L with u i=j, f i)=
      ∑ b ∈ L.powerset.filter (fun b : Finset ι => b.image u ∈ A ∧ Set.InjOn u b), ∏ i∈b, f i := by
  simp_rw [unique_fibers_prod]
  let D := L.powerset.filter fun b : Finset ι => Set.InjOn u b
  have h (a : Finset J) : (L.powerset.filter fun b : Finset ι => b.image u=a ∧ Set.InjOn u b) =
      D.filter (fun b => b.image u=a) := by ext; simp [D,and_left_comm,and_comm]
  simp_rw [h, Finset.sum_fiberwise_eq_sum_filter]
  congr 1
  ext; simp [D,and_left_comm,and_comm]
end YM.Multi
