import YM.Next.RANK.Escape

/-!
# Correct before computing corrected coefficients

Address D lives on a particular cell footprint currently; only when its complete
mask succeeds there is this part of a regular exponent. `clips` factors the
rest of that exponent without loss at mask jumps. Used per W entry in the corrected
geometry. All statements here are about THE COMPLETE polynomial.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Shift
open Lattice Wilson RG Finset MeasureTheory Marker Value Glyph EntryWord Exponential
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type*} [DecidableEq V] [Fintype V] {ζ : V → Site n} {τ : ℝ}

variable (W : SourceAt G ζ) (d : ℂ)
-- one connected W entry; d SIGNED correction. Shift on good.

def reg : SourceAt G ζ where
  extent := W.extent
  fires := W.fires
  chosen := W.chosen
  remembers := W.remembers
  value := fun U => W.value U + d
  meas := W.meas.add measurable_const
  loc := fun U V h => congr_arg (·+d) (W.loc U V h)
  inv := fun k U => congr_arg (·+d) (W.inv k U)

def fail (τ) : Refusal G ζ τ where
  extent := W.extent
  fires := W.fires
  chosen := W.chosen
  remembers := W.remembers
  value := fun U => if Healthy τ W.extent U then 0 else d
  meas := Measurable.ite (healthy_closed τ W.extent).measurableSet measurable_const measurable_const
  refuses U hn H := hn (if_pos H)
  only := by intro U V _ h; simp only [Healthy,Finset.disjoint_iff_inter_eq_empty,h]
  inv := by intro k U; simp only [Healthy, gauge_flags]; split_ifs <;> rfl

lemma mon (a t : ℂ) : Poly.send W.fires a + Poly.send W.fires t= Poly.send W.fires (a+t) := by
  ext v; rw [Poly.part_plus]; simp only [Poly.part_send]; split_ifs <;> simp

lemma clips (U) (τ) : Poly.send W.fires d + W.amount τ U = (reg W d).amount τ U + (fail W d τ).amount U := by
  unfold reg SourceAt.amount Refusal.amount fail; dsimp only
  by_cases h : Healthy τ W.extent U
  · rw [if_pos h,masked_eq _ _ _ U h,masked_eq _ _ _ _ h,Poly.send_zero, add_zero,add_comm]; exact mon W ..
  rw [if_neg h,masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,add_comm]

lemma nils (z : ℂ) : (Poly.send W.fires z).part (quiet _) = 0 := by
  simp only [Poly.part_send]; apply if_neg; exact fun h => W.chosen.ne_empty (Subtype.ext_iff.mp h.symm)

lemma one (τ) (U) : Poly.pass ((fail W d τ).amount U) = (fail W d τ).amount U + 1 := by
  let x := (fail W d τ).amount U
  have hi : x.part (quiet _) = 0 := nils W _
  have h : x^2=0 := by
    dsimp only [x,Refusal.amount]; rw [sq,plate_pair]; exact if_neg (fun H => Finset.disjoint_left.mp H W.chosen.choose_spec W.chosen.choose_spec)
  change Poly.pass x=_
  rw [pass_extend hi (Fintype.card V+1) (by omega),sum_range_succ',sum_range_succ']
  have he (i : ℕ) : x^(i+1+1)=0 := by rw [show i+1+1=i+2 from rfl,pow_add,h,mul_zero]
  simp_rw [he]; simp [x]

variable {κ α β : Type*} [DecidableEq κ] [Fintype κ] [Fintype α] [DecidableEq β] [Fintype β]
variable (D : Rep G n) (K : κ → Lifted G ζ D.p.threshold)

-- Complete output after correction. Includes right refusals on bad domains.
lemma made (H : α → SourceAt G ζ) (P : β → SourceAt G ζ) (C : β → ℂ) (U : Config G n) :
    Poly.pass (∑ i, Poly.send (P i).fires (C i))*dust D (Sum.elim H P) K U=
      dust D (Sum.elim H (fun i => reg (P i) (C i))) (merged K (fun i => fail (P i) (C i) D.p.threshold)) U := by
  let f : β → Refusal G ζ D.p.threshold := fun i => fail (P i) (C i) D.p.threshold
  let h : β → SourceAt G ζ := fun i => reg (P i) (C i)
  let e : κ → Lifted G ζ D.p.threshold := K
  let S := fun X : SourceAt G ζ => X.amount D.p.threshold U
  let X := ∑ i, S (H i)
  let Y := ∑ i,S (h i)
  have hx (x : SourceAt G ζ) : (S x).part (quiet _)=0 := nils x _
  let Vq := fun i => (f i).amount U
  let M := ∑ i,Poly.send (P i).fires (C i)
  have he : M + (X + ∑ i,S (P i)) = (X+Y)+∑ i,Vq i := by
    rw [add_left_comm, add_assoc X, ← sum_add_distrib, show Y=∑ i, S (reg (P i) (C i)) from rfl,← sum_add_distrib]
    congr 1; apply sum_congr rfl; intro i _; exact clips (P i) (C i) U D.p.threshold
  have hf i : (Vq i).part (quiet _) = 0 := nils (P i) _
  have ha : M.part (quiet _)=0 := by simp only [M,Poly.part_sum]; exact sum_eq_zero fun i _ => nils _ _
  have hb : X.part (quiet _)=0 := by simp only [X,Poly.part_sum]; exact sum_eq_zero fun i _ => hx _
  have hc : (∑ i,S (P i)).part (quiet _)=0 := by rw [Poly.part_sum]; exact sum_eq_zero fun i _ => hx _
  have hd : Y.part (quiet _)=0 := by simp only [Y,Poly.part_sum]; exact sum_eq_zero fun i _ => hx _
  have hn := coins K f U
  simp_rw [dust,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]; rw [mul_smul_comm]
  apply congr_arg (fun x : veil V => (Real.exp (D.exponent U):ℂ) • x)
  change Poly.pass M*(Poly.pass (X+∑ i, S (P i))*_) = Poly.pass (X+Y)*∑ i,Lifted.pack (merged K f) i U
  rw [← mul_assoc,← pass_add _ _ ha (by simp [hb,hc]), he, pass_add _ _ (by simp [hb,hd]) (by rw [Poly.part_sum]; exact sum_eq_zero fun i _ => hf i),
    pass_sum _ _ (fun i _ => hf i),← hn,mul_assoc,mul_comm (∏ i, Poly.pass (Vq i))]
  congr 2; apply prod_congr rfl; intro i _; exact one (P i) (C i) D.p.threshold U
end YM.Next.Rank.Shift
