import YM.Contacts.Score.Subdivide
import YM.Contacts.Coherent

/-! # Recursion at the level of finite pointwise expressions

This is the field-valued score not yet a distribution. See body for the limits in testing.
`ceiling` counts exactly possible retained weights (including the zero case when the degree is
negative). `leave`/`cascade` are chosen for lightweight algebra and pointwise show exact equations.
Tests in all identities below may vanish near all horizontal/mixed slabs but **not** in general
near child diagonals: use Taylor when they don't. The expressions are total (use natural zero
junk, including indicators on detector ranges). Estimates on prescribed supports and
applications to genuine Euclidean hierarchies will not use unseparated readings.

`System` is packaging input to this calculus (includes positions in ambient plane
with physical offsets). Heights, center projections, field system and probes will always be
filled by the same `fill`/Devices implementation for nonperturbative uses. Can then compare with
perturbative scores without identifying field spaces. Cumulant recursion is by cardinality,
NOT loss bound/expansion parameter. This source doesn't compute PT expansions yet.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory MultipleContact Submodule Ordered
open scoped Topology BigOperators Classical ContDiff TensorProduct InnerProductSpace
variable {k : ℕ} {E A B : Type*} [NormedAddCommGroup E][InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [CommRing A][Algebra ℂ A]
variable [CommRing B][Algebra ℂ B]
variable (P : E→ₗᵢ[ℝ] Points k)

structure System (E A : Type*) (k : ℕ) [NormedAddCommGroup E][InnerProductSpace ℝ E] [CommRing A][Algebra ℂ A] where
   deg : Fin k → ℕ
   reader (g : Group k) (w : ℕ) : E→ A→ₗ[ℂ] A
   field (i : Fin k) : E→ A

namespace System
variable (S : System E A k) (s : ℝ) (g : Group k)
/-- Total engineering degree of the original basis word. -/
def degree := g.sum S.deg
def relative (g : Group k) := 4*(g.card-1)
def depth := S.degree g +1 - relative g

def subtractAt (g : Group k) (F : Score E A) := - ∑ w:Fin (S.depth g), reshape (S.reader g w) F * instructionScore E A (taylor (normalOn P g) s ((S.depth g) - 1-w.val))
-- helper for finset strong recursion without measure unfolding through finite sums
private def replacing (g : Group k) (C : ∀ f : Group k, f.card < g.card → Score E A) : Group k → Score E A := fun f=> if h:f.card<g.card then C f h else 0

def elementary := (g.prod S.field) ⊗ₜ[ℂ] (1:Optical E)
def cumulant (g : Group k) : Score E A := if g.card < 2 then elementary S g else
    S.subtractAt P s g (receding (replacing g fun f _=> cumulant f) g)
termination_by g.card
-- `cumulant` and all its operations on a region are on originally assigned engineering grades.
def punctured (g : Group k) := receding (S.cumulant P s) g
def full := totalForm (S.cumulant P s) g
lemma single_op {i : Fin k} : S.cumulant P s {i}= S.field i ⊗ₜ[ℂ] (1:Optical E) := by rw [cumulant]; simp [elementary]
lemma equation_subtract (hg : 1 < g.card) : S.cumulant P s g= S.subtractAt P s g (S.punctured P s g) := by
  rw [cumulant,if_neg (show ¬ _ by omega)]; congr 1; unfold punctured receding
  refine Finset.sum_congr rfl fun i hi=> Eq.symm (?_ : parcel (S.cumulant P s) i= _)
  refine eq_product (p:=S.cumulant P s) (?_) -- arguments name etc
  intro j hj; have he:= Finset.card_lt_card (inner_piece i (Finset.mem_erase.mp hi).1 hj); rw [replacing,dif_pos he]
lemma full_formula (hg : g.Nonempty) : S.full P s g= S.punctured P s g+ S.cumulant P s g := partition_cases hg
lemma full_single (i : Fin k) : S.full P s {i}= S.field i ⊗ₜ[ℂ] (1:Optical E) := by
   rw [full_formula P S s {i} (Finset.singleton_nonempty _), single_op]
   unfold punctured receding
   rw [Finset.sum_eq_zero (fun P h=> ((Finset.mem_erase.mp h).1 (top_of_single i P)).elim), zero_add]
lemma uses_part {g : Group k}{q : Group k → Score E A}(Q : Pieces g)(hQ : ∀ y∈ Q.parts, Mark (Uses (normalOn P y)) (q y)) : Mark (Uses (normalOn P g)) (parcel q Q):= by
   apply Mark.chain _ _ _ (fun i hi=> Mark.switch (hQ i hi) (fun v hv=> hv.widen (normal_le P (Q.subset hi))))
   intro x hx y hy h; exact (hQ _ hx).agree (hQ _ hy) (fun _ _ ha hb=> ha.independent hb (normals_distinct P (Q.disjoint hx hy h)))
lemma uses_cumulant : Mark (Uses (normalOn P g)) (S.cumulant P s g):=by
   induction g using Finset.strongInductionOn with
   | _ g ih=>
     by_cases hg : g.card<2
     · rw [cumulant,if_pos hg]; exact .atom _ Uses.id
     rw [S.equation_subtract P s g (by omega)]
     have ht : Mark (Uses (normalOn P g)) (S.punctured P s g) := by apply Mark.sum; intro i hi; exact uses_part P _ fun j hj=> ih j (inner_piece i (Finset.mem_erase.mp hi).1 hj)
     apply Mark.minus; apply Mark.sum; intro i hi; exact Mark.prod (ht.transformed _) (Mark.inst (Uses.taylor _ le_rfl _ _)) (fun _ _ hf hg=> hf.times hg)
lemma uses_full (g : Group k) : Mark (Uses (normalOn P g)) (S.full P s g) := Mark.sum fun i _=> uses_part P i (fun _ _=> S.uses_cumulant ..) -- S not binder?
lemma compatible : permitted (S.cumulant P s):= fun a b h=> (S.uses_cumulant P s a).agree (S.uses_cumulant P s b) fun _ _ ha hb=> ha.independent hb (normals_distinct P h)
lemma can_use : permitted (S.full P s) :=fun a b h=> (S.uses_full P s a).agree (S.uses_full P s b) fun _ _ ha hb=> ha.independent hb (normals_distinct P h)
lemma uses_punctured : Mark (Uses (normalOn P g)) (S.punctured P s g):= Mark.sum fun i _=> uses_part P i (fun _ _=> S.uses_cumulant ..)

/-- True term seen only at germs on its total collapsing point. -/
lemma translatesOrigin : Mark (fun q=> Germ q (slide (normalOn P g) 0)) (S.cumulant P s g):= by
   by_cases hg : g.card<2
   · have hp : normalOn P g= ⊥:= by unfold normalOn; rw [rank_eq_zero (by omega)]; exact LinearMap.ker_eq_bot.mpr P.injective
     rw [cumulant,if_pos hg]; apply Mark.atom _; rw [hp, show ⇑(slide (⊥:Submodule ℝ E) 0) = id from funext fun x=>by simp only [slide_zero,starProjection_bot,zero_apply,sub_zero,id_eq]] -- coe?
     exact Germ.identity
   rw [S.equation_subtract P s g (by omega)]
   exact Mark.minus (Mark.sum fun i _=> Mark.prod ((S.uses_punctured P s g).transformed (S.reader g i)) (Mark.inst (focal s ((S.depth g)-1-i.val))) (fun _ _ h=> Germ.right h))

/-- Restrict right by the indicated mask-test. This equates optical instructions in an equality
of tensors, not just isolated tests when no more projections or group operations are performed. -/
lemma refines (v : SmoothTests E) (Q : Pieces g) (hg : plane g ≤ LinearMap.range P.toLinearMap)
    (hv : ∀ x∈ tsupport v.val, ∀ i∈Q.parts, ∀ j∈Q.parts,i≠j → ∀ a∈ i,∀ b∈ j,(P x) a≠(P x) b) :
    S.full P s g*instructionScore E A (mask v) = parcel (S.full P s) Q * instructionScore E A (mask v) := by
  let p:= S.cumulant P s; change totalForm p _ * _ = parcel (totalForm p) _ * _
  rw [← full_expands p Q (S.compatible P s), Finset.sum_mul, totalForm,Finset.sum_mul]; symm
  apply Finset.sum_subset (Finset.filter_subset ..); intro a _ hi; obtain ⟨b,hb,u,hu,y,hy,hxy,c,hc,d,hd,hcu,hdy⟩:= crossing (P:=a) (Q:=Q) (fun h=> hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
  rw [parcel,split_last _ hb p ((S.compatible P s).stands a),mul_assoc, all_off (f:=v) (K:=normalOn P b) (?_) (S.translatesOrigin P s b),mul_zero]; intro x hx hp; have h := Submodule.starProjection_apply_eq_zero_iff (normalOn P b) |>.2 hx; exact hv _ hp _ hu _ hy (Ne.symm hxy) _ hcu _ hdy ((collapsed_iff ..).1 ((local_collapse (le_trans (plane_le (a.subset hb)) hg) x).2 h) _ hc _ hd)

end System
end YM.Contacts.Normal
