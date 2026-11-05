import YM.RemainderComparison.Script.Certificate
/-!
# Capacity pricing for substitutes (apply to d-th hedges derivatives independent of volume via kernel prototypes)
Do NOT debit arbitrary norms here. Pointwise summability maps using norm at *current* FinGeom separately; numerical estimates exported via registrations use actual tag price. Connect disjoint log-count.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Serif
open Function Filter Lattice RG Finset MeasureTheory Marker Push Push.AbsoluteSums
open scoped Topology BigOperators Classical
open Mosaic Muse
variable {ι τ:Type} [DecidableEq τ] {J:Census τ} {φ:τ→ℝ} {k:ℕ} {z:ι→ Poly J} {Z:Set ι}
open Verse
structure Chorus (J:Census τ) (φ:τ→ℝ) (Z:Set ι) (z:ι→Poly J) (k:ℕ): Prop where
   votes x: 0<φ x
   square i : z i*z i=0
   material i : i∈Z→ Poly.price φ (z i)≤1
   capacity q : Verse.load Z q > k → Verse.controls Z z q=0
variable (h:Chorus J φ Z z k)
include h
lemma bought (p:Multiset ι) : Poly.price φ (controls Z z p) ≤ 1:=by
   induction p using Multiset.induction_on with
   | empty=>rw [controls,Multiset.map_zero, Multiset.prod_zero,Poly.one_price]
   | cons i s he=>
      unfold controls; rw [Multiset.map_cons, Multiset.prod_cons]; split
      next H=> exact (Poly.multiplication h.votes ..).trans ((mul_le_one₀ (h.material i H) (Poly.nonnegative h.votes _) he))
      next=> rw [one_mul]; exact he
lemma housing {U:Type} (V:Verse ι U)(l:ι→ℝ)(u:U): Poly.price φ (V.paint Z l z u) ≤ ‖V.emit l u‖:=by
    unfold paint; rw [Poly.adapted, Complex.norm_real]; exact mul_le_of_le_one_right (norm_nonneg _) (bought h V.letters)

-- capacity check when τ live horizon: can certify here, e.g require each square-zero (or each mode monomial) independently along analytic Mix. Covers all V incl large count. No factorial. Inputs Z can themselves repeat name: same name, modes disallow all clashes; labels preserve through expansion.
omit h
lemma low_zero (p:Multiset ι) (i:J.Mode) (hz:∀ i,i∈ Z→(z i).part J.quiet=0) (hi:i.val.card<Verse.load Z p): (controls Z z p).part i=0:= by
   induction p using Multiset.induction_on generalizing i with
   | empty=> simp [Verse.load] at hi
   | @cons j p he=>
      unfold controls; rw [Multiset.map_cons,Multiset.prod_cons]; unfold load at hi; split
      next H =>
       rw [Multiset.filter_cons_of_pos _ H,Multiset.card_cons] at hi
       rw [Poly.part_mul]; apply sum_eq_zero; intro p' _; apply sum_eq_zero; intro y _; split; next h=>
         by_cases h':p'=J.quiet
         · rw [h',hz j H, zero_mul]
         refine mul_eq_zero_of_right _ (he y ?_)
         have hb : i.val.card=p'.val.card+y.val.card:= by rw [←h.2,card_union_of_disjoint h.1]; -- adjust implies
         have hl:0< p'.val.card:= Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr fun hb=> h' (Subtype.ext hb))
         change i.val.card<load Z p+1 at hi; omega
       next=>rfl
      next h=>rw [one_mul]; rw [Multiset.filter_cons_of_neg _ h] at hi; exact he i hi
lemma production (z : ι→Poly J) (p:τ→ℝ)(Z : Set ι)(h:∀ i,0<p i) (hp:∀ i,z i*z i=0) (hk:∀ i,i∈Z→ Poly.price p (z i) ≤ 1∧(z i).part J.quiet=0) (k:ℕ)(hu:∀ v:J.Mode,v.val.card≤ k): Chorus J p Z z k:=by
   refine ⟨h,hp,fun i hi=> (hk i hi).1,fun q h=>?_⟩; ext i; rw [low_zero q i (fun i hi=>(hk i hi).2) ((hu i).trans_lt h), Poly.part_nil]
end YM.RemainderComparison.Serif
