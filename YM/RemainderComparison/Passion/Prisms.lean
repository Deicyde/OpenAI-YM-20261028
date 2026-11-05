import YM.RemainderComparison.Solos.Horns
import YM.Push.LOCAL_SPLITTING.Funding
/-!
# Capacities and pitches

Normalize kernel asset sizes ONCE per combination/census. θ tests (slot-specific,
may include jets/h and positions) source roots. ι is occurrence seal referring to
full payload provenance (analytic kernel path, mark set etc.). Retain both. Multiple
uses with overlapping θ names die in this quotient. Even several mark-set
inputs held apart analytically, required to correspond to named coefficients on THAT
layout (not just something null after forgetting names). Can specialize under any
further downward substitutions obeying proof of compatibility.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Passion
open Function Filter Lattice RG Wilson MeasureTheory Marker
open Solos Mosaic Verse Serif Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
-- One label projected for each eligible monomial with θ. Can keep disjointness stricter as ideal.AUTH request. Polynomial coefficients cost summed after all support & sup choices
variable {θ ι:Type}[DecidableEq θ]{Z:Set ι}
variable (D:ι→ Finset θ) (J:Census θ) (Z:Set ι) (z:ι→Poly J)
/-- each alive mark leaf maps to exactly its θ names (possibly zero). The actual kernels (their phase and normalized amplitude costs) are prescribed BEFORE these controls. -/
structure Oriented : Prop where
   tags : Articles Z D
   note (i:ι) : i∈Z→ ∀ s:J.Mode,s.val≠D i→ (z i).part s=0
variable {D J Z z} {a:ι}{s:J.Mode}
open scoped Classical
-- multi θ price, per-label supports may include many sites.APP charge repeated sets before projecting.
omit [DecidableEq θ] in
lemma lit (u:ι) (i:Multiset ι) : Solos.mapWord D (u ::ₘ i)=(D u).val+mapWord D i := by rw [← Multiset.singleton_add,map_add, show mapWord D ({u}:Multiset ι)=(D u).val by simp [mapWord]]
variable (h:Oriented D J Z z)
include h
lemma spark (p:Multiset ι) (s:J.Mode) (hp:(controls Z z p).part s≠0): s.val.val= mapWord D p:=by
   induction p using Multiset.induction_on generalizing s with
   | empty=>
       classical
       simp only [controls,Multiset.map_zero,Multiset.prod_zero] at hp
       change (Poly.send J.quiet 1).part s≠0 at hp; rw [Poly.part_send] at hp; split at hp; next h=>subst s; rw [map_zero]; rfl
       next=>exact (hp rfl).elim
   | cons x p hi=>
       rw [lit]; unfold Verse.controls at hp; rw [Multiset.map_cons,Multiset.prod_cons] at hp; split at hp
       next he =>
         let v:=controls Z z p
         rw [Poly.part_mul] at hp
         obtain ⟨w,hw⟩: ∃ i:J.Mode,(∑ j:J.Mode,if Poly.merges i j s then (z x).part i * v.part j else 0)≠0:= Classical.byContradiction (fun hn=> hp (Finset.sum_eq_zero fun j _=> Classical.byContradiction fun hh=> hn ⟨j, hh⟩)) -- by_contrad leads proof orientation ¬... double
         obtain ⟨j,hj⟩:∃ j:J.Mode,(if Poly.merges w j s then (z x).part w * v.part j else 0)≠0:= Classical.byContradiction fun hn=> hw (Finset.sum_eq_zero fun j _=> Classical.byContradiction fun hh=> hn ⟨j,hh⟩)
         split at hj; next hH=>
            have hW: w.val=D x:=Classical.byContradiction (fun hx=>left_ne_zero_of_mul hj (h.note x he w hx)); have hl:= hi _ (right_ne_zero_of_mul hj); rw [←hH.2,←hW,←hl]; rw [Finset.union_val,Multiset.add_eq_union_iff_disjoint.mpr (Finset.disjoint_val.mpr hH.1)]
         next=> exact (hj rfl).elim
       next he=>
         rw [one_mul] at hp; have hx:D x=∅:=Finset.not_nonempty_iff_eq_empty.mp (mt ((h.tags.used x).mpr) he); rw [hx]; exact (hi s hp).trans (Multiset.zero_add _).symm
-- Quiet gas.Moor.Merz
lemma positive (x:Multiset ι)(hP:Verse.load Z x≠0): (controls Z z x).part J.quiet=0:= Classical.byContradiction (fun hv=> hP ((Solos.Articles.law D Z x h.tags).2 ((spark h x J.quiet hv).symm)))
lemma silence (p:Multiset ι)(hp:¬ (mapWord D p).Nodup): Verse.controls Z z p=0:=by ext i; rw [Poly.part_nil]; exact Classical.byContradiction fun he=> hp ((spark h p i he) ▸ i.val.nodup)
-- Cost: normal denominations REAL fractional powers of every fixed tag.A.G.
lemma pedigree {i:Multiset ι}(x:θ)(hp:(Verse.controls Z z i).part (J.fire x) ≠ 0): mapWord D i={x} := (spark h i _ hp).symm
-- T independent label.LMB Derι.N. marks with no connectors have exterior roots specified too.
end YM.RemainderComparison.Passion
