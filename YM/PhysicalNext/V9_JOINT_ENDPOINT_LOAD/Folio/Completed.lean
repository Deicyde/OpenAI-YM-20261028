import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Portion
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Reach
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind

/-!
# Using these extensions at points with only local true output-flags

Treat actual reads of output plaquettes at every tested site as dependencies,
including at equality. Only transfer regularity through agreements of
*fixed-table expressions*. Never exchange the tables or change k under ∫ or
leftDerivs. `T.high` etc and all path kernels periodized from same data.
The correction matrix INVERSE below only used expanded on full bona fide
sectors! At partially wrong sectors its individual polynomials are still
meaningful finite-window products & that's what these reads price there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Pressure Precision Wilson Tree Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Wisps Schur Push.SectorMeasure
open AnalyticBridge.NonflatCovarianceLocality
open AnalyticBridge.NonflatCovarianceLocality.Matching AnalyticBridge.NonflatCovarianceLocality.Placement
open AnalyticBridge.NonflatCovarianceLocality.Full (point groupWindow)
open AnalyticBridge.SectorAffine (Offset.b Offset.mean Offset.f0 Offset.fixedBase panels_within)
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {A B : Stores S} {F H : Forest S.ratio}
    {k k' : S.Choices} {V W U : Config G c} {T : Tube G S} {P : Teller G} {x : ℝ} {o : Site c} {r : ℕ} {q : Chi} {d g : ℝ}

lemma completion_reads (h : Printed x A V o r) (F : Forest S.ratio) (k : S.Choices) (U : Config G c) :
    ReadsWithin o r A (amended x A V) F F U U k k :=
  ⟨fun _ _=>rfl,h,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩




namespace Bulletin
variable (b : Bulletin x P T) (h : Printed x A V o r)
include b h
lemma f0_correct (p : Rows.Receipt G S) (he : separation o (down S p)+enough S x ≤ r) (F : Forest S.ratio) (Y : LinkArray G (Frozen A x F)) :
    Offset.f0 T x A F k V q d Y p = source T x V k (shots S x) A F q d Y p := by
  let B := amended x A V
  have hb := (completion_reads h F k V).correspond x p (by unfold enough at he; omega)
  have hx := congr_fun (b.apply_base B F V k rfl) p.1
  have he' : Rows.restrict x (shots S x) A F (Offset.fixedBase T x V k) p.1 = Rows.restrict x (shots S x) A F (base T x V k) p.1 := by
    simpa only [Rows.restrict, B, hb] using! hx
  unfold Offset.f0 source; rw [restrict_add,restrict_add,tape_read,tape_read,Pi.add_apply,Pi.add_apply,he']
lemma b_correct (Y : LinkArray G (Frozen A x F)) (i : In x A F (G:=G)) (he : separation o (front A F i)+enough S x+span S.patch x ≤ r) :
    Offset.b T x k A F q d Y V i=Rows.blame T x V k (shots S x) A F q d Y i := by
  apply Finset.sum_congr rfl; intro j _
  change move T x V k _ A F j i*_ = move T x V k _ A F j i*_
  by_cases hv : separation (down S j) (front A F i) ≤ span S.patch x
  · have ht := separation_triangle o (front A F i) (down S j); rw [separation_comm] at hv
    rw [b.f0_correct h j (by omega)]
  rw [AnalyticBridge.SectorAffine.no_dispatch T x A F k j i (funds_branch b.priced) hv V,zero_mul,zero_mul]
lemma m_correct (Y : LinkArray G (Frozen A x F)) (i : In x A F (G:=G)) (he : separation o (front A F i)+shiftR S x ≤ r) :
    Offset.mean T x k A F q d Y V i=meanLog A F T x V k q d Y i := by
  apply Finset.sum_congr rfl; intro j _; dsimp only [Matrix.neg_apply, Matrix.transpose_apply]
  by_cases ht : j∈panels A F i
  · have hx := panels_within F A ht; have hh := separation_triangle o (front A F i) (front A F j)
    rw [b.b_correct h Y j (by unfold shiftR at he; omega)]
  simp only [per_zero (panels A F) _ ht,neg_zero,zero_mul]

lemma relay (i : Active A x F) (he : separation o (site i)+settleR x ≤ r) :
    engaged x (amended x A V) F i.val.val :=
  have hB : 120≤radiusB x := b.geometry
  ((completion_reads h F (Classical.arbitrary S.Choices) V).enabled x (e:=i.val.val)
    (by change separation o (site i)+10*radiusB x+_ ≤ r; unfold settleR at he; omega)).mp (fresh_active ..)

end Bulletin
end YM.PhysicalNext.JointLoad.Folio
