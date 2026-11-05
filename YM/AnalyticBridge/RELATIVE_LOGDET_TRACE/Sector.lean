import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Corners
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Marked
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.PatchCost
import YM.Next.BOUNDARY.Coordinates
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Post
import YM.Push.CUTOFF_PROJECTORS.Equations
import YM.Push.SECTOR_MEASURE.Overlap
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Bore

/-!
# Pairing and integrating full determinant prices

Full  convention in the actual one-step identity licensed by
SectorChange; the reference is the same *cut* Aflat, paired on exactly the
physical keys. Doesn't estimate connected log of sleeves or drop them,
including affine subtraction, tags, cut contributions. No change to likelihood
or Allocation; no division by a partition function. Values assigned to
series at incompatible A.flags have no significance (they multiply 0;
use e.g. 0 directly outside flag license).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet.Export
open Filter Function Set Matrix Lattice RG Precision Wilson Pressure Tree Input MeasureTheory
open Next.SectorChange Next.Scheduling Bid Pressure.Testing RG.Supply RG.Shoot
open Push.SectorMeasure Push.SectorMeasure.Presented Next.Fluctuations.Sector
open Gaussian Physical 
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

section comparison
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {x a v C η b d : ℝ}
    {l : ℕ} {V : Config G c} {A : Stores S}

lemma no_seeds (G : Gauge) (S : StepData c f) (x) : (voidStore S).flags=RG.flags (temp x) (1:Config G c) := by
  ext i
  simp only [voidStore,Finset.notMem_empty,false_iff,RG.flags_spec]
  rintro ⟨j,-,h⟩
  have he : faceValue (1:Config G c) j=1 := by rw [← Precision.link_one]; exact YM.Push.stroll_zero ..
  rw [he,G.chord_one] at h; exact (not_lt_of_ge (Push.SectorMeasure.temp_nonneg x)) h

/-- The Fsct RHS argument is the determinant of the flat *cut* matrix. -/
lemma normal (hb : Certified S T x v C η b) (F : Forest S.ratio) (k : S.Choices) (hS : S.patch.Branches S.kernel G) :
    let Q := Rows.gram T x 1 k (shots S x) (voidStore S) F
    (Native.kinetic T F k x).PosDef ∧ Q.det=(Native.kinetic T F k x).det := by
  intro Q
  let e : Precision.Key F G ≃ Rows.In (G:=G) x (voidStore S) F := Native.lineEquiv F x
  have he : Q.submatrix e e=Native.kinetic T F k x := Native.ground_gram T F k x hS
  have ht : Q.PosDef := (hb.text (voidStore S) F k 1 (no_seeds G S x)).2.1
  rw [← he,det_submatrix_equiv_self]; exact ⟨ht.submatrix e.injective,rfl⟩

def account (T : Tube G S) (x : ℝ) (F : Forest S.ratio) (k : S.Choices) (A : Stores S) (V : Config G c) (s : ℝ) :=
  let Y:= AFull T A F x V k
  let Q:= AFull T (voidStore S) F x 1 k
  let W:= windows S x
  Real.exp (- (Fintype.card (Frozen A x F):ℝ)*Real.log s -
    (1/2)*((∑ i, (letterBase W Y i-letterBase W Q i)) +(∑' z,(page W Y z-page W Q z)))+
    (1/2)*(∑' z,errata W Y z))

lemma receipt (hp : Certified S T x v C η b) (F : Forest S.ratio) (k : S.Choices) {l} (a : ℝ) (ha : 0≤a) (s : ℝ)
    (hS : S.patch.Branches S.kernel G) (hA : A.flags=RG.flags (temp x) V)
    (h0 : parcel G S l a v C b d (radiusB x) 0) (h1 : parcel G S l a v C b d (radiusB x) 1) :
    let P := Rows.gram T x V k (shots S x) A F
    let I := (Native.kinetic T F k x).det
    let R := fog A F T x V k
    let Y:= AFull T A F x V k; let Q:= AFull T (voidStore S) F x 1 k; let W:= windows S x
    Summable (page W Y) ∧ Summable (page W Q) ∧ Summable (errata W Y) ∧
      account T x F k A V s = Real.exp (-(Fintype.card (Frozen A x F):ℝ)*Real.log s - (1/2)*(Real.log P.det-Real.log I)+
        (1/2)*Real.log (1+(P*R-1)).det) := by
  intro P I R Y Q W
  have hh B X (hz : B.flags=RG.flags (temp x) X) := (hp.writes F k (A:=B) (V:=X) hz).contributions hp.small (hp.fogs F k hz).2
    (furnished T k X hS B F hp.geometry) ha h1 h0
  obtain ⟨hy,hz,hq,hx⟩ := hh A V hA
  obtain ⟨hr,-,hu,-⟩ := hh (voidStore S) 1 (no_seeds G S x)
  refine ⟨hy,hr,hz,?_⟩
  unfold account; dsimp only
  rw [a_det] at hq hu
  rw [(hp.excessive F k hA)] at hx
  rw [(show det (Rows.gram T x 1 k (shots S x) (voidStore S) F)=I from (normal hp F k hS).2)] at hu
  unfold P R; rw [hu, hq,hx,hy.tsum_sub hr,Finset.sum_sub_distrib]; ring_nf
end comparison

section live
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y} {P : PostCost D}
    {K : MapPrices} {Z : ChartRatio G} (F : Directed G I Z K P)


end live
end YM.AnalyticBridge.RelativeLogdet.Export
