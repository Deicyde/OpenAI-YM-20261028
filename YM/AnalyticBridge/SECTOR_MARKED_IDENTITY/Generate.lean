import YM.AnalyticBridge.SECTOR_MARKED_IDENTITY.Bands
import YM.AnalyticBridge.SECTOR_MARKED_IDENTITY.Mixed

set_option warningAsError false

/-!
# Mixed derivatives of the actual marked transfer

The density with sources (`combine` at l=`[]`) uses the project marker
algebra coefficientwise. The SAME Bought licenses all the words and derivatives
and all amplitudes in this real lift. Real derivatives commute with the actual
integrals. At zero, derivative once in each name of a permitted T (any
order) returns precisely the response of that T, no factorial. At other
amplitudes unselected sources retain their values as per `rest`. In
the general result `g`, the coefficients can already include physical
spectators. They needn't have the `Bands` presentation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Marked.SourceJet
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix
open Gaussian Rows YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid
open YM.Push.SectorMeasure Overlay Marker
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {x w : ℝ}
    {I X : Type*} [DecidableEq I] {B : Census I} [NormedAddCommGroup X] [NormedSpace ℝ X]

def combine (g : B.Mode → Config G f → X) (l : List I) (t : I → ℝ) (U : Config G f) := read (fun i => g i U) l t



variable {R : Rep G f} {T : Tube G S} {F : Forest S.ratio} {D : Allocation G S x w}
  {q : Chi} {J : ChartRatio G} {d : ℝ}





variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompleteSpace X]
variable (L : Bought T x R F D q J d) (g : B.Mode → Config G f → X) (he : ∀ i, Envelope (g i))

omit L [CompleteSpace X] in
include he in
lemma gains (l : List I) (t : I → ℝ) : Envelope (combine g l t) :=
  Env.total _ (g:=fun (p : B.Mode) U => rest l p t • g p U) fun p => Env.scale (Envelope.const _) (he p)

include L he





/-- Equality of actual amplitude derivatives of the push. We retain `ink`
for termwise estimation after taking the mixed derivatives. -/
theorem push_with (hi : ∀ i, GaugeInvariant (g i)) (l : List I) (t : I → ℝ) (V) :
    let u := combine g l t
    mixed (fun s => S.push R.beta (combine g [] s) V) l t = S.push R.beta u V ∧
    S.push R.beta u V = paidSum T x R F D q J d u V ∧
    ∀ (A : Stores S) (k : S.Choices), Permission T x V k A R (shots S x) F D q J d
      (fog A F T x V k) (meanLog A F T x V k q d) u := by
  have hh (l : List I) (t : I → ℝ) : GaugeInvariant (combine g l t) := by
    intro y U; unfold combine; simp_rw [hi _ y U]
  have hf (l t) : S.push R.beta (combine g l t) V = read (fun i => S.push R.beta (g i) V) l t := by
    let p i (U : Config G f) := S.density R.beta U V • g i U
    unfold StepData.push; simp_rw [combine, smul_read]
    exact (integral_read _ l p _ (fun i => StepData.push_slice (S.isKernel L.branches _) V (g i)
      (Env.integrableX (he i) _))).2
  intro u
  refine ⟨?_,congrFun (L.apply_push (gains g he l t) (hh l t)) V,fun A k => L.fixedTerm (gains g he l t) A k V⟩
  unfold u; simp_rw [hf]; exact congrFun (mixed_lift l _) _

omit he in
/-- In particular for the E square-zero density with its common genuine gas
packets. -/
theorem decides [Fintype I] {U : Bands B R} (ha : U.Active)
    {r : I → ℝ} {a b c' d' : ℝ} (hr : U.Radial r a b c' d')
    (i : B.Mode) (l : List I) (hn : l.Nodup) (hp : l.toFinset=i.val) (V) :
    mixed (fun s => S.push R.beta (combine (mark U) [] s) V) l 0 = paidSum T x R F D q J d (mark U i) V := by
  obtain ⟨σ,n,Λ,δ,v,h⟩ := L.lawful
  let g := mark U
  obtain ⟨hu,hv,_⟩ := push_with L g (mark_envelope h L.beta.le ha hr) (mark_gauge h ha) l 0 V
  rw [hu, hv, show combine g l 0=mark U i from ?_]
  funext U'; unfold combine
  rw [← mixed_lift]; exact names _ _ hn hp _

end YM.Next.SectorChange.Marked.SourceJet
