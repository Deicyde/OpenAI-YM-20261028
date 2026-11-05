import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Amass

/-!
# First integrated polymer gas on gauge-fixed sectors (value)

Full discrete coverage G. Keep exact Hastings density; scalar tree correction
and true clipped base. Cost proofs apply separately PER component, extensive
part never asserted local. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Matter
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G} {p : Molecule S} {V : Finset (Molecule S)} {b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (X : Coat T F) (H : Cash W X.x μ L Q o C T R) (hk : X.width=o.K)
include H hk

lemma trace (A : Stores S) :
    let D:= X.χ.profiles G S X.x W H.laws.data.W_pos H.laws.data.room.fiery
    HasSum (fun v : Finset ℕ×ListsAt c f=> overhead X R Q.table*receiptM R X W o.a Q.halo Q.table (crew S Q.halo X.B (A,v)))
      (cutEntry D F T R A X.V) := by
  intro D
  have hz:= hasSum_sum (s:=univ) fun (k:S.Choices) _=> incomeK X H hk A k
  have hL := H.laws.intake
  rw [← (hL.allocation H.laws.data.grant).2 F D|>.each];
  have he (v : Finset ℕ× ListsAt c f) := distributed (R:=R) (Q:=Q) (o:=o) X ⟨A,v⟩
  simp_rw [← he]; exact hz

lemma render : HasSum (fun p : Molecule S=> overhead X R Q.table*receiptM R X W o.a Q.halo Q.table p) (S.push R.beta R.eval X.V) := by
  let D:= X.χ.profiles G S X.x W H.laws.data.W_pos H.laws.data.room.fiery
  let V:= crew S Q.halo X.B
  let p s:= overhead X R Q.table * receiptM R X W o.a Q.halo Q.table s
  have hv : HasSum (p ∘ V) (∑ A, cutEntry D F T R A X.V) := Raw.finite_start _ _ fun i=> trace X H hk i
  have he : Injective V := LeftInverse.injective (show LeftInverse obtainBack V from fun x=> deposit x)
  rw [(H.laws.intake.allocation H.laws.data.grant).2 F D|>.total]
  apply (he.hasSum_iff (f:=p) ?_).1 hv
  intro i hi
  unfold p receiptM; dsimp only; rw [if_neg (fun ha=> hi ⟨_,recovery ha.2⟩),mul_zero]

/-- Actual density relative to probability Haar PRIOR on output V (not
unit-z partition). `F` common in X; still need mode B charts in dynamics.
Keep `KetFlags` one. Smoke adds progress. -/
theorem real_push : HasSum
    (fun Z : Finset (Molecule S)=> overhead X R Q.table * ejections R X W o.a Q.halo Q.table Z)
    (S.push R.beta R.eval X.V) := by
  let f Z:= overhead X R Q.table * ejections R X W o.a Q.halo Q.table Z
  let g (p : Molecule S):= Ac.Parts H.supportP p
  have hg p : f (g p)= overhead X R Q.table * receiptM R X W o.a Q.halo Q.table p := by unfold f g; rw [fromOne X H hk p]
  have he : Injective g := LeftInverse.injective (show LeftInverse (fun t=>t.biUnion id) g from fun i=> Ac.reconstruct ..)
  apply (he.hasSum_iff (f:=f) (fun i hi => ?_)).1
  · simp_rw [Function.comp_def,hg]; exact render X H hk
  unfold f ejections; rw [if_neg (fun hh=> hi ⟨i.biUnion id,separates hh.1⟩),mul_zero]

omit hk in
lemma overhead_pos : 0<overhead X R Q.table := by
  let β:=R.beta
  have hp := H.laws.intake.positive
  have h1 : 0 < measure_g Q.table β := by have hh:= Q.table_exists.scale; unfold measure_g gStep β; positivity
  have hz : 0 < prefactor S G β := by have h:= S.penaltyZ_pos (G:=G) β; unfold prefactor; positivity
  unfold overhead levy deducted; unfold β at *; unfold Raw.stone; positivity


end YM.ConnectedActivityE6.Matter
