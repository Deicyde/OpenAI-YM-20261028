import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Embassy
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Song
open Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset VerifiedReset.Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {I R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ} {F : Tree.Forest S.ratio}
variable (p : BudgetPoint) (H : Cash W s μ L Q o α T I) {J : Cash W s μ L Q o α T R}
    (X : Match.Alliance H J 1 0) (χ : Chi) (γ : ℝ)

variable (N : Captain J j C' d v Y A b r B q k χ) (O : Tree.Forest S.ratio) (hp : p.threshold=Pressure.temp s) (hP : p.order ≤ j)
    (hB : p.B=radiusB s) {σ C Λ : ℝ} (hx : T.down.Bounds T.low σ C Λ) (h : Cash.Renewed n a δ e J)
include h hP hp N hx
lemma creditRing (V : Config G c) : Real.exp ((Collection.frozen (posting p H) T.down T.low p (plusone H X χ γ) R.beta (weighty J χ O)).exponent V-γ*Collection.receipt T.down T.low p V)=overhead (prism T s χ o.K V O) R Q.table * J.homesteadPool χ V:= by
  let r:= (posting p H).read (plusone H X χ γ)
  have ht t := language p H X χ N hp hP γ h hx (Seat.view t V)
  have hz : ∀ t: Seat c, HasSum (fun i=> masked p.threshold (scaleT p H i).support (opus H X χ γ i) (Seat.view t V)) (-(Real.log (J.homesteadPool χ V)) + (-(γ*Collection.receipt T.down T.low p V+(R.beta*(billOf p T.down.cubic V+billOf p T.down.quartic V)+billOf p T.down.loop V)))) := by
    intro t; have hb:= ht t; rw [harmony χ h V t,Seat.view, Collection.receipt, layer_spread,
      bill_spread p _ hx.width hx.three,bill_spread p _ hx.width hx.four,bill_spread p _ hx.width hx.two] at hb; exact hb
  have hd := voices (scaleT p H) (opus H X χ γ) p V _ hz
  have hL : r.additive p V=_ := ((pennant H).hasSum_iff.mpr hd).tsum_eq
  let X':= prism T s χ o.K V O; let y:=overhead X' R Q.table; let C := J.homesteadPool χ V
  have hm : Real.exp (weighty J χ O * Fintype.card (Site c)- T.down.inChannels T.low p R.beta V - r.additive p V)*Real.exp (-γ* Collection.receipt T.down T.low p V)=y*C := by
    rw [← Real.exp_add,chan, hL, show y=_ from grants p (J:=J) χ O hp V]
    have hv : 0<C := by unfold C; rw [← (J.threshold_logPool χ V h).2]; positivity
    rw [← Real.exp_log hv,← Real.exp_add]; apply congr_arg Real.exp
    unfold C at *; ring
  rw [sub_eq_add_neg,Real.exp_add,← neg_mul]; exact hm
end YM.PhysicalNext.Repeat.Song
