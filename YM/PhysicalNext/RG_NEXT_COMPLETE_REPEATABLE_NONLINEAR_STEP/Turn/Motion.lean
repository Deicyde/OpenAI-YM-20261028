import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Whistle

/-! # Finish scalar angular invoices for E6. Keep Gaussian even on moves. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Turn
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Precision Tree MeasureTheory Matrix
open AnalyticBridge.GaussianFieldAlignment Locations Channels Orthogonal Tensor
open ConnectedActivityE6 Shell Coat SliceRows Pulse Itinerary Control Window
open Next.Fluctuations Next.SectorChange Push.SectorMeasure Push.AbsoluteSums Oriented
open OrderedAffine2B.SymWhole
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {s : Signed} {b : Site c}

def rotationFuel (s : Signed) (b : Site c) (S : StepData c f) : Equiv.Perm (ChainIndex f) := Equiv.sumCongr
    (portage s b S _) (Equiv.sumCongr (portage s b S _) (Equiv.sumCongr (portage s b S _) (Equiv.sumCongr (diagram s b S) (portage s b S _))))

namespace Tuned
variable {F : Forest S.ratio} {P : Teller G} {T : Tube G S} {X : Coat T F} {Y : Coat T (Locations.forest s b F)}
    (h : Tuned s b X Y) (hp : P.Funds S T) {W C : ℝ} (ht : ShellAccess S G X.x W X.width C)
include h hp ht
lemma hatted_eq (β : ℝ) : Y.hatted β=Rev s b X.V S (X.hatted β) := by
  unfold Coat.hatted; rw [h.toParked.coherent hp, h.means hp ht,h.line hp ht,warp_mv]; rw [smulRev,sumRev]

omit hp ht in
lemma cone_eq (a : ℝ) (x : Directions G f) (i : Bond f) : Y.cone a (wheels (S:=S) s b X.V x) i=X.cone a x (diagram s b S i) := by
  unfold cone; rw [h.χ,h.toParked.aligned.1]; unfold wheels; rw [lifting_apply,(fiber s b X.V S i).norm_map]

lemma wide_eq (a β : ℝ) (z : Air f G) (i : Bond f) :
    Y.aperture β (exhale s b X.V S z) a i=X.aperture β z a (diagram s b S i) := by
  unfold aperture; rw [h.axle hp ht, h.cone_eq, if_congr (h.toParked.eligible i) rfl rfl]

lemma deposited (a β : ℝ) (z : Air f G) (i : Bond f) : Y.qfirst β (exhale s b X.V S z) a i=X.qfirst β z a (diagram s b S i) := by
  unfold qfirst; rw [h.wide_eq hp ht]; apply congr_arg
  unfold qlinear; simp_rw [h.hatted_eq hp ht]
  exact OrderedAffine2B.SymRows.Test.single_pair (fiber s b X.V S) (diagram s b S) (WithLp.ofLp z) _ _

lemma rolled (a β : ℝ) (z : Air f G) (i : Ledger f 2) :
    Y.chain β (exhale s b X.V S z) a i=X.chain β z a (portage s b S 2 i) := by
  let O:=fiber s b X.V S; let f₀:=diagram s b S; let R:= asMatrix O
  rcases i with ⟨n,j,p⟩; unfold Coat.chain; rw [h.wide_eq hp ht,h.wide_eq hp ht]
  change X.aperture β z a (f₀ j) * X.aperture β z a (f₀ (arrive j p))*_ = X.aperture β z a (f₀ j) * X.aperture β z a (arrive (f₀ j) (sequence f₀ (n+2) p))*X.qunique z ⟨n,f₀ j,sequence f₀ (n+2) p⟩
  rw [proceed]
  apply congr_arg; unfold qunique circle; dsimp only; apply congr_arg
  let k:=arrive j p; let g (v : Air f G) (i : Bond f) := fun x:G.ColorIndex=> v (i,x); let w:=exhale s b X.V S z
  have he (i : Bond _) : g w i= R i *ᵥ g z (f₀ i) := by
    unfold R; rw [show g z _= (tape (G:=G) (WithLp.ofLp z) (f₀ i)).ofLp from rfl,asMatrix_apply,← move_tape O f₀]; rfl
  rw [proceed]
  change dotProduct (g w j) (combo j p (Y.finale n)*ᵥ g w k)= dotProduct (g z (f₀ j)) (combo (f₀ j) (sequence f₀ _ p) (X.finale n) *ᵥ g z _)
  let M := combo (f₀ j) (sequence f₀ _ p) (X.finale n)
  have hh : combo j p (Y.finale n)=R j*M*(R k)ᵀ := thrust O f₀ _ _ _ (fun i _=> by
    unfold finale; split
    next hh => rw [h.toParked.shuts hp]; exact (spray_neg ..).symm
    next hh => exact h.toParked.coherent hp) j
  rw [he,he,hh]; rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (R j * M), matrix_orth,Matrix.mul_one,← Matrix.mulVec_mulVec]
  rw [dotProduct_comm (R j *ᵥ _), Matrix.dotProduct_mulVec,← Matrix.transpose_transpose (R j), Matrix.vecMul_transpose,transpose_transpose,mulVec_mulVec,matrix_orth,Matrix.one_mulVec,dotProduct_comm]

omit hp ht in
lemma unspent : Parked s b X.blank Y.blank := by
  refine ⟨?_,h.x,?_⟩
  · simp [Coat.blank,Locations.book]
  change 1=pull s b (1:Config G c); funext i; rw [read_back]; split <;> simp
variable {η q r Q A : ℝ} {L : Side} (hx : Port P L η r Q A X) (hy : Port P L η r Q A Y)
include hx hy
omit ht in
lemma condensate (i : Bond f) : Y.condensation i=X.condensation (diagram s b S i) := by unfold condensation; rw [show Batch.joint Y.blank.plate Y.shutter i = _ from h.unspent.transported_j hp hx.empty hy.empty i, h.toParked.transported_j hp hx.sails hy.sails]; rfl

lemma hired (a β : ℝ) (z : Air f G) (i : ChainIndex f) : Y.fuel a β (exhale s b X.V S z) i=X.fuel a β z (rotationFuel s b S i) := by
  rcases i with i|i|i|i|i <;> simp only [Coat.fuel,rotationFuel,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,Sum.elim]
  · rw [h.toParked.transported_A hp hx.sails hy.sails]
  · exact congr_arg (fun x=>x/2) (h.unspent.transported_A hp hx.empty hy.empty i)
  · exact congr_arg (fun x=>x/2) (h.toParked.transported_S hp i)
  · exact h.deposited hp ht a β z i
  exact h.rolled hp ht a β z i

omit hp ht hx hy in
lemma gentry_eq (a : ℝ) (x : Directions G f) (i : Bond f) {Ñ : ChartRatio G} (hÑ : LocalRatio Ñ) (hv : 0<a*X.t) (hr : 4*a*X.t<Ñ.radius) :
    Y.gentry Ñ a (wheels (S:=S) s b X.V x) i=X.gentry Ñ a x (diagram s b S i) := by
  unfold gentry; rw [h.cone_eq]; by_cases hp : X.cone (2*a) x (diagram s b S i)=0
  · rw [hp,zero_mul,zero_mul]
  apply congr_arg; apply congr_arg
  unfold wheels; rw [lifting_apply]; unfold fiber scatter; split
  next hs =>
    let v:= (replica S.ratio X.V (diagram s b S i))⁻¹
    have hj : x (diagram s b S i) ∈ Metric.ball (0:G.Color) Ñ.radius := by
      have ht := X.amount (a:=2*a) (by linarith only [hv]) x _ hp
      apply Metric.mem_ball.mpr; rw [dist_zero_right]; nlinarith only [ht,hr]
    have he : G.adjoint v (x (diagram s b S i))∈ Metric.ball (0:G.Color) Ñ.radius := Metric.mem_ball.mpr (by rw [dist_zero_right,G.norm_adjoint,← dist_zero_right]; exact Metric.mem_ball.mp hj)
    change Ñ.J (-G.adjoint v _)=_
    rw [← ratio_even hÑ he]; exact Hues.keyship hÑ _ _ hj
  rfl
end Tuned
end YM.PhysicalNext.Repeat.Turn
