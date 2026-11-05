import YM.TraceExtension.Shepherd.Folly
import YM.SectorNext.VACUUM_NORMALIZATION.Covered
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums Extra.Multi StressFlux MeasureTheory Cells Accent Menu
open Push.GridApprox
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {G:Gauge}{n:Side}(R:Rep G n) (U:Config G n)(t:ℝ)
local notation "Y"=>R.path
local notation "Z"=>R.p
local notation "p"=>R.p.threshold
local notation "K"=>R.clip
local notation "a"=>R.beta
-- per flag τ and clipping
lemma valour (ht:0<t) (hv:2*t≤R.p.threshold) : R.clip.linear /5*t^2*(flags t U).card ≤ ∑ i:Face (Per n), R.path.baseTerm R.clip R.p U i:=by
    let F:=(flags t U); let q:= Next.Rank.Alarm.sceneAt (G:=G) (n:=n) K p t; have he: ∑ i∈flags t U,q i U= Next.Rank.Alarm.Shift K p t U:=Next.Rank.Alarm.scenes _ U (by linarith : t ≤ p)
    have hm :  R.clip.linear/5*t^2*F.card ≤∑ i∈ F,q i U:=by
       refine le_trans ?_ (sum_le_sum (f:=fun _=>R.clip.linear/5*t^2) fun i hi=> Next.Rank.Alarm.scene_pay K ht hv U i hi); exact le_of_eq (by simp; ring)
    rw [show F=flags t U from rfl,he] at hm; refine hm.trans (sum_le_sum (fun i _=> ?_)); unfold PathData.baseTerm Next.Rank.Alarm.Delta; split_ifs with h
    · apply (sub_le_self _ ?_).trans (le_add_of_nonneg_right (by positivity)); unfold PathData.clipped; have he:=G.chord_nonneg (faceValue U i); have hu:=R.clip.quadratic_pos; have h':= R.clip.tail_pos; split_ifs<;>positivity
    rw [add_zero]; unfold PathData.clipped; have he:=G.chord_nonneg (faceValue U i); have hu:=R.clip.quadratic_pos; have h':= R.clip.tail_pos; apply sub_le_self; split_ifs<;>positivity
lemma ardor (ht:0<t) (hv:2*t≤R.p.threshold) (hs: 0≤R.beta){σ A Λ δ w:ℝ} (h:R.Lawful σ A Λ δ w): R.exponent U ≤ R.scalar+ Fintype.card (Site n)*R.exCost A Λ δ - R.beta*(R.clip.linear / 5*t^2*(flags t U).card):=by
   let x:=Fintype.card (Site n); let f(V:Config G n):=R.path.principal K Z R.beta V
   let L:=PathData.loopsPrice Z a A Λ; let b:= R.beta*(R.clip.linear/5*t^2*(flags t U).card)-x*L
   have he(s: Signed): b≤R.path.principal K Z a (pull s 0 U):=by
      let V:=pull s 0 U; have hp : (flags t V).card=(flags t U).card:=by rw [← Work.H03.flags_send s (0:Site n) t U]; exact (card_image_of_injective _ (Push.Local.turnSites s 0|>.injective)).symm
      have hi:= valour R V t ht hv; rw [hp] at hi; let q:=Y; have hx:= (abs_le.mp (q.volume_price K Z a hs V h.paths)).1
      unfold b; linarith only [hx,mul_le_mul_of_nonneg_left hi hs]
   have hh : b≤ R.path.inChannels K Z a U:= by
      have hm:= sum_le_sum (f:=fun _ : Signed=> b) (fun i (_:i∈univ)=> he i); exact (le_trans (le_of_eq (b:=factor * ∑ i:Signed,b) (by simp only[sum_const, card_univ,nsmul_eq_mul,← mul_assoc,factor_card,one_mul])) (mul_le_mul_of_nonneg_left hm factor_pos.le))
   have hy := (abs_le.mp (volumeE _ h.labels U)).1
   unfold Rep.exponent Rep.scalar Rep.exCost; unfold b at hh; linarith only [hh,hy]
lemma flourishX {σ A Λ δ w:ℝ}(h:R.Lawful σ A Λ δ w) (hw: w ≤ 1) (hv:0 ≤ R.beta)(k:ℕ) (hs:k ≤ (flags t U).card)(ht:0<t) (hT:2*t≤p): ‖R.eval U‖ ≤ Real.exp (R.scalar + Fintype.card (Site n)*R.exCost A Λ δ - R.beta*(R.clip.linear / 5*t^2*k)):=by
    unfold Rep.eval; rw[norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]; apply (mul_le_of_le_one_right (Real.exp_pos _).le (SectorNext.Vacuum.gas_le_one R.activities hw h.labels U)).trans
    have he:=R.clip.tail_pos; refine Real.exp_monotone ((ardor R U t ht hT hv h).trans ?_); gcongr
end YM.Trace.Shepherd
