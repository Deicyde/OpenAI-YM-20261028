import YM.FullVolume.Fields.Cloak
import YM.FullVolume.Fields.Shave
/-! Transpose inflation experiment down *real* Mark steps. gives height-uniform estimate of influence, without cost loss exp(volume(k)), no representations convergence for the mixed pins. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Sever
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Overlay
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi MergeProof MergeProof.Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
lemma touch (f:ℂ→ℂ)(B S:ℝ)(hf:2<S)(h:DifferentiableOn ℂ f (Metric.ball 0 S))(hp:∀ z∈Metric.ball 0 S, ‖f z‖≤ B): ‖f 1-f 0‖ ≤ B/(S/2):=by
    let t:=S/2; let M:= Metric.closedBall (0:ℂ) 1; have ht:0 < t:=by unfold t; linarith
    have hu(z:ℂ)(hz:z∈M):Metric.closedBall z t ⊆ Metric.ball 0 S:=by
       intro x hx; have h₁:= Metric.mem_closedBall.mp hz;have h₂:= Metric.mem_closedBall.mp hx; unfold M t at *; rw [Metric.mem_ball]; linarith only [hf,h₁,h₂,dist_triangle x z 0]
    have hv M' (hM:M'∈ M) := hu M' hM (Metric.mem_closedBall_self ht.le)
    have hD(z:ℂ)(hz:z∈ M): ‖deriv f z‖≤ B/t:=by
       refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le ht ⟨h.mono ((Metric.ball_subset_closedBall).trans (hu _ hz)),h.continuousOn.mono (Metric.closure_ball_subset_closedBall.trans (hu _ hz))⟩ (fun z' hz'=> hp z' (hu z hz (Metric.sphere_subset_closedBall hz')))
    simpa using! (Convex.norm_image_sub_le_of_norm_deriv_le (𝕜:=ℂ) (fun z (hz:z∈ M)=> (h z (hv _ hz)).differentiableAt (Metric.isOpen_ball.mem_nhds (hv _ hz))) hD (convex_closedBall 0 1) (x:=(0:ℂ)) (y:=1) (Metric.mem_closedBall_self zero_le_one) (by simp [M,Metric.mem_closedBall]))

variable {V:Type}[DecidableEq V][Fintype V] {B:Census V} {G:Gauge}{n:Side}
variable (A:RG.History G)(N p:ℕ) (h:A.Selected)
def stamp (m:ℕ)(P:Config G (A.S.side m p)→ Poly B)(i:B.Mode) := (∫ U,(P U).part i∂prior G _)/(Wilson.partition G (A.S.side N p) (A.β N p N):ℂ)
local notation "R"=> A.rep N p
local notation "S"=> A.levels
local notation "P"=> A.levels.budget
set_option quotPrecheck false
-- allowed root x,y real not nonnegative for arity zero; cost still positive

def refreeze (A: Levels G)(p k:ℕ)(x y:ℝ)(t:B.Mode)(s:V→ℝ):ℝ:= Real.exp (Fintype.card (Site (A.S.side k p))*Vac.treasury A k+Fintype.card V*(x+y+2*1)) / Poly.toll s t
section root
include h in
lemma charges {k:ℕ} {k₁: V→ Config G (A.S.side k p)→ℂ}{k₂:V→Box (A.S.side k p)→ Config G (A.S.side k p)→ℂ}{X:Config G (A.S.side k p)→ Poly B}{o:V→Site (A.S.side k p)} {x y:ℝ}{w:V→ℝ}(hk:k≤N) (hs:∀ i,0<w i)
          (hp:Served (A.rep N p k) k₁ k₂ X o w (A.levels.budget k).supportExponent 1)(he:Vault w k₁ k₂ x y)(hx:Integrable X (prior G _))(t:B.Mode): ‖stamp A N p k X t‖ ≤ refreeze (A.levels) p k x y t w:=by
    let Q:= A.levels.clock; have hv:= h.represents N p k hk; have hq:0<Q.hatCoupling k:= inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (A.levels.fits.delayed k)))
    have hf: Q.hatCoupling k ≤ (R k).p.threshold:=by rw [hv.vac]; exact le_mul_of_one_le_right hq.le (Real.one_le_exp (sq_nonneg _))
    have hg:= (sail hs hp hv.good (Overlay.beta_positive h hk).le he (A.levels.budget k|>.exponent_pos.le) t hx _ hq hf (History.nonnegative A h N p k hk)).trans (Real.exp_monotone (Vac.suffices_bill h hk (Fintype.card V) ..))
    unfold stamp refreeze; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (partition_pos _).le]; rw [History.partition_eq A h N p k hk,mul_one] at hg; exact (le_div_iff₀ (Poly.worth hs _)).mpr hg
end root
section before
variable {o:∀ i,V→ Site (A.S.side i p)}{w: ℕ→ V →ℝ} {X:∀ i,V→ Config G (A.S.side i p)→ℂ}{g:∀ i,V→ℕ→ Config G (A.S.side i p)→ℂ}
variable {D:∀ N p m,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}{δ u:ℕ→ℝ}{r:ℕ→ℕ} {j k:ℕ}
local notation "M₀"=> tapes A p N g
variable (hN:j≤ N)(T:Retain A r δ u D N p k)(W:∀ i:V,Wakes A k j N p (fun m=>o m i) (fun m=>w m i) (fun m=> X m i) (fun m=>g m i) D hN)
variable (ht:k<j)(hq:Matchup A r δ p j k o w B) (hy:Drake B (A.levels.budget j).B (o j))(hf:8 ≤ (A.levels.budget j).B)(hw:2 < brisk (A.levels.budget j).B)(hx:0 ≤ (A.levels.budget j).supportExponent-2)
   (he:∀ i,Measurable (X j i))(hp:∀ i p',Measurable (tapes A p N g j i p')) {s s' x y:ℝ}
   (hJ: Vault (w j) (X j) (tapes A p N g j) s s') (hs : Vault (w k) (X k) (tapes A p N g k) x y)
   {U:Config G (A.S.side j p)→ Poly B} (hx':Served (A.rep N p j) (X j) (tapes A p N g j) U (o j) (w j) (A.levels.budget j).supportExponent 1)
local notation "P'"=> restore (A.rep N p j) (X j) (M₀ j)
include h hN T W ht hq hy hf hw hx he hp hJ hs hx'
lemma omissions (i:B.Mode): ‖stamp A N p j U i-stamp A N p j (P' 0 0) i‖≤ refreeze A.levels p k x y i (w k)/(brisk (A.levels.budget j).B/2):=by
    let S':=A.levels; let R':= A.rep N p j; have hZ:=h.represents N p j hN
    have hR : R'.p=A.levels.budget j:=hZ.vac
    obtain ⟨P₀,P₁,H,H₀,H₁,hP⟩:=hx'; let f(z:ℂ):= restore R' (X j) (M₀ j) (z • P₀) (z • P₁); let R_:=brisk R'.p.B
    let k₀:= (P j).supportExponent; let b:= refreeze A.levels p k x y i (w k); have hi:= hq.pos j ht.le le_rfl
    obtain ⟨hx₀,hx₁⟩:= paidB he hp hZ.good (hR.symm ▸ hf) (hR.symm ▸ hy) H H₀ H₁ hJ hi (Overlay.beta_positive h hN).le hx i -- order
    let Y(z:ℂ):= stamp A N p j (f z) i; have hM : DifferentiableOn ℂ Y (Metric.ball 0 R_):= hx₁.div_const _; have hδ (z:ℂ)(hz:z∈Metric.ball (0:ℂ) R_): ‖Y z‖ ≤ b:=by
        let v:= f z; have hM:v=f z:=rfl; have hV:Integrable v (prior G _):= hx₀ z hz
        let X':= gust A N p j v k ht.le; have hZ : Served (R k) (X k) (M₀ k) X' (o k) (w k) (P k).supportExponent 1:=by
           have hc : Served (A.rep N p j) (X j) (M₀ j) v (o j) (w j) (k₀-2) 1:= garnish _ _ _ (hR.symm ▸ hf) H H₀ H₁ hi (hR.symm ▸ hy) z (by simpa using hz : ‖z‖<_).le
           have hh:= Retain.waft A r δ u D N p hN o w X g h hq T W hc hV k le_rfl ht.le
           rwa [if_neg ht.ne] at hh
        have he := gust_sum A N p j v hV (k:=k) ht.le -- variable k not m
        let L:= (Poly.get i).restrictScalars ℝ; let X₁' U:= (X' U).part i
        have ha:= gust_live A N p j v hV (k:=k) ht.le
        have hf:(∫ U,X₁' U∂prior G _)= (∫ U,(v U).part i∂prior G _):= (L.integral_comp_comm ha)|>.trans ((congr_arg L he).trans (L.integral_comp_comm hV).symm) -- method orientation check.
        apply le_trans _ (charges A N p h (ht.le.trans hN) (hq.pos k le_rfl ht.le) hZ hs ha i); change ‖stamp A N p j v i‖ ≤ ‖stamp A N p k X' i‖; unfold stamp; rw [← hf]
    have he: U=f 1:=by rw [hP]; unfold f; rw [one_smul,one_smul]
    have hg:P' 0 0=f 0:=by unfold f; rw [zero_smul,zero_smul]
    rw [he,hg]; exact hR ▸ touch Y b R_ (by unfold R_; rwa [hR]) hM hδ -- proof type hack
end before
end YM.FullVolume.Sever
#print axioms YM.FullVolume.Sever.omissions
