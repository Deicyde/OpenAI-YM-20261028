import YM.TraceExtension.Shepherd.Stout
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums Extra.Multi StressFlux MeasureTheory Cells Accent Menu
open Push.GridApprox Overlay
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {G:Gauge}{C:Family G}(H:C.Makes) {b:ℝ} {J p k N:ℕ}
set_option quotPrecheck false
local notation "S"=>C.S
local notation "n!"=>C.side k p
local notation "R"=>(C.path.rep N p k)
local notation "Z"=>Wilson.partition G (C.side N p) (C.beta N p)
def goad {n:Side} (b:ℝ)(x:Site n)(U:Config G n):ℝ:= if x∈flags b U then 1 else 0
lemma furs {n:Side} (b:ℝ)(x:Site n):Envelope (goad (G:=G) b x):=⟨Measurable.ite (flags_open ..|>.measurableSet) measurable_const measurable_const,1,fun U=>by unfold goad;split<;>simp⟩
include H
lemma health (hk:k ≤ N)(hm:J ≤ k)(hb:0 < b)(hT:2*b ≤ (C.path.rep N p k).p.threshold)(hr:Push.GridApprox.room C.path.levels J k 8)(j:Site (C.side k p)) :
    (∫ U:Config G n!, ((C.path.rep N p k).eval U)*goad b j U∂prior G _)≤ Z*Real.exp (brinkP C J p k N b):=by
   let s:=goad (G:=G) (n:=n!) b 0; let f:Config G n!→ℂ:= Complex.ofReal ∘ s; let t:=C.path.rep N p k
   let F (U:Config G n!):= (t.eval U)*s U
   have hh:=H.wilson.represents N p k hk|>.good; have he:Envelope F:= (t.envelope hh).mul (furs b _)
   let A U:=pull 1 j (K:=G.El) U
   have hν:MeasurePreserving A (prior G n!) (prior G n!):= prior_pull ..
   have hμ:(∫ U,F (A U)∂prior G n!) =∫ U,F U∂prior G n!:= (integral_map hν.measurable.aemeasurable he.meas.aestronglyMeasurable).symm.trans (by rw[hν.map_eq])
   have hG(U): (t.eval U)*goad b j U=F (A U):=by
       obtain ⟨m⟩:=hh.labels.moves 1 j; have hp : t.eval (A U)=t.eval U:= Push.Local.eval_pull m U; unfold F; rw [hp]; refine congr_arg₂ (· * ·) rfl ?_
       unfold s goad A; by_cases hz: 0∈flags b (pull 1 j U)
       · rw [if_pos hz,if_pos]; rw [← Work.H03.flags_send 1 j b U]; exact mem_image.mpr ⟨0,hz,by simp [affine]⟩
       rw [if_neg hz,if_neg]; rw [← Work.H03.flags_send 1 j b U]; simpa only[mem_image] using! (show ¬ ∃ x∈flags b (pull 1 j U), affine 1 j x=j from fun he=> by obtain ⟨x,hx,h⟩:=he; rw [show x=0 from by simpa [affine] using! h] at hx;exact hz hx)
   change (∫ U,t.eval U * _∂_)≤ _; simp_rw [hG,hμ]; apply (Real.le_norm_self _).trans
   have hp:f=mama b 0:= by funext U; unfold f s mama goad; simp only[Function.comp_apply,apply_ite Complex.ofReal];split<;>simp
   let M:= tilesAt C.S p (hm.trans hk); let y:=backTo C.path N p hk f
   have hv: Interior (M.chamber 0) y:= by
      apply (backTo_local C.path N p hm hk 0 8 (F:=f) ?_).enlarges (room_fits p C.path.levels 8 hm hk hr 0)
      rw [show anchor _ _ hm 0=0 from Extra.Histories.Motion.embed_origin _,hp]
      exact mommy b
   have hx := M.planted (seamless H N p) (fun _:Unit=>0) (Function.injective_of_subsingleton _) (fun _=>y) (fun _=>hv)
   have hs : ‖moment (C.beta N p) y‖≤ Real.exp (brinkP C J p k N b):=by
       simpa [y,hp] using hx.trans (by simpa [M,y,hp] using! ritual (p:=p) H hk hm hb hT hr)
   rw [← Complex.norm_real, ← integral_complex_ofReal]; simp_rw [F,Complex.ofReal_mul]; change ‖(∫ U,(t.eval U:ℂ)*f U∂prior G n!)‖ ≤ _; rw [forfeit C.path hk H.wilson f (fromR (furs ..)),norm_mul,Complex.norm_real, Real.norm_of_nonneg (partition_pos _).le]; exact mul_le_mul_of_nonneg_left hs (partition_pos _).le
lemma soils (hk:k ≤ N)(hm:J ≤ k)(hb:0 < b)(hT:2*b ≤ (C.path.rep N p k).p.threshold)(hr:Push.GridApprox.room C.path.levels J k 8) (P:Support n!)(f:Config G n!→ℂ)(hf:Envelope f)(U V:ℝ)(hv:0≤V) (hx:∀ u,‖f u‖ ≤ V)(hp:∀ u, Healthy b P u→ ‖f u‖ ≤ U) (hd:0 ≤ U):
   ‖moment (C.beta N p) (backTo C.path N p hk f)‖≤ U+ V*P.card*Real.exp (brinkP C J p k N b):=by
   have h₀:0 < Z:= partition_pos _; apply le_of_mul_le_mul_left _ h₀; let D:= (C.path.rep N p k); let r:=D.eval
   have he:=forfeit C.path hk H.wilson f hf; have hh:= D.envelope (H.wilson.represents N p k hk|>.good); have hB(y):0≤ r y:= History.nonnegative C.path H.wilson N p k hk y
   rw [← show ‖(↑Z:ℂ)‖ = Z from (Complex.norm_real _).trans (Real.norm_of_nonneg h₀.le)]
   let c(u):=∑ j∈P,r u*goad b j u
   have hP(y) : ‖(r y:ℂ) * f y‖ ≤ r y * U+ V*c y:=by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hB y)]; have hF (i): 0 ≤ r y*goad b i y:=by unfold goad;split; simp[hB];simp
      by_cases h:Healthy b P y; exact le_trans (mul_le_mul_of_nonneg_left (hp y h) (hB y)) (le_add_of_nonneg_right (mul_nonneg hv (sum_nonneg (fun i _=> hF i))))
      obtain ⟨j,hi,hG⟩:= Finset.not_disjoint_iff.mp h; have hz:r y ≤ c y:=by
          have ht:= single_le_sum (f:= fun i=> r y*goad b i y) (fun i _=> hF i) hi; rwa [goad,if_pos hG,mul_one] at ht
      exact (mul_le_mul_of_nonneg_left (hx y) (hB y)).trans ((mul_comm (r y) V).trans_le ((mul_le_mul_of_nonneg_left hz hv).trans (le_add_of_nonneg_left (mul_nonneg (hB y) hd))))
   have hv':Envelope c:= Envelope.sum P (fun j y=>r y*goad b j y) (fun j=> hh.mul (furs b j)); rw [← norm_mul,show (↑Z:ℂ)*moment _ _=_ from he.symm,Complex.norm_real, Real.norm_of_nonneg h₀.le]
   apply le_trans (norm_integral_le_integral_norm _); apply le_trans (integral_mono ((capped (envUmul (fromR hh) hf) (prior G _)).norm) (((hh.integrable (prior G _)).mul_const U).add ((hv'.integrable (prior G _)).const_mul V)) hP); change (∫ u:Config G n!, r u*U+V*c u∂prior G _)≤_; rw [integral_add ((hh.integrable _).mul_const U) ((hv'.integrable (prior G _)).const_mul V), integral_mul_const,integral_const_mul]
   have ht:∫ U', r U' ∂prior G _=Z:= History.partition_eq C.path H.wilson N p k hk
   unfold c; rw [ht, integral_finsetSum]; swap; · exact fun i _=> (hh.mul (furs b _)).integrable _
   apply le_trans (add_le_add_right (mul_le_mul_of_nonneg_left (sum_le_sum (fun i (_:i∈P)=>health H hk hm hb hT hr i)) hv) _); simp only[sum_const,nsmul_eq_mul]; apply le_of_eq;ring
end YM.Trace.Shepherd
