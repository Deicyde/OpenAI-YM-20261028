import YM.FullVolume.Regent.Boneyard
/-! read path jet at actual U. One function.Log.No continuity on V assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Beacon
open Lattice RG Precision Wilson Filter Function Laurent Bloch Exterior Next.Free.Retort Tralis Shade Flagship
open WilsonStartup.Change WilsonStartup.Change.Reading
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{n:Side}{t:ℕ}[NeZero t]{X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]
private lemma sumV {ι:Type}(S:Finset ι){Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y]{a:ι→ℕ→ X→Y}{A:ι→X→Y}(hv:∀ i,View (a i) (A i) 0 0): View (fun i x=> ∑ j∈ S, a j i x) (fun x=>∑ j∈S,A j x) 0 0:=by
    induction S using Finset.induction_on with
    | empty=>simp only [Finset.sum_empty]; exact View.checked contDiffAt_const tendsto_const_nhds
    | insert i S he ih=> simp_rw [Finset.sum_insert he]; exact (hv i).plus ih
lemma arena {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]{R:ℕ→PathData G}{P}{w A}(h:Drive R P w A) (U:X→Config G n)(hu:∀ i,ContDiffAt ℝ ω (fun x=> G.mat (U x i)) 0)(p:Clip): View (fun i x=>secondTerm p (R i) (U x)) (fun x=> secondTerm p P (U x)) 0 0:=by
    refine View.coin (c:=(Fintype.card Signed:ℝ)⁻¹) (sumV Finset.univ (a:=fun s i x=> quadratic p (R i) (pull s 0 (U x))) (A:=fun s x=>quadratic p P (pull s 0 (U x))) fun s=>?_)
    let Z x:= pull s 0 (U x); have hX b : ContDiffAt ℝ ω (fun x=> G.mat (Z x b)) 0:=by
         unfold Z pull Step.read; split
         · exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (hu _)
         exact hu _
    let g (f:Face (Per n)) x := p.direct* G.price (faceValue (Z x) f)
    let f (P:PathData G) b x:= g b x + ‖P.ell (Z x) b‖^2/2
    refine sumV Finset.univ (a:=fun b i x=>f (R i) b x) (A:=fun b x=> f P b x) fun b=>?_
    have hs :ContDiffAt ℝ ω (g b) 0:= by
         refine contDiffAt_const.mul (Work.F03.price_smooth ?_)
         simp_rw [faceValue, ← Work.F02.stringMat_physical]; exact ((Work.F02.stringMat_contDiff (G:=G) _ _).restrict_scalars ℝ).contDiffAt.comp _ (Work.F02.physical_contDiffAt hX)
    let K (x:G.Color):=‖x‖^2/2; have hK :ContDiff ℝ ω K:= (contDiff_norm_sq ℝ).div_const _
    exact (View.checked (x:=0) hs tendsto_const_nhds).plus ((h.summons b Z hX).compose hK.contDiffAt)
lemma frame_port {x:ℕ→ Cameo G t}{C:Cameo G t}{b:ℝ}{σ}(h:0<σ)(hv:Gleam x C b): View (fun i=>turnSeries (ringT σ (x i)) (m:=n)) (turnSeries (ringT σ C)) 0 0 := ⟨Eventually.of_forall fun i=> (shineN h|>.contDiffAt),shineN h|>.contDiffAt,fun _=>starry h hv⟩
-- unwrap chart at any analytic input
lemma reverse_run (U:X→Config G n)(he:U 0=1)(hv:∀ i,ContDiffAt ℝ ω (fun x=>G.mat (U x i)) 0) : ∃ x:X→ Link G n,x 0=0∧ ContDiffAt ℝ ω x 0∧ (input G n ∘ x)=ᶠ[𝓝 0] U:=by
   let F (v:X): Bid.Dir G n:=fun i=> G.plog (G.mat (U v (i.1,axisEquiv.symm i.2)))
   let g:= (arm G n 1).symm ∘ F; have hf : F 0=0 :=by ext1 i; simp [F,he]
   have hh :represent∘ F =ᶠ[𝓝 0] U:=by
     have ht (i):Tendsto (fun v=> U v i) (𝓝 0) (𝓝 1):=by
         have hx:ContinuousAt (fun v=> U v i) 0:=(G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuousAt_iff.mpr (hv i).continuousAt
         simpa only [he,Pi.one_apply] using hx.tendsto
     filter_upwards [eventually_all.mpr (fun i=>(ht i).eventually G.plog_right)] with v hv
     ext1 i; simpa only [comp_apply,F,represent,increment,collect,show axisEquiv.symm (coord i.2)=i.2 from axisEquiv.symm_apply_apply _, Pi.one_apply,mul_one] using! hv i
   refine ⟨g,by simp [g,hf],?_,hh.mono fun v h=>?_⟩
   · refine (arm G n 1).symm.contDiff.contDiffAt.comp _ (contDiffAt_pi.mpr fun i=>?_)
     exact (ContDiffAt.comp (f:=fun v=> G.mat (U v (i.1,axisEquiv.symm i.2))) 0 (show ContDiffAt ℝ ω G.plog (G.mat (U 0 (i.1,axisEquiv.symm i.2))) by rw [he]; exact G.plog_diff) (hv _))
   simpa only [g,comp_apply,input,ContinuousLinearEquiv.apply_symm_apply] using h

structure Calm (V:Reel G)(S:ℕ→PathData G)(Q: PathData G)(p:Clip)(w a c:ℝ):Prop where
    retained:∀ᶠ i in atTop,(S i).Bounds p w a c
    hearth:Drive S Q w a
    wide: V.Price w
    stars:∃ (x:ℕ→Flagship G)(F:Flagship G) (A B:ℝ), Flagship.Beacon x F A B ∧ Lash V F Q ∧ ∀ᶠ i in atTop,Lash V (x i) (S i)
namespace Calm
variable {V:Reel G}{S Q}{p:Clip}{w a c:ℝ}
lemma guides (h:Calm V S Q p w a c): Q.Bounds p w a c:=by
    obtain ⟨x,F,D,L,hp,hS,hQ⟩:=h.stars; exact Flagship.proved h.hearth hp h.wide hS (hQ.and h.retained)
lemma harvest (h:Calm V S Q p w a c): View (fun i=> intended p (S i) (m:=n)) (intended p Q) 0 0 ∧ View (fun i=> turnSeries (S i).loop (m:=n)) (turnSeries Q.loop) 0 0:=by
    obtain ⟨x,F,D,L,hp,hS,hQ⟩:=h.stars
    have hx : View (fun i=> inputSeries p (S i) (m:=n)) (inputSeries p Q) 0 0:= arena h.hearth (input G n) (fun i=> ((Work.F03.represent_smooth i).comp (arm G n 1).contDiff).contDiffAt) p
    constructor
    · refine ((hx.plus (frame_port V.e3.hired hp.b)).plus (frame_port V.e4.hired hp.c)).ferry ?_ ?_
      · rw [intent,hS.2.1,hS.2.2]
      refine hQ.mono fun i hi=>?_ ; rw [intent,hi.2.1,hi.2.2]
    refine (frame_port V.e2.hired hp.a).ferry (?_) (hQ.mono fun i hi=> by rw [hi.1]); rw [hS.1]
end Calm
end YM.Stationary.Beacon
