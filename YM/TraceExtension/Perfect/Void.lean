import YM.TraceExtension.Perfect.Honey
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}(p:Clip)
def lone (f:Side): Ratio f f:= ⟨1,by simp⟩
def arid (f : Side): Forest (lone f):= Classical.choice (Tree.select _ (by exact ⟨0,rfl⟩))
lemma arid_no(x:Edge (Site f)) : x∉ (arid f).trunks :=by
 intro h; obtain ⟨v,hv,h⟩:= ((arid f).trunk_mem_iff x).mp h
 haveI : Subsingleton (Site 1) := inferInstanceAs (Subsingleton (Four (ZMod 1)))
 have hr:(lone f).residue v=0:=Subsingleton.elim (α:=Site 1) ..
 exact hv (((lone f).root_id v).mpr hr)
private def dustV (x:Lines G f 1) : Push.Uniform.Joint (arid f) G:= Sum.inr ((⟨edgeOf (x.1,x.2.1),arid_no _⟩:(arid f).Free),x.2.2)
private lemma dustW (x:Lines G f 1): address (arid f) G (dustV x)=x.1:=rfl
private def pru (u:Edge (Site f))(i:G.ColorIndex):Lines G f 1 := (u.1,coord u.2,i)
private lemma duet_b (v: Key (arid f) G):dustV (pru v.1.val v.2)= Sum.inr v:=by
 unfold dustV pru; congr 2; apply Subtype.ext; exact Prod.ext rfl (axisEquiv.symm_apply_apply _)
private lemma duet_c(x:Lines G f 1): pru (edgeOf (x.1,x.2.1)) x.2.2=x:=Prod.ext rfl (Prod.ext (axisEquiv.apply_symm_apply _) rfl)
private lemma dustI : Injective (dustV (G:=G) (f:=f)):=by
 intro x y h; unfold dustV at h
 have hv:= Sum.inr_injective h; have hx:= congr_arg (fun i: Key (arid f) G=>pru i.1.val i.2) hv; exact ((duet_c _).symm.trans hx).trans (duet_c _)

private def mom (G:Gauge)(f:Side): Link G f→L[ℝ] Push.Uniform.Positions (Push.Uniform.Joint (arid f) G):= ContinuousLinearMap.pi fun i=> Sum.elim 0 (fun v=>ContinuousLinearMap.proj (pru v.1.val v.2)) i
private lemma bolt_mom (i:Lines G f 1): mom G f (bolt i)=bolt (dustV i):=by
 ext1 j; cases j with
 | inl j=> simp [mom,dustV, bolt]
 | inr j=>
   rw [mom,ContinuousLinearMap.pi_apply]; change bolt i (pru (j.1.val) j.2) =_
   simp only [bolt,Pi.single_apply]; rw [← duet_b j, dustI.eq_iff]
private lemma mom_pays (x:Link G f): input G f x = Push.Uniform.fine G (arid f) (mom G f x):=by
 let P:=paint (arid f) G (mom G f x)
 have h: P.1=0:=by funext u; ext1 i; exact rfl
 have hs:Push.Uniform.outer G (arid f) (mom G f x)=1:=by unfold outer; rw[h,link_one]
 ext1 b; rw[input_color, fine,lifting]
 have ht(a): edgeColor x a=P.2 (⟨a,arid_no _⟩:(arid f).Free):=by
    ext k; exact rfl
 rw [show ((arid f).drape _ b)=_ from (arid f).off_tree (fun i=>G.lieExp (_) * replica _ _ _) ⟨b,arid_no b⟩]; rw [← ht]; rw [hs,replica_one]; simp

lemma lone_spread (G:Gauge)(μ C:ℝ)(h:0<μ)(k:ℕ): ∃ a A:ℝ,0<a∧ 0≤A∧∀ (R:PathData G)(Λ:ℝ), R.Bounds p μ C Λ→ ∀ f:Side, ContDiffAt ℝ ω (intended (m:=f) p R) 0 ∧ Scatter Prod.fst a k (intended (m:=f) p R) 0 A:=by
 obtain ⟨Z,H⟩:= paint_supply G k
 obtain ⟨Z',V⟩:= square_pay G k Z μ C
 let s:=entryWidth k (1:Side) μ; let a:= weaker k s; let A:= mainCost G k Z Z' μ C p 1
 have hs:0<s:=width_positive h k 1
 refine ⟨a,max 0 A,by unfold a weaker; positivity,le_max_left ..,fun R Λ h f=>?_⟩
 let Y x:= mainTerm p R (Push.Uniform.fine G (arid f) x); let C' := intended (m:=f) p R; let X:= mom G f
 obtain ⟨hv,hq⟩:= main_beacons (arid f) h H V 0 (Metric.mem_ball_self zero_lt_one); have hy:C'=Y ∘ X:=funext fun x=> congr_arg (mainTerm p R) (mom_pays x)
 change ContDiffAt ℝ ω C' _∧_
 refine ⟨hy ▸ (show ContDiffAt ℝ ω Y (X 0) from (map_zero X).symm ▸ hv).comp _ X.contDiff.contDiffAt,Scatter.mono (C:=A) ?_ (le_max_right ..)⟩
 intro m hm q j
 have hh:= hq m hm (dustV ∘ q) j; have he(v): address (arid f) G (dustV v)=v.1:=rfl; simp only[Function.comp_apply, dustW,spanSites] at hh
 apply le_trans (le_of_eq (b:= ‖entry Y 0 (dustV ∘ q)‖) ?_) hh
 apply congr_arg; unfold entry; change iteratedFDeriv ℝ m C' _ _ =_; rw [hy,wired X (by rw[map_zero]; exact hv.analyticAt),map_zero]; congr 1; funext i; exact bolt_mom (q i)
end YM.Trace.Perfect
#print axioms YM.Trace.Perfect.lone_spread
