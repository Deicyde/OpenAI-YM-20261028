import YM.Planned.PRIMARY_INTEGRAL_295.Festoons

/-!
# xCut thermal leading derivative and truncation cost

Using literal Cell orientations.Lom.Scope. Truncating in F1 E.Pulse
numerical comparison only, not changing K elsewhere. f computed via
Festor finite slot groups exact. Leading comparison along actual 
linear b chart directions, subsequently Ember op. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Xacts
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place Next.Fluctuations
open Villa Fizz Fizz.Gush Bazaars Cedar  Oval
open Bunks Little Work.F01 Little.Core Push.Uniform   Density  Festoons Work.F03
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Gauge} {k n d:ℕ} {c f : Side} {S:StepData c f} {σ C Λ:ℝ}

-- cut formula even equality. combine rows anchored.
variable (A:Clip) (P:PathData G) (a:Dir G c)

def cutX (d n:ℕ) (i:Twin c) := if i.2 then clamp P i.1.2 d n (fun s=>Work.F03.faceCurl (Work.F03.slotFace s i.1.1) a) else Real.sqrt A.direct • Work.F03.faceCurl i.1 a

lemma cutX_add (b:Dir G c) (d n:ℕ)(i:Twin c): cutX A P (a+b) d n i = cutX A P a d n i + cutX A P b d n i:=by
   have he (p:Cell c): faceCurl p (a+b)=faceCurl p a+faceCurl p b:=by
     ext j; simp only [faceCurl,dColor,parts_add, Matrix.mulVec_add,PiLp.add_apply,WithLp.ofLp_toLp, Pi.add_apply]
   unfold cutX; split
   · unfold clamp; simp_rw [he,smul_add,Finset.sum_add_distrib]
   rw [he,smul_add]

variable (d n)
lemma flat_der (h:P.Bounds A σ C Λ) (hd:0<d) (i:Twin c): HasDerivAt (fun y:ℝ=> plotted P A n d (represent (y • a)) i) (cutX A P a d n i) 0 := by
   unfold cutX plotted; split
   · simp_rw [Festoons.clipped_short P h _ _ n d hd]; unfold clamp
     exact HasDerivAt.fun_sum (fun s _=> (slot_deriv s i.1.1 a).const_smul (chip P i.1.2 s))
   exact (curvature_of_hasDerivAt (face_deriv i.1 a)).const_smul (Real.sqrt A.direct)
omit a in
lemma plotted_zero (A:Clip) (P:PathData G) (d n:ℕ) (i:Twin c) : plotted P A n d 1 i=0:=by
   have he (p:Cell c): faceValue (1:Config G c) p=1:=by rw [← (link_one (G:=G))]; apply Push.stroll_zero
   unfold plotted; split
   · have he (j:ℕ): shortenTerm P n d 1 i.1 j=0 := by
        unfold shortenTerm PathData.ellTerms; split
        · rw [Work.F03.atSite_path,he,G.curvature_unit,map_zero,smul_zero]
        rfl
     simp [Pressure.shorten,he]
   simp [Pressure.shoot,he,G.curvature_unit]

-- post universal rates a nativeσ, pricing linear precursor arguments.
lemma costs (p:Stage) (G:Gauge): ∃ C:ℝ, 1≤C∧∀ d (_ :0<d) n (c: Side) (P:PathData G), (∃ Λ,P.Bounds p.clip p.width p.paths Λ) →∀ i:Twin c,∀ v:Dir G c,
   ‖xLin p.clip P v i‖ ≤ C*‖v‖ ∧ ‖xLin p.clip P v i-cutX p.clip P v d n i‖ ≤ C*Real.exp (-(p.width/d)*n)*‖v‖ :=by
   obtain ⟨C,r,hC,hr,h⟩:= face_chart_cost G
   let B:=p.paths*C; let u:=Real.sqrt p.clip.direct*C
   have hb:0≤B:= mul_nonneg p.paths_pos.le hC.le; have hu:0≤u:=mul_nonneg (Real.sqrt_nonneg _) hC.le
   refine ⟨1+B+u,by linarith,fun d hd n c P ⟨Λ,hP⟩ ⟨i,p'⟩ v=>?_⟩
   have hf (i:Cell c): ‖faceCurl i v‖≤C*‖v‖:= (h v i).1
   let e:=1+B+u; have he:1 ≤ e:=by unfold e; linarith
   cases p'
   · have hc : ‖Real.sqrt p.clip.direct • faceCurl i v‖ ≤ u*‖v‖:=by rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)];
                                                                       apply (mul_le_mul_of_nonneg_left (hf i) (Real.sqrt_nonneg _)).trans_eq; rw [←mul_assoc]
     refine ⟨hc.trans (mul_le_mul_of_nonneg_right (show u≤e by unfold e; linarith) (norm_nonneg _)), ?_⟩
     rw [show cutX p.clip P v d n (i,false)=xLin p.clip P v (i,false) from rfl,sub_self,norm_zero]; exact mul_nonneg (mul_nonneg (zero_le_one.trans he) (Real.exp_pos _).le) (norm_nonneg _)
   obtain ⟨hF,hx⟩:= Price.tail_cost P hP i.2 (fun s=> faceCurl (slotFace s i.1) v) d n hd (C*‖v‖) (fun x=> hf _)
   let y(k:ℕ):=(P.row i.2 k).2; let w(k:ℕ):= |(P.row i.2 k).1| * Real.exp (p.width*(y k).length)
   have hk:=hP.rows i.2; let f (k:ℕ):= (P.row i.2 k).1 • faceCurl (slotFace (y k) i.1) v
   have hh(k): ‖f k‖≤ w k * (C*‖v‖):=by
      unfold f; rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg p.width_pos.le (by positivity)))) (hf _) (norm_nonneg _) (by unfold w; positivity)
   constructor
   · have hs := hk.2.1.mul_right (C*‖v‖)
     have ha:Summable fun k=>‖f k‖:=Summable.of_norm_bounded hs (fun i=>by rw [norm_norm]; exact hh i)
     apply le_trans (b:=B* ‖v‖) (_:(‖∑' k,f k‖)≤_) (mul_le_mul_of_nonneg_right (show B≤e by unfold e; linarith) (norm_nonneg _))
     refine (norm_tsum_le_tsum_norm ha).trans ((ha.tsum_le_tsum hh hs).trans ?_)
     rw [tsum_mul_right]; apply (mul_le_mul_of_nonneg_right hk.2.2 (show 0≤C*‖v‖ by positivity)).trans_eq; rw [←mul_assoc]
   let D:= Real.exp (-(p.width/d)*n)
   apply hx.trans; calc
    _ = B*D*‖v‖ := by unfold B D; ring
    _ ≤ _:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (show B≤e by unfold e; linarith) (by unfold D; positivity)) (norm_nonneg _)
end YM.Planned.PrimaryIntegral295.Xacts
