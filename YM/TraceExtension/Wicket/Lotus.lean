import YM.TraceExtension.Wicket.Circum
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Wicket
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels
open Cask
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}(R:Rep G n)(e:Lines G n 1){U:Config G n}
local notation "p"=> (beaconR e)
local notation "X"=>Config G n
variable (s:ℝ)
def loomH (v:G.El):= G.lieExp (s • tuna e v)
lemma LilyH:Continuous (loomH e s):= G.lieExp_cont.comp ((tuneH e).const_smul s)
variable (Y:Gal G n)
def windowH (U:Config G n)(v:G.El):ℝ:= if Healthy (R.p.threshold/4) {p.1} U then clamor p Y (tuna e v) U else 0
def tailH (U:Config G n)(v:G.El):ℂ:= windowH R e Y U v
def whisk (ν:X→ℝ)(U:X)(v:G.El):ℝ:= let A:= Tint p (tuna e v) s U; windowH R e Y A v*Real.exp (ν A-ν U)-windowH R e Y U v
def lute (ν:X→ℝ)(U:X):ℝ:=∫ i:G.El,whisk R e s Y ν U i ∂G.probHaar
variable (P:Support n)(hP:Clouded Y P)
include hP
lemma petra :Envelope (uncurry (windowH R e Y)):=by
    let f(U:X×G.El):= clamor p Y (tuna e U.2) U.1; have hx:Continuous f:= (calls_c hP).comp (continuous_fst.prodMk ((tuneH e).comp continuous_snd)); exact Envelope.piece (measurable_fst (healthy_closed ..|>.measurableSet)) ⟨hx.measurable,isCompact_univ.exists_bound_of_continuousOn (f:=f) hx.continuousOn|>.imp fun C h U=> h U (Set.mem_univ _)⟩ (Envelope.const _)
lemma continued (ν:X→ℝ)(hv: Envelope ν) : Envelope (uncurry (whisk R e s Y ν)):=by
    have h:= petra R e Y P hP; let W(z:X × G.El):= Tint p (tuna e z.2) s z.1; have hh: Continuous W:= (tint_c p s).comp (f:=fun z:X × G.El=>(tuna e z.2,z.1)) (((tuneH e).comp continuous_snd).prodMk continuous_fst);
    unfold whisk uncurry; simp_rw [sub_eq_add_neg]; refine Envelope.add (Envelope.mul ?_ ?_) h.neg
    · obtain ⟨c,hc⟩:=h.cost; exact ⟨h.meas.comp (f:=fun i:X × G.El=>(W i,i.2)) (hh.measurable.prodMk measurable_snd),c,fun i=>hc (W i,i.2) ⟩
    obtain ⟨c,hc⟩:=hv.cost; exact ((⟨hv.meas.comp hh.measurable,c,fun i=>hc (W i)⟩ : Envelope (fun z:X × G.El=>ν (W z))).add (Envelope.neg (⟨hv.meas.comp measurable_fst,c,fun i=> hc i.1⟩:Envelope fun i:X × G.El=> ν i.1))).exp
lemma lute_e (ν:X→ℝ)(hv:Envelope ν): Envelope (lute R e s Y ν) := by
    obtain ⟨h,c,hc⟩:= continued R e s Y P hP ν hv; refine ⟨h.stronglyMeasurable.integral_prod_right.measurable,c,fun U=>?_⟩; exact le_trans (norm_integral_le_of_norm_le_const (Eventually.of_forall (fun i=> hc (U,i)))) (by simp)
lemma horn (Q:Support n)(hx:inspected {p.1}⊆ Q)(hp:P⊆ Q){D:ℝ}(hT:64*D≤ R.p.threshold)(he:∀ v:G.Color, ‖v‖≤1→ G.chord (G.lieExp (s • v)) ≤ D) : ProofC R p.1 (tailH R e Y) (loomH e s) Q D:=by
    refine ⟨fromR (petra R e Y P hP),?_,?_,fun u v H=>?_,fun i j=>?_,fun j=> he _ (litChrom _ _|>.le),by linarith only[hT,R.p.threshold_pos],(LilyH e s).measurable⟩
    · intro v u w hu; unfold tailH windowH; dsimp only; apply congr_arg Complex.ofReal; have he : Healthy (R.p.threshold/4) {p.1} u ↔ Healthy (R.p.threshold/4) {p.1} w:=by unfold Healthy; rw [disjoint_iff_inter_eq_empty,disjoint_iff_inter_eq_empty,flags_agree _ _ _ _ (agrees_mono hu (coe_subset.mpr hx))];
      by_cases h:Healthy (R.p.threshold/4) {p.1} u; rw [if_pos h,if_pos (he.mp h),clamor,clamor,hP.stout u w (agrees_mono hu (coe_subset.mpr hp))]; rw [if_neg h,if_neg (mt he.mpr h)]
    · intro j U v; unfold tailH windowH Healthy; rw [gauge_flags]; apply congr_arg Complex.ofReal; split
      · rw [clamor,hP.paints,tuna,Gauge.adjoint_mul,← Swift.loy,loyS]; rfl
      exact rfl
    · by_contra hx; exact H (by simp [tailH,windowH,hx])
    unfold loomH tuna; rw [Gauge.adjoint_mul,←map_smul,adjoint_exp]
lemma canon_evt (ν:X→ℝ)(h:Envelope ν)(U:X): Integrable (whisk R e s Y ν U) G.probHaar:=by
    obtain ⟨hp,c,hc⟩:= continued R e s Y P hP _ h; exact (show Envelope (whisk R e s Y ν U) from ⟨hp.comp (f:=fun v=>(U,v)) (measurable_const.prodMk measurable_id), _,fun i=> hc (U,i)⟩).integrable _
lemma closer (m:ℕ)(ε:ℝ)(hε:0< ε){σ A Λ δ w:ℝ}(hp:R.Lawful σ A Λ δ w)(ht:Geo.Width R.p R.clip σ)(he:WilsonStartup.Decent R.clip R.p)(hV:4 ≤ R.p.supportExponent) :∀ᶠ T:Vest n in atTop,∀ U:X, |lute R e s Y (Shepherd.field R m) U-lute R e s Y (cabinet R m T) U| ≤ ε:=by
    obtain ⟨C,hC⟩:= (petra R e Y P hP).cost
    have h:C≥0:= (norm_nonneg _).trans (hC (1,1)); filter_upwards [exp_forms R hp ht m he hV (show 0< ε/(C+1) from by positivity)] with T hT U
    unfold lute; rw [← integral_sub (canon_evt R e s Y P hP _ (froth R hp ht he hV _) _) (canon_evt R e s Y P hP _ (framed_c R hp ht _ _ he) _)]; rw[← Real.norm_eq_abs]; refine le_trans (norm_integral_le_of_norm_le_const (μ:=G.probHaar) (C:=ε) (Eventually.of_forall ?_)) (by simp); intro i; change |_ - _|≤ε; unfold whisk; dsimp only; rw [sub_sub_sub_cancel_right,← mul_sub,abs_mul]; exact (mul_le_mul ((hC (_,i)).trans (le_add_of_nonneg_right zero_le_one)) (hT _ _) (abs_nonneg _) (by positivity:C+1≥0)).trans_eq (by field_simp)
omit hP
lemma tracks(m:ℕ): Complex.ofReal ∘ (lute R e s Y (Shepherd.field R m))= lensF R p.1 p.2 (loomH e s) (tailH R e Y) m:=by
    funext U; unfold lute lensF; rw[Function.comp_apply,← integral_complex_ofReal]; apply integral_congr_ae (Eventually.of_forall fun v=>?_); unfold whisk rink aura tailH spur stunt loomH Tint; push_cast; rw [seatB]
include hP
-- global coarse bound uses wings.Seal only D; captures even arbit rare.
lemma lampG (Q:Support n)(D:ℝ)(hp: ProofC R p.1 (tailH R e Y) (loomH e s) Q D)(m:ℕ){σ A v δ w:ℝ}(h:R.Lawful σ A v δ w)(H:Geo.Width R.p R.clip σ)(hv:WilsonStartup.Decent R.clip R.p)(he:4 ≤ R.p.supportExponent)(ht: Shepherd.tariff R (wingC R D σ A v) (2*δ) ≤ 1)(hO: p.1∈Q)(W:ℝ) (hw: ∀ U j, |windowH R e Y U j| ≤ W): ∀ U:X, |lute R e s Y (Shepherd.field R m) U| ≤ W*Real.exp 2+W:=by
   have hY: ∀ U v, ‖tailH R e Y U v‖ ≤ W:=fun U v=>(Complex.norm_real _).trans_le (hw _ _); have hW: 0≤ W:= (abs_nonneg _).trans (hw 1 1);
   obtain ⟨b,hb,hg⟩:= Shepherd.wings R h H (by linarith only [he]) D ((G.chord_nonneg _).trans (hp.price 1))
   obtain ⟨c,hc,hT⟩:= earns R p.1 (posDir p.2) h H hv he m _ _ hp hO 0 W le_rfl (by linarith only [he]) hY hW _ hb _ hg ht; simp only [zero_mul,Real.exp_zero, mul_one] at hT
   intro U; rw [← Real.norm_eq_abs];rw [← show ‖(↑(lute R e s Y (Shepherd.field R m) U):ℂ)‖ = _ from Complex.norm_real _,show (↑(lute R e s Y (Shepherd.field R m) U):ℂ)= _ from congr_fun (tracks R e s Y m) U]; unfold lensF; exact meanN (H:=W*Real.exp 2+W) (fun v=> (norm_sub_le ..).trans (by rw [← fills R p.1 (posDir p.2) h hv m _ _ hp U v]; refine add_le_add ?_ (hY _ _); apply le_trans (norm_sum_le ..) ; exact (sum_le_sum fun i _=>(hc i).2 _ _).trans hT)) _
end YM.Trace.Wicket
