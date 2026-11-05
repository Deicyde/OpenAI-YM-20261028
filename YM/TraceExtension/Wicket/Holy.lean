import YM.TraceExtension.Wicket.Abacus
import YM.Planned.ATOM_REGULAR_ESTIMATE.Pass
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Wicket
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{R:Rep G n}{o:Edge (Site n)}{A K:ℝ}{B:BudgetPoint}{P Q:Support n}{U:Config G n}{F H:Mellow G n}
lemma Cohort.up (h:Cohort B P o F)(hp:P ⊆ Q): Cohort B Q o F:=⟨fun v u w H=> h.sites v u w (agrees_mono H (coe_subset.mpr hp)),h.shift,h.meas,fun _ _ _ hV hx hv he=> h.earns _ _ _ hV hx (Disjoint.mono_left hp hv) he⟩
lemma Cohort.real {e:Lines G n 1} (h:Cohort B P (beaconR e) F) (U:Config G n)(hp:Healthy B.threshold P U): Integrable (F U ∘ tuna e) G.probHaar:=by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _); apply continuous_iff_continuousAt.mpr fun v=>?_ ; exact ((h.earns (fun _:G.Color=>U) (tuna e v) id (Army.park U _) contDiffAt_id hp (litChrom _ _ |>.le)).continuousAt).comp (tuneH e).continuousAt
lemma Cohort.blend (h:Cohort B P o F) (hg:Cohort B P o H): Cohort B P o (F*H):=⟨fun w U V hv=> congr_arg₂ (·*·) (h.sites w U V hv) (hg.sites w U V hv),fun U v g=>congr_arg₂ (· * ·) (h.shift U v g) (hg.shift U v g),h.meas.mul hg.meas,fun V p t hv hx hU he=> (h.earns V p t hv hx hU he).mul (hg.earns V p t hv hx hU he)⟩
lemma Cohort.sprout (h:Cohort B P o F): Cohort B P o (fun U v=>Real.exp (F U v)-1):= ⟨fun w U V H=> congr_arg (fun j=> Real.exp j-1) (h.sites w U V H),fun U v g=> by rw[h.shift],h.meas.exp.sub measurable_const,fun V p t hP hx hU he=>(h.earns V p t hP hx hU he).exp.sub contDiffAt_const⟩
lemma Career.up (h:Career B P F A)(hp:P ⊆ Q): Career B Q F A:=fun U hU=>h U (Disjoint.mono_left hp hU)
lemma Career.blend (h:Career B P F A)(he: Career B P H K):Career B P (F*H) (2^B.order*(A*K)):=fun U hU v hv=>(h U hU v hv).mul (he U hU v hv)
-- reuse port Ebon but adapt Pt->Real. inputs no globally regular but every germ even flag edge. integrates after at Chart.Valid. integrable off domain not needed.
variable {e:Lines G n 1}
abbrev warp (F:Mellow G n)(e:Lines G n 1)(U:Config G n):ℝ:= ∫ v:G.El,F U (tuna e v) ∂ G.probHaar
open Planned.AtomRegular
lemma Cohort.attire (h:Cohort B P (beaconR e) F) (hv:Healthy B.threshold P U): Covered G.probHaar (fun v w=> F (increment U w) (tuna e v)) B.order (0:Directions G n):=by
    let K:= fun w t=> F (increment U w) t
    apply Ebon.course G.probHaar K (tuna e) 0 _ (tuneH e); intro v; let W(i:Directions G n × G.Color):= increment U i.1; let a:G.Color:=tuna e v
    have hz: W (0,a)=U:=by unfold W; simp
    exact h.earns W (0,a) Prod.snd (fun i=> (incrementA U 0 i).comp (f:=Prod.fst) (g:=fun t:Directions G n=>G.mat (increment U t i)) (0,a) contDiffAt_fst) contDiffAt_snd (hz.symm ▸ hv) (litChrom _ _|>.le)
lemma Cohort.garment (h:Cohort B P (beaconR e) F): B.Regular P (warp F e):=by
    have hm : StronglyMeasurable (uncurry (fun U v=> F U (tuna e v))):= (h.meas.comp (measurable_fst.prodMk ((tuneH e|>.measurable).comp measurable_snd))).stronglyMeasurable
    have ht(u) (hu:Healthy B.threshold P u): Chart B.order (warp F e) u:= (h.attire hu).leaves (EventuallyEq.refl ..)
    refine ⟨fun U V hv=> congr_arg (fun f:G.El→ℝ=>∫ v,f v∂G.probHaar) (funext (fun v:G.El=> h.sites (tuna e v) U V hv)),hm.integral_prod_right.measurable,?_,ht,fun u hv A _ hV=> Next.Foundations.left_has A hV (ht _ hv)⟩
    intro k U; unfold warp; rw [← integral_mul_left_eq_self (f:=fun v=>F (gauge k U) (tuna e v)) (k (beaconR e).1)]; refine integral_congr_ae (Eventually.of_forall (fun v=> ?_)); unfold tuna; dsimp only; rw [Gauge.adjoint_mul]; exact h.shift ..
lemma Cohort.instep(h:Cohort B P (beaconR e) F)(hu:Healthy B.threshold P U)(l:List (Directions G n))(hv:l.length ≤B.order) : leftDerivs (warp F e) l U= ∫ v:G.El,leftDerivs (fun U=>F U (tuna e v)) l U ∂G.probHaar:=by
    let f(v:G.El)(U):= (F U (tuna e v)); let K:=warp F e; let L:=l.get
    have hZ: Covered G.probHaar (fun v z=> Complex.ofRealCLM (f v (increment U z))) B.order 0 :=by
       let K(u:Directions G n)(t:G.Color):= Complex.ofReal (F (increment U u) t)
       apply Ebon.course G.probHaar K (tuna e) 0 _ (tuneH e); intro v; let W:= fun p:Directions G n × G.Color=> increment U p.1; let q:=tuna e v
       refine Complex.ofRealCLM.contDiff.contDiffAt.comp _ (h.earns W (0,q) Prod.snd ?_ contDiffAt_snd ?_ (show ‖q‖ ≤ _ from litChrom _ _|>.le)); exact fun i=> (incrementA U 0 i).comp (f:=Prod.fst) (g:=fun t:Directions G n=>G.mat (increment U t i)) (0,q) contDiffAt_fst; simpa [W] using hu
    let g:=Complex.ofRealCLM
    obtain ⟨hx,hx',H⟩:= left_integral (K:= (g ∘ K)) (f:=fun v=> g ∘ f v) U L hv hZ (show (g ∘ K) ∘ increment U =ᶠ[𝓝 0] _ from (Eventually.of_forall fun i=> integral_complex_ofReal.symm))
    have ht(v:G.El) : Chart B.order (f v) U:=by let V:= increment U; exact h.earns V 0 (fun _=>tuna e v) (incrementA U _) contDiffAt_const (by simpa [V] using hu) (litChrom _ _|>.le)
    have hz(v:G.El): iteratedFDeriv ℝ l.length ((g ∘ f v) ∘ journey U _ L) 0 WardBin.Lies.cart= g (leftDerivs (f v) l U):=by
       rw [← left_linear g _ (ht v) hv]; exact (Germ.ordered L (show Germ l.length (g ∘ f v) U from (g.contDiff.contDiffAt.comp _ (ht v)).of_le (Nat.cast_le.mpr hv))).symm.trans (by unfold L; rw[List.ofFn_get])
    apply Complex.ofReal_injective; change g _= Complex.ofReal (∫ v:G.El,leftDerivs (f v) l U ∂ G.probHaar); rw[← left_linear g l (h.garment.smooth _ hu) hv]; unfold L at H; rw [List.ofFn_get] at H; rw[show warp F e=K from rfl,H]; simp_rw [show l.get=L from rfl,hz]; exact integral_complex_ofReal
lemma Cohort.limitH (h:Cohort B P (beaconR e) F) (hh:Career B P F A)(hA:0≤ A) : B.supBounds (0:Site n) P (warp F e) A:=by
    refine ⟨hA,fun u hu l hv hx=> ?_⟩; rw [h.instep hu l hv]; exact le_trans (norm_integral_le_of_norm_le_const (Eventually.of_forall (fun j:G.El=>(hh u hu (tuna e j) (litChrom _ _|>.le)|>.pay l hv hx)))) (by simp)
end YM.Trace.Wicket
