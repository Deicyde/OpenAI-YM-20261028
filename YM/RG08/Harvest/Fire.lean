import YM.RG08.Harvest.Eye
/-!
# Root capture in one closed real continuum cell. Use normalized Lebesgue
- no growing-window variation constant.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Harvest
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands Pill Wings PowerSeries Taste Plot Plot.High
open MeasureTheory
open scoped BigOperators Topology Real ContDiff Classical ENNReal
variable {k i r τ D:ℕ}{R θ:ℝ}{G:Gauge}
section tape
abbrev yard:=Scores.examinable (1/2)
lemma yard_meas : MeasurableSet yard:= (grounds _|>.1).isClosed.measurableSet
lemma yard_has : volume yard ≠ 0 ∧ volume yard≠ ⊤:= by
   have hx : Metric.ball (0:E4) (1/2) ⊆ yard:= by intro i hi a; exact (PiLp.norm_apply_le i a).trans (le_of_lt (by simpa using! hi))
   exact ⟨((Metric.isOpen_ball.measure_pos volume ⟨(0:E4),by simp⟩).trans_le (measure_mono hx)).ne', (grounds _|>.1).measure_lt_top.ne⟩
abbrev Rest:= Scores.Close (1/2)
def abide : Measure Rest := (volume yard)⁻¹ • volume.comap (Subtype.val)
instance : IsProbabilityMeasure abide:=⟨by rw [abide,Measure.smul_apply]; simp [comap_subtype_coe_apply yard_meas,yard_has.1,yard_has.2]; exact ENNReal.inv_mul_cancel yard_has.1 yard_has.2⟩ -- namespace
lemma samples (f:E4→ℝ): ∫ i: Rest,f i.val ∂abide= ((volume yard)⁻¹).toReal * ∫ x in yard,f x:= by unfold abide; rw [integral_smul_measure, integral_subtype_comap]; rfl; exact yard_meas
private def title (D:ℕ):Sheet D := ⟨⟨0,by omega⟩,fun _=>0⟩
def inset (i: Rest)(h:1/2≤R): Close R:= ⟨i.val,fun v=>(i.property v).trans h⟩
def scoop (i:Rest)(h:1/2≤R) : Voice D R:= Scores.utter _ _ (inset i h) (title D)
lemma scoop_s (h:1/2≤ R)(i:Rest)(φ:Exam D): scoop i h (sheet D R φ)=φ.val i.val:= by unfold scoop; rw [Scores.whisper]; change iteratedFDeriv ℝ 0 φ.val (i.val) (basis ∘ (title D).2)= _; simp [title]
lemma live_eyes (f:Sight D R)(h:1/2≤R): Continuous (fun i:Rest=> scoop i h f):= (f.val (title D)).continuous.comp (continuous_subtype_val.subtype_mk _)
def drink (F:Rest→ℝ)(h:1/2≤R)(v:Sight D R):= ∫ i: Rest,F i*scoop i h v ∂abide
private lemma living {F:Rest→ℝ}(h:Continuous F): Integrable F abide:= Continuous.integrable_of_hasCompactSupport h ((isClosed_tsupport _).isCompact)
private lemma drinks {F:Rest→ℝ}(D:ℕ)(hp:Continuous F)(h:1/2≤ R) : ∃ V:Voice D R,(V:Sight D R→ℝ)=drink F h ∧ ‖V‖ ≤ ∫ i:Rest,‖F i‖ ∂abide:= by
   have hM(v:Sight D R): Integrable (fun i=>F i*scoop i h v) abide:= living (hp.mul (live_eyes v h))
   let V:Sight D R→ₗ[ℝ]ℝ := { toFun:=drink F h,
                                map_add':=fun x y=> by unfold drink; simp_rw [map_add,mul_add, integral_add (hM x) (hM y)],
                                map_smul':=fun c x=> by simp only [drink,_root_.map_smul,smul_eq_mul,mul_left_comm _ c,integral_const_mul]; rfl }
   let C:= ∫ i:Rest,‖F i‖ ∂abide; have hz:0≤C:= integral_nonneg (fun _=> norm_nonneg _)
   have he v: ‖V v‖ ≤ C*‖v‖:= by
      unfold C; change ‖∫ i:Rest,F i*scoop i h v ∂abide‖ ≤ _; rw [← integral_mul_const]; exact (norm_integral_le_integral_norm _).trans (integral_mono (hM v|>.norm) (living ((hp.norm).mul continuous_const)) (fun i=>by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (Scores.norm_mark _ _ _ _ v) (norm_nonneg _)))
   exact ⟨V.mkContinuous C he,rfl,LinearMap.mkContinuous_norm_le _ hz he⟩
def hold (F:Rest→ℝ)(h:1/2≤R) : Voice D R:= if hp:Continuous F then (drinks D hp h).choose else 0
lemma holding {F:Rest→ℝ}(hp:Continuous F)(h:1/2≤R):(hold F h : Sight D R→L[ℝ] ℝ).toFun=drink F h ∧ ‖hold (D:=D) F h‖ ≤ ∫ i:Rest, ‖F i‖ ∂abide:= by unfold hold; rw [dif_pos hp]; exact (drinks D hp h).choose_spec
lemma weight_s {F:Rest→ℝ}(hp:Continuous F)(h:1/2≤R)(p:ℝ): hold (D:=D) (p • F) h=p • hold F h:= by
   ext x; change (hold (p•F) h).toFun x= p*(hold F h).toFun x; rw [(holding (hp.const_smul p) h).1,(holding hp h).1]; simp only [drink,Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]
lemma together {F V:Rest→ℝ}(hp:Continuous F)(hv:Continuous V)(h:1/2≤R): hold (D:=D) (F+V) h= hold F h+hold V h:= by
   ext x; change (hold (F+V) h).toFun x=(hold F h).toFun x+(hold V h).toFun x; rw [(holding (hp.add hv) h).1,(holding hp h).1,(holding hv h).1]; simp only [drink,Pi.add_apply,add_mul]; exact integral_add (living (hp.mul (live_eyes ..))) (living (hv.mul (live_eyes ..)))
variable {h:1/2≤R} {F V:Rest→Tale G}
def rip (F:Rest→Tale G)(h:1/2≤R) (D:ℕ): BoardU D R G:= fun i r b=> hold (fun j=> F j i r b) h
lemma generated (hx: Via G τ F)(i j b): Continuous (fun x:Rest=>F x i j b):= by
   induction hx with
   | head F h p g he=> exact he.mul continuous_const
   | plus F V h p ih ik=> exact ih.add ik
lemma punched (h:1/2≤R)(V:Via G τ F)(b:Beads (Loc G 1) r)(g:Exam D): (plug g R) (rip F h D i r b)=∫ j:Rest, F j i r b*g.val j.val ∂abide:= by
   change (hold _ h).toFun (sheet D R g)=_; rw [(holding (generated V i r b) h).1]; unfold drink; simp_rw [scoop_s]
lemma ripping (h:1/2≤R)(he:Via G τ F)(hp:Via G k V) : rip (F+V) h D= rip F h D+rip V h D:= by
   ext1 i; ext1 j; funext b; exact together (generated he i j b) (generated hp i j b) h
lemma burdens (h:1/2 ≤ R)(he:Via G τ F) : Marvel τ (rip F h D) ∧ Lank (rip F h D):= by
   induction he with
   | head F he hF g hg=>
     let A:=hold (D:=D) g h; let U:= (fun i:Rest=> g i • F); have H e k: rip U h D e k=(fun b=>F e k b • A):= by funext b; unfold rip U; rw [show (fun j:Rest=> (g j • F) e k b)= (F e k b • g) from funext fun i=> (mul_comm _ (F e k b))]; exact weight_s hg h (F e k b)
     let K:ℝ→L[ℝ] Voice D R:= (ContinuousLinearMap.id ℝ ℝ).smulRight A
     constructor
     · have hc g':ringU g' (rip U h D)= (plug g' R A) • F:= funext fun i=>funext fun j=>funext fun b=>by unfold ringU; rw [H i j]; simp only [Function.comp_apply,_root_.map_smul]; exact mul_comm ..
       refine ⟨fun i j hj=> he.cap i j (fun h=> hj (by rw [H i j,h]; funext b; exact zero_smul ..)),fun i j=> ?_, fun m g i=> ?_⟩
       · change Tidy (rip U h D i j); rw [H i j]; exact Tidy.map K (he.tidy ..)
       change Shore i τ (ringU g (rip U h D)); rw [hc]; exact (he.weight _).shore m i
     · intro i j; change Vale.Polished (rip U h D i j); rw [H i j]; exact polished_fun (hF i j) K
   | plus F V H hv ih ik=> rw [ripping h H hv]; exact ⟨choir_plus ih.1 ik.1,lank_add ih.2 ik.2⟩
end tape
end YM.RG08.Harvest
