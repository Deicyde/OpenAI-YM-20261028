import YM.Contacts.Variation

/-! # Equivariant detectors

Construct one system of projection readouts on the **whole algebra of physical expressions** (not a pointwise OPE on pairs). Fixed finite point probes at each horizon, averaged over their compact orthogonal orbits, and with the real symmetrization. Use an aperture at each basic probe system. Operate only on this aperture; junk defined outside to keep expressions uniform. (If gluing, retain the collar qualifications on uses of Q; changes away from collapse where there are no Taylor jets will not involve Q.)
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts
open Function Filter Set MeasureTheory Table OPE MultipleContact Metric
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} {P : DiffPlan S}
variable {W I : Type} [TopologicalSpace W] [Fintype I] {U : Set W}

/-- Fix all choices & orientations. Unselected hierarchy. -/
structure Devices (P : DiffPlan S) where
  basis : OPE.Prescription P
  coherent : basis.Coherent
  rotation : S.Rotation
  hierarchy : S.Hierarchy
  incl : P.Inclusions S
  orientation : P.Orientation hierarchy.spin
  laws : rotation.Laws P hierarchy.spin
  turns : rotation.Oriented S
  tests (d : ℕ) : Detector S d

lemma continuousOn_move {s : W→ Ortho} {x : W→ E4} (hs : ContinuousOn s U) (hx : ContinuousOn x U) :
    ContinuousOn (fun i=> Ortho.move (s i) (x i)) U := by
  let f : Ortho→Axis→Axis→ℝ := Subtype.val
  have hf : Continuous f:= continuous_subtype_val (p:=(·∈Matrix.unitaryGroup Axis ℝ))
  have he : ContinuousOn (fun i j=> Ortho.move (s i) (x i) j) U := continuousOn_pi.mpr fun j=> by
    change ContinuousOn (fun i=> Ortho.move (s i) (x i) j) U; unfold Ortho.move; simp_rw [M4.at_coord]
    apply continuousOn_finsetSum _ fun k _ => ?_
    exact (((continuous_apply k).comp ((continuous_apply j).comp hf)).comp_continuousOn hs).mul
      ((PiLp.continuous_apply 2 _ k).comp_continuousOn hx)
  exact (PiLp.continuous_toLp _ _).comp_continuousOn he

-- Scoped instances
scoped instance rotationsCompact : CompactSpace Ortho := YM.Work.A15.compact_ortho
scoped instance rotationsCountable : SecondCountableTopology Ortho := by
  haveI : SecondCountableTopology M4 := inferInstanceAs (SecondCountableTopology (Axis → Axis → ℝ))
  exact inferInstanceAs (SecondCountableTopology ↥((Matrix.unitaryGroup Axis ℝ : Set M4)))
scoped instance rotationsMeasurable : MeasurableSpace Ortho := borel Ortho
scoped instance rotationsBorel : BorelSpace Ortho := ⟨rfl⟩

def allO : TopologicalSpace.PositiveCompacts Ortho := ⟨⟨Set.univ,isCompact_univ⟩, by simp⟩
def averageO : Measure Ortho := Measure.haarMeasure allO
instance : averageO.IsHaarMeasure := by unfold averageO; infer_instance
instance : IsProbabilityMeasure averageO := ⟨@Measure.haarMeasure_self Ortho _ _ _ _ _ allO⟩

variable (M : Devices P)
namespace Devices
local notation "D" => M.basis
local notation "R" => M.rotation
local notation "ρ" => M.hierarchy.spin
local notation "hS" => M.hierarchy.laws.toSymmetric

lemma continuousOn_act {d : ℕ} {x : W→ S.Field d} {s : W→ Ortho} (hs : ContinuousOn s U) (hx : ContinuousOn x U) : ContinuousOn (fun i => M.rotation.act d (s i) (x i)) U := by
  conv => lhs; intro i; rw [← (M.coherent d).rebuilds (x i),map_sum]; simp only [map_smul]
  apply continuousOn_finsetSum _ fun j _=>?_ ; exact (((M.basis.test j d).continuous_of_finiteDimensional).comp_continuousOn hx).smul ((M.laws.spin ..).comp_continuousOn hs)

local notation "Cstar" => starRingEnd ℂ

def conjugation (d : ℕ) : S.Field d →L[ℝ] S.Field d :=
  LinearMap.toContinuousLinearMap {
    toFun:= S.conj ρ d, map_add':=map_add _, map_smul':=fun r u=> by
      change S.conj ρ d (r • u) = r • S.conj ρ d u
      simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ]; simp }

/-- unrotated point probe product, include the conjugated ones -/
def probeWord (e : Exterior L) (b : Bool) : Expression P := tokenWord D (bearing e) (if b then L.conjugate ∘ e.letter else e.letter)
lemma conj_false_probe (e : Exterior L) : realExpr D ρ (M.probeWord e false)= M.probeWord e true := by
  unfold probeWord tokenWord; rw [map_prod]; refine Finset.prod_congr rfl fun i hi=>?_
  change realExpr D ρ (insertField D (bearing e i) (e.letter i).1 (S.project _ _))=_
  rw [real_field D hS M.incl M.orientation M.coherent, S.conj_project]; rfl
lemma probe_reply (e : Exterior L) {d : ℕ} (v : S.Field d) : readExpr D S (insertField D 0 d v * M.probeWord e false)= response S d e v := by
  obtain ⟨p,rfl⟩:= S.onto d v
  change readExpr D S (insertToken D 0 (⟨d,p⟩:L.Token) * tokenWord D (bearing e) e.letter)=_
  rw [← token_sole,← token_beside,read_word D M.coherent S hS (fun _=> le_rfl) M.incl,response_self,← Prescription.one_test d _ p M.hierarchy]
  simp only [Prescription.reading,totalObserve,sole,sub_zero]; rfl -- edit

lemma orbit_visible (e : Exterior L) (b : Bool) {s : W→ Ortho} {A : W→ Set E4} (hs : ContinuousOn s U)
    (ha : ∀ t∈U,Set.range (Ortho.move (s t) ∘ bearing e) ⊆ A t) :
    Displays U A (fun t=>turnExpr D R (s t) (M.probeWord e b)) := by
  let p:= if b then L.conjugate ∘ e.letter else e.letter
  change Displays _ _ (fun t=>turnExpr D R (s t) (tokenWord D (bearing e) p)); simp_rw [token_to_field,turn_word D R M.laws hS M.incl M.coherent]
  exact Displays.word («D»:=D) (d:=fun i=>(p i).1) ha
    (fun t _=> (Ortho.move_injective _).comp ((beside_distinct.mp (bearing_clear e)).2.1))
    (continuousOn_pi.mpr fun i=> continuousOn_move hs continuousOn_const)
    (fun i=> continuousOn_act M (d:=(p i).1) (x:=fun _=> (S.project _ (p i).2)) hs continuousOn_const)

def aperture (d : ℕ) := (MultipleContact.detector_clearance (M.tests d)).choose
lemma aperture_pos (d : ℕ) : 0 < M.aperture d := (MultipleContact.detector_clearance _).choose_spec.1

-- keep uses closedBall
local notation "O" d => closedBall (0:E4) (M.aperture d)
lemma aperture_clears {d : ℕ} (e : (M.tests d).probes) (s : Ortho) (i : Fin e.val.n) :
    2*(M.aperture d) ≤ ‖Ortho.move s (bearing e.val i)‖ := by
  rw [Ortho.move_norm]; exact (MultipleContact.detector_clearance (M.tests d)).choose_spec.2 e.val e.property i
lemma detectors_outside {d : ℕ} (e : (M.tests d).probes) (s : Ortho) : Set.range (Ortho.move s ∘ bearing e.val) ⊆ (O d)ᶜ := by
  rintro x ⟨i,rfl⟩ hx
  exact not_le_of_gt ((lt_of_lt_of_le (by linarith only [M.aperture_pos d] : M.aperture d < 2*M.aperture d) (M.aperture_clears e s i))) (by simpa only [Function.comp_apply,Metric.mem_closedBall,dist_zero_right] using hx)
lemma keep_spin {d : ℕ} (s : Ortho) (e : Expression P) : turnExpr D R s (keep (O d) e)=keep (O d) (turnExpr D R s e) :=
  turn_keep D R (O d) (O d) s (by simp [Ortho.move_norm]) e

local notation "TS" d => M.tests d

/-- single unrotated probe on expressions, clipped at aperture (outside uses no kernel) -/
def direct (d : ℕ) : Expression P →ₗ[ℂ] S.Field d where
  toFun e := (TS d).decode (fun i=>(readExpr D S (keep (O d) e * M.probeWord i false)))
  map_add' x y := by simp_rw [map_add,add_mul,map_add]; exact map_add _ _ _
  map_smul' c x := by simp_rw [map_smul,smul_mul_assoc,map_smul]; exact map_smul (TS d).decode c _

lemma directs (d : ℕ) (v : S.Field d) : M.direct d (insertField D 0 d v)=v := by
  change (TS d).decode _=_; simp_rw [keep_field,if_pos (show (0:E4)∈O d from mem_closedBall_self (M.aperture_pos d).le), M.probe_reply]; exact (TS d).fixes v

/-- integrand before real symmetrization -/
def plain (s : Ortho) (d : ℕ) : Expression P →ₗ[ℂ] S.Field d :=
  (M.rotation.act d s).toLinearMap.comp ((M.direct d).comp (turnExpr D R s⁻¹).toLinearMap)
lemma plainly (s : Ortho) (d : ℕ) (e : Expression P) : M.plain s d e= M.rotation.act d s (M.direct d (turnExpr D R s⁻¹ e)) := rfl

/-- query in the original positions to display the orbits of the finite tests -/
def survey (s : Ortho) {d : ℕ} (i : (TS d).probes) (b : Bool) (e : Expression P) := readExpr D S (e * turnExpr D R s (M.probeWord i b))

lemma survey_conj (s : Ortho) {d : ℕ} (i : (TS d).probes) (e : Expression P) :
    M.survey s i false (realExpr D ρ e)=star (M.survey s i true e) := by
  have hh:= real_read D hS M.incl M.orientation M.coherent S M.hierarchy (fun _=>le_rfl) M.incl (realExpr D ρ e * turnExpr D R s (M.probeWord i false))
  rw [map_mul,real_twice D hS M.incl M.orientation M.coherent,real_turn D R M.laws hS M.incl M.orientation M.coherent,M.conj_false_probe] at hh
  unfold survey; rw [hh,star_star]
lemma plain_survey (s : Ortho) (d : ℕ) (e : Expression P) :
    M.plain s d e= M.rotation.act d s ((TS d).decode (fun i=>M.survey s i false (keep (O d) e))) := by
  refine congr_arg (M.rotation.act d s) (congr_arg ((TS d).decode) (funext fun i=>?_))
  change readExpr D S (keep (O d) (turnExpr D R s⁻¹ e)*_) = _
  rw [← keep_spin M,← turn_read D R M.laws hS M.incl M.coherent S M.hierarchy (fun _=>le_rfl) M.incl M.turns s,
    map_mul,turn_mul D R M.laws hS M.incl M.coherent,mul_inv_cancel,turn_one D R M.laws hS M.incl M.coherent]; rfl
lemma survey_on {d : ℕ} {A : W → Set E4} {E : W→ Expression P} (h : Displays U A E) (hA : ∀ t∈U,A t ⊆ O d)
    {s : W→ Ortho} (hs : ContinuousOn s U) (i : (TS d).probes) (b : Bool) : ContinuousOn (fun t=> M.survey (s t) i b (E t)) U := by
  have he := orbit_visible M i.val b hs (A:=fun _=>(O d)ᶜ) fun t _=>detectors_outside M i _
  exact Displays.observes D S M.hierarchy (Displays.times (B:=fun _=>(O d)ᶜ) (fun t ht=> Set.disjoint_left.mpr fun a ha Hb=>Hb (hA t ht ha)) h he)

lemma survey_cont (d : ℕ) (i : (TS d).probes) (b : Bool) (e : Expression P) : Continuous (fun s => M.survey s i b (keep (O d) e)) := by
  induction e using expression_induction with
  | hm n x p =>
    by_cases he : ∀ i, x i∈ O d
    · have hh : keep (O d) (letterWord x p)=letterWord x p := by
        change keep (O d) (∏ i,unitLetter (x i) (p i)) = ∏ i,unitLetter (x i) (p i)
        rw [map_prod]; simp_rw [keep_unit,if_pos (he _)]
      simp_rw [hh]; by_cases hx: Injective x
      · exact continuousOn_univ.mp (survey_on M (A:=fun _=> O d) (.atom (Fin n) (fun _=>x) p continuousOn_const (fun _ _=>hx) (fun _ _ a ha=>by obtain ⟨i,rfl⟩:=ha; apply he)) (fun _ _=>by rfl) (s:=id) continuousOn_id i b)
      let q := if b then L.conjugate ∘ i.val.letter else i.val.letter
      have he (s : Ortho) : M.survey s i b (letterWord x p)=0 := by
        unfold survey; change readExpr D S (letterWord x p * turnExpr D R s (tokenWord D (bearing i.val) q))=_
        rw [← letter_to_token D hS M.incl M.coherent,token_to_field D (bearing i.val),turn_word D R M.laws hS M.incl M.coherent, field_to_token D (Ortho.move s ∘ bearing i.val),← token_beside,
          read_word D M.coherent S hS (fun _=> le_rfl) M.incl]; exact if_neg (fun h=> hx (beside_distinct.mp h).1)
      simp_rw [he]; exact continuous_const
    push Not at he; obtain ⟨j,hj⟩ := he
    have ht : keep (O d) (letterWord x p)=0:=by
      change keep (O d) (∏ i,unitLetter (x i) (p i))=0; rw [map_prod]; exact Finset.prod_eq_zero (Finset.mem_univ j) ((keep_unit ..).trans (if_neg hj))
    simp only [ht,survey,zero_mul,map_zero]; exact continuous_const
  | ha x y hx hy => unfold survey at *; simp_rw [map_add,add_mul,map_add]; exact hx.add hy
  | hs r a ha => unfold survey at *; simp_rw [map_smul,smul_mul_assoc,map_smul]; exact (continuous_const (y:=r)).smul ha
lemma plain_integrable (d : ℕ) (e : Expression P) : Integrable (fun s=> M.plain s d e) averageO := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  apply continuousOn_univ.mp; simp_rw [plain_survey]
  refine M.continuousOn_act continuousOn_id (((TS d).decode.continuous_of_finiteDimensional).comp (
    continuous_pi fun i=> survey_cont M d i false e)).continuousOn

def complexMean (d : ℕ) : Expression P →ₗ[ℂ] S.Field d where
  toFun e := ∫ s, M.plain s d e ∂averageO
  map_add' x y := by simp_rw [map_add]; exact integral_add (plain_integrable M d x) (plain_integrable M d y)
  map_smul' r x := by simp_rw [map_smul]; exact integral_smul ..
lemma mean_id (d : ℕ) (v : S.Field d) : M.complexMean d (insertField D 0 d v)=v := by
  have h (s : Ortho) : M.plain s d (insertField D 0 d v)=v := by
    rw [plainly,turn_field D R M.laws hS M.incl M.coherent,← Ortho.motion_at, map_zero, directs, ← M.laws.group, mul_inv_cancel,M.laws.fixes]
  change (∫ s, _ ∂averageO)=_; simp_rw [h]; simp
lemma mean_spin (d : ℕ) (k : Ortho) (e : Expression P) :
    M.rotation.act d k (M.complexMean d e) = M.complexMean d (turnExpr D R k e) := by
  have he:= plain_integrable M d e; change _ = ∫ s, M.plain s d (turnExpr D R k e) ∂averageO
  refine (LinearMap.toContinuousLinearMap ((M.rotation.act d k).toLinearMap.restrictScalars ℝ) |>.integral_comp_comm he).symm.trans ?_
  trans ∫ s, M.plain (k*s) d (turnExpr D R k e) ∂averageO
  · refine integral_congr_ae (Eventually.of_forall fun s=>?_)
    change M.rotation.act d k (M.plain s d e)= M.plain (k*s) d (turnExpr D R k e); rw [plainly,plainly,M.laws.group,turn_mul D R M.laws hS M.incl M.coherent]
    simp [mul_inv_rev, mul_assoc]
  exact (measurePreserving_mul_left averageO k).integral_comp (Homeomorph.mulLeft k).measurableEmbedding (fun s=>M.plain s d (turnExpr D R k e))

/-- The real and orthogonal averaged detector. -/
def base (d : ℕ) : Expression P →ₗ[ℂ] S.Field d where
  toFun e:= ((2:ℂ)⁻¹) • (M.complexMean d e + S.conj ρ d (M.complexMean d (realExpr D ρ e)))
  map_add' x y:= by simp only [map_add,smul_add]; abel
  map_smul' c x:= by simp only [real_coeff,map_smul,map_smulₛₗ]; simp [smul_add,smul_comm (2:ℂ)⁻¹] -- check
lemma base_formula (d : ℕ) (e : Expression P) : M.base d e=
    ((2:ℂ)⁻¹) • (M.complexMean d e+S.conj ρ d (M.complexMean d (realExpr D ρ e))) := rfl
lemma base_id (d : ℕ) (v : S.Field d) : M.base d (insertField D 0 d v)=v := by
  rw [base_formula,real_field D hS M.incl M.orientation M.coherent, M.mean_id,M.mean_id, S.reflect_star,← two_smul ℂ, inv_smul_smul₀ (two_ne_zero)]
lemma base_real (d : ℕ) (e : Expression P) : S.conj ρ d (M.base d e)= M.base d (realExpr D ρ e):= by
  simp_rw [base_formula,map_smulₛₗ,map_add,S.reflect_star,real_twice D hS M.incl M.orientation M.coherent]; rw [add_comm]; rw [map_inv₀, map_ofNat]
lemma base_spin (d : ℕ) (s : Ortho) (e : Expression P) : M.rotation.act d s (M.base d e)= M.base d (turnExpr D R s e):= by
  rw [base_formula, base_formula, map_smul, map_add,mean_spin,← M.laws.real,mean_spin,real_turn D R M.laws hS M.incl M.orientation M.coherent]
-- explicit evaluation on small aperture, both star transforms using point probe
lemma base_survey (d : ℕ) {e : Expression P} (he : e∈supportedAt (O d)) : M.base d e=
    ((2:ℂ)⁻¹) • ((∫ s:Ortho, M.rotation.act d s ((TS d).decode (fun i=> M.survey s i false e)) ∂averageO) +
       S.conj ρ d (∫ s:Ortho, M.rotation.act d s ((TS d).decode (fun i=> star (M.survey s i true e))) ∂averageO)) := by
  rw [base_formula]; have h':keep (O d) e=e:= keep_supportedAt _ _ (by rfl) e he
  simp_rw [complexMean,LinearMap.coe_mk,AddHom.coe_mk,plain_survey,← real_keep,h',survey_conj]
lemma base_continuous (d : ℕ) {A : W→ Set E4}{E : W→ Expression P}(h : Displays U A E)(hA : ∀ t∈ U,A t⊆ O d) :
    ContinuousOn (fun t=> M.base d (E t)) U := by
  let f (i : (TS d).probes) b (p : W×Ortho) := M.survey p.2 i b (E p.1)
  let V:= U ×ˢ (univ : Set Ortho)
  have hf (i b) : ContinuousOn (f i b) V := survey_on M (A:= A ∘ Prod.fst)
    (h.use (fun (_:W×Ortho) (h : _ ∈ V)=> h.1) continuousOn_fst) (fun t ht=> hA _ ht.1) continuousOn_snd i b -- maps binder implicit
  let θ (a:Bool) (t:W) := ∫ s:Ortho, M.rotation.act d s ((TS d).decode (fun i=> (if a then star (f i a (t,s)) else f i a (t,s)))) ∂averageO
  have hθ (a:Bool) : ContinuousOn (θ a) U := by
    refine continuousOn_integral_of_compact_support isCompact_univ ?_ (by simp)
    let m (p:W×Ortho):= (TS d).decode (fun i=>if a then star (f i a p) else f i a p)
    apply M.continuousOn_act (s:=Prod.snd) (x:=m) continuousOn_snd
    refine ((TS d).decode.continuous_of_finiteDimensional).comp_continuousOn (continuousOn_pi.mpr fun i=>?_)
    change ContinuousOn (fun p : W×Ortho=> if a then star (f i a p) else f i a p) V
    cases a; · exact hf i false
    exact continuous_star.comp_continuousOn (hf i true)
  exact (ContinuousOn.smul (continuousOn_const (c:=(2:ℂ)⁻¹)) ((hθ false).add ((M.conjugation d).continuous.comp_continuousOn (hθ true)))).congr (fun t ht=> M.base_survey d ((h.widen hA).supported ht)) -- lambda v implicit clip A inst
end Devices
end YM.Contacts
