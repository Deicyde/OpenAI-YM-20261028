import YM.Extra.ITERATION_NO_LOSS.ComplexDerivs
import YM.Next.SCHEDULE.Stadium
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Folios
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Postage
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Voice

/-! Physical, unmarked gates. Keep q decisions even for still-owned
incoming sites; every coarse-frame likelihood (inclusive of denominators)
retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Voice.Check
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussian.Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify
variable {G : Gauge} {c f : Side} {S : StepData c f} (D : AnalyticBridge.LocalGaussian.Desk G S)
local notation "s₀" => D.betaHat
local notation "B" => radiusB D.betaHat

inductive Test (c f : Side) : Type
  | fine (i : Cell f)
  | noise (i : Bond c)
  | void (i : Site f)
  | frame (i : Site c)
  | predictor (i : Bond c)
  | screen (i : Bond f)

instance : Finite (Test c f) := by
  let t : Cell f ⊕ Bond c ⊕ Site f ⊕ Site c ⊕ Bond c ⊕ Bond f → Test c f := Sum.elim Test.fine (Sum.elim Test.noise
    (Sum.elim Test.void (Sum.elim Test.frame (Sum.elim Test.predictor Test.screen))))
  apply Finite.of_surjective t
  rintro (i|i|i|i|i|i)
  · exact ⟨.inl i,rfl⟩
  · exact ⟨.inr (.inl i),rfl⟩
  · exact ⟨.inr (.inr (.inl i)),rfl⟩
  · exact ⟨.inr (.inr (.inr (.inl i))),rfl⟩
  · exact ⟨.inr (.inr (.inr (.inr (.inl i)))), rfl⟩
  · exact ⟨.inr (.inr (.inr (.inr (.inr i)))), rfl⟩

-- at all touched projections (either end), deterministic even at
-- unrealized queries
def post (S : StepData c f) (i : Test c f) : Support c := match i with
  | .fine i=> startPos S i
  | .noise i=>pinPos i
  | .void i=> (inspected {i}).image S.ratio.parent
  | .frame i=>{i}
  | .predictor i=>pinPos i
  | .screen i=> (pinPos i).image S.ratio.parent

def location (S : StepData c f) : Test c f→Site c
  | .fine i=>S.ratio.parent i.1
  | .noise i=>i.1
  | .void i=>S.ratio.parent i
  | .frame i=>i
  | .predictor i=>i.1
  | .screen i=>S.ratio.parent i.1

lemma at_post (i : Test c f) : location S i ∈ post S i := by
  cases i with
  | fine i=>exact Finset.mem_image_of_mem _ (Work.E01.base_touched i)
  | void i=>exact Finset.mem_image_of_mem _ (Finset.mem_union_left _ (Finset.mem_singleton_self i))
  | screen i=>exact Finset.mem_image_of_mem _ (Finset.mem_insert_self ..)
  | _ => simp [post,location,pinPos]

def films (i : Test c f) : Formula G S ℝ := fun F A b k V p=>
    let u:= chosen D F k A k
    let U:=skin D F A b k V p
    match i with
    | .fine i=>u.fineBit i U
    | .noise i=>u.noiseBit i V U
    | .void i=>D.qVoid b i U
    | .frame i=>u.frameBit i U
    | .predictor i=>u.connectorBit i U
    | .screen i=> if Physical.openBond A F s₀ i then broad D.broadCut D.radius (aura D F A b k V p i) else 1 -- padded unit

abbrev custody (i : ℕ) := (inspected (D.labels.forced i).support).image S.ratio.parent

def cargo (i : ℕ) : Formula G S ℝ := fun F A b k V p=>D.labels.K i (skin D F A b k V p)

def historical (g : Spot D) {b : Finset ℕ} : g.Gates b → Test c f ⊕ ℕ
  | .inl (.inl i)=>.inl (.fine i)
  | .inl (.inr (.inl i))=>.inl (.noise i)
  | .inl (.inr (.inr (.inl i)))=>.inl (.frame i)
  | .inl (.inr (.inr (.inr (.inl i))))=>.inl (.predictor i)
  | .inl (.inr (.inr (.inr (.inr i))))=>.inl (.screen i.val.val)
  | .inr (.inl i)=>.inr i.val
  | .inr (.inr i)=>.inl (.void i)

lemma admits (u : Spot D) {b : Finset ℕ} : Injective (historical D u (b:=b)) := by
  rintro ((i|i|i|i|i)|i|i) ((j|j|j|j|j)|j|j) hj <;>
    simp only [historical,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq,Test.fine.injEq,Test.noise.injEq,
      Test.frame.injEq,Test.void.injEq,Test.screen.injEq,Test.predictor.injEq,Subtype.val_inj] at hj ⊢ <;> first | exact hj.elim | exact hj

theorem true_gate (h : Route.Badge.App D) (F : Forest S.ratio) (A : Stores S) (k k₀ : S.Choices) (V : Config G c) (b : Finset ℕ)
    (hv : A.flags=RG.flags (temp D.betaHat) V) (p : Refs G f) (i : (chosen D F k₀ A k).Gates b) :
    let u := chosen D F k₀ A k
    u.gate b i V (Print.see s₀ A F p)=Sum.elim (fun j=>films D j F A b k V p) (fun j=>cargo D j F A b k V p) (historical D u i) := by
  intro u
  obtain ⟨C,hC⟩:=h.earns A F V hv; obtain ⟨η,hη,hP⟩:=h.gaps A F V k hv
  have he := Print.painted D.tube s₀ D.broadCut D.radius D.g k V h.aperture hC hη hP p
  have hl : skin D F A b k V p = u.hard V (Print.see s₀ A F p):= he
  rcases i with (i|i|i|i|i)|i|i
  all_goals simp only [Spot.gate,Spot.test,historical,Sum.elim_inl,Sum.elim_inr,cargo,films]
  · simp only [hl,fineBit,chosen,Route.Badge.camera,u]
  · simp only [hl,noiseBit,chosen,Route.Badge.camera,u]
  · simp only [hl,frameBit,chosen,Route.Badge.camera,u]
  · simp only [hl,connectorBit,chosen,Route.Badge.camera,u]
  · rw [if_pos (show Physical.openBond A F s₀ i.val.val from ⟨i,rfl⟩)]
    exact congr_arg (broad D.broadCut D.radius) (Print.tinting D.tube s₀ D.broadCut D.radius D.g k i V h.aperture hC hη hP p).symm
  · exact congr_arg (D.labels.K i.val) hl.symm
  exact congr_arg (D.qVoid b i) hl.symm

set_option maxHeartbeats 600000 in
lemma film (h : Route.Badge.App D) (i : Test c f) : Care D (post S i) (films D i) := by
  obtain ⟨P,hP⟩:=h.valid.funds
  obtain ⟨a,c₀,v,w,r,hR⟩:=h.valid.lawful
  constructor
  · intro F A b k
    let U (z : Config G c × Refs G f) := skin D F A b k z.1 z.2
    have ht : Measurable U := Print.printed_meas D.tube s₀ D.broadCut D.radius D.g hP k A F h.valid.positive h.enough
    have hm {f : Config G c × Refs G f → ℝ} (d : ℝ) (h : Measurable f) : Measurable (fun z=>D.profile.innerShare d (f z)) :=
      D.profile.smooth.continuous.measurable.comp ((h.div_const _).pow_const _)
    cases i with
    | fine i=>
      unfold uncurry films; dsimp only [fineBit,chosen,Route.Badge.camera]
      split
      · exact measurable_const.sub (hm _ (toll_meas i ht))
      exact hm _ (toll_meas i ht)
    | noise i=>
      unfold uncurry films; dsimp only [noiseBit,chosen,Route.Badge.camera]
      have hw : Measurable (fun z : Config G c × Refs G f => wire (S.prediction (U z) k) z.1 i) := wire_meas k i h.aperture.branched ht measurable_fst
      split
      · exact measurable_const.sub (hm (D.W*fiery G D.betaHat S.patch.L) hw)
      exact hm (D.W*fiery G D.betaHat S.patch.L) hw
    | void i=>
      change Measurable (fun z => D.qVoid b i (U z))
      unfold Desk.qVoid
      by_cases he : i∈D.Owners b
      · simp only [he,true_or,↓reduceIte]; exact measurable_const
      simp only [he,false_or]
      exact Measurable.ite (ht ((RG.flags_open i _).measurableSet.compl)) measurable_const measurable_const
    | frame i=>
      unfold uncurry films; dsimp only [frameBit,chosen,Route.Badge.camera]
      have hf : Continuous (fun z : Config G f=>expandAt (S.ratio.embed i) z) := by unfold expandAt; fun_prop
      have hr : Measurable (fun z=> expandAt (S.ratio.embed i) (U z)) := hf.measurable.comp ht
      have hu := (S.patch.frameMass_meas (C:=S.kernel) (G:=G) (k.1 i)).comp hr
      exact (measurable_const (a:=(Fintype.card S.patch.FrameTag : ℝ))).mul hu
    | predictor i=>
      unfold uncurry films; dsimp only [connectorBit,chosen,Route.Badge.camera]
      have hi := ((S.patch.predictorMass_meas (G:=G) (C:=S.kernel) (k.2 i)).comp (S.connector_meas h.aperture.branched k.1 i)).comp ht
      exact (measurable_const (a:=(Fintype.card S.patch.Points : ℝ))).mul hi
    | screen i=>
      by_cases fl : Physical.openBond A F s₀ i
      · unfold films uncurry; dsimp only; simp_rw [if_pos fl]
        exact (broad_smooth _ _).continuous.measurable.comp
          (Print.shade_meas D.tube D.betaHat D.broadCut D.radius D.g hP k A F h.valid.positive h.enough i)
      unfold films uncurry; dsimp only; simp_rw [if_neg fl]; exact measurable_const
  intro F F' A A' b b' k k' V V' p p' H
  let X:=post S i; let o:=location S i
  let U:=skin D F A b k V p; let U':=skin D F' A' b' k' V' p'
  have hB:=h.aperture.scale
  have hv : Shields (ambient D X) o (40*B) := covers_shield _ (at_post i)
  have he : AgreeNear S.ratio.parent o (14*B) U U':=daily D h H o (at_post i)
  have hf := Geo.Reads.visit H.fields (r:=B) (hv.shrink (by omega)); have hl := Geo.Reads.way H.fields (r:=B) (hv.shrink (by omega))
  have hi {i j : Site c} (ht : separation o i≤1) : TagNe S i 1 k k' := TagNe.close o B k k' hl (by omega)
  have hr {j : Bond c} : j.1=o → (frameRate S k U j.1=frameRate S k' U' j.1 ∧ bondRate S k U j=bondRate S k' U' j) := fun hj=>
    rates_local h.aperture.branched k k' U U' j (hi (by rw [hj,separation_self]; omega) (j:=j.1))
      (by rw [hj]; exact anchored he (by have := h.aperture.visits; omega))
  cases i with
  | void i=>
    have hg := H.owners i (halo_subset _ X (at_post (S:=S) (Test.void i)))
    have hy := flags_agree D.input.p.threshold U U' {i} (ink D h H (Finset.Subset.refl _))
    change D.qVoid b i U=D.qVoid b' i U'
    unfold Desk.qVoid
    have hk : i∈RG.flags D.input.p.threshold U ↔ i ∈ RG.flags D.input.p.threshold U' := by
      have hh := iff_of_eq (congr_arg (fun t : Finset (Site f)=> i∈t) hy)
      simpa only [Finset.mem_inter,Finset.mem_singleton_self,true_and] using hh
    simp_rw [propext hg,propext hk]
  | fine i=>
    unfold films; dsimp only; unfold fineBit
    have hk := H.fields.cost i (show startPos S i⊆ ambient D X from halo_subset ..)
    have hm := congr_arg G.chord (face_near (Work.E03.parent_step S) i U U' (anchored he (by omega)))
    unfold toll
    dsimp only [chosen, Route.Badge.camera,U,U'] at hk hm ⊢
    simp only [hk,hm]; split_ifs <;> rfl
  | noise i=>
    unfold films; dsimp only; unfold noiseBit
    have hk := H.fields.aisle i (show pinPos i ⊆ ambient D X from halo_subset ..)
    have hm := transmission D.tube D.betaHat U U' k k' h.aperture i (anchored he (by omega)) hl
    have hn : V i=V' i := hf i (by change separation o o ≤ B; simp)
    unfold wire
    dsimp only [chosen,Route.Badge.camera,U,U'] at hk hm ⊢
    simp only [hk,hm,hn]; split_ifs <;> rfl
  | frame i=> exact (hr (j:=(i,(0:Axis))) rfl).1
  | predictor i=>exact (hr (j:=i) rfl).2
  | screen i=>
    have hx:=floor_reach D (e:=i) (Y:=X) (at_post (S:=S) (Test.screen i)) (by change separation _ _ ≤ _; rw [show location S (Test.screen i)=portOf S i from rfl,separation_self]; omega) hB
    have hQ:=dress D h H hx.1 hx.2
    unfold films; dsimp only; rw [hQ.1,hQ.2.2]

lemma packed (h : Route.Badge.App D) (i : ℕ) : Care D (custody D i) (cargo D i) := by
  obtain ⟨P,hP⟩:=h.valid.funds
  obtain ⟨a,c,v,w,r,hR⟩:=h.valid.lawful
  have hp := hR.labels.forced.reads i
  constructor
  · intro F A b k; exact (hR.labels.forced.meas i).comp (Print.printed_meas D.tube D.betaHat D.broadCut D.radius D.g hP k A F h.valid.positive h.enough)
  intro F F' A A' b b' k k' V V' p p' H
  have he := ink D h H (Z:=inspected (D.labels.forced i).support) (Finset.Subset.refl _)
  exact hp _ _ (agrees_mono he (fun w hx => Finset.mem_union_left _ hx)) (flags_agree _ _ _ _ he)
end YM.PhysicalNext.Dictionary.Voice.Check
