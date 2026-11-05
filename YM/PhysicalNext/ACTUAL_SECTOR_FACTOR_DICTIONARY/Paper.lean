import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Legends

/-! Locality of every log in this dictionary. One can enlarge also for
queries of its eligibility (separate accounting before gathering).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Voice
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussian.Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify
variable {G : Gauge} {c f : Side} {S : StepData c f} (D : AnalyticBridge.LocalGaussian.Desk G S)
    (h : Route.Badge.App D) {F F' : Forest S.ratio} {A A' : Stores S} {V V' : Config G c} {k k' : S.Choices}
local notation "y₀" => D.betaHat
local notation "B" => radiusB D.betaHat
local notation "T" => D.tube

lemma zap {R : Type*} [Zero R] {X : Support f} {H : Config G f → R} (hC : LocalOn X H)
    {s : ℝ} {U V : Config G f} (ht : Agrees (inspected X) U V) : masked s X H U=masked s X H V :=
  -- masking lemma in Paths private
  by
    have hp := flags_agree s U V X ht
    by_cases hr : Healthy s X U
    · rw [masked_eq s X H U hr,masked_eq s X H V (by
        unfold Healthy at *; simpa only [disjoint_iff_inf_le, Finset.inf_eq_inter,hp] using hr)]
      exact hC U V (agrees_mono ht fun i hi=> Finset.mem_union_left _ hi)
    rw [masked_ne s X H U hr,masked_ne s X H V (by unfold Healthy at *; simpa only [disjoint_iff_inf_le, Finset.inf_eq_inter,hp] using hr)]

omit h in
private lemma collapse {X : Support c} (h : Physical.Reads X A A' F F' V V' k k') (V V' : Config G c)
    (hv : Agrees X V V') (A : Stores S) : Physical.Reads X A A F F' V V' k k' :=
  ⟨hv,h.frame,h.bond,h.tree,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl,fun _ _=>Iff.rfl⟩

include h

set_option maxHeartbeats 800000 in
lemma local_series (i : ListID S) : Care D (Voice.native D i) (sew D i) := by
  obtain ⟨P,hP⟩:=h.valid.funds
  obtain ⟨a,xω,v,w,r,hR⟩:=h.valid.lawful
  cases i with
  | row i=>exact coin_care D h i
  | opened i=>exact supplied D h i
  | thin i=>exact (dispatch D h 0 i).follows (fun p:ℝ=> -(slip^2*p)/D.g^2) (by fun_prop)
  | surge i=>exact smoky_care D h i
  | glaze i=>
    constructor
    · intro F A b k; unfold uncurry sew; dsimp only; split
      next _ =>
        exact (logGuard_smooth _ h.valid.ratio h.valid.positive h.valid.charted).continuous.measurable.comp
          (Print.shade_meas T D.betaHat _ _ _ hP k A F h.valid.positive h.enough i)
      exact measurable_const
    intro F F' A A' b b' k k' V V' p p' H
    have hx := floor_reach D (o:=portOf S i) (Y:=native D (.glaze i)) (Finset.mem_singleton_self _) (e:=i) (by
      rw [separation_self]; omega) h.aperture.scale
    have hf := dress D h H hx.1 hx.2
    unfold sew; dsimp only; rw [hf.2.2, hf.1]
  | deficit i=>
    refine ⟨fun F A _ _ => measurable_const (a:=if Print.winter y₀ A F i then -Real.log (spare D.chart D.input.beta) else 0),?_⟩
    intro F F' A A' b b' k k' V V' p p' H
    unfold sew; dsimp only; rw [Print.winter_read y₀ H.fields i h.aperture.scale ((covers_shield (40*B) (Finset.mem_singleton_self _)).shrink (by omega))]
  | spark i j n=>
    by_cases hp : n∈Set.range (barcode (Sequence (Bond f)))
    · obtain ⟨z,rfl⟩:=hp
      constructor
      · intro F A b k; unfold sew uncurry; dsimp only; unfold chainBuy; split
        next _=>
          have hm (i : Bond f) (j:G.ColorIndex) : Measurable (fun p : Config G c × Refs G f=>p.2.2 i j) := by
            have hh : Continuous (fun y : G.Color=>y j) := PiLp.continuous_apply ..
            exact hh.measurable.comp ((measurable_pi_apply i).comp ((measurable_snd (α:=Config G f)).comp (measurable_snd (α:=Config G c))))
          refine Finset.measurable_fun_sum _ fun u _=>Finset.measurable_fun_sum _ fun s _ => ?_
          simp_rw [Notify.charged]
          have ht : Measurable (fun V=>itinerary D F A k V (i,u) (j,s) z) := Finset.measurable_fun_sum _
            (fun i _ => Notify.Typeset.lead (fun i j=>Wires.beam_meas T k y₀ A F i j h.aperture.branched) (Wires.cloudX_meas T _ k A F h.aperture.branched) _ _ _)
          exact ((hm i u).mul ((ht.comp measurable_fst).mul (hm j s))).div_const _
        exact measurable_const
      intro F F' A A' b b' k k' V V' p p' H
      let X:= Voice.native D (.spark i j (barcode _ z))
      have ht : portOf S i∈X := Finset.mem_insert_self ..
      have hs : portOf S j∈X := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
      have hy := oxygen D h H i ht; have hv := oxygen D h H j hs
      unfold sew chainBuy; dsimp only; simp_rw [propext hy.2, propext hv.2, Notify.charged, hy.1,hv.1]
      unfold itinerary
      have hq : walkLens S B i j z ⊆ ambient D X := by
        unfold X Voice.native offset; dsimp only; rw [placed]; exact fun t hl=>halo_subset _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hl))
      simp_rw [fun u s=>Notify.strand_law T h.aperture (i,u) (j,s) z hq H.fields]
    refine (show sew D (.spark i j n)=(fun _ _ _ _ _ _=>0) from ?_) ▸ Care.constant 0
    ext; unfold sew chainBuy; simp [Notify.unused _ _ hp]
  | folio n=>
    by_cases hp : n∈Set.range (barcode (Dots f))
    · obtain ⟨i,rfl⟩ := hp
      rw [show Voice.native D (.folio (barcode _ i))=columns D i from placed _ i]
      have he : sew D (.folio (barcode _ i))=fun F A b k V p=> -(1/2)*(dark D F A k V i) := by
        funext _ _ _ _ _ _; unfold sew; dsimp only; rw [Notify.charged]
      rw [he]
      let W:=Physical.windows S y₀ (G:=G)
      have ha (F : Forest S.ratio) (A : Stores S) (k : S.Choices) : Measurable (fun V => dots D F A k V i) := by
        cases i with
        | inl i=> exact Finset.measurable_fun_sum (Finset.univ:Finset G.ColorIndex) fun j _=> Notify.Typeset.first W (fun u v=> Wires.beam_meas T k y₀ A F u v h.aperture.branched) (i,j)
        | inr i=> exact Finset.measurable_fun_sum _ fun j _=>Notify.Typeset.article W (fun u v=> Wires.beam_meas T k _ A F u v h.aperture.branched) (Paint.hue i j)
      constructor
      · intro F A b k
        exact measurable_const.mul (((ha F A k).comp measurable_fst).sub (measurable_const (a:=dots D F _ k 1 i)))
      intro F F' A A' b b' k k' V V' p p' H
      let X:=columns D i
      have hf : Physical.Reads X A A' F F' V V' k k' := Geo.Reads.mono H.fields (halo_subset ..)
      have hl := collapse hf (1:Config G c) 1 (fun _ _ _=>rfl) (Push.SectorMeasure.voidStore S)
      have hz {A A' : Stores S} {V V' : Config G c} (ht : Physical.Reads X A A' F F' V V' k k') : dots D F A k V i=dots D F' A' k' V' i := by
        rcases i with i|i
        · simp only [dots,Sum.elim_inl,prime]; exact Finset.sum_congr rfl fun j _=>
            (Wires.positioned T h.aperture ht).local_value (show 15≤20 by omega) (i,j) (Finset.Subset.refl _)
        exact Notify.essay_law T h.aperture i (Finset.Subset.refl _) ht
      unfold dark; rw [Pi.sub_apply,hz hf,hz hl]; rfl
    refine (show sew D (.folio n)=(fun _ _ _ _ _ _=>0) from ?_) ▸ Care.constant 0
    ext; simp [sew,Notify.unused _ _ hp]
  | starboard n=>
    by_cases hp : n∈Set.range (barcode (Letter (Bond f) 0))
    · obtain ⟨i,rfl⟩ := hp
      rewrite [show Voice.native D (.starboard (barcode _ i))=inventory (portOf S) 20 B i from placed _ i]
      rewrite [show sew D (.starboard (barcode _ i))=fun F A b k V p=> (1/2)*(customs D F A k V i) from by funext; unfold sew; dsimp only; rw [Notify.charged]]
      constructor
      · intro F A _ k
        have ht : Measurable (fun V=> customs D F A k V i) := Finset.measurable_fun_sum _ fun u _=> Notify.Typeset.printing
          (Physical.windows S y₀ (G:=G)) (fun i j=>Wires.beam_meas T k _ A F i j h.aperture.branched) (Paint.hue i u)
        exact measurable_const.mul (ht.comp measurable_fst)
      intro F F' A A' b b' k k' V V' p p' H
      have ht := H.fields
      exact congr_arg _ (Notify.errata_law T h.aperture i (halo_subset ..) ht)
    refine (show sew D (.starboard n)=(fun _ _ _ _ _ _=>0) from ?_) ▸ Care.constant 0
    ext; simp [sew,Notify.unused _ _ hp]
  | letter i=>
    let Z:=D.labels.reg i
    have hp := hR.labels.regular.smooth i
    constructor
    · intro F A b k
      exact ((masked_measurable _ _ _ hp.borel).comp (Print.printed_meas T y₀ _ _ _ hP k A F h.valid.positive h.enough)).neg
    intro F F' A A' b b' k k' V V' p p' H; unfold sew; dsimp only; unfold Activities.regularOccurrence
    exact congr_arg Neg.neg (zap hp.sites (ink D h H (Z:=inspected Z.support) (Finset.Subset.refl _)))
end YM.PhysicalNext.Dictionary.Voice
