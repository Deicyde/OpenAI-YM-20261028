import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Armor

/-! # Polar coat respects the packed chart. W independent. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Armor
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Raw Matter Scroll Vine Polar Frond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {x : Site c} {X : Coat T F} {l m : ℕ} {k : Finset ℕ} {R : Rep G f} {Z : Support c}
variable {w v : Air f G} {u b : Directions G f} {a : ℝ} {U V : Config G f}
variable (H : Armor X a u U V) (p : Room P S T X.x)
include p H
lemma bast (k : Finset ℕ) (W : ℝ) (R : Rep G f) (Ñ : ChartRatio G) (A : Stores S) :
    stock X a R W Ñ u U k A=stock X a R W Ñ u V k A := by
  let Z:= A.dome (304*X.B); by_cases hz : X.enforce a u (X.plaza Z)=0
  · unfold stock; split <;> dsimp only [Z] at hz <;> simp [hz]
  have hv:= X.covering H.pulse (X.plaza Z) u (fun i hi he=> hz (Finset.prod_eq_zero hi he)); have hp := H.heading Z (by rw [hv]; norm_num)
  have hb x d (he : d≤301*X.B) (hh : Inside x A d) : AgreeNear S.ratio.parent x X.B U V := fun j hj=> hp j
    (touch_extend hh (by change separation x (atEdge S j) ≤ _ at hj; omega))
  have hh : plumeLog X a R Ñ u U A=plumeLog X a R Ñ u V A := by
    unfold plumeLog
    suffices he : chalky X u U A=chalky X u V A by rw [he]
    apply congr_arg averaged; funext s; apply sum_congr rfl; intro i hi; exact Armor.roots X p s i (hb _ _ (by exact
      (show 200*X.B ≤ 301*X.B by omega)) ((rotates_dome ..).mp (mem_filter.mp hi).2)) _
  have hf: 100≤X.B ∧ 4*X.R+4+predReach S.patch≤X.B/100 := p.sight
  let Y:=A.dome (300*X.B)
  have hF i (hi:i∈readFine Y S) : Mask.fine A X.χ i X.t U=Mask.fine A X.χ i X.t V := by
    obtain ⟨x,hx,ht⟩:= Finset.not_disjoint_iff.mp (mem_filter.mp hi).2; let o:= S.ratio.parent i.1
    have hc : AgreeNear S.ratio.parent o 4 U V := (hb x (300*X.B) (by omega) hx).shrink
      (by rw [separation_comm]; have hh: separation o x ≤ 1 := Packets.price_one S (.inl i) x ht; omega)
    simp only [Mask.fine,toll,LocalRows.facesight _ (parent_step S) U V i hc]
  have hs i (hi:i∈ readBonds Y) : pinMass U X.k i=pinMass V X.k i ∧ Mask.noise A X.χ i X.t W U X.k X.V=Mask.noise A X.χ i X.t W V X.k X.V := by
    obtain ⟨x,hx,ht⟩:=Finset.not_disjoint_iff.mp (mem_filter.mp hi).2
    obtain ⟨hk,hP⟩:= (Emblems.choices U V i X.k X.k (funds_branch p.accepted) rfl rfl rfl ((hb x (300*X.B) (by omega) hx).shrink
      (by rw [separation_comm]; have h : separation i.1 x ≤ 1 := Packets.price_one S (.inr (.inl i)) x ht; omega))).2
    exact ⟨hk,by unfold Mask.noise wire; rw [hP]⟩
  have hm i (hi:i∈Y) : siteMass U X.k i=siteMass V X.k i := (Emblems.frames_agree U V i _ _ (funds_branch p.accepted) rfl
    ((hb i (300*X.B) (by omega) hi).shrink (by rw [separation_self]; omega))).2
  unfold stock; rw [hh]; unfold tickets Contract.order profiles; dsimp only
  rw [prod_congr rfl (fun i (hi:i∈ vias S A (300*X.B))=> unveils X (k:=k) p i (hb _ _ (by
    exact (show 300*X.B ≤ 301*X.B by omega)) (mem_filter.mp hi).2) R), prod_congr rfl hm,
    prod_congr rfl (fun i hi=> (hs i hi).1), prod_congr rfl hF, prod_congr rfl (fun i hi=> (hs i hi).2)]
  -- X.t

lemma reeled (W : ℝ) (Ñ : ChartRatio G) (k : Finset ℕ) (l : ℕ) (h : Intake P T X.x R) (i : Head S) (z : Air f G) :
    ember X a R W Ñ u U z k l i=ember X a R W Ñ u V z k l i := by
  unfold ember; rcases i with i|i|i|i
  · simp only [Sum.elim,H.bast ‹_› k W R Ñ i]
  · unfold sheath; dsimp only [Sum.elim]; by_cases he : X.enforce (2*a) u (X.plaza (forcedFoot S.ratio 0 X.B R i))=0
    · rw [he,mul_zero,mul_zero]
    exact congrArg (·*X.enforce (2*a) u (X.plaza (forcedFoot S.ratio 0 X.B R i))) (UsesFinal.allReads _ _ _ (h.cap.labels.forced.reads i) _ _ (H.venial _ he))
  · suffices hv : logMoment X a R Ñ u U z i=logMoment X a R Ñ u V z i by simp only [Sum.elim,hv]
    rcases i with i|i|i
    · exact H.uplinks ‹_› h _
    · change whelp _ _ _ _ _ _ _=whelp _ _ _ _ _ _ _; unfold whelp; rcases i with i|i|i <;> simp only [Sum.elim]
      exact H.motives ‹_› _ _
    simp only [logMoment,Sum.elim]
  unfold Polar.sprinkle; cases i <;> simp only [Sum.elim]
  exact H.foreign _ ‹_› _ k _
end YM.ConnectedActivityE6.Blaze.Armor
