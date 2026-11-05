import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Lighting


/-!
# Direct passage to the tag integrals for a *Rank* column

Literal reweighting `spooled`, including true Jacobian,
chartCost, noise likelihood; tagRef times forest-site weights in the
probability formula. Pay once (do NOT put a separate guard cost in this
truth transform for each W). We won't divide the W insertions by the
incoming Rep, which can carry forced parts. Works all indicated
Lantern/forest choices throughout, not an identity a.e. in V. This is
before any bounds on density/remainder. Using SectorMeasure library,
apply without the original geometry's spent `Ready` or flag sizes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station Peak Ac Thirst Glyph
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    AnalyticBridge.GaussianFieldAlignment.Locations SectorNext.Vacuum
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (T : Tube G S) (F : Lantern G S) (J : ChartRatio G) {x w : ℝ} (D : Allocation G S x w) (β : ℝ)

/-- Permissions for this step; post-L. -/
def Coupler : Prop := ∀ A (k : Streak F.park) V, A.flags=RG.flags (temp x) V →
    Permitted x V k.tag A k.wood D J F.hood β (palette T A k.wood k.tag x V .endpoint)
       (portrait T A k.wood k.tag x V .endpoint F.χ F.hood)
-- Buy on any S,Teller and outputs on this post-L. no choice of V.
variable {D}
lemma coupling_issue (P : Teller G) (hJ : LocalRatio J)
    (Q : Patch) (hB : Q.Branches P.bind G) (w : ℝ) (hw : 0<w) :
    ∃ a, 0 < a ∧ ∀ᶠ x in atTop, 0 < a*fiery G x Q.L ∧ 2*(a*fiery G x Q.L) < firstRadius G ∧
      ∀ (c f) (S : StepData c f) (T : Tube G S), S.patch=Q → 100*(1+radiusB x) ≤ c.val → P.Funds S T →
      ∀ (F : Lantern G S), F.hood=a*fiery G x Q.L → ∀ (D : Allocation G S x w) β, 0<β → Coupler T F J D β := by
  obtain ⟨C,E,hA,-,H⟩ := sponsored_permit P J hJ Q hB w hw; refine ⟨C,hA,?_⟩
  filter_upwards [H] with x hx
  obtain ⟨-,hh,ht,-,h⟩ := hx
  refine ⟨hh,ht,fun c f S T hs hp hz F hf D β hb A k V he => ?_⟩
  rw [← Q_endpoint,← mean_endpoint,hf]
  exact (((h c f S T hs hp hz).2.2 A k.wood k.tag V D F.χ).2 he β hb).1
variable (D)
section Coat
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def spooled (g : Config G f→X) (A : Stores S) (k : Streak F.park) (V : Config G c) (Y : RoomView A x k.wood G) : X :=
    let U (p : Config G f) := S.noise β (S.prediction p k.tag) V • g p
    let b:=coupling β
    let Q:= palette T A k.wood k.tag x V .endpoint
    (Fintype.card S.Choices : ℝ) • (J.scale ^ Fintype.card (Active A x k.wood) * chartCost Q b) •
       Real.exp (force Q Y.2/2) • regularized D A k.wood V k.tag F.χ J F.hood U Y.1
         (displaced (portrait T A k.wood k.tag x V .endpoint F.χ F.hood Y.1) b Y.2)
variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompleteSpace X]
-- needing the result for poly arguments, not assuming the probability
-- estimate on opened r; masks tested here and preserved.
omit [CompleteSpace X] in
private theorem integrable_price {Z : Type*} [MeasurableSpace Z] {A : Type} [DecidableEq A] [Fintype A]
    (b : ℝ) (M : Measure Z) [SigmaFinite M] (m : Z → Prices G A)
    (Q : Gaussian.Table (A×G.ColorIndex)) (r : Z → LogArray G A → X) (hm : Measurable m) (hr : Measurable (uncurry r))
    (hh : Q.PosDef) (hb : 0<b) (hy : ∀ Y, Integrable (r Y)) (hπ : Integrable (fun Y=>∫ a, ‖r Y a‖) M) :
    let v Y (z : Prices G A) := Real.exp (force Q z/2) • r Y (displaced (m Y) b z)
    Integrable (uncurry v) (M.prod (cloud Q)) ∧
      (∫ y, (∫ a, r y a) ∂M) = chartCost Q b • ∫ y, uncurry v y ∂(M.prod (cloud Q)) := by
  intro v
  let C:= chartCost Q b
  have H : 0<C:= chartCost_pos Q hh hb
  have hs Y : Integrable (v Y) (cloud Q) ∧ (∫ a,r Y a) = C • ∫ z,v Y z ∂cloud Q :=
    ⟨(at_price Q hh hb (m Y) (r Y)).1.mp (hy Y),(at_price Q hh hb (m Y) (r Y)).2⟩
  have hi : Integrable (uncurry v) (M.prod (cloud Q)) := by
    have hv : Measurable (uncurry v) := by
      let σ (x : Z×Prices G A) := (x.1, displaced (m x.1) b x.2)
      have hs : Measurable σ:= measurable_fst.prodMk (tape.measurable.comp ((hm.comp measurable_fst).add (by fun_prop)))
      have hf : Continuous (fun z : Prices G A => force Q z) := by unfold Gaussian.force dotProduct mulVec; fun_prop
      change Measurable (fun x : Z×Prices G A=> Real.exp (force Q x.2/2) • r (σ x).1 (σ x).2)
      exact (Real.continuous_exp.measurable.comp ((hf.measurable.comp measurable_snd).div_const _)).smul (hr.comp hs)
    apply (integrable_prod_iff hv.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall fun Y=> (hs Y).1,?_⟩
    have he Y : (∫ a, ‖r Y a‖) = C * ∫ z, ‖v Y z‖ ∂cloud Q := by
      rw [(at_price Q hh hb (m Y) (fun a=>‖r Y a‖)).2]; unfold C v
      simp only [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le,smul_eq_mul]
    simp_rw [he] at hπ
    have hp := hπ.const_mul C⁻¹; simp_rw [←mul_assoc,inv_mul_cancel₀ H.ne',one_mul] at hp; exact hp
  refine ⟨hi,?_⟩; rw [integral_prod _ hi]
  simp_rw [fun y => (hs y).2,integral_smul]; rfl

lemma prepaid (ht : S.patch.Branches S.kernel G) (g : Config G f→X) (hg : Envelope g) (A : Stores S) (k : Streak F.park) (V : Config G c)
    (he : A.flags=RG.flags (temp x) V) (hp' : Coupler T F J D β) :
    let L:=k.wood
    let f:=spooled T F J D β g A k V
    let μ:= viewer T A x L k.tag V
    Integrable f μ ∧ (∫ a, D.portion A L V (through S L β V (fun _ a=>g (L.drape a))) k.tag a ∂L.order G) = tagRef k.tag • ∫ y, f y ∂μ := by
  intro L f' μ
  let U (p : Config G f) := S.noise β (S.prediction p k.tag) V • g p
  have hu : Envelope U := Env.scale (env_noise S β (V:=fun _=>V) (S.prediction_meas ht k.tag) measurable_const) hg
  let A' := Active A x L; let F' := Frozen A x L; let b:=coupling β
  let Q := palette T A L k.tag x V .endpoint; let p Y:= portrait T A L k.tag x V .endpoint F.χ F.hood Y
  let r:= regularized D A L V k.tag F.χ J F.hood U; let c' := chartCost Q b; let w' := J.scale ^ Fintype.card A'
  let v Y (z : Prices G A') := Real.exp (force Q z/2) • r Y (displaced (p Y) b z)
  have hp:= hp' A k V he
  have hb : 0<b := coupling_pos hp.bpos; have H : 0<c' := chartCost_pos Q hp.nativePos hb
  obtain ⟨-,hy,hπ,-,HH⟩ := regularized_price D A L V k.tag hp.trueChart F.χ hp.doorPos hp.scalePaid hp.core U ht hu
  obtain ⟨hi,hj'⟩:=integrable_price b (piHaar G F') p Q r hp.shift
    (regularized_meas D A L V k.tag hp.trueChart F.χ hp.doorPos hp.scalePaid U ht hu) hp.nativePos hb hy hπ
  change (∫ y,(∫ a, r y a) ∂_) = c' • ∫ y, uncurry v y ∂μ at hj'
  have hj : D.portion A L V (through S L β V (fun _ a=>g (L.drape a))) k.tag=attending D A L V k.tag U:= by
    funext a
    unfold Allocation.portion Push.SectorMeasure.through U attending taggedKernel; rw [mul_smul,mul_smul]
  refine ⟨(hi.smul (w'*c')).smul (Fintype.card S.Choices:ℝ),?_⟩
  rw [hj,HH]
  change w' • (∫ y, (∫ a, r y a) ∂piHaar G F') = tagRef k.tag • ∫ y, (Fintype.card S.Choices:ℝ) • (w'*c') • uncurry v y ∂μ
  haveI : Nonempty S.Choices := ⟨k.tag⟩; have hk' : 0 < (Fintype.card S.Choices:ℝ) := by exact_mod_cast Fintype.card_pos
  rw [hj',integral_smul,integral_smul,smul_smul,smul_smul,tagRef,inv_mul_cancel₀ hk'.ne',one_smul]

/-- Direction of reading. Only omit wrong-flag sectors after allocation
identity. Uses `temp` at the recording x. -/
theorem arriving (ht : S.patch.Branches S.kernel G) (g : Config G f→X) (hg : Envelope g) (hy : GaugeInvariant g)
    (hp' : Coupler T F J D β) (V : Config G c) : S.push β g V = ∑ A : Stores S,
      if A.flags=RG.flags (temp x) V then ∑ k : Streak F.park, k.share • ∫ y, spooled T F J D β g A k V y ∂viewer T A x k.wood k.tag V else 0 := by
  have hi : Integrable g (prior G f) := by
    obtain ⟨hm,C,hC⟩:=hg; exact Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hC)
  have hv (t : F.park.Seeds) : S.push β g V = ∑ A : Stores S,
      if A.flags=RG.flags (temp x) V then ∑ k:S.Choices, tagRef k • ∫ y, spooled T F J D β g A ⟨t,k⟩ V y ∂viewer T A x (F.park.grow t) k V else 0 := by
    rw [← push_columns D (F.park.grow t) β g ht hi hy V]
    refine Finset.sum_congr rfl fun A _ => ?_
    unfold output Allocation.column tagTotal
    split_ifs with H
    · exact Finset.sum_congr rfl fun k _ => (prepaid T F J D β ht g hg A ⟨t,k⟩ V H hp').2
    have h (k : S.Choices) (U : Config G f) : D.bill A k U V=0:= not_not.mp fun hu=> H (D.actual _ _ _ _ hu).exactFlags
    simp [Allocation.portion,h]
  let v (t : F.park.Seeds) (A : Stores S) := if A.flags=RG.flags (temp x) V then ∑ k:S.Choices, tagRef k • ∫ y, spooled T F J D β g A ⟨t,k⟩ V y ∂viewer T A x (F.park.grow t) k V else 0
  calc
    _=∑ _t:F.park.Seeds, F.park.solo • S.push β g V:= by rw [← Finset.sum_smul,F.park.solo_one,one_smul]
    _=∑ t:F.park.Seeds,∑ A,F.park.solo • v t A:= Finset.sum_congr rfl fun t _=> by rw [show S.push β g V=∑ A,v t A from hv t,Finset.smul_sum]
    _=_:= by
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun A _ => ?_
      split_ifs with H; swap; simp [v,H]
      simp_rw [v,if_pos H,Finset.smul_sum,smul_smul]
      symm; rw [← Equiv.sum_comp (Streak.entered S F.park).symm (fun k:Streak F.park => k.share • ∫ y, spooled T F J D β g A k V y ∂viewer T A x k.wood k.tag V),Fintype.sum_prod_type]; rfl
end Coat
end YM.PhysicalNext.InteractingRank
