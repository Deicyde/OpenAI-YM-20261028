import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Shore
import YM.Work.F05.PiDensity

/-!
# On chart relative to real V

Use `Work.F05` argument only on Active link set. Keep X.Y ALL, including
probability on unused. Γ tautological while Allocation choose all profiles. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets Presented LabelSum Sector
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A W γ μ C : ℝ} {L : Side} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (X : Coat T F)

private def patch (Ñ : ChartRatio G) := Metric.ball (0:G.Color) Ñ.radius
private def native (P : ChartRatio G) (a : G.Color) := ENNReal.ofReal (P.scale * P.J a)
private def localP (V : G.El) (P : ChartRatio G) := (fun z : G.Color=> G.lieExp z*V) '' patch P
private def capP (Ñ : ChartRatio G) := Set.univ.pi fun i : X.Signal => localP (replica S.ratio X.V i.1.1) Ñ

private lemma exposing {P : ChartRatio G} (h : LocalRatio P) (V : G.El) :
    MeasurePreserving (fun a => G.lieExp a * V)
      ((volume.restrict (patch P)).withDensity (native P)) (G.probHaar.restrict (localP V P)) := by
  let L := MeasurableEquiv.mulRight V
  have hp : MeasurePreserving L G.probHaar G.probHaar := measurePreserving_mul_right _ _
  have hf : MeasurePreserving G.lieExp ((volume.restrict (patch P)).withDensity (native P))
      (G.probHaar.restrict (G.lieExp '' patch P)) := ⟨G.lieExp_cont.measurable,h.actual⟩
  have hk := L.restrict_map G.probHaar (localP V P)
  rw [hp.map_eq] at hk
  have he : localP V P = L '' (G.lieExp '' patch P) := Set.image_comp L G.lieExp _
  have hx : MeasurePreserving L (G.probHaar.restrict (G.lieExp '' patch P)) (G.probHaar.restrict (localP V P)) := by
    rw [hk, he,L.injective.preimage_image]; exact ⟨hp.measurable,rfl⟩
  exact hx.comp hf

private def rangeP (Ñ : ChartRatio G) := Set.univ.pi fun _ : X.Signal => patch Ñ
private def expandP (a : X.Signal→G.Color) := (fun i : X.Signal=> G.lieExp (a i)*replica S.ratio X.V i.1.1)

private lemma expansion {Ñ : ChartRatio G} (h : LocalRatio Ñ) : MeasurePreserving X.expandP
    ((volume.restrict (X.rangeP Ñ)).withDensity (fun y => ∏ i : X.Signal, native Ñ (y i)))
    (X.stages.restrict (X.capP Ñ)) := by
  let μ : Measure G.Color := volume.restrict (patch Ñ)
  have hm : volume.restrict (X.rangeP Ñ)=Measure.pi fun _ => μ := Measure.restrict_pi_pi ..
  haveI : SigmaFinite μ := by unfold μ; infer_instance
  have hv : Measurable (native Ñ) := (measurable_const.mul h.borel).ennreal_ofReal
  haveI : SigmaFinite (μ.withDensity (native Ñ)) := SigmaFinite.withDensity_ofReal _
  rw [hm, Work.F05.piDensity (fun _ : X.Signal=> μ) (fun _=>native Ñ) (fun _=>hv),stages,capP,Measure.restrict_pi_pi]
  exact measurePreserving_pi _ _ fun i : X.Signal=> exposing h (replica S.ratio X.V i.1.1)

/-- Signal rel extends Hot. Ghost on its own. -/
def tune (a : X.Signal→G.Color) : Directions G f := fun i => if h : X.Hot i then a ⟨⟨i,h.1⟩,h⟩ else 0

/-- Restricted comparison. -/
def seats := X.Signal→G.Color

def advance (X : Coat T F) : X.Signal≃X.tier where
  toFun := fun i=> ⟨i.1.1,mem_filter.mpr ⟨mem_univ _,i.2⟩⟩
  invFun := fun i=> ⟨⟨i.1,((mem_filter.mp i.2).2).1⟩,(mem_filter.mp i.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma regains (u) (i : X.Signal) : X.shifted u i.val=u i := by
  change (if h : X.Hot i.1.1 then u _ else _ )=_; exact dif_pos i.2
private lemma expend (a : X.Signal→G.Color) : X.view (X.tune a) = X.shifted (X.expandP a) := by
  funext i; by_cases h : X.Hot i.val
  · rw [show X.shifted (X.expandP a) i = X.expandP a ⟨i,h⟩ from X.regains _ ⟨i,h⟩,view, if_pos h,increment, tune, dif_pos h]; rfl
  rw [view, if_neg h]; symm
  change (if hh : X.Hot i.val then _ else X.Y i)=_; exact dif_neg h

/-- Borel scaled weight post-chart. -/
def inward (R : Rep G f) (Ñ : ChartRatio G) (W a : ℝ) (l : Finset ℕ) (u : Directions G f) :=
    (X.tangible R W (X.view u) l *Ñ.scale ^ X.tier.card)*Real.exp (∑ i∈X.tier, X.gentry Ñ a u i)*X.enforce a u X.tier

variable (K : Cash W X.x μ L Q o C T R) (hk : X.width=o.K)

include K hk in
lemma shoreside (l : Finset ℕ) :
    (∫ u,X.tangible R W (X.shifted u) l ∂X.stages)=∫ a : X.Signal → G.Color,X.inward R Q.table W o.a l (X.tune a) := by
  let P' := Q.table; have h := Q.table_exists
  have hb := K.laws.data; have hh := hb.covers; rw [← hb.funds.length_eq] at hh
  have hc := mul_pos o.large hb.room.fiery
  have hΔ : 2*o.a*X.t < P'.radius := by dsimp only [Coat.t,P']; nlinarith only [hc,hh]
  let s := X.capP Q.table
  let t := X.rangeP Q.table
  let f (u) := X.tangible R W u l
  have hX : MeasurableSet t := MeasurableSet.univ_pi (fun i => Metric.isOpen_ball.measurableSet)
  have he (u : F.Slice G) (hf : f u≠0) (i : X.Signal) : ∃ v∈patch P', ‖v‖≤o.a*X.t ∧
        (u i.val)=G.lieExp v*replica S.ratio X.V i.val.val := by
    rw [← F.off_tree u i.val]; exact X.licenses _ K hk hf _ i.2
  have hg z (hz : z ∉ s) : f (X.shifted z)=0 := by
    by_contra hp; apply hz; intro i _; obtain ⟨v,hv,-,he⟩ := he _ hp i
    exact ⟨v,hv, he.symm.trans (regains ..)⟩
  let g (a : X.Signal→G.Color) := X.inward R P' W o.a l (X.tune a)
  let ν (u : X.Signal → G.Color) := ∏ i : X.Signal,native P' (u i)
  have hM : Measurable ν := Finset.measurable_fun_prod _ fun i _=>
    ((show Measurable (native P') from (measurable_const.mul h.borel).ennreal_ofReal).comp (measurable_pi_apply i))
  have hW a (i : X.Signal) : X.tune a i.val.val=a i := dif_pos i.2
  have ht (a) (ha : a ∈ t) : (ν a).toReal • f (X.shifted (X.expandP a))=g a := by
    rw [← X.expend]; unfold g inward
    by_cases hi : f (X.view (X.tune a))=0
    · change _=f _ * _ * _ * _; rw [hi]; simp
    have hf (i : X.Signal) : X.cone o.a (X.tune a) i.val.val=1 := by
      obtain ⟨v,hv,hk,hy⟩ := he _ hi i
      rw [X.expend,X.regains] at hy
      apply X.premiere (a:=o.a) hc
      rw [hW a i,h.inject (ha i (Set.mem_univ i)) hv (mul_right_cancel hy)]; exact hk
    have hR (i : X.Signal) : Real.exp (X.gentry P' o.a (X.tune a) ((X.advance i).val))=P'.J (a i) := by
      rw [show (X.advance i).val=i.1.1 from rfl, (X.doorway (a:=o.a) hc _ _ (by rw [hf]; norm_num) h hΔ).2,hW]
    unfold ν enforce; rw [Real.exp_sum,ENNReal.toReal_prod]
    have hF : Fintype.card X.Signal = X.tier.card := (Fintype.card_congr X.advance).trans (Fintype.card_coe _)
    have hG i : (native P' (a i)).toReal=P'.scale*P'.J (a i) := ENNReal.toReal_ofReal (mul_nonneg h.scale.le (h.pos (a i) (ha i (Set.mem_univ _))).le)
    have hv (F : Bond _ → ℝ) : ∏ i∈X.tier,F i=∏ i : X.Signal,F (X.advance i) := by
      rw [← Finset.prod_coe_sort X.tier, X.advance.prod_comp (fun i=> F i.val)]
    simp_rw [hv,hG,hR, prod_mul_distrib,prod_const,card_univ,hF]
    change _= f _*_*(∏ i : X.Signal,P'.J (a i))*(∏ i : X.Signal,X.cone o.a (X.tune a) i.val.val); simp_rw [hf]; simp only [prod_const_one,smul_eq_mul,mul_one]; ring
  have hy (a) (ha : a ∉ t) : g a=0 := by
    by_contra hp
    have he : X.enforce o.a (X.tune a) X.tier≠0 := right_ne_zero_of_mul hp
    apply ha; intro i _
    rw [← hW a i]; exact (X.doorway hc _ _ (fun hm=> he (prod_eq_zero (X.advance i).2 hm)) h hΔ).1
  have hr := X.expansion h
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hg, ← setIntegral_eq_integral_of_forall_compl_eq_zero hy]
  have hm : Measurable (X.shifted) := X.shore.symm.measurable.comp (measurable_id.prodMk measurable_const)
  have hM' : Measurable (fun i=> f (X.shifted i)) := (X.tangibleB l K.laws.intake hb.W_pos).comp hm
  rw [← hr.map_eq,integral_map hr.measurable.aemeasurable hM'.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hM (ae_of_all _ fun i => lt_top_iff_ne_top.mpr (ENNReal.prod_ne_top (by intro; simp [native])))]
  exact setIntegral_congr_fun hX ht
end YM.ConnectedActivityE6.Coat
