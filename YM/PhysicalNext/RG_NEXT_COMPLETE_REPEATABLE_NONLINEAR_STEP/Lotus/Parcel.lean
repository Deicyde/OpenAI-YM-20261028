import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Parrot
import YM.Push.ABSOLUTE_SUMS.Gas
/-!
 # Real reference insertion and rollback. Adapt E6.Buoy machinery WITHOUT dividing by densities. 
 Use true held active patches and measures on *complete* raw Ledger incl force eras.
 -/
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


open PhysicalNext.Repeat.Lotus
variable (M : Leaf R) (l : Finset ℕ)
lemma shore_touch (hR : Intake P T X.x R) (hw : 0<W)  :
    (∫ Y, M.realP X Y l W ∂F.order G)=∫ Y, ∫ z,M.realP X ((X.wrapY Y).shifted z) l W ∂X.stages ∂F.order G := by
  let f (Y) := M.realP X Y l W
  have he : Integrable (f ∘ X.shore.symm) _ := (X.propagation.symm.integrable_comp_emb
    X.shore.symm.measurableEmbedding).mpr ((M.world X hR hw).1 l)
  let g (v) := ∫ z,f (X.shore.symm (z,v)) ∂X.stages
  have hr : Integrable (fun w : (X.Signal → G.El) × (X.Fog→G.El) => g w.2) (X.stages.prod X.forecast) :=
    he.integral_prod_right.comp_snd _
  rw [← X.propagation.symm.integral_comp' f]; symm
  change (∫ Y, ∫ z, f _ ∂X.stages ∂_)=_
  rw [← X.propagation.symm.integral_comp' (fun Y=> ∫ z,f ((X.wrapY Y).shifted z) ∂X.stages)]
  simp_rw [shifted]
  change (∫ v, ∫ z, f (X.shore.symm (z,(X.shore (X.shore.symm v)).2)) ∂X.stages ∂_)=_
  simp_rw [X.shore.apply_symm_apply]; rw [Function.comp_def] at he; rw [integral_prod_symm _ hr, integral_prod_symm _ he]; simp [g]

lemma licensesP (K : Cash W X.x μ L Q o C T R) (hk : X.width=o.K)
    {Y : F.Slice G} (h : M.realP X Y l W ≠ 0) (i : Bond f) (hi : X.Hot i) :
    ∃ v ∈ Metric.ball (0:G.Color) Q.table.radius, ‖v‖ ≤ o.a*X.t ∧
      F.drape Y i=G.lieExp v*replica S.ratio X.V i := by
  have hz := K.laws.data
  let A := X.χ.profiles G S X.x W hz.W_pos hz.room.fiery
  have hv : A.bill X.seeds X.k (F.drape Y) X.V ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  have hu : S.likelihood (F.drape Y) X.k≠0 := left_ne_zero_of_mul (left_ne_zero_of_mul (right_ne_zero_of_mul h))
  have hf := hz.covers; rw [← hz.funds.length_eq] at hf
  refine buys_empty X (γ:=o.γ) (?_) (?_) Q.table_exists (?_) (F.drape Y) (A.actual _ _ _ _ hv)
    (lt_of_le_of_ne (S.likelihood_pos ..) (Ne.symm hu)) (fun i hi=> F.on_tree _ ⟨_,hi⟩) i hi
  · rw [hk]; exact hz.access
  · rw [hk]; exact o.gamma
  nlinarith only [hf, mul_pos o.large hz.room.fiery]

private def passP (Ñ : ChartRatio G) := Metric.ball (0:G.Color) Ñ.radius
private def native (P : ChartRatio G) (a : G.Color) := ENNReal.ofReal (P.scale * P.J a)
private def localP (V : G.El) (P : ChartRatio G) := (fun z : G.Color=> G.lieExp z*V) '' passP P
private def capP (Ñ : ChartRatio G) := Set.univ.pi fun i : X.Signal => localP (replica S.ratio X.V i.1.1) Ñ

private lemma exposing {P : ChartRatio G} (h : LocalRatio P) (V : G.El) :
    MeasurePreserving (fun a => G.lieExp a * V)
      ((volume.restrict (passP P)).withDensity (native P)) (G.probHaar.restrict (localP V P)) := by
  let L := MeasurableEquiv.mulRight V
  have hp : MeasurePreserving L G.probHaar G.probHaar := measurePreserving_mul_right _ _
  have hf : MeasurePreserving G.lieExp ((volume.restrict (passP P)).withDensity (native P))
      (G.probHaar.restrict (G.lieExp '' passP P)) := ⟨G.lieExp_cont.measurable,h.actual⟩
  have hk := L.restrict_map G.probHaar (localP V P)
  rw [hp.map_eq] at hk
  have he : localP V P = L '' (G.lieExp '' passP P) := Set.image_comp L G.lieExp _
  have hx : MeasurePreserving L (G.probHaar.restrict (G.lieExp '' passP P)) (G.probHaar.restrict (localP V P)) := by
    rw [hk, he,L.injective.preimage_image]; exact ⟨hp.measurable,rfl⟩
  exact hx.comp hf

private def rangeP (Ñ : ChartRatio G) := Set.univ.pi fun _ : X.Signal => passP Ñ
private def expandP (a : X.Signal→G.Color) := (fun i : X.Signal=> G.lieExp (a i)*replica S.ratio X.V i.1.1)

private lemma expansion {Ñ : ChartRatio G} (h : LocalRatio Ñ) : MeasurePreserving X.expandP
    ((volume.restrict (X.rangeP Ñ)).withDensity (fun y => ∏ i : X.Signal, native Ñ (y i)))
    (X.stages.restrict (X.capP Ñ)) := by
  let μ : Measure G.Color := volume.restrict (passP Ñ)
  have hm : volume.restrict (X.rangeP Ñ)=Measure.pi fun _ => μ := Measure.restrict_pi_pi ..
  haveI : SigmaFinite μ := by unfold μ; infer_instance
  have hv : Measurable (native Ñ) := (measurable_const.mul h.borel).ennreal_ofReal
  haveI : SigmaFinite (μ.withDensity (native Ñ)) := SigmaFinite.withDensity_ofReal _
  rw [hm, Work.F05.piDensity (fun _ : X.Signal=> μ) (fun _=>native Ñ) (fun _=>hv),stages,capP,Measure.restrict_pi_pi]
  exact measurePreserving_pi _ _ fun i : X.Signal=> exposing h (replica S.ratio X.V i.1.1)

private lemma regains (u) (i : X.Signal) : X.shifted u i.val=u i := by
  change (if h : X.Hot i.1.1 then u _ else _ )=_; exact dif_pos i.2
private lemma expend (a : X.Signal→G.Color) : X.view (X.tune a) = X.shifted (X.expandP a) := by
  funext i; by_cases h : X.Hot i.val
  · rw [show X.shifted (X.expandP a) i = X.expandP a ⟨i,h⟩ from X.regains _ ⟨i,h⟩,view, if_pos h,increment, tune, dif_pos h]; rfl
  rw [view, if_neg h]; symm
  change (if hh : X.Hot i.val then _ else X.Y i)=_; exact dif_neg h

/-- Borel scaled weight post-chart. -/
def ascentP (M : Leaf R) (Ñ : ChartRatio G) (W a : ℝ) (l : Finset ℕ) (u : Directions G f) :=
    (M.realP X (X.view u) l W *Ñ.scale ^ X.tier.card)*Real.exp (∑ i∈X.tier, X.gentry Ñ a u i)*X.enforce a u X.tier

variable (K : Cash W X.x μ L Q o C T R) (hk : X.width=o.K)

include K hk in
lemma chartersM (l : Finset ℕ) :
    (∫ u,M.realP X (X.shifted u) l W ∂X.stages)=∫ a : X.Signal → G.Color,X.ascentP M Q.table W o.a l (X.tune a) := by
  let P' := Q.table; have h := Q.table_exists
  have hb := K.laws.data; have hh := hb.covers; rw [← hb.funds.length_eq] at hh
  have hc := mul_pos o.large hb.room.fiery
  have hΔ : 2*o.a*X.t < P'.radius := by dsimp only [Coat.t,P']; nlinarith only [hc,hh]
  let s := X.capP Q.table
  let t := X.rangeP Q.table
  let f (u) := M.realP X u l W
  have hX : MeasurableSet t := MeasurableSet.univ_pi (fun i => Metric.isOpen_ball.measurableSet)
  have he (u : F.Slice G) (hf : f u≠0) (i : X.Signal) : ∃ v∈passP P', ‖v‖≤o.a*X.t ∧
        (u i.val)=G.lieExp v*replica S.ratio X.V i.val.val := by
    rw [← F.off_tree u i.val]; exact X.licensesP M _ K hk hf _ i.2
  have hg z (hz : z ∉ s) : f (X.shifted z)=0 := by
    by_contra hp; apply hz; intro i _; obtain ⟨v,hv,-,he⟩ := he _ hp i
    exact ⟨v,hv, he.symm.trans (regains ..)⟩
  let g (a : X.Signal→G.Color) := X.ascentP M P' W o.a l (X.tune a)
  let ν (u : X.Signal → G.Color) := ∏ i : X.Signal,native P' (u i)
  have hM : Measurable ν := Finset.measurable_fun_prod _ fun i _=>
    ((show Measurable (native P') from (measurable_const.mul h.borel).ennreal_ofReal).comp (measurable_pi_apply i))
  have hW a (i : X.Signal) : X.tune a i.val.val=a i := dif_pos i.2
  have ht (a) (ha : a ∈ t) : (ν a).toReal • f (X.shifted (X.expandP a))=g a := by
    rw [← X.expend]; unfold g ascentP
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
  have hM' : Measurable (fun i=> f (X.shifted i)) := (((M.escorts X K.laws.intake hb.W_pos).2 l)).comp hm
  rw [← hr.map_eq,integral_map hr.measurable.aemeasurable hM'.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hM (ae_of_all _ fun i => lt_top_iff_ne_top.mpr (ENNReal.prod_ne_top (by intro; simp [native])))]
  exact setIntegral_congr_fun hX ht

def tokenU (M : Leaf R) (W a : ℝ) (Ñ : ChartRatio G) (z : Air f G) (l : Finset ℕ) :=
    let U := X.liftA R.beta z
    M.realP X (X.view U) l W * X.ribbons z Ñ R.beta a * X.enforce a U X.tier


include K hk
theorem seatP (l : Finset ℕ) :
    (∫ u,M.realP X (X.shifted u) l W ∂X.stages)=∫ z, X.tokenU M W o.a Q.table z l := by
  rw [X.chartersM M K hk l]; symm
  let g := gStep R.beta; have hg : 0<g := by unfold g gStep; have := K.laws.intake.positive; positivity
  let p := X.arised.card; let h:=Units.mk0 _ hg.ne'
  let f (i) := X.ascentP M Q.table W o.a l i
  let D : (X.Speck→ℝ) ≃ᵐ( X.Signal→G.Color) := (blast h (fun i => X.μ i.val.1 i.val.2)).trans X.tunes
  let Y (x) := f (X.tune (D x))
  have hD : MeasurePreserving D (ENNReal.ofReal (g^p) • volume) volume := by
    unfold D p; rw [X.arised_size]; exact X.preserves_tunes.comp (preserving_blast h hg _)
  have hM := hD.integral_comp' (fun i=> f (X.tune i))
  rw [integral_smul_measure] at hM
  simp only [ENNReal.toReal_ofReal (pow_nonneg hg.le _),smul_eq_mul] at hM
  have hv (z) : X.tokenU M W o.a Q.table z l=Y (X.partB z).1*g^p*X.comfort (X.partB z).2 := by
    let x := X.liftA R.beta z; let x':= X.tune (D (X.partB z).1)
    have hx (j) (he : X.Hot j) : x j=x' j := by
      unfold x' tune; rw [dif_pos he]; ext k
      let i:X.Speck := ⟨(j,k),he⟩
      change _= X.tunes _ _ k; rw [X.tunes_val _ i ⟨⟨j,he.1⟩,he⟩ k rfl]; rfl
    have he : X.view x=X.view x' := by
      funext i; unfold view; split <;> rename_i h
      · unfold increment; rw [hx _ h]
      rfl
    have hg : X.enforce o.a x X.tier = X.enforce o.a x' X.tier := by
      unfold enforce; apply prod_congr rfl; intro i hi; unfold cone; rw [hx _ (mem_filter.mp hi).2]
    have hd : (∑ j∈X.tier, X.gentry Q.table o.a x j)= ∑ j∈X.tier, X.gentry Q.table o.a x' j := by
      apply sum_congr rfl; intro j hj; unfold gentry cone; rw [hx _ (mem_filter.mp hj).2]
    unfold Y f ascentP tokenU; dsimp only
    rw [he,hg,ribbons, hd,comfort,inv_pow,Real.exp_add]; rw [X.dormant_energy, neg_div]; unfold x' g p; ring
  rw [← X.partP.symm.integral_comp' (fun z=> X.tokenU M W o.a Q.table z l)]
  simp_rw [hv,X.partB.apply_symm_apply]
  rw [← hM]; change (∫ z : ((X.Speck→ℝ) × (X.Vacant→ℝ)), Y z.1*g^p*X.comfort z.2 ∂volume.prod volume)=_
  rw [integral_prod_mul (fun i=> Y i*g^p) X.comfort, X.comfy,mul_one, integral_mul_const]; exact mul_comm ..


end YM.ConnectedActivityE6.Coat
