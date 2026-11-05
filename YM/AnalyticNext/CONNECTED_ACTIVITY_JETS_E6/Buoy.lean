import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Sift
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Skyline

/-!
# Insert the *actual* reference in Bochner integrations
Same K ballot on every term. μ shift not switched; unit swept variables. -/
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

def comfort (u : X.Vacant → ℝ) := bell⁻¹^X.dozing.card*Real.exp (-‖(WithLp.toLp 2 u)‖^2/2)

lemma comfy : ∫ v, X.comfort v=1 := by
  let A := ProbabilityTheory.stdGaussian (Poll.Body X.Vacant)
  let B (x : Poll.Body X.Vacant) := (bell ^ Fintype.card X.Vacant)⁻¹*Real.exp (-‖x‖^2/2)
  have hA : A = volume.withDensity (fun x => ENNReal.ofReal (B x)) := Poll.std_pdf
  have hi : (∫ _, (1:ℝ) ∂A)=1 := by unfold A; simp
  have hg x : ENNReal.toReal (ENNReal.ofReal (B x)) • (1:ℝ)=B x := by
    simp only [ENNReal.toReal_ofReal (show 0≤B x by unfold B bell; positivity), smul_eq_mul, mul_one]
  have hx : Measurable (fun x=> ENNReal.ofReal (B x)) := by unfold B; fun_prop
  rw [hA, integral_withDensity_eq_integral_toReal_smul hx (ae_of_all _ fun _=> by simp)] at hi
  simp_rw [hg] at hi
  rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp X.Vacant).symm.integral_comp' B] at hi
  unfold comfort; rw [inv_pow,← Fintype.card_coe X.dozing,← Fintype.card_congr X.vacancies]; exact hi

theorem dormant_energy (x : Air f G) : X.ghost x=‖WithLp.toLp 2 (X.partB x).2‖^2/2 := by
  rw [EuclideanSpace.real_norm_sq_eq, ghost]; congr 1; unfold dotProduct
  calc
    _ = ∑ j∈X.dozing,(x j)^2 := by
      unfold dozing; rw [sum_filter]; apply sum_congr rfl; intro i _; rw [X.sleepy_act]; split
      next _ => simp 
      next h => exact (pow_two _).symm
    _ = _ := by
      rw [← Finset.sum_coe_sort,← X.vacancies.sum_comp (fun i=> (x i.val)^2)]; rfl

/-- Equivalence full coordinate split; allows precise inverse-density on Air
before pairing the constant blank extensive factors. -/
theorem seat (K : Cash W X.x μ L Q o C T R) (hk : X.width=o.K) (l : Finset ℕ) :
    (∫ u,X.tangible R W (X.shifted u) l ∂X.stages)=∫ z, X.ticketK R W o.a Q.table z l := by
  rw [X.shoreside K hk l]; symm
  let g := gStep R.beta; have hg : 0<g := by unfold g gStep; have := K.laws.intake.positive; positivity
  let p := X.arised.card; let h:=Units.mk0 _ hg.ne'
  let f (i) := X.inward R Q.table W o.a l i
  let D : (X.Speck→ℝ) ≃ᵐ( X.Signal→G.Color) := (blast h (fun i => X.μ i.val.1 i.val.2)).trans X.tunes
  let Y (x) := f (X.tune (D x))
  have hD : MeasurePreserving D (ENNReal.ofReal (g^p) • volume) volume := by
    unfold D p; rw [X.arised_size]; exact X.preserves_tunes.comp (preserving_blast h hg _)
  have hM := hD.integral_comp' (fun i=> f (X.tune i))
  rw [integral_smul_measure] at hM
  simp only [ENNReal.toReal_ofReal (pow_nonneg hg.le _),smul_eq_mul] at hM
  have hv (z) : X.ticketK R W o.a Q.table z l=Y (X.partB z).1*g^p*X.comfort (X.partB z).2 := by
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
    unfold Y f inward ticketK; dsimp only
    rw [he,hg,ribbons, hd,comfort,inv_pow,Real.exp_add]; rw [X.dormant_energy, neg_div]; unfold x' g p; ring
  rw [← X.partP.symm.integral_comp' (fun z=> X.ticketK R W o.a Q.table z l)]
  simp_rw [hv,X.partB.apply_symm_apply]
  rw [← hM]; change (∫ z : ((X.Speck→ℝ) × (X.Vacant→ℝ)), Y z.1*g^p*X.comfort z.2 ∂volume.prod volume)=_
  rw [integral_prod_mul (fun i=> Y i*g^p) X.comfort, X.comfy,mul_one, integral_mul_const]; exact mul_comm ..

lemma ticket (K : Cash W X.x μ L Q o C T R) (h : X.manifest) (hk : X.width=o.K) (k) (Y)
    (hp : Layout X.seeds Q.halo X.B Y) (hl : Contract.sealed R k) :
    (∫ u,X.tangible R W (X.shifted u) k ∂X.stages) = (Fintype.card S.Choices:ℝ)⁻¹ * X.levy R * X.deducted Q.table R.beta*
      ∫ z,X.summedUp R Q.table W o.a z k Y ∂X.dice := by
  let g (z) := ENNReal.ofReal (X.thetaRef z)
  have hd : X.dice = volume.withDensity g := Poll.sweep_pdf (K.laws.data.localP F X rfl hk h).sails.fullC
  have hg : Measurable g := by unfold g thetaRef dotProduct; fun_prop
  rw [X.seat K hk k, hd, integral_withDensity_eq_integral_toReal_smul hg (ae_of_all _ fun _=> ENNReal.ofReal_lt_top),
    ← integral_const_mul]
  apply integral_congr_ae; filter_upwards with z
  rw [X.consolidated k K h hk z hp hl]; unfold g; rw [ENNReal.toReal_ofReal (show 0≤ X.thetaRef _ by unfold thetaRef bell; positivity),smul_eq_mul]; ring
end YM.ConnectedActivityE6.Coat
