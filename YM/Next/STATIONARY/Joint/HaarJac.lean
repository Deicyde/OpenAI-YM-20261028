import YM.Next.STATIONARY.Joint.Completion

set_option autoImplicit false
/-! # Probability Haar to real counting ratio inside the exponential patches.

Reindex Free tangent to LEFT coordinates based at actual slice point. Use
`order_exposed` for the physical order; no statement about density off
these open chart neighborhoods. We compare densities on compact sets
(by F05.Jacobian method) rather than assuming an inverse for a ratio or
spin ≡ 1 in the germ.
-/
noncomputable section
namespace YM.Stationary
open Function MeasureTheory Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius ENNReal
open Work.F05
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)

-- Free left increments in exp patch

def buck (y x : AxisChart G F) := fun i : F.Free => G.lieExp (x i) * (G.lieExp (y i))⁻¹
def saver (y x : AxisChart G F) : AxisChart G F := fun i => plogC G (buck F y x i)
@[simp] lemma buck_zero (y : AxisChart G F) : buck F y y=1 := by funext i; rw [buck,mul_inv_cancel]; rfl
@[simp] lemma saver_zero (y : AxisChart G F) : saver F y y=0 := by funext i; rw [saver,buck_zero]; exact plogC_one

lemma buck_lit (y : AxisChart G F) : Army (buck F y) y := by
  intro i
  simp only [buck,G.mat_mul]; exact ContDiffAt.mul (G.exp_jet.contDiffAt.comp _ (contDiffAt_apply ..)) contDiffAt_const
lemma cologne (y : AxisChart G F) : ContDiffAt ℝ ω (saver F y) y := by
  apply contDiffAt_pi.mpr; intro i; unfold saver plogC
  refine ContDiffAt.comp (g:=G.plog) (f:=fun x => G.mat (buck F y x i)) y ?_ (buck_lit F y i)
  rw [buck_zero,Pi.one_apply,G.mat_one]; exact G.plog_diff
lemma spends (y : AxisChart G F) : ∀ᶠ x in 𝓝 y, ∀ i, G.lieExp (saver F y x i)=buck F y x i := by
  have hp : Tendsto (buck F y) (𝓝 y) (𝓝 1) := by rw [← buck_zero F y]; exact (buck_lit F y).cont.tendsto
  refine eventually_all.mpr (fun i => (tendsto_pi_nhds.mp hp i).eventually G.plog_right)

section jacobian
open Set Metric

-- pointwise extraction from compact chart tests (cf Work.F05.Jacobian)
private lemma account_comp {X : Type} [MetricSpace X] [MeasureSpace X] [BorelSpace X]
    [IsFiniteMeasureOnCompacts (volume : Measure X)] [Measure.IsOpenPosMeasure (volume : Measure X)]
    [ProperSpace X] (x : X) {s : Set X} (h : s∈𝓝 x) (f g : X→ℝ)
    (he : ∀ A : Set X, IsCompact A → A⊆s → (∫⁻ y in A, ENNReal.ofReal (f y))=∫⁻ y in A,ENNReal.ofReal (g y))
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (p : 0≤f x) : g x ≤ f x := by
  by_contra! hu
  obtain ⟨a,ha,hb⟩ := exists_between hu
  obtain ⟨b,hc,hd⟩ := exists_between hb
  have hm : ∀ᶠ y in 𝓝 x,y∈s ∧ f y<a ∧ b<g y := (show ∀ᶠ y in 𝓝 x,y∈s from h).and
      ((hf.eventually (gt_mem_nhds ha)).and (hg.eventually (lt_mem_nhds hd)))
  obtain ⟨r,hr,h⟩ := nhds_basis_closedBall.mem_iff.mp hm
  let A := Metric.closedBall x r
  have hA : IsCompact A := isCompact_closedBall ..
  have h' y (hy : y ∈ A) : y∈s ∧ f y<a ∧ b<g y := h hy
  have hh : 0<volume A := lt_of_lt_of_le (Metric.isOpen_ball.measure_pos volume ⟨x,mem_ball_self hr⟩) (measure_mono ball_subset_closedBall)
  apply (he A hA (fun y hy => (h' y hy).1)).not_lt
  calc
    _ ≤ ∫⁻ _ in A, ENNReal.ofReal a := setLIntegral_mono' hA.measurableSet fun y hy => ENNReal.ofReal_le_ofReal (h' y hy).2.1.le
    _ < ∫⁻ _ in A, ENNReal.ofReal b := by
      simp only [lintegral_const,Measure.restrict_apply_univ]; exact ENNReal.mul_lt_mul_left hh.ne' hA.measure_lt_top.ne ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (p.trans ha.le)).mpr hc)
    _ ≤ _ := setLIntegral_mono' hA.measurableSet fun y hy => ENNReal.ofReal_le_ofReal (h' y hy).2.2.le

lemma treasury (U : Bid.Dir G c) (P : ChartRatio G) (h : LocalRatio P) (y : AxisChart G F) (hy : y∈parcel F P) :
    toll F P y = |(fderiv ℝ (saver F y) y).det| := by
  let X := AxisChart G F
  let d := exposure F U
  let R := saver F y
  let L := load F P
  let H (z : X) := |(fderiv ℝ R z).det| *  L (R z)
  have hx : R y=0 := saver_zero F y
  let T : Set X := {x : X | x∈parcel F P ∧ R x∈parcel F P ∧ ContDiffAt ℝ ω R x ∧
      exposure F 0 (R x) = d x*(d y)⁻¹}
  have hR : ContDiffAt ℝ ω R y := cologne F y
  have ht : T∈𝓝 y := by
    have he : IsOpen (parcel F P) := isOpen_set_pi finite_univ fun _ _ => Metric.isOpen_ball
    have hn : Tendsto R _ (𝓝 0) := hx ▸ hR.continuousAt.tendsto
    filter_upwards [he.mem_nhds hy,hn.eventually (parcel_zero F h),hR.eventually (by simp),spends F y] with v hv hp hu hz
    refine ⟨hv,hp,hu,?_⟩
    funext i; unfold R d; simp only [exposure, hz,buck,link_one,replica_one,Pi.one_apply,mul_one,Pi.mul_apply,Pi.inv_apply]; group
  have h0 : (0:X)∈parcel F P := mem_of_mem_nhds (parcel_zero F h)
  have hf := load_cont F h hy
  have hg : ContinuousAt H y := by
    apply ContinuousAt.mul
    · exact ContinuousAt.abs (ContinuousLinearMap.continuous_det.continuousAt.comp (hR.fderiv_right (m:=ω) (by simp)).continuousAt)
    exact ContinuousAt.comp (g:=L) (f:=R) (by rw [hx]; exact load_cont F h h0) hR.continuousAt
  have he (A : Set X) (hA : IsCompact A) (h' : A⊆T) :
      (∫⁻ x in A,ENNReal.ofReal (L x))=∫⁻ x in A,ENNReal.ofReal (H x) := by
    let C := R '' A
    let m := fun x : F.Slice G => x*(d y)⁻¹
    let Q := exposure F (0:Bid.Dir G c)
    have ha (x) (hx : x ∈ A) : HasFDerivAt R (fderiv ℝ R x) x := ((h' hx).2.2.1.differentiableAt (by simp)).hasFDerivAt
    have hc : IsCompact C := hA.image_of_continuousOn fun x hx => (ha x hx).continuousAt.continuousWithinAt
    have hQ : Continuous Q := (exposure_continuous F).comp (f:=fun x => (0,x)) (continuous_const.prodMk continuous_id)
    have hv : InjOn R A := fun x hx y hy hab =>
        exposure_inj F h U (h' hx).1 (h' hy).1 (mul_right_cancel (((h' hx).2.2.2).symm.trans ((congr_arg Q hab).trans (h' hy).2.2.2)))
    have hT : MeasurePreserving m (F.order G) (F.order G) := measurePreserving_pi _ _ (fun i : F.Free => measurePreserving_mul_right G.probHaar ((d y)⁻¹ i))
    have hm := hT.measure_preimage ((hc.image hQ).measurableSet.nullMeasurableSet (μ:=F.order G))
    have hu : m ⁻¹' (Q '' C)=d '' A := by
      have hp : Q '' C=m '' (d '' A) := by
        unfold C
        rw [Set.image_image,Set.image_image]
        exact Set.EqOn.image_eq (f₁:=fun z => Q (R z)) (f₂:=fun z => m (d z)) fun z hz => (h' hz).2.2.2
      rw [hp,(show Injective m from fun x y p => mul_right_cancel p).preimage_image]
    rw [hu] at hm
    have hb : C⊆parcel F P := by rintro _ ⟨x,hx,rfl⟩; exact (h' hx).2.1
    calc
    _ = _ := (order_exposed F h U A hA (fun x hx => (h' hx).1)).symm
    _ = (F.order G) (Q '' C) := hm
    _ = ∫⁻ x in C, ENNReal.ofReal (L x) := order_exposed F h _ C hc hb
    _ = ∫⁻ x in A, ENNReal.ofReal |(fderiv ℝ R x).det| * ENNReal.ofReal (L (R x)) := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA.measurableSet (fun x hx => (ha x hx).hasFDerivWithinAt) hv _
    _ = _ := by simp only [H, ENNReal.ofReal_mul (abs_nonneg _)]
  have hh : L y=H y := le_antisymm (account_comp _ ht _ _ (fun A hA hs => (he A hA hs).symm) hg hf (by unfold H; rw [hx]; exact mul_nonneg (abs_nonneg _) (load_pos F h h0).le)) (account_comp _ ht _ _ he hf hg (load_pos F h hy).le)
  unfold H L at hh; rw [hx,load_eq,load_eq,show toll F P 0=1 by simp [toll,h.anchored],mul_one,mul_comm |(fderiv ℝ R y).det|] at hh
  exact mul_left_cancel₀ (pow_ne_zero _ h.scale.ne') hh
end jacobian
end YM.Stationary
end

/-! # Factorization in the actual Haar score functions, finite period -/
noncomputable section
namespace YM.Stationary
open Function MeasureTheory Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius ENNReal
open Work.F05
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio}

variable (p : Clip) (R : PathData G) (x : Bid.Dir G c)
section single
variable (a : AxisChart G F)
lemma saving : ∀ᶠ b in 𝓝 a, Stationary.extend ((pad F (saver F a b)),0)*abode S F (represent x) a=abode S F (represent x) b := by
  filter_upwards [spends F a] with b hb; refine Prod.ext ?_ ?_
  · funext e; simp only [Prod.fst_mul, Pi.mul_apply,Stationary.extend,abode,lifting,input_color]
    by_cases h : e ∈ F.trunks
    · have hl (u : F.Slice G) : F.drape u e=1 := F.on_tree _ ⟨e,h⟩
      rw [hl,hl,show edgeColor (pad F _) e=0 from pad_trunk F _ ⟨e,h⟩]; simp
    let i : F.Free := ⟨e,h⟩
    have hh (u : F.Slice G) : F.drape u e=u i := F.off_tree u i
    rw [hh,hh,show edgeColor (pad F _) e=_ from pad_free F (saver F a b) i,hb,buck]; group
  simp [Stationary.extend,abode]
lemma certified (t : S.Choices) (h : Shell S t p R (represent x) (abode S F (represent x) a)) :
    let K := damage (helmets _ _ _) (canon S t p R (represent x) (abode S F (represent x) a)) 0
    (hessian F t p R x a).det=(fderiv ℝ (saver F a) a).det^2 * ((rangers F G)ᵀ*K*rangers F G).det := by
  intro K
  let Q := canon S t p R (represent x) (abode S F (represent x) a)
  let L : AxisChart G F →L[ℝ] Vault G c f := (pad F).prod 0
  let D := saver F a
  have he : tested F t p R x =ᶠ[𝓝 a] Q ∘ (L ∘ D) := by
    filter_upwards [saving x a] with b hb
    rw [← merit_pin]; change _=muster S t p R (represent x) _; exact congr_arg (muster S t p R (represent x)) hb.symm
  have hv : (L ∘ D) a=0 := by simp [D]
  have hk : damage (countingBasis F G) (tested F t p R x) a=
      (billsM (countingBasis F G) (helmets G c f) (L ∘L fderiv ℝ D a))ᵀ * K *billsM (countingBasis F G) (helmets G c f) (L ∘L fderiv ℝ D a) := by
    rw [damage_congr _ he, damage_comp _ (helmets G c f) _ (L.contDiff.contDiffAt.comp a (cologne F a)) _,hv,(L.hasFDerivAt.comp a ((cologne F a).differentiableAt (by simp)).hasFDerivAt).fderiv]
    · rw [hv]; exact h.1
    rw [hv]; exact h.2
  let A := billsM (countingBasis F G) (countingBasis F G) (fderiv ℝ (saver F a) a)
  rw [show hessian F t p R x a = damage _ _ _ from hessian_eq ..,hk]
  rw [show billsM _ _ (L ∘L fderiv ℝ D a)=rangers F G*A from bill_multiply _ (countingBasis F G) _ _ _]
  rw [transpose_mul, show (Aᵀ*(rangers F G)ᵀ)* K * (rangers F G*A) = Aᵀ * ((rangers F G)ᵀ*K*rangers F G) * A by simp only [Matrix.mul_assoc], det_mul, det_mul,det_transpose,
    show A.det=_ from (show A.det=(fderiv ℝ (saver F a) a).det from LinearMap.det_toMatrix ..)]
  ring
end single
section wealth
variable (S) (μ : ℝ)

def bounty (t : S.Choices) (K : Robe G c f) (V : Config G c) (U : Joint G c f) :=
    (1/2:ℝ)*Real.log (medals S t p R μ K V U).det-Real.log (grenade μ U.1).det
-- all logarithms real for moment evaluation, signs provided near origin by price and graph.
end wealth

variable {p R x} {σ A Λ μ η : ℝ} {ρ : Bid.Dir G c → AxisChart G F}
    (h : Critical F p R ρ) (hb : S.patch.Branches S.kernel G) (hp : R.Bounds p σ A Λ)
    (hv : PriceGap F p R η) (hh : 0<η) (hg : 0<μ) (t : S.Choices) {C : ChartRatio G} (hC : LocalRatio C)
include h hb hp hv hh hg hC

-- faithful det branch and real sign. No family compatibility assumed.
theorem tribute : ∀ᶠ z : Link G c in 𝓝 0,
    0 < (medals S t p R μ 1 (input G c z) (encamp F ρ z)).det ∧
    let T := thermal F t p R ρ C
    T (arm G c 1 z)=Precision.loop R (encamp F ρ z).1+bounty S p R μ t 1 (input G c z) (encamp F ρ z) := by
  have hm : Tendsto (arm G c 1) (𝓝 0) (𝓝 0) := by simpa using (arm G c 1).continuous.tendsto 0
  have hr : Tendsto ρ (𝓝 0) (𝓝 0) := h.1 ▸ h.2.1.continuousAt.tendsto
  filter_upwards [camp_station h hb hp t,explosive S t hb root_customs (camp_thaw h) (by rw [encamp_zero h]; rfl),hm.eventually (hessian_pos hh hv h t),hm.eventually (hr.eventually (parcel_zero F hC))] with z hz he hx hf
  let a := ρ (arm _ _ _ z)
  let Gm := grenade μ (encamp F ρ z).1
  let M := (hessian F t p R (arm G c 1 z) (ρ (arm G c 1 z)))
  let P := medals S t p R μ 1 (input G c z) (encamp F ρ z)
  let T := toll F C a
  have hi : T^2 * P.det=M.det*Gm.det^2 := by
    have hy := root_determines F (represent (arm G c 1 z)) a t hb hp hz (μ:=μ) he
    have hu : ρ (arm _ _ _ z) = a := rfl
    unfold T; rw [treasury F (arm G c 1 z) C hC a hf,sq_abs,show P.det=_ from hy]
    unfold M; rw [hu,certified p R (arm G c 1 z) a t hz]
    have heG : grenade μ (abode S F (represent (arm G c 1 z)) a).1=Gm := rfl
    rw [heG]; ring
  have hK : 0<Gm.det := (grenade_safe _ hg).det_pos
  have ha : 0<T := toll_pos F hC hf
  have hc : 0<M.det := hx
  have hP : 0<P.det := pos_of_mul_pos_right (show 0<T^2*P.det from hi ▸ mul_pos hc (pow_pos hK _)) (by positivity)
  refine ⟨hP,?_⟩; dsimp only
  change Precision.loop R (encamp F ρ z).1+_*Real.log M.det - Real.log T = Precision.loop R (encamp F ρ z).1 + (_*Real.log P.det - Real.log Gm.det)
  have hk := congr_arg Real.log hi; rw [Real.log_mul (pow_ne_zero _ ha.ne') hP.ne', Real.log_mul hc.ne' (pow_ne_zero _ hK.ne'), Real.log_pow, Real.log_pow] at hk; push_cast at hk; linarith
end YM.Stationary
end
