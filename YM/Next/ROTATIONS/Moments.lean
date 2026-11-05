import YM.Next.ROTATIONS.Axis
import YM.Next.ROTATIONS.MomentFD
/-!
# Moment bounds, before interpolation orders

Energy is `p i`; moments transverse. The constants (per cluster etc) chosen here use
no rotations beyond coordinate RP and the old discrete symmetries.
-/
noncomputable section
namespace YM.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Row OS Word
open scoped Topology InnerProductSpace ContDiff NNReal ENNReal BigOperators ComplexConjugate
variable {G : Gauge} {L : Register G} {S : Table L} {i : Axis} {V : Chamber S i}

/-- A line estimate even on an OPEN context rather than global smoothness. -/
lemma line_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E→ℂ} {D : Set E} (h : IsOpen D)
    (M : ℝ →L[ℝ] E) (b : E) (k : ℕ) (hf : ContDiffOn ℝ k f D) (t : ℝ) (he : b+M t∈D) :
    ‖iteratedDeriv k (fun u : ℝ => f (b+M u)) t‖ ≤ ‖iteratedFDeriv ℝ k f (b+M t)‖ * ‖M‖^k := by
  let R := (fun x => b+x) ⁻¹' D
  have hr : IsOpen R := h.preimage (by fun_prop)
  let F (x) := f (b+x)
  have hp : ContDiffOn ℝ k F R := ContDiffOn.comp hf (g:=f) (by
    apply ContDiff.contDiffOn; fun_prop) (mapsTo_preimage ..)
  have hw : IsOpen (M ⁻¹' R) := hr.preimage M.continuous
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hz := M.iteratedFDerivWithin_comp_right hp hr.uniqueDiffOn hw.uniqueDiffOn (show M t∈R from he) (i:=k) le_rfl
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hw.uniqueDiffOn
    (((hp.comp_continuousLinearMap M) t he).contDiffAt (hw.mem_nhds he)) he,
    iteratedFDerivWithin_eq_iteratedFDeriv hr.uniqueDiffOn ((hp _ he).contDiffAt (hr.mem_nhds he)) he] at hz
  dsimp only [F] at hz
  rw [iteratedFDeriv_comp_add_left] at hz
  rw [show (fun u => f (b+M u))=F ∘ M from rfl,hz]
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq (by simp)

private def direct (v w : L.Word) (d : E4) := points (Fin.append (fun _ : Fin v.length => (0:E4)) (fun _ : Fin w.length => d))
private lemma turnsLine (v w : L.Word) (t : ℝ) (c d : E4) : composite v w (c+t • d)=composite v w c+t • direct v w d := by
  ext1 k
  refine Fin.addCases ?_ ?_ k <;> intro j <;> simp [composite,direct,add_assoc]

private lemma reflect_eq_conj (i : Axis) (v : Core L) : conjugate ((rotate (Signed.mirror i) v).val.reverse)=Word.reflect v.val i := by
  change conjugate (act _ _).reverse = act _ (conjugate _)
  rw [act_conj]; simp only [act,List.map_reverse]

/-- Distinct words have a genuine internal separation. -/
lemma internal {n : ℕ} (v : Points n) (h : v∈conf n) : ∃ r₀ : ℝ,0<r₀ ∧ spaced r₀ v := by
  have he (i j : Fin n) : ∀ᶠ r in 𝓝[>] (0:ℝ), i≠j → r ≤ cubedist (v i) (v j) := by
    by_cases hp : i=j; · simp [hp]
    have hv : 0 < cubedist (v i) (v j) := dist_pos.mpr fun e => hp (h (WithLp.ofLp_injective _ e))
    filter_upwards [(gt_mem_nhds hv).filter_mono (nhdsWithin_le_nhds (s:=Ioi 0))] with r hr _
    exact le_of_lt hr
  exact ((show ∀ᶠ r in 𝓝[>] (0:ℝ), 0<r from self_mem_nhdsWithin).and (eventually_all.mpr fun i => eventually_all.mpr (he i))).exists

private lemma buffer (i : Axis) (v w : Core L) (η : ℝ) (hp : spaced η (positions (reflect v.val i)))
    (hw : spaced η (positions w.val)) (r u : ℝ) (hr : 0<r) (hj : r≤η) (hv : ∀ p∈v.val, r ≤ p.1 i+u)
    (hg : ∀ p∈w.val, r ≤ p.1 i+u) (x : E4) (hx : u+u ≤ x i) :
    spaced r (composite (reflect v.val i) w.val x) := by
  let A := reflect v.val i
  have hc (k : Fin A.length) (j : Fin w.val.length) : r ≤ cubedist (positions A k) (positions w.val j+x) := by
    have ha : (positions A k) i ≤ u-r := by
      have he : A.get k∈reflect v.val i := List.get_mem ..
      rw [reflectedPoint,List.mem_map] at he
      obtain ⟨p,hpz,hh⟩ := he
      have H := hv p (by simpa using hpz)
      change (A.get k).1 i ≤ _; rw [← hh]
      simp only [Signed.mirrored, ↓reduceIte]; linarith
    have hG : r ≤ positions w.val j i + u := hg (w.val.get j) (List.get_mem ..)
    refine le_trans ?_ (dist_le_pi_dist (positions A k).ofLp (positions w.val j+x).ofLp i)
    rw [Real.dist_eq]; apply le_trans _ (neg_le_abs _)
    change r ≤ -((positions A k) i - (positions w.val j i+x i)); linarith
  intro k j
  refine Fin.addCases ?_ ?_ k
  · intro l
    refine Fin.addCases ?_ ?_ j
    · intro t ht
      simp only [composite, points_apply, Fin.append_left]
      exact hj.trans (hp l t (fun h => ht (congr_arg _ h)))
    intro t ht
    simpa [composite] using hc l t
  intro l
  refine Fin.addCases ?_ ?_ j
  · intro t ht
    simpa [composite, cubedist,dist_comm (positions A t).ofLp] using hc t l
  intro t ht
  simp only [composite,points_apply,Fin.append_right,Points.across_coord,cubedist,WithLp.ofLp_add,dist_add_right]
  exact hj.trans (hw l t (fun h => ht (congr_arg _ h)))

/-- All-points line estimate: no κ chosen from a width test on a rotated table. -/
private lemma terms (H : S.Hierarchy) (i j : Axis) (hji : j≠i) (k : ℕ) (v w : Core L) :
    ∃ (C : ℝ) (D : ℕ) (η : ℝ), 0 ≤ C ∧ 0<η ∧ η≤1 ∧ ∀ r : ℝ, 0<r → r≤η → ∀ u : ℝ≥0,
      (∀ p∈v.val,r≤p.1 i+(u:ℝ)) → (∀ p∈w.val,r≤p.1 i+(u:ℝ)) →
      let f := fun t : ℝ => bare S (rotate (Signed.mirror i) v) w (↑(u+u:ℝ≥0) • basis i+t • basis j)
      ContDiff ℝ ∞ f ∧ ∀ x, ‖iteratedDeriv k f x‖ ≤ C*r⁻¹^D := by
  let A := reflect v.val i
  let x := positions A
  obtain ⟨r₁,hR,hs⟩ := internal x (Word.reflects i v.property)
  obtain ⟨r₂,hN,ht⟩ := internal (positions w.val) w.property
  let q := Fin.append (tokens A) (tokens w.val)
  obtain ⟨D,C,hC,hD⟩ := H.order _ (fun i => (q i).1) (fun i => (q i).2) k
  let M := (ContinuousLinearMap.id ℝ ℝ).smulRight (direct A w.val (basis j))
  let p := min 1 (min r₁ r₂)
  refine ⟨C*‖M‖^k,D,p,by positivity,lt_min (by norm_num) (lt_min hR hN),min_le_left ..,fun r hr he u h1 h2 => ?_⟩
  let c : E4 := ((u+u:ℝ≥0):ℝ) • basis i
  have hw (t : ℝ) : spaced r (composite A w.val (c+t • basis j)) := by
    have h₁ : ∀ a b, a≠b → min r₁ r₂ ≤ cubedist (x a) (x b) := fun a b h => (min_le_left ..).trans (hs a b h)
    have h₂ : spaced (min r₁ r₂) (positions w.val) := fun a b h => (min_le_right ..).trans (ht a b h)
    exact buffer i v w _ h₁ h₂ r u hr (he.trans (min_le_right ..)) h1 h2 _ (by simp [c,Ne.symm hji])
  let b := composite A w.val c
  have hf (t : ℝ) : composite A w.val (c+t • basis j)=b+M t := by rw [turnsLine]; rfl
  let g : Points (A.length + w.val.length) → ℂ := fun y => S.read y q
  have hy : (fun t : ℝ => bare S (rotate (Signed.mirror i) v) w (c+t • basis j)) = (fun t => g (b+M t)) := by
    funext t
    unfold bare
    rw [if_pos]
    swap
    · rw [reflect_eq_conj,placements,realized]; exact spaced_conf hr (hw t)
    rw [reflect_eq_conj,placements,Table.readAt]
    rw [← hf]
  change ContDiff ℝ ∞ (fun t : ℝ => bare S (rotate (Signed.mirror i) v) w (c+t • basis j)) ∧ ∀ x, ‖iteratedDeriv k (fun t : ℝ => bare S _ _ (c+t • basis j)) x‖ ≤ _
  rw [hy]
  have hl t : spaced r (b+M t) := hf t ▸ hw t
  have hq t : b+M t∈conf _ := spaced_conf hr (hl t)
  have hg : ContDiffOn ℝ ∞ g (conf _) := S.smooth_read H.smooth q
  refine ⟨contDiff_iff_contDiffAt.mpr fun v => ((hg _ (hq v)).contDiffAt ((conf_open _).mem_nhds (hq v))).comp v (f:=fun v => b+M v) (by fun_prop), fun z => ?_⟩
  refine (line_norm (conf_open _) M b k (hg.of_le (by exact_mod_cast le_top)) z (hq z)).trans ?_
  have hQ : ‖iteratedFDeriv ℝ k g (b+M z)‖ ≤ C*r⁻¹^D := hD _ hr (he.trans (min_le_left ..)) (b+M z) (hl z)
  rw [mul_right_comm C]; gcongr


def KeepsMargin (i : Axis) (A : Weight L) (r : ℝ) (u : ℝ≥0) := ∀ v∈A.support,∀ p∈v.val, r ≤ p.1 i + (u:ℝ)
lemma keeps_lower {r} (A : Weight L) (i : Axis) (u : ℝ≥0) (hr : 0<r) (h : KeepsMargin i A r u) :
    Lowered i A u := fun v hv p hp => hr.trans_le (h v hv p hp)
private def poly (k : ℕ) (P : ℝ → ℝ≥0 → Prop) (f : ℝ≥0 → ℝ→ℂ) :=
    ∃ (C : ℝ) (D : ℕ) (η : ℝ), 0 ≤ C ∧ 0<η ∧ η≤1 ∧ ∀ r : ℝ, 0<r → r≤η → ∀ u : ℝ≥0, P r u →
      ContDiff ℝ ∞ (f u) ∧ ∀ x, ‖iteratedDeriv k (f u) x‖ ≤ C*r⁻¹^D
private lemma poly_add {f g k P} (h : poly k P f) (l : poly k P g) : poly k P (fun u t => f u t+g u t) := by
  obtain ⟨C,D,e,hC,he,hE,h⟩ := h
  obtain ⟨R,N,v,hR,hv,hV,l⟩ := l
  refine ⟨C+R, max D N,min e v,add_nonneg hC hR,lt_min he hv,(min_le_left ..).trans hE,fun r hr hb u ht => ?_⟩
  obtain ⟨H,h⟩ := h r hr (hb.trans (min_le_left ..)) u ht
  obtain ⟨K,l⟩ := l r hr (hb.trans (min_le_right ..)) u ht
  have hx : 1≤r⁻¹ := (one_le_inv₀ hr).mpr (hb.trans ((min_le_right ..).trans hV))
  refine ⟨H.add K, fun x => ?_⟩
  rw [iteratedDeriv_fun_add (H.of_le (m:=↑k) (by exact_mod_cast le_top)).contDiffAt
    (K.of_le (m:=↑k) (by exact_mod_cast le_top)).contDiffAt,add_mul]
  apply (norm_add_le ..).trans
  exact add_le_add ((h x).trans (by gcongr;exact le_max_left ..)) ((l x).trans (by gcongr; exact le_max_right ..))
private lemma poly_scale {f k P} (h : poly k P f) (z : ℂ) : poly k P (fun u t => z * f u t) := by
  obtain ⟨C,D,e,hC,he,hE,h⟩ := h
  refine ⟨‖z‖*C,D,e,by positivity,he,hE,fun r hr hb u ht => ?_⟩
  obtain ⟨H,h⟩ := h r hr hb u ht
  refine ⟨contDiff_const.mul H,fun x => ?_⟩
  rw [iteratedDeriv_const_mul_field,norm_mul,mul_assoc]
  gcongr; exact h x
private lemma poly_sum {ι : Type*} (p : Finset ι) {F : ι → ℝ≥0 → ℝ → ℂ} {k P}
    (h : ∀ i∈p,poly k P (F i)) : poly k P (fun u t => ∑ i∈p,F i u t) := by
  classical
  induction p using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨0,0,1,by norm_num,by norm_num,by norm_num,fun r _ _ u _ => ⟨contDiff_const, fun x => ?_⟩⟩
    simp 
  | @insert i p hi ih =>
    simp_rw [Finset.sum_insert hi]; exact poly_add (h i (by simp)) (ih fun v hv => h v (by simp [hv]))

private lemma rent (H : S.Hierarchy) (i j : Axis) (hji : j≠i) (k : ℕ) (A : Weight L) :
    poly k (KeepsMargin i A) (fun u t => readsCluster S (ink (Signed.mirror i) A) A (((u+u:ℝ≥0):ℝ) • basis i+t • basis j)) := by
  simp_rw [reads_ink_l,Finsupp.sum]
  refine poly_sum _ (fun v hv => poly_scale ?_ _)
  refine poly_sum _ (fun w hw => poly_scale ?_ _)
  obtain ⟨C,D,e,hC,he,hE,h⟩ := terms H i j hji k v w
  refine ⟨C,D,e,hC,he,hE,fun r hr ht u hp => h r hr ht u (hp v hv) (hp w hw)⟩

def mom (i j : Axis) (k : ℕ) (u : ℝ) (p : E4) := Real.exp (-u*p i)*‖p j‖^(2*k)
lemma mom_nn (i j k u p) : 0 ≤ mom i j k u p := by unfold mom; positivity

/-- All transverse spectral moments, from separated reflection-positive assumptions ONLY.
Cost paid for a true placement. Includes `k=0`, includes energy zero. -/
lemma moments (V : Chamber S i) (H : S.Hierarchy) (A : Weight L) (j : Axis) (hj : j≠i) (k : ℕ) :
    ∃ (C : ℝ) (D : ℕ) (η : ℝ), 0 ≤ C ∧ 0<η ∧ η≤1 ∧ ∀ r : ℝ, 0<r → r≤η → ∀ u : ℝ≥0,
      KeepsMargin i A r u → Integrable (mom i j k (u+u:ℝ≥0)) (ν V A) ∧
      (∫ p, mom i j k (u+u:ℝ≥0) p ∂ν V A) ≤ C*r⁻¹^D := by
  obtain ⟨C,D,e,hC,he,hE,h⟩ := rent H i j hj (2*k) A
  refine ⟨C,D,e,hC,he,hE,fun r hr he u hd => ?_⟩
  obtain ⟨hs,h⟩ := h r hr he u hd
  let F := fun t : ℝ => readsCluster S (ink (Signed.mirror i) A) A (((u+u:ℝ≥0):ℝ) • basis i+t • basis j)
  have hv := keeps_lower A i u hr hd
  let μ := V.flow.ℚmeasure.diagonal (root V A u)
  haveI : IsFiniteMeasure μ := Spectral.PVM.finite ..
  have hh (t : ℝ) : F t=∫ p : E4, plane (p j) t ∂μ := by
    let b : Cross i := ⟨t • basis j,by change (t • basis j) i=0; simp [Ne.symm hj]⟩
    have hw := placed V H.translations A A u 0 b hv hv
    simp only [mul_zero,ofReal_zero,NNReal.coe_zero,add_zero] at hw
    change readsCluster S (ink _ A) A _= _
    rw [show t • basis j=b.val from rfl,← hw]
    have hz := V.flow.joint (root V A u) b.val
    rw [charFun_apply] at hz
    simp only [Semigroup.J,Semigroup.ray,zero_re,zero_im,Real.toNNReal_zero,V.flow.birth,V.flow.eZero,ContinuousLinearMap.id_apply]
    rw [← hz]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    change cexp _= cexp _
    congr 3
    change inner ℝ p (t • basis j)=inner ℝ (p j) t
    rw [real_inner_smul_right,real_inner_comm,basis_inner]; simp
  obtain ⟨hx,hv'⟩ := Dif.estimate μ (fun p : E4 => p j) (by fun_prop) k (C*r⁻¹^D) (by positivity) F hh hs h
  dsimp only [μ] at hx hv'
  rw [← band V _ _ hv] at hx hv'
  constructor
  · exact (integrable_withDensity_iff_integrable_smul (Semigroup.measurable i _)).mp hx
  · unfold Semigroup.transform at hv'
    rw [integral_withDensity_eq_integral_smul (Semigroup.measurable i _)] at hv'
    exact hv'


theorem placed_moment (V : Chamber S i) (H : S.Hierarchy) (A : Weight L) (j : Axis) (hj : j≠i) (k : ℕ)
    (u : ℝ≥0) (hp : Lowered i A u) : Integrable (mom i j k (u+u:ℝ≥0)) (ν V A) := by
  classical
  obtain ⟨C,D,e,hC,he,hE,h⟩ := moments V H A j hj k
  have hv (v : Core L) (hh : v∈A.support) : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ p∈v.val.toFinset, r≤p.1 i+(u:ℝ) := by
    refine (eventually_all_finset _).mpr fun p hw => ?_
    have hu := hp v hh p (by simpa using hw)
    filter_upwards [(gt_mem_nhds hu).filter_mono (nhdsWithin_le_nhds (s:=Ioi 0))] with r hr
    exact le_of_lt hr
  have hb : ∀ᶠ r in 𝓝[>] (0:ℝ), r∈ Ioc 0 e := Ioc_mem_nhdsGT he
  obtain ⟨r,hr,hv⟩ := (hb.and
    ((eventually_all_finset A.support).mpr hv)).exists
  exact (h r hr.1 hr.2 u fun v hh p hp => hv v hh p (by simpa using hp)).1

theorem point_moment (V : Chamber S i) (H : S.Hierarchy) (A : Weight L) (ha : Pressed i A) (j : Axis) (hj : j≠i) (k : ℕ) :
    ∃ (C : ℝ) (D : ℕ), 0 ≤ C ∧ ∀ t : ℝ, 0<t → t≤1 →
      Integrable (mom i j k t) (ν V A) ∧ (∫ p, mom i j k t p ∂ν V A) ≤ C*t⁻¹^D := by
  obtain ⟨C,D,e,hC,he,hE,h⟩ := moments V H A j hj k
  refine ⟨C * ((e/2)⁻¹)^D, D, by positivity,fun t ht hp => ?_⟩
  let r := t*(e/2)
  let u : ℝ≥0 := ⟨t/2,by positivity⟩
  have hr : 0<r := by unfold r;positivity
  have hl : r ≤ e := by dsimp only [r]; nlinarith
  have hu := h r hr hl u (by
    intro v hv p hx
    rw [ha v hv p hx,zero_add]
    change r ≤ t/2; unfold r; nlinarith)
  rw [show ((u+u:ℝ≥0):ℝ)=t by rw [NNReal.coe_add]; exact add_halves t] at hu
  refine ⟨hu.1,hu.2.trans_eq ?_⟩
  unfold r; rw [mul_inv, mul_pow]; ring

/-- Polynomial weight form, before temporal moments/projectors. -/
theorem pay_moment (V : Chamber S i) (H : S.Hierarchy) (A : Weight L) (ha : Pressed i A) (j : Axis) (hj : j≠i) (k : ℕ) :
    ∃ D : ℕ, Integrable (fun p : E4 => ((1+p i)⁻¹)^D * ‖p j‖^(2*k)) (ν V A) := by
  obtain ⟨C,D,hC,h⟩ := point_moment V H A ha j hj k
  let f := fun (p : ℝ × E4) => p.1 ^ D * mom i j k p.1 p.2
  let μ := volume.restrict (Ioc 0 (1:ℝ))
  have hi t : IntegrableOn (fun x => f (x,t)) (Ioc 0 1) :=
    ((show Continuous (fun x => f (x,t)) by unfold f mom;fun_prop).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hm : AEStronglyMeasurable f (μ.prod (ν V A)) := by unfold f mom;fun_prop
  haveI : IsFiniteMeasure μ := by unfold μ; infer_instance
  have hf : Integrable f (μ.prod (ν V A)) := by
    apply (integrable_prod_iff hm).2
    constructor
    · have hy : ∀ᵐ x ∂μ,x∈ Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
      filter_upwards [hy] with t ht
      exact (h t ht.1 ht.2).1.const_mul (t^D)
    apply (integrable_const C).mono' hm.norm.integral_prod_right'
    have hy : ∀ᵐ x ∂μ,x∈ Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
    filter_upwards [hy] with t ht
    have hz := h t ht.1 ht.2
    have hx : 0<t := ht.1
    have he : (0:ℝ) ≤ t^D := pow_nonneg hx.le D
    change ‖∫ p, ‖f (t,p)‖ ∂ν V A‖ ≤ C
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg_of_ae (ae_of_all _ fun _ => norm_nonneg _)),
      show (fun p => ‖f (t,p)‖) = fun p => t^D * mom i j k t p from funext fun p => Real.norm_of_nonneg (mul_nonneg he (mom_nn ..)), integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hz.2 he).trans_eq (by rw [inv_pow]; field_simp)
  let z := Real.exp (-1)
  have hz : 0 < z := Real.exp_pos _
  let d := (D+1 : ℕ)
  have he (p : E4) (hp : 0 ≤ p i) : z*((d:ℝ)⁻¹*((1+p i)⁻¹)^d * ‖p j‖^(2*k)) ≤ ∫ t, f (t,p) ∂μ := by
    let r := (1+p i)⁻¹
    have hr : 0<r := by unfold r; positivity
    have hr' : r ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    calc
      _ = ∫ t : ℝ in Ioc 0 r,t^D*(z * ‖p j‖^(2*k)) := by
        rw [integral_mul_const,← intervalIntegral.integral_of_le hr.le,integral_pow]
        simp only [d,r,Nat.cast_add,Nat.cast_one, zero_pow (show D+1 ≠ 0 by omega),sub_zero,div_eq_mul_inv]
        ring
      _ ≤ ∫ t : ℝ in Ioc 0 r,f (t,p) := by
        apply setIntegral_mono_on ((show Continuous _ from ((continuous_id.pow D).mul_const (z * ‖p j‖^(2*k)))).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
          ((hi p).mono_set (Ioc_subset_Ioc_right hr')) measurableSet_Ioc
        intro x hx
        change x^D*_ ≤ x^D*(Real.exp _ * _)
        have Hx : 0<x := hx.1
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity)) (by positivity)
        have hu : x ≤ r := hx.2
        have hh : x*(1+p i) ≤ 1 := (le_div_iff₀ (by linarith)).mp (by simpa only [one_div] using hu)
        linarith
      _ ≤ _ := by
        refine setIntegral_mono_set (hi p) ?_ (.of_forall fun x hx => Ioc_subset_Ioc_right hr' hx)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact mul_nonneg (pow_nonneg hx.1.le D) (mom_nn ..)
  refine ⟨d,(hf.integral_prod_right.const_mul ((d:ℝ)/z)).mono' (by fun_prop) ?_⟩
  have hd : 0<(d:ℝ) := by simp [d]; positivity
  filter_upwards [before V A] with p hp
  rw [Real.norm_of_nonneg (by positivity)]
  -- pay
  apply le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (he p hp) (by exact div_nonneg hd.le hz.le))
  field_simp
end YM.Outer
