import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Cues
import YM.Next.BOUNDARY.Derived
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Survey

/-!
# Lie predictor in the bare schedule: deviation at first order

Take a real infinitesimal test only in the *bare* stencil. Then true and
smoothly extended expressions match (NOT globally for other stores at a
mask boundary). Use the LocalGaussianLaws selected price at every
reading position to pass to a uniform tangent norm by a limit (no loss in
the nonlinear rate of the value comparison, in particular no extra period
or number-of-rows charge). This predictor is still in the tree gauge; the
re-gauging for E's low-order map is later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Matrix Next Next.Fluctuations Next.SectorChange
    Next.SectorChange.Rows Schur Wisps AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
    AnalyticBridge.SectorAffine.Offset AnalyticBridge.LocalGaussianLaws.Lift Exterior Bloch Bid Push.SectorMeasure
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}

section tangent
variable (T) (F : Forest S.ratio) (x : ℝ) (k : S.Choices)

def shaped (K : Matrix (Body 1 f) (Body 1 c) ℝ) : Directions G c →L[ℝ] Directions G f := LinearMap.toContinuousLinearMap {
  toFun u i := (WithLp.toLp 2 (fun j : G.ColorIndex => (K *ᵥ parts G 1 (Flat.labels u) j) (i.1,Exterior.coord i.2)))
  map_add' u v := by
    funext i; ext j; exact congr_fun (K.mulVec_add (parts G 1 (Flat.labels u) j) (parts G 1 (Flat.labels v) j)) (i.1,Exterior.coord i.2)
  map_smul' t v := by
    funext i; ext j; exact congr_fun (K.mulVec_smul (t:ℝ) (parts G 1 (Flat.labels v) j)) (i.1,Exterior.coord i.2) }

def carriedCopy (S : StepData c f) : Directions G c →L[ℝ] Directions G f := LinearMap.toContinuousLinearMap {
  toFun := linearCopy S.ratio
  map_add' u v := by funext i; unfold linearCopy; split <;> simp [*]
  map_smul' t v := by funext i; unfold linearCopy; split <;> simp [*] }

def treeMap := shaped (G:=G) (extracted S F (installed S.ratio T.R.A0)) - carriedCopy S
lemma tree_value (u : Directions G c) : treeMap T F u=doc T F (Flat.labels u) := by
  funext i; ext j
  simp_rw [doc,collect,low,Pi.sub_apply,PiLp.sub_apply]
  rw [show (stretch F _ (i.1, Exterior.coord i.2)) j= _ from congr_fun (Work.F04.parts_stretch F (installed S.ratio T.R.A0) (Flat.labels u) j) _]
  change _ - (linearCopy S.ratio u i) j = (extracted S F (installed S.ratio T.R.A0) *ᵥ parts G 1 (Flat.labels u) j) _ - _
  change _ - (linearCopy S.ratio u i) j = _ - (blueprint S (Flat.labels u) (i.1, Exterior.coord i.2)) j
  unfold blueprint; rw [Flat.collected]; unfold Flat.labels
  rw [← coord_map,axisEquiv.symm_apply_apply]; rfl

def pick := ContinuousLinearMap.pi (R:=ℝ) (M:=Directions G f) fun (i : In x (bareStores S) F (G:=G)) =>
  (PiLp.proj 2 (fun _ : G.ColorIndex => ℝ) i.2).comp (ContinuousLinearMap.proj i.1.val.val)

def first := (pick (G:=G) F x).comp (treeMap T F)
lemma first_read (u : Directions G c) : first T F x u=Lift.marked (bareStores S) x F (doc T F (Flat.labels u)) := by
  unfold first; rw [ContinuousLinearMap.comp_apply,tree_value]; rfl

def difference := forecast T x F k - (first T F x : Directions G c → Prices G (clear S x F))
end tangent

variable {D ε : ℝ}
private lemma favor {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (h : ∀ᶠ y in 𝓝 (0:E), ‖f y‖ ≤ ‖y‖*(D*‖y‖+ε)) (hh : 0≤ε) (hf : DifferentiableAt ℝ f 0) :
    f 0=0 ∧ ‖fderiv ℝ f 0‖ ≤ ε := by
  have h₀ : f 0=0 := norm_le_zero_iff.mp (by simpa using h.self_of_nhds)
  refine ⟨h₀,ContinuousLinearMap.opNorm_le_bound _ hh fun v => ?_⟩
  let g (s : ℝ) := s • v
  have hV : HasDerivAt (f ∘ g) (fderiv ℝ f 0 v) 0 := hf.hasFDerivAt.comp_hasDerivAt_of_eq _ (by unfold g; simpa using (hasDerivAt_id' (0:ℝ)).smul_const v) (by simp [g])
  have hv := hV.tendsto_slope.norm
  let u (s : ℝ) := (D*‖g s‖+ε)*‖v‖
  have hg : Tendsto g (𝓝[≠] 0) (𝓝 (0:E)) := ((by simpa [g] using (show Continuous g from by unfold g; fun_prop).tendsto 0 : Tendsto g (𝓝 0) (𝓝 0)).mono_left nhdsWithin_le_nhds)
  have hu : Tendsto u (𝓝[≠] 0) (𝓝 (ε*‖v‖)) := by simpa only [u,norm_zero,mul_zero,zero_add] using (((hg.norm.const_mul D).add_const ε).mul_const ‖v‖)
  refine le_of_tendsto_of_tendsto hv hu ?_
  filter_upwards [hg.eventually h, self_mem_nhdsWithin (a:=(0:ℝ)) (s:={0}ᶜ)] with s he hs
  rw [slope_def_module,Function.comp_apply,Function.comp_apply,show g 0=0 from zero_smul ..,h₀,sub_zero,sub_zero,norm_smul,norm_inv]
  have hs' : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  change ‖s‖⁻¹ * ‖f (g s)‖ ≤ _
  apply (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq
  nth_rw 1 [show ‖g s‖=‖s‖*‖v‖ from norm_smul ..]; unfold u; field_simp

private def fees (P : Patch) (G : Gauge) (V M A u : ℝ) (x : ℝ) := V*(Remote.pieces P G*LocalJet.grain (span P x))*M*A*u
private def residualFare (P : Patch) (G : Gauge) (V M A E s τ X u x : ℝ) :=
  fees P G V M A u x*Real.exp (-τ*(Stores.till x))+(M*E*X*u)*Real.exp (-s*radiusB x)
private lemma declines (P : Patch) (G : Gauge) {M A E V X u s τ : ℝ} (hv : 0≤V) (hm : 0≤M) (ha : 0≤A) (he : 0≤E) (hX : 0≤X)
    (hu : 0≤u) (hs : 0<s) (hτ : 0<τ) : ∀ᶠ x : ℝ in atTop, residualFare P G V M A E s τ X u x ≤ temp x := by
  open Extra.Iteration.Scales in
    have hh := Tiny.cover_size.pow tendsto_id 4
    let C := V*Remote.pieces P G*M*A*u*2^4 + M*E*X*u; have hp := Remote.pieces_nonneg P G
    have hC : 0≤C := by unfold C; positivity
    filter_upwards [small_span P, hh _ zero_lt_one, Tiny.const tendsto_id C hC _ zero_lt_one, plume τ 3 hτ, Extra.Iteration.Scales.first s 3 hs,
      eventually_gt_atTop (1:ℝ)] with x hx he hL ht hQ h
    simp only [id_eq, Real.rpow_one] at he hL
    have hw : (LocalJet.grain (span P x) : ℝ) ≤ 2^4*x := by
      unfold LocalJet.grain; push_cast
      have h : (span P x:ℝ) ≤ radiusB x := by exact_mod_cast hx.trans (Nat.div_le_self ..)
      apply le_trans (b:=(2*(1+(radiusB x:ℝ)))^4) (by gcongr; linarith)
      rw [mul_pow]; gcongr; exact he.2
    have hb : fees P G V M A u x ≤ V*Remote.pieces P G*M*A*u*2^4*x := by unfold fees; refine le_trans (b:=V*(Remote.pieces P G*(2^4*x))*M*A*u) ?_ (le_of_eq (by ring)); gcongr
    have hx : x⁻¹ ≤ temp x := by
      unfold temp; apply le_trans _ (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity)))
      exact inv_anti₀ (by positivity) (Real.sqrt_le_self_iff.mpr (Or.inr h.le))
    have ht' : 0<x := zero_lt_one.trans h
    unfold residualFare
    calc
      _ ≤ (V*Remote.pieces P G*M*A*u*2^4*x)*x^(-(3:ℝ)) + (M*E*X*u*x)*x^(-(3:ℝ)) := by
        exact add_le_add (mul_le_mul hb ht (by positivity) (by positivity)) (mul_le_mul (le_mul_of_one_le_right (by positivity) h.le) hQ (by positivity) (by positivity))
      _ = C*(x*x^(-(3:ℝ))) := by unfold C; ring
      _ ≤ x * (x*x^(-(3:ℝ))) := by gcongr; exact hL.2
      _ = x⁻¹ := by rw [Real.rpow_neg ht'.le, show x^(3:ℝ)=x^(3:ℕ) from by norm_num]; field_simp
      _ ≤ temp x := hx

theorem dissent (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) :
    ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Lift.Booth Pt S T → 100*(1+radiusB x) ≤ c.val →
      ∀ (F : Forest S.ratio) (k : S.Choices), difference T F x k 0=0 ∧ ‖fderiv ℝ (difference T F x k) 0‖ ≤ temp x := by
  obtain ⟨A,X,s,E,V,M,τ,δ,ha,hX,hs,hE,hV,hM,hτ,hδ,H⟩ := focused G P Pt.bind Pt hp rfl
  obtain ⟨C,b,hC,hb,hB⟩ := chord_chart_cost G
  obtain ⟨r,Y,hr,hY,h⟩ := survey G P Pt hp 1
  let u := max C 1; have hu : 1 ≤ u := le_max_right ..; have hu' := zero_lt_one.trans_le hu
  filter_upwards [H,h,Offset.correct_f0 G P Pt,declines P G (zero_le_one.trans hV) (zero_le_one.trans hM) ha hE hX hu'.le hs hτ,
    eventually_gt_atTop (0:ℝ)] with x H h hq hw hx c f S T hP hT hF F k
  let g := difference T F x k
  have hg : DifferentiableAt ℝ g 0 := (((h S T hP hT.1 hF F k 0 (by simpa using hr.le)).smooth.differentiableAt (by norm_num)).sub
    (first T F x).differentiableAt)
  have Ht := Work.E09.temp_pos hx; let U := bareStores S
  let q := Chi.canonical
  let D := fees P G V M A u x * ((1+(Stores.till x:ℝ))*u)
  have hp := Remote.pieces_nonneg P G; have hD : 0 ≤ D := by unfold D fees LocalJet.grain; positivity
  refine favor (D:=D) ?_ Ht.le hg
  let ε := min b (min (δ/u) ((temp x)/(4*C)))
  have he : 0<ε := lt_min hb (lt_min (by positivity) (by positivity))
  filter_upwards [Metric.closedBall_mem_nhds (0:Directions G c) he] with y hy
  have he : ‖y‖ ≤ ε := by simpa using hy
  let t := u * ‖y‖; have ht : 0≤t := mul_nonneg hu'.le (norm_nonneg _)
  have h₂ : t ≤ δ := (mul_comm ..).trans_le ((le_div_iff₀ hu').mp (he.trans ((min_le_right ..).trans (min_le_left ..))))
  let v := Flat.labels y; let Q := represent v
  have hv : ‖v‖ ≤ t := ((pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr fun i => norm_le_pi_norm y _).trans (le_mul_of_one_le_left (norm_nonneg y) hu)
  have hvQ : Q=increment 1 y := by unfold Q represent v; rw [Flat.collected]
  have h₁ : ∀ i, G.chord (Q i) ≤ C*‖y‖ := by
    intro i; rw [hvQ,increment]; simp only [Pi.one_apply,mul_one]; have ht := norm_le_pi_norm y i
    exact (hB _ (ht.trans (he.trans (min_le_left ..)))).trans (mul_le_mul_of_nonneg_left ht hC.le)
  have hf : U.flags=flags (temp x) Q := by
    ext i; constructor
    · exact False.elim ∘ Finset.notMem_empty i
    intro hi; obtain ⟨p,hp,hQ⟩ := (flags_spec ..).mp hi
    have h := travel_chord Q (square p.2.val.1 p.2.val.2) p.1 _ h₁
    norm_num only [square,List.length_cons,List.length_nil, Nat.reduceAdd, Nat.cast_ofNat] at h
    change G.chord (faceValue Q p) ≤ 4*(C*‖y‖) at h
    have he' := (le_div_iff₀ (show 0<4*C by positivity)).1 (he.trans ((min_le_right ..).trans (min_le_right ..)))
    linarith
  have hQ o : Remote.paid S (replica S.ratio Q) o (radiusB x) t := by
    intro i _; unfold replica; split
    · rw [G.chord_one]; exact ht
    exact (h₁ _).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (norm_nonneg _))
  apply (pi_norm_le_iff_of_nonneg (show 0≤ ‖y‖*(D*‖y‖+temp x) by positivity)).mpr
  intro i
  let Y : LinkArray G (Frozen U x F) := 1
  have hq' := congr_fun (hq S T hP hT.1 U F Q hf k q 1) Y
  have hp : forecast T x F k y = meanLog U F T x Q k q 1 Y := by
    unfold forecast Function.comp; rw [school_eq hT.1 F x k q 1 Y (reader G c y),reader_field,← hvQ]; exact (Offset.reads_actual T x k U F _ _ _ _ hq').2.1
  let o := Wisps.front U F i
  have hU : Remote.Clears U x o (radiusB x) := by simp [Remote.Clears,U,bareStores,Stores.dome,Stores.place,halo_spec]
  have h := H t ht h₂ S T hP hT hF U o F hU Q hf v hv (hQ o) (fun i _ => rfl) k q 1 Y i (by simp [o]) Assembly.Geometry.endpoint
  dsimp only at h
  rw [show offCenter _ _= meanLog U F T x Q k q 1 Y from ?_] at h
  · rw [difference,Pi.sub_apply,hp,first_read]
    change |meanLog U F T x Q k q 1 Y i - Lift.marked U x F (doc T F v) i| ≤ _
    apply h.trans
    calc
      _ = ‖y‖*(D*‖y‖+residualFare P G V M A E s τ X u x) := by unfold t D residualFare fees widen; ring
      _ ≤ _ := by gcongr
  rw [pane_zero]; rfl
end YM.PhysicalNext.JointLoad.Heir
