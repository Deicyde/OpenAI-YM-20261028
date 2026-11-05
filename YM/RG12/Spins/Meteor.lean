import YM.RG12.Spins.Ultra
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Chorus
/-! Tangent-station approximation with sharp tolerance (all powers after block). Finite-pack algebra adapted from Heir.dissent. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir.Pace
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Matrix Next Next.Fluctuations Next.SectorChange
    Next.SectorChange.Rows Schur Wisps AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
    AnalyticBridge.SectorAffine.Offset AnalyticBridge.LocalGaussianLaws.Lift Exterior Bloch Bid Push.SectorMeasure
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}

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
    (hu : 0≤u) (hs : 0<s) (hτ : 0<τ) : RG12.Spins.Super (residualFare P G V M A E s τ X u):= by
   let C := V*Remote.pieces P G*M*A*u*2^4 + M*E*X*u
   have hp:= Remote.pieces_nonneg P G; have hC: 0 ≤ C:= by unfold C; positivity
   have hR:= RG12.Spins.super_gate (lt_min hs hτ) hC 4
   intro d
   filter_upwards [small_span P, hR d] with x hx hX' -- ids
   let r:ℝ:= radiusB x; have hr:0≤ r:= Nat.cast_nonneg _
   have hx': (span P x:ℝ) ≤ r:=Nat.cast_le.mpr (hx.trans (Nat.div_le_self ..))
   have hw : (LocalJet.grain (span P x):ℝ) ≤ (2*(1+r))^4:=by
     unfold LocalJet.grain; push_cast; gcongr; linarith only [hx',hr]
   have hf : fees P G V M A u x ≤ V*Remote.pieces P G*M*A*u*2^4*(1+r)^4:=by
     rw [mul_assoc (V*_*_*_*_),← mul_pow]; unfold fees; calc
       _ ≤ V*(Remote.pieces P G*((2*(1+r))^4))*M*A*u:=by gcongr
       _ = _:=by ring
   apply le_trans _ hX'; unfold residualFare; rw [abs_of_nonneg (by unfold fees LocalJet.grain; positivity)]; apply le_trans _ (le_abs_self _)
   let s':ℝ:= min s τ; have h1 : 1≤ (1+r)^4:= one_le_pow₀ (by simp [r])
   calc
    _ ≤ V*Remote.pieces P G*M*A*u*2^4*(1+r)^4*Real.exp (-s'*(Stores.till x))+(M*E*X*u)*((1+r)^4*Real.exp (-s'*r)):=by
      apply add_le_add
      · gcongr; exact min_le_right ..
      · gcongr _ * ?_
        apply le_trans (Real.exp_monotone ?_) (le_mul_of_one_le_left (Real.exp_pos _).le h1)
        change -s*r ≤ -s'*r; exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left ..)) hr
    _ ≤ C * (1+r)^4 * (Real.exp (-s'*r)+ Real.exp (-s'* Stores.till x)):=by
       have hh : ∀ a b c d t:ℝ,0≤a →0≤b→0≤c→0≤d→0≤t → a*t*c+b*(t*d) ≤ (a+b)*t*(d+c):= fun a b c d t ha hb hc hd ht=> by nlinarith only [show 0 ≤ a*t*d by positivity,show 0 ≤ b*t*c by positivity]
       exact hh _ _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) -- maybe positivity won't do inequalities

theorem dissent (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (p:ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Lift.Booth Pt S T → 100*(1+radiusB x) ≤ c.val →
      ∀ (F : Forest S.ratio) (k : S.Choices), difference T F x k 0=0 ∧ ‖fderiv ℝ (difference T F x k) 0‖ ≤ (x^p)⁻¹ := by
  obtain ⟨A,X,s,E,V,M,τ,δ,ha,hX,hs,hE,hV,hM,hτ,hδ,H⟩ := focused G P Pt.bind Pt hp rfl
  obtain ⟨C,b,hC,hb,hB⟩ := chord_chart_cost G
  obtain ⟨r,Y,hr,hY,h⟩ := survey G P Pt hp 1
  let u := max C 1; have hu : 1 ≤ u := le_max_right ..; have hu' := zero_lt_one.trans_le hu
  filter_upwards [H,h,Offset.correct_f0 G P Pt,declines P G (zero_le_one.trans hV) (zero_le_one.trans hM) ha hE hX hu'.le hs hτ p,
    eventually_gt_atTop (0:ℝ)] with x H h hq hw hx c f S T hP hT hF F k
  let g := difference T F x k
  have hg : DifferentiableAt ℝ g 0 := (((h S T hP hT.1 hF F k 0 (by simpa using hr.le)).smooth.differentiableAt (by norm_num)).sub
    (first T F x).differentiableAt)
  have Ht := Work.E09.temp_pos hx; let U := bareStores S
  let q := Chi.canonical
  let D := fees P G V M A u x * ((1+(Stores.till x:ℝ))*u)
  have hp := Remote.pieces_nonneg P G; have hD : 0 ≤ D := by unfold D fees LocalJet.grain; positivity
  refine favor (D:=D) ?_ (by positivity) hg
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
  apply (pi_norm_le_iff_of_nonneg (show 0≤ ‖y‖*(D*‖y‖+(x^p)⁻¹) by positivity)).mpr
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
      _ ≤ _ := by gcongr; exact (le_abs_self _).trans hw
  rw [pane_zero]; rfl
end YM.PhysicalNext.JointLoad.Heir.Pace
