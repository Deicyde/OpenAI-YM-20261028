import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Lagoon

/-!
# Tuning broadcast post-L, uniform remainder for every possible E singleton
 lens. Can NOW use signed principal Φ with full stencil-M data shapes on
 THIS scale (as an addition to above, carrying actual gardens rhythm). No
 statement about loan/UUID of Heir and Forest in isolation. Kernel discrepancy
 paid; Φ not substituted on m_U without passing intake. No Rank Range charged
 via a vacuous Gauge (cap on Θ independent of future pledges).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mercury
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism Brim Lotus Peak
open WardBin.Lies Push.PriceCompiler Foramen Gate
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {B B' : BudgetPoint} {Y : Support c} {K : Support f} {U : Config G c} {p j n : ℕ} {L : Side}
variable {d A t C' w M N z β W k ε J' L₀ X' : ℝ}

variable (G : Gauge) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (n p : ℕ) (C : Libretto G n) (D' : Record) (hn : 2≤n)
variable (W : ℝ) (o : ConnectedActivityE6.Target.Order G W) (χ κ : Chi)

-- terminology: royal = full *bars at head at actual T*, not Script. Tuning appears before F resummation.
include hn hD
set_option maxHeartbeats 300000 in
lemma trove (hD' : D'.ε≤1/4) : ∃ B : ℝ→ℝ, Rate G L (-(1/2)) B ∧ ∀ᶠ s in atTop,
    ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L s S T →
    ∀ (R : Rep G f) (Q : ConnectedActivityE6.Target G P) (μ α:ℝ) (H:Cash W s μ L Q o α T R),
    ∀ (F : Forest S.ratio) (X : Coat T F) (i : ℕ), H.supportP (Opacity.key S i)=yFoot S (R.activities.reg i).support s Q.halo →
    X.x=s → X.width=o.K→X.χ=χ→ X.manifest → ∀ (P':BudgetPoint), P'.B=radiusB s→ P'.power=p → Plays C D' P' R.p P T s →
    ∀ (Y : Support c) (I:Type) [Fintype I] [DecidableEq I] (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I) (q : Chi) (b : ℝ), ∀ y∈Y,
    coverNumber (radiusB s) Y ≤ radiusB s → Healthy P'.threshold Y X.V → Scrim X a →
    ∀ (M:Lotus.Leaf R),M.turn=.logKey i → ∀ (L' : Config G f→ℝ), R.p.Regular (R.activities.reg i).support L' → M.ingredient=masked R.p.threshold (R.activities.reg i).support L' →
    ∀ j ≤ n, ∀ U : Slab G c j, (∀ i,P'.dirBound y (U i))→ (∀ i, ‖U i‖ ≤ canopyW G L p s) →
    let V:= journey X.V j U
    let g x:= M.cinema (vary X (V x)) {Opacity.key S i} W o.a Q.table Q.halo (podium S G Y X.B)
    let u:= a.hymn T (gStep R.beta) q b X.k L' (Baffle.magic D' R.p R.beta κ) 1
    Brush n (M.weight*(2*|B s|)) 1 (fun x=> g x-u (V x)) 0 := by
  obtain ⟨A⟩:= Prism.anthems n
  obtain ⟨M,X,J,v,t,h,hM,h₀,hX,hJ,hv,ht,hl⟩:= spicules G P L D hD n p C D' hn W o χ
  obtain ⟨d,Y,hD'₀⟩:= weave G
  let K x:= Coat.burst G L x; let S' x:= K x*(5*o.a*fiery G x L+|o.cap| *fiery G x L)
  have hscaleLux : Rate G L 0 S' := by simpa only [add_neg_cancel] using! ((burst_rate G L).mul (((Rate.flame).mul_left _).add ((Rate.flame).mul_left _)))
  obtain ⟨N,δ,V,hN,hδ,hV,hS⟩:= sweaters G P L n A D' χ κ W o d Y hD'₀ hM hX hJ hv ht hscaleLux
  let r h:= incomingE G L h; let U:=sliceD G L D'
  have hj:= incomingE_rate G L
  have hy := blends n A h hN hV hδ (hj.weaken (show -(11/10:ℝ)≤ -(1/2) by norm_num)) (by norm_num) (waft G L D' _)
  refine ⟨_,hy,?_⟩
  have hv := hD'₀.warm
  filter_upwards [hS,hl, snip G L P D' hδ, hj.below (by norm_num) 1 zero_lt_one,
    ((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hv), ((absolut hJ).mul (inverse_mist G L)).below (by norm_num) (1/2) (by norm_num)]
    with s hQ hL h' he hj hg c f S T hs h'' R Q μ α H F X' i hht hX hw hk hM P' hm hp hh Z I _ _ a q b y hY ho hV hu u' hU L' hL' hu' j hJ' E hE hr V' g u
  subst s; let x:=X'.x; have he' := H.laws.data; have hy : Intake P T X'.x R:= H.laws.intake
  have ht := he'.localP F X' rfl hw hM |>.sails
  have hx₁:= ht.room
  obtain ⟨hC,hC',hG,hΓ⟩:= he'.safety; have hκ:= hΓ F X' rfl hw hM; have hvU := ht.room.temperatures
  have hZ : 0<X'.t:= ht.room.fiery
  have hb' : X'.t=fiery G x L := by unfold Coat.t x; rw [he'.funds.length_eq]
  have hθ : R.p.threshold=X'.t:= hy.received.temp
  have hh' := hL c f S T hs he'.funds he'.access F X' rfl hk hw hM ht P' R.p hp hh I Z _ a q b y hY hm (hm.symm ▸ ho) hu hV j E hJ' hE hr
  have hp g : ‖volume6 X' a g X'.V‖ ≤ o.cap*X'.t := by change ‖voltage X' _‖≤_; rw [← Vine.agrees_all _ ht.room hM]; exact hκ.1 _
  have hc:0<o.a*X'.t:= mul_pos o.large hZ
  have hz : V' 0=X'.V:= Planned.AtomRegular.Sample.journey_origin .. -- edit
  have hw' g : ContinuousAt (volume9 X' a q 1 b g ∘ V') 0 := by
    have hj := (hh'.offset g).smooth.add (hh'.out g).smooth
    apply ContinuousAt.congr hj.continuousAt
    exact Eventually.of_forall (fun x=> sub_add_cancel (volume9 X' a q 1 b g (V' x)) _)
  have hk' : 8*o.a*X'.t≤d/2 := by rw [hb']; exact (le_abs_self _).trans hj
  let hD'Z:=hh'.toward
  have he₀ := Silica.nearby X' hD'₀ hz hh'.sunny
  obtain ⟨ht₀,H₀,-⟩:= h' c f S T R he'.funds.length_eq hy
  have hϖ : 0< K x:= by
    unfold K burst; have hh :0 < betaF G x L:= by rw [← he'.funds.length_eq]; exact zero_lt_one.trans hy.height
    positivity
  have hJ : |J x| ≤ X'.t/2:= by
    apply le_of_mul_le_mul_right _ (inv_pos.mpr hZ); rw [hb',div_mul_eq_mul_div,mul_inv_cancel₀ (by rw [← hb']; exact hZ.ne')]; exact (le_abs_self _).trans hg
  let scaleLux := S' x
  have hs': 0 ≤ scaleLux:= mul_nonneg hϖ.le (by rw [← hb']; rw [show 5*o.a*X'.t=5*(o.a*X'.t) by ring]; positivity)
  have ht' : Ranks X' i R a q κ b D' V' d o.a 0 n := lighthouse X' i R a q κ b D' hD'₀ hz hy o.a hD'Z.self_of_nhds.1 hD'Z.self_of_nhds.2 (fun i j=> (hh'.area.liable i j).smooth) (fun i j=> (hh'.skies.liable i j).smooth) (fun i=> (hh'.out i).smooth) (fun i=> (hh'.offset i).smooth)
    (fun i=> (Silica.chargeMode X' _ hh'.sunny (a.address i)).smooth)
  refine (wickets X' i R a q κ b D' hy hu ht.room u' hU L' hL' hu' hD'₀ A (fun z hh=> hQ c f S T F X' rfl he'.funds hk hk' i R hy I Z a q b y hY ho h j E hh' z hh) ht' hc
    (flowJourney X'.V E) hh'.horizon ht₀ H₀ hh hV (hD'Z.and he₀|>.mono fun _ h=> ⟨h.1.1,h.2⟩) (fun i=> show Tendsto (volume9 X' a q 1 b i ∘ V') _ (𝓝 (volume9 X' a q 1 b i X'.V)) from by have ht := (hw' i).tendsto; rwa [Function.comp_apply,hz] at ht) (m:=o.cap+1/2) (L:=scaleLux) ?_ ?_ hk' hp ?_ hs' ?pos Q.halo W Q.table).climb
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self _) zero_le_two) u'.profit) le_rfl
  case pos => unfold incomingE; have hx : 0 < betaF G X'.x L:= by rw [← he'.funds.length_eq]; exact zero_lt_one.trans hy.height
              positivity
  · intro i; let A:=volume9 X' a q 1 b i X'.V; let B:=volume6 X' a i X'.V
    have hf:= (hh'.offset i).bound; change ‖volume9 X' a q _ _ _ (V' 0)- volume6 X' a i (V' 0)‖ ≤ |J x| at hf; rw [hz] at hf
    refine le_trans (show ‖A‖ ≤ ‖A-B‖+‖B‖ by simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub A B 0) ?_; apply (add_le_add (hf.trans hJ) (hp i)).trans; linarith only
  · rw [hθ]; nlinarith only [mul_le_mul_of_nonneg_right hD' hZ.le, mul_le_mul_of_nonneg_right hC' hZ.le,hZ]
  unfold Baffle.screen
  change (5*_ * X'.t + _*X'.t)/_ ≤ S' x
  unfold S' -- edit
  rw [← hb', abs_of_pos hC, div_eq_mul_inv, mul_comm (K x)]
  have ht : (gStep R.beta)⁻¹ ≤ K x := burst_h (by rw [← he'.funds.length_eq]; exact hy.window.2)
  exact mul_le_mul_of_nonneg_left ht (by rw [show 5*o.a*X'.t=5*(o.a*X'.t) by ring]; positivity)
end YM.PhysicalNext.Repeat.Mercury
