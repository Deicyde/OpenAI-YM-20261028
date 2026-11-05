import YM.TraceExtension.Quince.Vent
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Chant

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury
open Bid Planned.PrimaryIntegral295 WaterLevels
open Cub
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Circlet PPX Next.Free
variable {G : Gauge}{M : Sheet G}{K : MapPrices}{C:Programs M}{R:ℕ→ℕ→Record}{V: Targets M K}{Y: Expenses V}{l:ℕ→ℝ}{W : Return.Wages}{r : ℕ→ℕ→ℕ} {J N n :ℕ} {P:Teller G}
variable (D: Rolls M) (h:Register D Y W l)
lemma bairn (Lx : Side)(C : Libretto G n)(D:Record)(K : KernelChoices)(M: ConnectedActivityE6.Target G P) (μ t:ℝ)(d j i r:ℕ)(P0 P1 : Stage)(o:Target.Order G t)(hD:D.ε≤1/4) (hi:4≤ i)(hj:4≤j)(hn:2≤ n)(hz:d≤j)(hm:0<μ)(Zζ:ℝ)(hζ:0<Zζ):∀ᶠ x in atTop, ∃ I:Eve j i d n Lx P0 P1 P K C D M t o μ x r,I.current ≤ sprite G x Lx Zζ ∧ I.sail ≤ sprite G x Lx Zζ:=by
  let F:=(Labels.frames G).level d; let A:= hol G; let S0:=localSection G d
  let e:= title G P1; let a:=title G P0; have he₀:1≤e:=title_one ..; have ha:1≤a:=title_one ..
  let h:= credibility G P1.supportExponent P1.order P1.power
  have hh :0<h:=mul_pos (Real.exp_pos _) (zero_lt_one.trans_le he₀); let y:=Doors.rate Lx; have hy:0<y:= Doors.rate_pos _
  let z:=Motion.orbitCost F * Local.errorPrice (hol G) F*(corn G d*a)
  have hw := (Local.probe_budget F).choose_spec.choose_spec.1; let Z:= Local.testPrice F; have hk:1 ≤ Z:=hw
  have hx:0< z:=mul_pos (mul_pos (zero_lt_one.trans_le (Motion.orbitCost_one_le F)) (zero_lt_one.trans_le (Local.errorPrice_pos A F))) (mul_pos (zero_lt_one.trans_le cornBig) (zero_lt_one.trans_le ha))
  let κ:= min ((y/2)/(z*Z)) Zζ; let V:=Push.Local.tests F; have hκ:0<κ:=lt_min (div_pos (half_pos hy) (mul_pos hx (zero_lt_one.trans_le hk))) hζ
  let g (p:Local.Probe G d) (x:ℝ):=Push.Local.partPrice A p*(Cub.gaugeMeter d*((Lx.val:ℝ)^d*(2*(e*x+x))))+x
  have he (p:Local.Probe G d) : ∀ᶠ x in nhds (0:ℝ), g p x ≤ κ:= ((show Continuous (g p) by unfold g; fun_prop).continuousAt (x:=0)).eventually (ge_mem_nhds (show g p 0 < κ by simpa [g] using hκ))
  obtain ⟨b,(hv:0<b),hb⟩:= Metric.mem_nhds_iff.mp (V.eventually_all.mpr (fun i _=> he i))
  let Q:= b/2; have hQ':0<Q:=half_pos hv; have hg (p) (hz:p∈ V) : g p Q ≤ κ:= hb (Metric.mem_ball.mpr (by rw [Real.dist_eq,sub_zero,abs_of_pos hQ']; exact half_lt_self hv)) p hz
  obtain ⟨u,hu,hγ⟩:= Mercury.tuned M P0.power C D t μ o Chi.canonical Lx hn hD
  let B:= (Lx.val:ℝ)^d; let T:=Local.readPrice A F; have h':1 ≤ T:=Push.Local.readPrice_pos A F
  let S:= (y/2)/(z*T*h); have hS:0<S:=div_pos (half_pos hy) (mul_pos (mul_pos hx (zero_lt_one.trans_le h')) hh)
  filter_upwards [Rebuild.geometry (G.slopeConstant*Real.log Lx.val), V.eventually_all.mpr (fun p _=> eventually_all.mpr (fun i=> highstar p S0 A (sound G d) (Next.Foundations.valuation G d) K.penalty_pos hj hi hz (i: F.Index) Lx hQ')), hγ, sprited (fGood hu (by norm_num)) hQ', scales_m C D Lx P0.power r (Q/e) (div_pos hQ' (zero_lt_one.trans_le he₀)), (swell G Lx).eventually_ge_atTop 1, Delay.shift_pos G Lx, sprited (fGood hu (by norm_num)) hζ, Blush.fruition hm (L:=Lx) M B S hS] with x hx' ha' H hf hU hs hhP hℓ hM
  -- hu may negative; take abs.Survey.
  have ht(P' P'': BudgetPoint)(ht:P'.threshold=temp x)(hQ:P''.threshold=fiery G x Lx) : Blend 2 P''.threshold P'.threshold:=by
     refine ⟨one_le_two,P''.threshold_pos,P'.threshold_pos,P''.threshold_le,P'.threshold_le,?_ ,?_⟩
     · apply (div_le_iff₀ P''.threshold_pos).mpr; rw [ht,hQ]; exact hx'.2.2
     apply (div_le_iff₀ P'.threshold_pos).mpr; rw [ht,hQ]; exact hx'.2.1
  let κ' := sprite G x Lx κ
  have hτ:=@coinP_pos G Lx x
  have hπ: κ'≤κ :=div_le_self hκ.le (Real.one_le_sqrt.mpr hs)
  refine ⟨⟨sprite G x Lx Q,sprite_pos x hQ',ht,|u x|,abs_nonneg _,?_,fun P' P'' _ f X α β a δ ψ μ hω=>?_,(fun p hp a c f S T Y A C C' b c' hB hX _ _=> (ha' _ hp a) _ _ _ _ _ A C C' b c' hB hX),κ',(sprite_pos x hκ).le,fun p hp=> ?_, fun c h' N H Z hZ=>?_⟩,div_le_div_of_nonneg_right (min_le_right ..) hτ.le,hℓ⟩
  · intro c f' S T hk R e H0 F X i hx hh hχ hu J hK hb hP Y I _ _ a q b z hz hy he' hA M hM L' hL hL' j U hj hu' hn; exact (H c f' S T hk R e H0 F X i hx hh hχ hu J hK hb hP Y I a q b z hz hy he' hA M hM L' hL hL' j U hj hu' hn).climb (mul_le_mul_of_nonneg_left (le_abs_self _) M.profit) le_rfl
  · have hc:=ht _ _ α β; have hΩ:= hU μ hω f X P' P'' β ((div_le_iff₀ hc.fine).1 hc.accounted) (a.symm ▸ hx'.1.1) δ (ψ.trans (by unfold packing; have h:= Lx.property; exact one_le_pow₀ (by omega)))
    obtain ⟨h'ω,hR⟩:=hΩ
    have hb : 0 < μ := (div_pos hhP (by norm_num)).trans_le hω
    have hk:= opal_part C D P' P'' (Malachite.radiusD x) Lx X r x _ (show 0 ≤ gStep μ from inv_nonneg.mpr (Real.sqrt_nonneg _))
    have heξ:= clocks_pos C (zero_le_one.trans he₀)
    refine ⟨hk.trans h'ω,?_⟩
    have hi:0 ≤ AnalyticBridge.LocalGaussian.Moments.meter (Lute.heads G P'' Lx X r x) 0 D.K (2*((n+1)+(n+1))):=by unfold AnalyticBridge.LocalGaussian.Moments.meter AnalyticBridge.LocalGaussian.Moments.inflate; positivity [D.peak]
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk heξ) hi).trans; apply (hR e (zero_le_one.trans he₀)).trans_eq; unfold sprite; field_simp
  · have h:=@Cub.horizon d; have ht:= Local.partPrice_pos A p
    apply le_trans (_ : _ ≤ g p (sprite G x Lx Q))
    · exact (show g p _=sprite G x Lx (g p Q) by unfold g sprite; ring).trans_le (div_le_div_of_nonneg_right (hg p hp) hτ.le)
    unfold g; gcongr
  let Y:= H.p.mass Z.live.crest Z.live.weight
  set m:= Blush.marvel (Q:=M) (L:=Lx) (x:=x) Z
  have hB:0≤ B:=by unfold B; positivity
  have hL:= hM N H Z (B:ℂ) (by rw [Complex.norm_real,Real.norm_of_nonneg hB]); rw [Complex.norm_real,Real.norm_of_nonneg hB] at hL
  have he': B*(m+m)≤ S* h:= hL.1.trans (mul_le_mul_of_nonneg_left (hZ.trans_le (by exact h')) hS.le)
  intro Fp kp
  change Motion.orbitCost F*(Local.errorPrice (hol G) F*(corn G d*a*kp)) ≤ y
  have hh: T*(B*(m+m)) ≤ (y/2)/z:= (mul_le_mul_of_nonneg_left he' (by positivity)).trans_eq (by unfold S; field_simp)
  calc
     _ = z*kp:=by unfold z; ring
     _ = z*(Local.testPrice F*κ'+(T*(B*(m+m)))):=by unfold kp; unfold Fp; congr 2; ring
     _ ≤ z*(Local.testPrice F*κ+(y/2)/z):=mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hπ (zero_le_one.trans hk)) hh) hx.le
     _ ≤ z*(Local.testPrice F*((y/2)/(z*Local.testPrice F)) + (y/2)/z):=by
        apply mul_le_mul_of_nonneg_left _ hx.le; apply add_le_add_left; exact mul_le_mul_of_nonneg_left (min_le_left ..) (zero_le_one.trans hk)
     _ = y:=by change z*(Local.testPrice F*((y/2)/(z*Local.testPrice F))+(y/2)/z)= y; field_simp [(show Local.testPrice F≠0 from (zero_lt_one.trans_le hk).ne')]; ring
end YM.PhysicalNext.Repeat.Quince
