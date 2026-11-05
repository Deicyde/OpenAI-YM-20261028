import YM.RG05Readout.Offsets.Torus
import YM.RG05Readout.Offsets.Rows
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Chant
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Direction
/-!
# Delays for moving primary roots (actual Wilson history).

Adapted from `Cub.logos`, now only requesting the bounded INPUT-grade
projection approximation, but doing so uniformly over a whole centered
preimage and all required finite probes. Reserve the same L pre-budget;
offsets enlarge post-L demands before release. Does NOT assert that
blowing assembly in a different construction paid this reserve.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
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
open PPX Circlet Next.Free
open YM.RG05Readout.Offsets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
set_option quotPrecheck false
variable {G : Gauge} {n : ℕ} {P:Teller G}

-- keep separate from Eve. Provide post-L payments on finite offset set.
structure Angle (j i d n:ℕ)(L₀:Side) (P P': Stage)(Γ: Teller G)(Kn:KernelChoices)(C:Libretto G n)(R:Record) (v : ConnectedActivityE6.Target G Γ)(w:ℝ)(Q:Target.Order G w)(μ x :ℝ)(r:ℕ) where
   small : ℝ
   pos : 0<small
   sail : ℝ
   sailing : 0≤ sail
   sails : Mercury.PermitY v C R P.power w Q Chi.canonical μ x sail L₀
   cap(P'':BudgetPoint)(B:BudgetPoint)(f:Side)(X:Support f) :P''.threshold=temp x → B.threshold=fiery G x L₀→ B.B=radiusB (betaF G x L₀) → P''.power=P.power → coverNumber B.B X≤1 → ∀ β:ℝ,betaF G x L₀/2≤ β → opal C R P'' B L₀ X r x (gStep β)≤1 ∧ Cub.clocks C (Cub.title G P') * opal C R P'' B L₀ X r x (gStep β)*AnalyticBridge.LocalGaussian.Moments.meter (Lute.heads G B L₀ X r x) 0 R.K (2*((n+1)+(n+1))) ≤ small
   paths (p : Local.Probe G d):p∈ Local.tests ((Labels.frames G).level d)→ ∀ (a: ((Labels.frames G).level d).Index), (p.2.val ≤ (((Labels.frames G).level d).grades a).1) → ∀ (c f:Side)(S:StepData c f)(b':Site f), S.ratio.parent b'=0 → ∀ (T:Tube G S)(K : Flight j i),S.ratio.count=K.L→K.L=L₀→ HEq T.R.A0 (Carrier.linesOf K Kn.penalty)→ ∀ (w y),∀ hB:Blend 2 w y, 2*Heir.reach x<c.val→
      ∀ (hk: 4≤ i)(hu:d ≤ j), let R':=localSection G d; let F:=(Labels.frames G).level d; let u:=ocean T (Push.Local.presented R' b' w (Place.copy F a)) x; let V:= (hol G).testLinks d 0 (y • p.1); let Z:=Seal.donne R' (sound G d) Kn.penalty_pos hk (Next.Foundations.valuation G d) K hu hB
      ‖(L₀.val:ℝ)^d • iteratedDeriv p.2.val (u ∘ (V: ℝ → Config G c)) 0 - Local.runProbe F p (Z.leads L₀ (Place.copy F a))‖ ≤ small
   current : ℝ
   later : 0 ≤ current
   law (p : Local.Probe G d): p∈ Local.tests ((Labels.frames G).level d)→
      Push.Local.partPrice (hol G) p * (Cub.gaugeMeter d * ((L₀.val:ℝ)^d*(2*(Cub.title G P'*sail+small)))) + small ≤ current
   pricedC (c:ℝ): c≤ credibility G P'.supportExponent P'.order P'.power → ∀ (f:Side)(H:Rep G f)(Z:Cloud H),H.p.mass Z.live.crest Z.live.weight=c→
       (let F:= (Labels.frames G).level d; let kp:=Local.testPrice F*current+Local.readPrice (hol G) F*((L₀.val:ℝ)^d*(2*marvel (Q:=v) (L:=L₀) (x:=x) Z)); kp ≤ Doors.rate L₀)

set_option maxHeartbeats 450000 in
lemma aim_off (Lx : Side)(C : Libretto G n)(D:Record)(K : KernelChoices)(M: ConnectedActivityE6.Target G P) (μ t:ℝ)(d j i r:ℕ)(P0 P1 : Stage)(o:Target.Order G t)(hD:D.ε≤1/4) (hi:4≤ i)(hj:4≤j)(hn:2≤ n)(hz:d≤j)(hm:0<μ):∀ᶠ x in atTop, Nonempty (Angle j i d n Lx P0 P1 P K C D M t o μ x r):=by
  let F:=(Labels.frames G).level d; let A:= hol G; let S0:=localSection G d
  let e:= Cub.title G P1; have he₀:1≤e:= Cub.title_one ..
  let h:= credibility G P1.supportExponent P1.order P1.power; have hh :0<h:=mul_pos (Real.exp_pos _) (zero_lt_one.trans_le he₀)
  let y:=Doors.rate Lx; have hy:0<y:= Doors.rate_pos _
  let Z:=Local.testPrice F; have hk:1≤Z:=(Local.probe_budget F).choose_spec.choose_spec.1
  let κ := (y/2)/Z; have hκ : 0<κ:=div_pos (half_pos hy) (zero_lt_one.trans_le hk)
  let V:= Push.Local.tests F
  let g (p:Local.Probe G d) (x:ℝ):=Push.Local.partPrice A p*(Cub.gaugeMeter d*((Lx.val:ℝ)^d*(2*(e*x+x))))+x
  have he (p:Local.Probe G d) : ∀ᶠ x in nhds (0:ℝ), g p x ≤ κ:= ((show Continuous (g p) by unfold g; fun_prop).continuousAt (x:=0)).eventually (ge_mem_nhds (show g p 0 < κ by simpa [g] using hκ))
  obtain ⟨b,(hv:0<b),hb⟩:= Metric.mem_nhds_iff.mp (V.eventually_all.mpr (fun i _=> he i))
  let Q:= b/2; have hQ:0<Q:=half_pos hv; have hg (p) (hz:p∈ V) : g p Q ≤ κ:= hb (Metric.mem_ball.mpr (by rw [Real.dist_eq,sub_zero,abs_of_pos hQ]; exact half_lt_self hv)) p hz
  obtain ⟨u,hu,hγ⟩:= Mercury.tuned M P0.power C D t μ o Chi.canonical Lx hn hD
  let B:= (Lx.val:ℝ)^d; let T:=Local.readPrice A F; have hT:1 ≤ T:=Push.Local.readPrice_pos A F; have hT':0<T:=zero_lt_one.trans_le hT
  let S:= (y/2)/(T*h); have hS:0<S:=div_pos (half_pos hy) (mul_pos hT' hh)
  have ha(p:Local.Probe G d)(i':F.Index)(hp:p.2.val ≤ (F.grades i').1) : ∀ᶠ x:ℝ in atTop, ∀(c f:Side)(s:StepData c f)(b':Site f), s.ratio.parent b'=0 → ∀ (T:Tube G s)(P:Flight j i),s.ratio.count=P.L → P.L=Lx → HEq T.R.A0 (Carrier.linesOf P K.penalty) → ∀ w y,∀ hB:Blend 2 w y, 2*Heir.reach x<c.val →
       let u:=ocean T (Push.Local.presented S0 b' w (Place.copy F i')) x; let V := A.testLinks d 0 (y • p.1)
       let z:= Seal.donne S0 (sound G d) K.penalty_pos hi (Next.Foundations.valuation G d) P hz hB; ‖((Lx.val:ℝ)^d) • iteratedDeriv p.2.val (u ∘ (V:ℝ→ Config G c)) 0 - Local.runProbe F p (z.leads Lx (Place.copy F i'))‖ ≤ Q:=by
    filter_upwards [eventually_all.mpr (fun a:Site Lx=> retained p S0 A (sound G d) (Next.Foundations.valuation G d) K.penalty_pos hj hi hz i' hp Lx (lift a) hQ)] with x hx
    intro c f s b' he T' P ht hf hr w y hB hW
    obtain ⟨q,hq⟩: ∃ z: Site Lx,wrap f (lift z)=b':=by
      have hz:= s.ratio.unpack_at b'; rw [he,← s.ratio.root_embed,map_zero,zero_add] at hz
      rw [← hf,← ht]
      exact ⟨_,hz⟩
    rw [← hq]; exact hx q c f s T' P ht hf hr w y hB hW
  filter_upwards [V.eventually_all.mpr (fun p _=> eventually_all.mpr (fun i:F.Index=> (Set.toFinite (Set.univ : Set (PLift (p.2.val ≤ (F.grades i).1)))).eventually_all.mpr (fun x _=> ha p i x.down))),Rebuild.geometry (G.slopeConstant*Real.log Lx.val),hγ,hu.below (by norm_num) Q hQ,Cub.garnets C D Lx r P0.power (zero_le_one.trans he₀) hQ, Blush.fruition hm (L:=Lx) M B S hS] with x ha hx' H hf hU hM
  have ht(P' P'': BudgetPoint)(ht:P'.threshold=temp x)(hQ:P''.threshold=fiery G x Lx) : Blend 2 P''.threshold P'.threshold:=by
    refine ⟨one_le_two,P''.threshold_pos,P'.threshold_pos,P''.threshold_le,P'.threshold_le,?_ ,?_⟩
    · apply (div_le_iff₀ P''.threshold_pos).mpr; rw [ht,hQ]; exact hx'.2.2
    apply (div_le_iff₀ P'.threshold_pos).mpr; rw [ht,hQ]; exact hx'.2.1
  refine ⟨Q,hQ,|u x|,abs_nonneg _,?_,fun P' P'' f α hp hY hC hZ η q' hq' => ?_,(fun p hp a hA c f s b' h T Y A C C' b c' hB hX _ _=> (ha _ hp a ⟨hA⟩ (Set.mem_univ _)) _ _ _ _ h _ _ A C C' b c' hB hX),κ,hκ.le,fun p hp=> le_trans ?_ (hg _ hp), fun c h' N H Z' hZ=> ?_⟩
  · intro c' f' S' T' hk' R e H0 F X i ht hn hc hw P' hB hs he Z I _ _ a q b u hu hz hY hX M hκ L' hL hL' j H' hj hZ hH; exact (H c' f' S' T' hk' R e H0 F X i ht hn hc hw P' hB hs he Z I a q b u hu hz hY hX M hκ L' hL hL' j H' hj hZ hH).climb (mul_le_mul_of_nonneg_left (le_abs_self _) M.profit) le_rfl
  · -- cap
    have h:= ht _ _ hp hY; exact hU P' P'' hZ hY (hC.symm ▸ hx'.1.1) ((div_le_iff₀ h.fine).1 h.accounted) q' hq' f α η
  · unfold g; have h:=@Cub.horizon d; have ht:= Local.partPrice_pos (hol G) p; gcongr
  let Y:= H.p.mass Z'.live.crest Z'.live.weight
  set m:= Blush.marvel (Q:=M) (L:=Lx) (x:=x) Z'
  have hB:0≤ B:=by unfold B; positivity
  have hL:= hM N H Z' (B:ℂ) (by rw [Complex.norm_real,Real.norm_of_nonneg hB]); rw [Complex.norm_real,Real.norm_of_nonneg hB] at hL
  have he': B*(m+m)≤ S* h:= hL.1.trans (mul_le_mul_of_nonneg_left (hZ.trans_le h') hS.le)
  have hQ: T*(B*(m+m)) ≤ y/2:= (mul_le_mul_of_nonneg_left he' hT'.le).trans_eq (by unfold S; field_simp)
  intro Fp kp
  change Local.testPrice F*((y/2)/Z)+T*(B*(2*m)) ≤ y
  have hP: Local.testPrice F*((y/2)/Z)=y/2:= mul_div_cancel₀ _ (by positivity: Z ≠ 0)
  rw [hP,two_mul]; linarith only [hQ]

end YM.PhysicalNext.Repeat.Cub
