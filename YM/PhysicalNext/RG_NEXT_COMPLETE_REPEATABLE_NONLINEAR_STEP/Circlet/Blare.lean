import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Riddle
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Rope
import YM.Planned.PRIMARY_INTEGRAL_295.Gala
/-!
 # Birth extra wait transcribable at any B phases.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Circlet
open Function Filter Set Lattice RG RG.Supply Wilson Pressure Pressure.Tube Tree Next Next.Foundations Precision
open Push Push.PriceCompiler AnalyticBridge LocalGaussianLaws JointLoad JointLoad.Heir JointLoad.Heir.Suite
open Input Org Extra.Histories Planned.PrimaryIntegral295  Bloch Bid Planned.AtomRegular Planned.AtomRegular.Foliage
open AnalyticBridge.VerifiedReset.Time Next.Scheduling Repeat.Peak VerifiedReset ConnectedActivityE6 Pressure.Testing
open ProofPorts
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G: Gauge}{M : Sheet G} {K : MapPrices}{R:Targets M K}{E: Expenses R}{W : Return.Wages}{q:ℕ→ℝ}

variable (C: Programs M)(D:Rolls M)(Y: ℕ→ℕ→Heir.Record) (r : ℕ→ℕ→ℕ)(B:Register D E W q)
structure Hue (j i d: ℕ)(x:ℝ) : Prop where
   geometry:11*Planned.AtomRegular.toll (r j i) ≤ radiusB x∧minSide G d ≤ radiusB (betaF G x (D.L j))
   owed(P S:BudgetPoint) (he:P.power=(M.profile i).power)(hf:S.threshold=fiery G x (D.L j))(n:ℕ)(hn:n≤d) β : betaF G x (D.L j)/2 ≤ β→Peak.Rented n (C j i) (Y j i) P S (D.L j) (r j i) x (Coat.gStep β)
   optional:∃ u:ℝ, 0≤u∧u* Real.exp (Heir.Release.base ((M.profile i).supportExponent+2) (r j i)) ≤ ((D.L j).val:ℝ)⁻¹^d ∧ Mercury.PermitY (R j i) (C j i) (Y j i) (M.profile i).power (W j i) (B.o j i) SectorMeasure.Chi.canonical (B.μ j i) x u (D.L j)

lemma burst (j i d:ℕ)(hk:(Y j i).ε ≤ 1/4):∀ᶠ x in atTop,Hue C D Y r B j i d x:=by
   let L:=D.L j; let U:= (M.profile i).order; let Q:= C j i; let A:=Y j i; let z:=r j i; let y:= (M.profile i).supportExponent+2
   have hU:2≤U:= (by norm_num :2≤6).trans (M.profile _).order_ge
   have hv:= Work.E01.radiusB_tendsto; let A':= (D.L j).val; have hz : 0 < (A':ℝ):=by unfold A'; positivity
   let s:= Real.exp (Heir.Release.base y z); have hs:0<s:=Real.exp_pos _
   obtain ⟨f,hF,H⟩:= Mercury.tuned (R j i) (M.profile i).power Q A (W j i) (B.μ j i) (B.o j i) SectorMeasure.Chi.canonical L hU hk
   filter_upwards [H,(hF.mul_left s).below (by norm_num) (((A':ℝ))⁻¹^d) (by positivity),hv.eventually_ge_atTop _,(hv.comp (show Tendsto _ atTop atTop from tendsto_id.atTop_add (tendsto_const_nhds : Tendsto (fun _:ℝ=>G.slopeConstant*Real.log L.val) atTop _))).eventually_ge_atTop _, (Finset.range (d+1)).eventually_all.mpr (fun n _=> Peak.floats n Q A L z (M.profile i).power (by omega))] with x hp hf ht he hy
   rw [abs_mul,abs_of_pos hs] at hf
   refine ⟨⟨ht,he⟩,fun P S h k n hn β hv=> (hy n (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)) _ hv).2 _ _ k h,|f x|, abs_nonneg _,(mul_comm ..).trans_le hf,?_⟩
   intro c' f' S T h R e U F X i ht hn hc hw P' hB hs he Z I _ _ a q b u hu hz hY hX M hκ L' hL hL' j H hj hZ hH
   exact (hp _ _ _ _ h _ e U F X i ht hn hc hw P' hB hs he Z I a q b u hu hz hY hX M hκ L' hL hL' j H hj hZ hH).climb (mul_le_mul_of_nonneg_left (le_abs_self _) M.profit) le_rfl

variable {θ : Protection D}
structure Decked (T:Delays θ) :Prop where
   width(j i:ℕ)(h:StepStages j i):100*(r j i+20) ≤ T.shells j ∧ 1 ≤ T.growth j
   buys(j i:ℕ)(h:StepStages j i)(hx:M.first≤ i)(x:ℝ)(hx:T.betaEntry j≤x)(d:ℕ)(hd:d≤j): Hue C D Y r B j i d x

lemma chords (h:∀ j i,StepStages j i→ M.first≤ i→ (Y j i).ε≤1/4)(T:Delays θ): ∃ U:Delays θ, DelayLe T U∧∀ V:Delays θ,DelayLe U V→Decked C D Y r B V:=by
   have he j i (hi:StepStages j i):∀ᶠ x in atTop,M.first≤ i→∀ d:ℕ,d≤j→Hue C D Y r B j i d x:=by
     by_cases hz:M.first ≤ i
     swap; · simp [hz]
     filter_upwards [(Finset.range (j+1)).eventually_all.mpr (fun d _=> burst C D Y r B j i d (h _ _ hi hz))] with x hx hh d hd; exact hx _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hd))
   obtain ⟨x,-,hy,hS⟩:= collect_upper T.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i hi=>he j i hi))
   let u j:=100*(max (r j j) (r j (j-1))+20)
   refine ⟨{T with betaEntry:=x, shells:=fun j=>max (u j) (T.shells j), growth:=fun j=>max 1 (T.growth j)},⟨hy,le_rfl,fun j=>le_max_right ..,fun j=>le_max_right ..⟩,fun V H=>⟨fun j i h=> ?_,fun j i h ht b hv d hi=>hS _ _ ((H.beta j).trans hv) _ h ht d hi⟩⟩
   have h':100*(r j i+20) ≤ u j:=by unfold u; gcongr; rcases stepStages_target h with h|h <;> subst i <;> first| exact le_max_right .. | exact le_max_left ..
   exact ⟨h'.trans ((le_max_left ..).trans (H.shells j)), (le_max_left ..).trans (H.growth j)⟩
end YM.PhysicalNext.Repeat.Circlet
