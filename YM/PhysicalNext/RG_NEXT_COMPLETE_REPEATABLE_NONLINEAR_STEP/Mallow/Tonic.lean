import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Kitchen
import YM.Push.LOCAL_SPLITTING.Recovery

/-!
 # Generic differentiate force books. ξ can be 0. Exact paths imperative. Utility
    also works for linear hypotheses; charges literal accounts at WHERE.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Gas Ovens ConnectedActivityE6 Daisy.Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n: Side} {B : BudgetPoint}{A:Activities G n} {o:Site n}{F:ℝ → Ovens.Code G n} {d t r: ℝ}
lemma few (d: ℝ) : ∀ᶠ x in 𝓝 (0:ℝ),|x| * d≤1:=
    ((continuous_abs.continuousAt.mul_const _).eventually (gt_mem_nhds (by simp: |(0:ℝ)| *d<1))).mono fun i hi=>hi.le
-- Palates

def tonic (F:ℝ→Code G n)(i:ℕ)(V:Config G n):ℝ:= deriv (fun t=> F t i V) 0
def nectar (F:ℝ→Code G n)(i:ℕ)(V:Config G n):ℂ:=(tonic F i V:ℝ)
def petals (B:BudgetPoint)(A:Activities G n)(X:Code G n)(V:Config G n)(i:Finset ℕ):ℝ:=if A.admissible B V i then ∑ j∈i,X j V*∏ k∈i.erase j,A.K k V else 0
lemma herbs (V:Config G n) (B:BudgetPoint)(A:Activities G n)(F:ℝ→Code G n)(i:Finset ℕ):Push.Local.gasMark B A V i (nectar F)=(petals B A (tonic F) V i:ℝ):=by rw [Push.Local.gasMark_eq]; unfold petals; split_ifs<;> push_cast <;> rfl
variable (h : Season A B F o d t B.supportExponent)
include h
lemma gaze (U: Config G n) : HasDerivAt (fun v=> (black A (F v)).gas B U) (∑' i, petals B A (tonic F) U i) 0:=by
  let v i x := (black A (F x)).gasOccurrence B i U
  obtain ⟨ht,hc,hb,hX,p,hp,hv,hP⟩:= h
  let f (i:Finset ℕ):=∏ j∈i,p j
  have hm:= AbsoluteSums.Product.everyone_ne (fun i=>(A.forced i).support) _ hp (fun i _=> (A.forced i).inventory_ne.mono (A.forced i).inventory_sup) hv
  have he : Summable p:= hm.2.1.of_nonneg_of_le hp (fun i=> le_mul_of_one_le_right (hp i) (Real.one_le_exp (mul_nonneg B.exponent_pos.le (by positivity))))
  have hz: Summable f := summable_finsetProd_of_summable_norm he.norm
  obtain ⟨x,hx,h⟩:= Metric.mem_nhds_iff.mp (few d)
  let s:= Metric.ball (0:ℝ) x; have hy:0∈s:= Metric.mem_ball_self hx
  have hu (i x) (hy:x∈s): Est (f i) d x (v i) := by
    have hk(w:ℝ): (black A (F w)).admissible B U i↔A.admissible B U i:=Iff.rfl
    unfold v Activities.gasOccurrence; simp_rw [hk]; split
    · exact Est.summit _ _ _ hb (fun j _=> hP x (h hy) j U)
    exact Est.nil _ _ _ _ hb (abs_zero.le.trans (prod_nonneg (fun j _=> hp j)))
  have hG(i: Finset ℕ): HasDerivAt (v i) (petals B A (tonic F) U i) 0:=by
    have hk(w:ℝ): (black A (F w)).admissible B U i ↔ A.admissible B U i:=Iff.rfl
    unfold v Activities.gasOccurrence petals; simp_rw [hk]; split
    next hQ=>
      let g i (x:ℝ):= F x i U
      have ht':= HasDerivAt.fun_finsetProd (f:=g) (u:=i) (fun j (_:j∈i)=> (hP _ (h hy) j U).alive)
      refine (show HasDerivAt _ (∑ j∈i,(∏ k∈i.erase j, F 0 k U) • tonic F j U) _ from ht')|>.congr_deriv ?_
      rw [ht]
      exact sum_congr rfl (fun _ _=> mul_comm ..)
    exact hasDerivAt_const 0 0
  have hh i : deriv (v i) 0= petals B A (tonic F) U i:=(hG i).deriv
  have hQ := Est.seqOwnUp s Metric.isOpen_ball hy (convex_ball (E:=ℝ) 0 x|>.isPreconnected) v f hz hu; simp_rw [hh] at hQ; exact hQ

lemma real_force : Push.Local.ForceFormat B A o (nectar F) := by
  let g':ℕ→Code G n:=fun _=>0
  have hK:=few d; have h0:|0| *d≤1:=by simp
  refine ⟨fun i U hU=>?_,fun i hi=> ?_,fun i t V=> ?_,fun i U V hv ht=>?_,fun i=> ?_⟩
  · by_contra hp; apply hU; have hf : (fun t=> F t i U)=ᶠ[𝓝 (0:ℝ)] fun _=>0:=hK.mono fun x hh=>by by_contra hU; exact hp ((h.permit x hh).permit i U hU)
    unfold nectar tonic; rw [hf.deriv_eq]; simp
  · by_contra hu; apply hi; funext V; have he : (fun x=>F x i V)=ᶠ[𝓝 (0:ℝ)] fun _=> F 0 i V:=hK.mono fun x hi=> congr_fun (h.burn.2.1 x hi _ hu) V
    unfold nectar tonic; rw [he.deriv_eq]; simp
  · exact congr_arg Complex.ofReal ((show (fun x=> F x i (gauge t V))=ᶠ[𝓝 0] _ from hK.mono fun x he=>(h.permit x he).sym i t V).deriv_eq)
  · exact congr_arg Complex.ofReal ((show (fun x=> F x i U)=ᶠ[𝓝 0] _ from hK.mono fun x he=>(h.permit x he).reads i U V hv ht).deriv_eq)
  apply Complex.continuous_ofReal.measurable.comp
  let g i (x:ℝ)(U:Config G n):= if |x| *d≤1 then slope (fun x=>F x i U) 0 x else 0; have hg (x:ℝ) :Measurable (g i x):=by
    unfold g; split
    next hH=>
      have h0:Measurable (F 0 i):= (h.permit 0 h0).meas i; have hi : Measurable (F x i):=(h.permit x hH).meas i
      simp_rw [slope_def_module]; exact (hi.sub h0).const_smul ((x-0)⁻¹)
    exact measurable_const
  apply measurable_of_tendsto_metrizable' (g:=tonic F i) (𝓝[≠] 0) hg; apply tendsto_pi_nhds.mpr; intro x; obtain ⟨f,hf,hB,hQ⟩:= h.burn.2.2
  exact (hQ _ h0 i x|>.alive.tendsto_slope).congr' ((hK.filter_mono nhdsWithin_le_nhds).mono fun t h=> (if_pos h).symm)
lemma dimes : Push.Local.ForceCost B A (nectar F) (d*t):=by
  obtain ⟨u,hu,hX,hP⟩:=h.burn.2.2
  have hc:= real_force h
  let f i:= if o∈(A.forced i).support then d*u i else 0
  have h0 i : 0≤ f i:= by unfold f; split; exact mul_nonneg h.burn.1 (hu _); rfl
  refine ⟨f,?_ ,fun i=> ⟨h0 i,fun U=>?_⟩⟩
  · convert! budget_scale h.burn.1 (hX o) using 1; ext i; unfold f Push.Local.patch BudgetPoint.mass; split <;> ring
  unfold f; split
  · exact (Complex.norm_real ..).le.trans ((hP 0 (by simp) i U).high)
  next hh=> simp [not_not.mp (mt (hc.carried i) hh)]
end YM.PhysicalNext.Repeat.Mallow
