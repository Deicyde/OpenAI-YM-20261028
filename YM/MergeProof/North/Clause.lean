import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.IssuePlan
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Zest
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.MergeProof.Hens
import YM.MergeProof.North.Focal
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymSeason
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Postcards
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Hood
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Line


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Float
open Function Filter Set Lattice Gauge Wilson RG Source Accent Push Local Extra.Histories PhysicalNext.Repeat Lotus Finset Marker Ribbon
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:Side}{R:Rep G n}{κ e t z a:ℝ}
variable (M:Leaf R)
lemma posted {K:ℕ→ Config G n→ℂ}(h:ForceCost R.p R.activities K t): Dominated K:=by obtain ⟨f,ht,h⟩:=h; exact ⟨f,(sumBudget_uncharge (fun i=>(h i).1) ht).2.1,fun i U=> (h i).2 _⟩
lemma postage {K:ℕ→ Config G n→ℂ} (h:Dominated K) (R: Rep G n):∃ c,ForceCost R.p R.activities K c:=by
   obtain ⟨f,ht,h⟩:=h; let w(i:Support n):=R.p.mass i 1; obtain ⟨i,hx⟩:= Finite.exists_max w; let g(i) := R.p.mass (Local.patch R.activities i) (f i)
   have hf i:0 ≤ f i:=(norm_nonneg _).trans (h i 1)
   have hg i:0 ≤ g i:=mul_nonneg (Real.exp_pos _).le (hf i)
   have hs : Summable g:= (ht.mul_left (w i)).of_nonneg_of_le hg (fun i'=> by unfold g; unfold BudgetPoint.mass; exact mul_le_mul_of_nonneg_right ((le_of_eq (Eq.symm (mul_one _))).trans (hx (Local.patch R.activities i'))) (hf i'))
   exact ⟨_,f,⟨hg,hs,le_rfl⟩,fun i=>⟨hf i,h i⟩⟩
lemma combn {p q:ℕ→ Config G n→ℂ}(hp:Dominated p)(hq:Dominated q): Dominated (p+q):=by
   obtain ⟨z,h,hp⟩:=hp;obtain ⟨s,ht,hq⟩:=hq; exact ⟨z+s,h.add ht,fun i U=> (norm_add_le ..).trans (add_le_add (hp i U) (hq i U))⟩
lemma coin_open (R:Rep G n)(F:Config G n→ℂ)(K:ℕ→ Config G n→ℂ)(U:Config G n): Accent.coin R F K U=((R.eval U:ℝ):ℂ)*F U+ (Real.exp (R.exponent U):ℂ)*∑' i,gasMark R.p R.activities U i K:=by unfold Accent.coin; simp_rw [nickel,gasMark_eq]
lemma coin₀ (R:Rep G n)(U:Config G n)(f: Config G n→ℂ):coin R f 0 U=(R.eval U:ℂ)*f U:=by rw [coin_open]; simp
lemma coin_plus (R:Rep G n)(F L:Config G n→ℂ){p q:ℕ→ Config G n→ℂ}(hp:Dominated p)(hq:Dominated q) (hA:R.activities.KBound R.p t):coin R (F+L) (p+q)= coin R F p+coin R L q:=by
   funext U; have ht:= dominated_gasMark (postage hp R).choose_spec hA|>.summable U; have hv:= dominated_gasMark (postage hq R).choose_spec hA|>.summable U
   simp_rw [Pi.add_apply,coin_open,map_add,Summable.tsum_add ht hv,Pi.add_apply,mul_add]; ring
lemma coin_port (R:Rep G n)(F:Config G n→ℂ) {p q:ℕ→ Config G n→ℂ} (hp:Dominated p)(hq:Dominated q)(he:profile R.activities p=profile R.activities q)(h:R.activities.Valid R.p t z):coin R F p=coin R F q :=by
   funext U; unfold coin; congr 1; apply congr_arg
   let B:=Bud Unit; let g(i: Box n):= Poly.send B.quiet (profile R.activities (fun j=>Complex.ofReal ∘ R.activities.K j) i U)+Poly.send (B.fire ()) (profile R.activities p i U)
   have hh:R.activities=R.activities:=rfl; have hx := B.fire_hot ()
   have hH i:(g i).part B.quiet=profile R.activities (fun j=>Complex.ofReal ∘ R.activities.K j) i U:=by simp [g,hx.symm]
   have hr i:(g i).part (B.fire ())=profile R.activities p i U:=by simp [g,hx]
   exact (stageR _ _ _ (mass_crest _ h _) hH (hp.summable U) hr).symm.trans (stageR _ _ _ (mass_crest _ h _) hH (hq.summable U) (fun j=> (hr j).trans (congr_fun (congr_fun he j) U)))
end YM.MergeProof.Float
