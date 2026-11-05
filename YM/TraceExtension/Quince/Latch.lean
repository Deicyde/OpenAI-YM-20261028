import YM.TraceExtension.Quince.Surrey
import YM.Next.RANK.LineBox
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice RG Wilson Finset Source Extra.Histories Labels
open Push Local Next.Foundations
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{c:Side} {R:Rep G c}{B:BudgetPoint}{o:Site c}
-- interior with no labels.
def dent (B:BudgetPoint): Set (Config G c):= ⋂ p: Face (Per c), {x| G.chord (faceValue x p)<B.threshold }
lemma dent_open (B:BudgetPoint) : IsOpen (dent (G:=G) (c:=c) B):=by apply isOpen_iInter_of_finite; intro i; unfold faceValue; exact isOpen_lt (by fun_prop) continuous_const
lemma dent1 (B:BudgetPoint): (1:Config G c)∈ dent B:=by unfold dent; rw [mem_iInter]; intro p; change G.chord (faceValue 1 p)<_; simpa[faceValue, square, travel] using B.threshold_pos
lemma dent_clear {F:Config G c}(h:F∈dent B): flags B.threshold F=∅:=by apply Finset.eq_empty_iff_forall_notMem.mpr; intro j hv; obtain ⟨p,_,hx⟩:= (flags_spec ..).1 hv; exact hx.not_gt (mem_iInter.mp h p)
lemma dent_fine {F:Config G c}(h:F∈dent B)(X:Support c):Healthy B.threshold X F:=by simp only[Healthy,dent_clear h]; exact Finset.disjoint_empty_right _
section line
variable {G':Config G c→ℂ}{k:ℕ}{I:Type*}{f:I → Config G c→ℂ}{b:I→ℝ}{X:I→Support c}
-- genuine point on smooth neighborhood.density quotient
lemma rideA {k:ℕ}{f:Config G c→ℂ} (l:List (Directions G c))(hl:l.length<k)(a:Directions G c)(U:Config G c)(x:ℝ)(hp:Local.Chart k f (increment U (x • a))):
   let W t:= increment U (t • a); HasDerivAt (fun t:ℝ=>leftDerivs f l (W t)) (leftDerivs f (a::l) (W x)) x:=by
    intro W; let F(t:ℝ):=leftDerivs f l (increment (W x) (t • a)); have ht: HasDerivAt F (leftDerivs f (a::l) (W x)) (x-x):=by rw[sub_self]; exact left_has a hl hp
    have hh :=ht.scomp (h:=fun y:ℝ=> y-x) (x:=x) (hasDerivAt_id' x|>.sub_const x)
    simp only[one_smul] at hh; apply hh.congr_of_eventuallyEq (Eventually.of_forall fun t=>?_)
    change leftDerivs f l _=F (t-x); unfold F W; rw[← Next.Rank.Spindle.progress, add_sub_cancel]
variable (h:∀ i,B.Regular (X i) (f i))(hp:∀ i,B.supBounds o (X i) (f i) (b i))(he:Summable b)
include hp he
lemma line_caps (U:Config G c)(hU:U∈ dent B)(l: List (Directions G c))(hl:l.length ≤ B.order)(hA:∀ a∈l,B.dirBound o a) : Summable (fun i=> ‖leftDerivs (f i) l U‖):= .of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=> (hp i).2 _ (dent_fine hU _) l hl hA) he
include h
lemma line_fare (hR:∀ U:Config G c,U∈dent B→ G' U=∑' i,f i U)(U:Config G c)(hU:U∈dent B)(l: List (Directions G c))(hl:l.length ≤ B.order)(hA:∀ a∈l,B.dirBound o a) : leftDerivs G' l U=∑' i,leftDerivs (f i) l U:=by
    induction l generalizing U with
    | nil=> exact hR _ hU
    | cons a l ih=>
      let W(t:ℝ):=increment U (t • a); have h0:W 0=U:=by simp[W,Work.G07.at_zero_increment]
      obtain ⟨r,hr,hp'⟩:= Metric.mem_nhds_iff.mp (show ∀ᶠ x in 𝓝 (0:ℝ), W x∈dent B from ((show Continuous W from by unfold W increment; fun_prop).continuousAt.tendsto.eventually ((dent_open _).mem_nhds (h0.symm ▸ hU))))
      let p:=Metric.ball (0:ℝ) r; let v(i:I)(x:ℝ):=leftDerivs (f i) l (W x); let g(i:I)(x):=leftDerivs (f i) (a::l) (W x)
      have hc:0 ∈ p:= Metric.mem_ball_self hr
      have hh : l.length < B.order:=hl
      have hz(a'): a'∈l→B.dirBound o a':=fun ha=> hA a' (List.mem_cons_of_mem _ ha)
      have ht:= hasDerivAt_tsum_of_isPreconnected he (Metric.isOpen_ball (x:= (0:ℝ))) (convex_ball (0:ℝ) r|>.isPreconnected) (show ∀ i x,x∈p→ HasDerivAt (v i) (g i x) x from fun i x hx=> rideA _ hh a _ _ ((h i).smooth _ (dent_fine (hp' hx) _))) (fun i x hx=> (hp i).2 _ (dent_fine (hp' hx) _) _ hl hA) hc (line_caps hp he (W 0) (hp' hc) l hh.le hz|>.of_norm) hc
      have he:= (ht.congr_of_eventuallyEq (f₁:=fun t=>leftDerivs G' l (W t)) (by
           filter_upwards [Metric.ball_mem_nhds _ hr] with x hx; exact ih (W x) (hp' hx) hh.le hz)).deriv
      unfold g at he; rw[h0] at he; exact he
end line
end YM.PhysicalNext.Repeat.Quince
