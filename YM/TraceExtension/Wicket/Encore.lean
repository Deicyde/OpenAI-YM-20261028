import YM.TraceExtension.Swift.Troop
import YM.Push.LOCAL_SPLITTING.Calculus
import YM.TraceExtension.Shepherd.Triton
/-!
 # Paid C^k at each original mask equality chart (REP convention)

 Shifts are by constant when tested here, not remasked. Only if shift test says safe.
 Integration with respect to color will be separate. Constants insensitive to label count.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Wicket
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Matrix Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}
section point
variable {D:Directions G n→Prop} {k k':ℕ}{U:Config G n}{f g:Peat G n}{a b:ℝ}
structure Clear(k:ℕ)(D:Directions G n→Prop)(U:Config G n)(f:Peat G n)(a:ℝ) : Prop where
    wake : Chart k f U
    pay : ∀ l:List (Directions G n), l.length≤k→ (∀ v∈l,D v) → ‖leftDerivs f l U‖ ≤ a
lemma Clear.weaken (h:Clear k D U f a)(he:a ≤ b):Clear k D U f b:=⟨h.wake,fun l hl hv=> (h.pay l hl hv).trans he⟩
lemma Clear.congr (h:Clear k D U f a)(he:g ∘ increment U =ᶠ[𝓝 0] f ∘ increment U): Clear k D U g a:=⟨h.wake.congr_of_eventuallyEq he,fun l hl hv=> by rw[left_congr l U he]; exact h.pay l hl hv⟩
lemma clear_const (h:|a|≤ b) : Clear k D U (fun _=>a) b:=⟨contDiffAt_const,fun l hl _=> by rw[Work.G07.left_const]; split; exact h; rw[norm_zero]; exact (abs_nonneg _).trans h⟩
lemma Clear.amount (h:Clear k D U f a):|f U|≤a:=h.pay [] (by simp) (by simp)
lemma Clear.nonneg (h:Clear k D U f a):0≤a:= (abs_nonneg _).trans h.amount
lemma Clear.order (h:Clear k D U f a)(hk:k'≤k): Clear k' D U f a:= ⟨h.wake.of_le (Nat.cast_le.mpr hk), fun l hl=>h.pay l (hl.trans hk)⟩
lemma Clear.add (h:Clear k D U f a) (hp: Clear k D U g b): Clear k D U (f+g) (a+b):=⟨h.wake.add hp.wake,fun l hl hL=> by rw[left_add l h.wake hp.wake hl]; exact (norm_add_le ..).trans (add_le_add (h.pay l hl hL) (hp.pay l hl hL))⟩
lemma Clear.neg (h: Clear k D U f a): Clear k D U (-f) a:=by
    let L:= -ContinuousLinearMap.id ℝ ℝ; refine ⟨h.wake.neg,fun l hl hL=>?_⟩; change ‖leftDerivs (L ∘ f) l U‖ ≤ _; rw[left_linear L l h.wake hl]; simpa[L] using h.pay l hl hL
lemma Clear.sub (h:Clear k D U f a)(hp:Clear k D U g b): Clear k D U (f-g) (a+b):=by rw [sub_eq_add_neg];exact h.add hp.neg
lemma Clear.scale (h:Clear k D U f a)(p:ℝ): Clear k D U (p • f) (|p| * a):=by
    let L:= p • ContinuousLinearMap.id ℝ ℝ; refine ⟨ContDiffAt.const_smul (c:=p) h.wake,fun l hl hL=>?_⟩; change ‖leftDerivs (L ∘ f) l U‖ ≤ _; rw[left_linear L l h.wake hl]; exact (norm_smul p _).trans_le (mul_le_mul_of_nonneg_left (h.pay l hl hL) (abs_nonneg p))
lemma Clear.mul (h:Clear k D U f a)(hp: Clear k D U g b): Clear k D U (f*g) ((2:ℝ)^k*(a*b)):=⟨h.wake.mul hp.wake,fun l hl hd=> (left_mul_bound h.wake hp.wake h.pay hp.pay l hl hd).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hl) (mul_nonneg h.nonneg hp.nonneg))⟩
private lemma leaf_exp (A:Directions G n)(h: Chart 1 f U): leftDerivs (Real.exp ∘ f) [A] U = (leftDerivs f [A] U) * Real.exp (f U):=by
   have ht:= (left_has A (l:=[]) (by simp) h).exp; apply ht.deriv.trans;  simp only [zero_smul, Work.G07.at_zero_increment,leftDerivs]; exact mul_comm ..
def budC : ℕ→ℝ
 | 0=> 2
 | j+1=> budC j+2^j*(budC j+1)
lemma Clear.bud (hf:Clear k D U f a)(ha:a ≤1): Clear k D U ((Real.exp ∘ f)-1) (budC k * a):=by
    induction k with
    | zero=>
        refine ⟨hf.wake.exp.sub contDiffAt_const,fun l he hv=>?_⟩
        obtain rfl:l=[]:=List.eq_nil_of_length_eq_zero (show l.length=0 from by omega)
        exact (Real.abs_exp_sub_one_le (hf.amount.trans ha)).trans (mul_le_mul_of_nonneg_left hf.amount zero_le_two)
    | succ k ih=>
        have hu:= ih (hf.order (Nat.le_succ k)); let g:= Real.exp ∘ f
        have hP : 0 ≤ budC k :=by clear hf ih hu; induction k <;> unfold budC<;> positivity
        have hk :1 ≤ k+1:=by omega
        have hl : Clear k D U g (budC k+1):=by
             rw [show g=(g-1)+1 from (sub_add_cancel _ _).symm]; exact (hu.weaken (mul_le_of_le_one_right hP ha)).add (clear_const (a:=1) (b:=1) (by norm_num))
        let v:=g-1; have hv: Chart (k+1) v U:=hf.wake.exp.sub contDiffAt_const; refine ⟨hv,?_⟩; intro l he hL
        have ht : budC k * a ≤ budC (k+1)*a:= mul_le_mul_of_nonneg_right (show budC k≤ _ from (by rw[budC]; exact le_add_of_nonneg_right (by positivity))) hf.nonneg
        by_cases hx:l=[]; subst l; exact (hu.pay [] (by simp) hL).trans ht
        obtain ⟨m,b,H⟩: ∃ (m:List (Directions G n))(b:Directions G n), l=m++[b] := by clear he ht hL; induction l using List.reverseRecOn with
           | nil=> contradiction
           | append_singleton l b _=> exact ⟨l,b,rfl⟩
        subst l
        have hh : m.length≤k:=by simp only[List.length_append,List.length_singleton] at he; omega
        have he : leftDerivs v [b] ∘ increment U =ᶠ[𝓝 0] (leftDerivs f [b] * g) ∘ increment U:=by
            have ht := chart_eventually (W:=increment U) (x:=0) (k:=k+1) (f:=f) (by rw[Work.G07.at_zero_increment];exact hf.wake) (incrementA U 0); filter_upwards [ht] with y hy
            let V:=increment U y; let A:=leftDerivs f
            have hz: Chart 1 f V:= hy.of_le (Nat.cast_le.mpr hk)
            unfold v; rw [sub_eq_add_neg]
            show leftDerivs (g+ - (1:Peat G n)) [b] V = leftDerivs f [b] V * g V
            rw[left_add [b] (show Chart 1 g V from hz.exp) (show Chart 1 (- (1:Peat G n)) V from contDiffAt_const (c:= -(1:ℝ))) le_rfl,show leftDerivs (- (1:Peat G n)) [b] V=0 from (by rw[show -(1:Peat G n)=fun _=> -1 from rfl,Work.G07.left_const];simp),add_zero]; exact leaf_exp b hz
        let p:= leftDerivs f [b]; have hg: Clear k D U p a:= ⟨leftDerivs_chart _ k (by rw [List.length_singleton,add_comm (1:ℕ)]; exact hf.wake),fun l hl hv=> by rw [← Work.G07.left_append]; refine hf.pay _ (by simp; omega) ?_; simp only[List.mem_append,List.mem_singleton, or_imp, forall_and]; exact ⟨hv,fun v e=> e.symm ▸ hL b (by simp)⟩ ⟩
        change ‖leftDerivs v _ U‖ ≤ _; rw[Work.G07.left_append,left_congr m U he]; refine ((hg.mul hl).pay m hh (fun x hx=> hL _ (by simp [hx]))).trans ?_
        rw[budC.eq_2,add_mul]; have ht:0 ≤ budC k*a:=mul_nonneg hP hf.nonneg; nlinarith only [ht]
end point
end YM.Trace.Wicket
