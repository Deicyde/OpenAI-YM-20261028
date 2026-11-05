import YM.RG08.Ballast.Beads

/-! # Transport relative positions through one step, all ranks incl constant
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function
open UVExt.Paths Stationary Matrix
open scoped Topology ContDiff Classical
variable {α β ι : Type} {r : ℕ} {w η C A B : ℝ} {L c f : Side} {F H : Shale α r}

def carpet (p : Site L) (x : Beads α r) (i : Fin r) : Cover × Co L α := (carry p (x i).1,arrives p (x i).1,(x i).2)
def grapes (L : Side) (F : Shale α r) := ∑ p : Site L,pool F (carpet p)

lemma ling_as (p : Beads α r) (η : ℝ) : ling η p=∏ i, Real.exp (η*size (p i).1) := by
  unfold ling girth; rw [Nat.cast_sum,Finset.mul_sum,Real.exp_sum]
lemma carry_ling (p : Site L) (x : Beads α r) (hw : 0≤η) (hc : η ≤ L.val*w) :
    ling η (carpet p x) ≤ Real.exp (4*η)^r*ling w x := by
  rw [ling_as,ling_as]
  have hh : (∏ _i : Fin r, Real.exp (4*η))=Real.exp (4*η)^r := by simp
  rw [← hh,← prod_mul_distrib]; refine prod_le_prod (fun i _=> (Real.exp_pos _).le) ?_; intro i _
  rw [← Real.exp_add,add_comm]
  apply Real.exp_monotone; simpa only [carpet,sub_self,show size (0:Cover)=0 from by simp [size],Nat.cast_zero,mul_zero,add_zero] using size_scaled p (x i).1 (carry p (x i).1) hw hc
lemma grapes_glow (L : Side) (h : Glow F w A) (hh : 0≤η) (hp : η≤L.val*w) :
    Glow (grapes L F) η ((L.val:ℝ)^4*(Real.exp (4*η)^r*A)) := by
  let K := Real.exp (4*η)^r
  have hu (p : Site L) : Glow (pool F (carpet p)) η (K*A) := by
    apply Charge.poolage _ (ling_one hh)
    apply budget_mono (budget_scale (show 0≤K by unfold K; positivity) h) (fun i => mul_nonneg (ling_pos _ _).le (norm_nonneg _)) (fun i => ?_)
    exact (mul_le_mul_of_nonneg_right (carry_ling p i hh hp) (norm_nonneg _)).trans_eq (mul_assoc ..)
  unfold grapes; simpa [Glow,K,site_card] using Charge.sums (w:=ling η) (fun i => (ling_pos η i).le) (s:=univ) (fun i _=>hu i)
lemma grapes_sub (p : Side) (h : Summable F) (e : Summable H) : grapes p (F-H)=grapes p F-grapes p H := by unfold grapes; simp_rw [pool_minus _ h e, sum_sub_distrib]
lemma grapes_summable (p : Side) (h : Summable F) : Summable (grapes p F) := by
  have hv (x : Site p) : Summable (pool F (carpet x)) := (h.hasSum.tsum_fiberwise (carpet x)).summable
  refine (summable_sum (s:=univ) (fun x _=>hv x)).congr fun i=>?_ ; simp [grapes]

def carriesG (g : Ratio c f) (x : PAC (Co g.count α) c) : PAC α f := fun i => x (splitCo g α i)
lemma grapes_rec [Fintype α] (X : Ratio c f) (v : Fin r → PAC (Co X.count α) c) (h : Summable F) :
    recital (grapes X.count F) c v=recital F f (carriesG X ∘ v) := by
  have hv (x : Site X.count) : Summable (pool F (carpet x)) := (h.hasSum.tsum_fiberwise (carpet x)).summable
  rw [grapes,recital_sum _ _ (fun i _=>hv i),_root_.sum_apply]; simp_rw [recital_pool _ h]; rw [recital_eval _ h,sum_comm,← Fintype.sum_prod_type (f:=fun i => ∑' j, F j*rosary v i.1 (carpet i.2 j))]; symm
  refine Fintype.sum_equiv X.splitSites _ _ (fun z=>?_); apply tsum_congr; intro b
  congr 1; apply prod_congr rfl; intro i _
  simp only [Function.comp_apply,carriesG,silks,split_co,moves_parent,moves_residue,carpet,← X.unpack]
lemma grapes_stanza [Fintype α] (X : Ratio c f) (x : PAC (Co X.count α) c) (h : Summable F) :
    stanza (grapes X.count F) c x=stanza F f (carriesG X x) := grapes_rec X (fun _=> x) h

lemma ling_bead_sum (v : ℝ) (x : Beads α r) (y : Fin r → Cover) (hv : 0≤v) :
    (∏ i,Real.exp (v*size ((x i).1 + y i))) ≤ ling v x*∏ i,Real.exp (v*size (y i)) := by
  rw [ling_as,← prod_mul_distrib]
  refine prod_le_prod (fun _ _=> (Real.exp_pos _).le) (fun i _=>?_); rw [← Real.exp_add,← mul_add]; apply Real.exp_monotone
  apply mul_le_mul_of_nonneg_left _ hv; exact_mod_cast size_add ..
end YM.RG08
