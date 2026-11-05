import YM.Extra.WILSON_STARTUP.OnShell
/-! Compose.Decompose for Jet n (non-normalized) using Rest. No analytic eval clipped. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Change.Reading
open Function Filter Precision Work
open scoped Topology ContDiff BigOperators Classical
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]{n:ℕ}
lemma part_small (c:OrderedFinpartition n)(h:2≤c.length)(i): c.partSize i<n:=by
   have hi : (∑ i,c.partSize i)=n:=by simpa only [Fintype.card_fin,Fintype.card_sigma] using Fintype.card_congr c.equivSigma
   letI : Nontrivial (Fin c.length):= Fin.nontrivial_iff_two_le.mpr h
   obtain ⟨j,hj⟩:= exists_ne i
   apply lt_of_lt_of_le ?_ hi.le; rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
   exact lt_add_of_pos_left _ ((c.partSize_pos j).trans_le (Finset.single_le_sum (f:=fun i=> c.partSize i) (fun i _=>Nat.zero_le _) (Finset.mem_erase.mpr ⟨hj,Finset.mem_univ _⟩))) -- i issue
-- vanishing linear at >1
lemma dormant (S:X→L[ℝ] Y)(h:2≤n)(x:X) : iteratedFDeriv ℝ n S x=0:=by
   obtain ⟨p,hp⟩:=Nat.exists_eq_add_of_le h; rw [show n=p+1+1 by omega, iteratedFDeriv_succ_eq_comp_right, comp_apply]
   rw [show fderiv ℝ S=(fun _=> S) from funext fun _=> S.fderiv, iteratedFDeriv_succ_const]; simp; exact (continuousMultilinearCurryRightEquiv' ℝ (p+1) X Y).symm.map_zero --]

abbrev sign (f:X→Y)(x:X)(n:ℕ):= iteratedFDeriv ℝ n f x
def carta (g:Y→Z)(f:X→Y)(n:ℕ)(x:X)(y:Y) := ∑ c∈ Finset.univ.filter (fun c:OrderedFinpartition n=> 2≤c.length), (c.compAlongOrderedFinpartitionL ℝ X Y Z (sign g y c.length)) fun i=> sign f x (c.partSize i)
variable {f:X→Y}{g:Y→Z}{x:X}
lemma docking (hg:ContDiffAt ℝ ω g (f x))(hf:ContDiffAt ℝ ω f x)(hn:0<n):
   sign (g∘f) x n=(fderiv ℝ g (f x)).compContinuousMultilinearMap (sign f x n) + carta g f n x (f x):=by
    let S:= fderiv ℝ g (f x); let H:=g-(fun x=> S x)
    have he : ContDiffAt ℝ ω H (f x):= hg.sub S.contDiff.contDiffAt
    have hp : fderiv ℝ H (f x)=0:=by unfold H; rw [fderiv_sub (hg.differentiableAt (by simp)) S.differentiableAt,S.fderiv]; exact sub_self _
    have hρ : H ∘ f=g∘ f - (fun x=> S x)∘ f:=rfl
    have hs := iteratedFDeriv_comp he hf (show (n:WithTop ℕ∞)≤ω from le_top)
    rw [hρ, iteratedFDeriv_sub_apply ((hg.comp _ hf).of_le le_top) ((S.contDiff.contDiffAt.comp (g:=fun x=> S x) _ hf).of_le le_top)] at hs -- change static S
    have hk := S.iteratedFDeriv_comp_left hf (i:=n) (by simp)
    rw [show iteratedFDeriv ℝ n ((fun x=> S x) ∘ f) x= _ from hk] at hs
    rw [add_comm]; apply sub_eq_iff_eq_add.mp; apply hs.trans
    unfold carta; change ∑ c:OrderedFinpartition n, _ = _
    let F(c:OrderedFinpartition n):= c.compAlongOrderedFinpartitionL ℝ X Y Z (sign H (f x) c.length) fun i=> sign f x (c.partSize i)
    trans ∑ c∈Finset.univ.filter (fun c:OrderedFinpartition n=>2≤c.length), F c
    · refine Eq.symm (Finset.sum_subset (Finset.filter_subset ..) fun i hi hx=>?_)
      have hy : i.length=1:=by have he:= i.length_pos hn; simp only [Finset.mem_filter,Finset.mem_univ,true_and,not_le] at hx; omega
      have hv: iteratedFDeriv ℝ i.length H (f x)=0:=by rw [hy]; ext1 v; simp [hp]
      change F i=0; unfold F sign; rw [hv,map_zero]; rfl
    refine Finset.sum_congr rfl fun c hc=>?_ ; unfold F sign; rw [show H=_ from rfl, iteratedFDeriv_sub_apply (hg.of_le (by exact le_top : (↑c.length:WithTop ℕ∞) ≤ ω)) (S.contDiff.contDiffAt),dormant S (Finset.mem_filter.mp hc).2,sub_zero]
end YM.WilsonStartup.Change.Reading
