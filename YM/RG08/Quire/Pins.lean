import YM.RG08.Quire.Ink
import YM.RG08.Ballast.Coda
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Rooted Taylor stencils. Symmetry of actual coefficients. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Quire
open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary
open scoped Topology ContDiff Classical BigOperators

abbrev Rooted (E α : Type) (r : ℕ) := Beads α r → E
abbrev Spine (E α : Type) := (r : ℕ)→Rooted E α r
abbrev Screed (E α : Type) := ℕ→Spine E α
variable {E F α β γ ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {w A : ℝ} {r : ℕ} {x y : Rooted E α r} {f g : Shale α r} {m : Side}
abbrev Lit (f : Rooted E α r) (w A : ℝ) := Ink (ling w) f A
-- Invariance on actual stencils (could demand structurally sewn).
structure Tidy (f : Rooted E α r) : Prop where
  pens : Pens f
  woven : ∀ (b : Beads α r) (s : Equiv.Perm (Fin r)), f (b ∘ s)=f b
lemma Tidy.zero (E α : Type) [NormedAddCommGroup E] (r : ℕ) : Tidy (0: Rooted E α r) := ⟨Pens.zero ..,fun _ _=>rfl⟩
lemma Tidy.plus (h : Tidy x) (hp : Tidy y) : Tidy (x+y) := ⟨h.pens.plus hp.pens,fun i j=> congr_arg₂ (· + ·) (h.woven i j) (hp.woven i j)⟩
lemma Tidy.neg (h : Tidy x) : Tidy (-x) := by refine ⟨h.pens.neg,fun i j=>?_⟩; simp [h.woven]
lemma Tidy.less (h : Tidy x) (hp : Tidy y) : Tidy (x-y) := sub_eq_add_neg x y ▸ h.plus hp.neg
lemma Tidy.scale (h : Tidy x) (b : ℝ) : Tidy (b • x) := ⟨h.pens.scale b,fun i j=> congr_arg (b•·) (h.woven i j)⟩
lemma Tidy.additions {f : ι→Rooted E α r} {s : Finset ι}(h : ∀ i∈s,Tidy (f i)) : Tidy (∑ i∈s,f i) := by
  induction s using Finset.induction_on with
  | empty=>rw [sum_empty]; exact Tidy.zero ..
  | insert i s hi ih=>rw [sum_insert hi]; exact (h _ (mem_insert_self ..)).plus (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma Tidy.map (e : E→L[ℝ] F) (h : Tidy x) : Tidy (e ∘ x) := ⟨h.pens.shaped e,fun i j=> congr_arg e (h.woven i j)⟩

private def carousel (f : Rooted E α r) (s : Equiv.Perm (Fin r)) (b : Beads α r) := f (b ∘ s)
def sew (f : Rooted E α r) : Rooted E α r := (amplitude r)⁻¹ • ∑ s,carousel f s
private def permEq (s : Equiv.Perm (Fin r)) : Beads α r ≃ Beads α r := Equiv.arrowCongr s.symm (Equiv.refl _)
lemma stitching (hf : Lit x w A) : Lit (sew x) w A := by
  have hh (s) : Lit (carousel x s) w A := by
    have h b : ling w b=ling w (permEq s b) := congr_arg (fun z:ℕ=>Real.exp (w*z)) (Equiv.sum_comp s (fun i=>size ((b:Beads α r) i).1)).symm
    unfold Lit Ink; convert budget_pull (permEq s) (permEq s).injective hf using 1; funext b; rw [h]; rfl
  have hS : Lit (∑ s,carousel x s) w (∑ _ : Equiv.Perm (Fin r), A) := Ink.additions (fun i _=>hh i) (fun i=> (ling_pos w i).le)
  convert hS.scale (amplitude r)⁻¹ using 1
  · rfl
  have hp : 0<amplitude r := by unfold amplitude; positivity
  rw [sum_const,card_univ,nsmul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le), inv_mul_cancel_left₀ hp.ne']
lemma Tidy.sewn (h : Pens x) : Tidy (sew x) := by
  have he : Lit x 0 (∑' i,‖x i‖) := by rw [Lit,show ling (α:=α) (r:=r) 0=1 from funext fun _=>by simp [ling]]; exact h.priced
  constructor; exact (stitching he).pens (ling_one le_rfl)
  intro b t; simp only [sew,carousel,Pi.smul_apply,Finset.sum_apply]; congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft t) _ _ fun i=>rfl
-- also can sew before/after looking at any polynomial products in slots
lemma sewn_income (w : Beads α r→ℝ) (hp : 0≤w) (hk: ∀ z,∀ s:Equiv.Perm (Fin r),w (z∘s)=w z)(hx : Ink w x A): Ink w (sew x) A := by
  have he s : Ink w (carousel x s) A:= by
    unfold Ink; convert budget_pull (permEq s) (permEq s).injective hx using 1; funext b; rw [show w (permEq s b)=w b from hk b s]; rfl
  have hg : 0<amplitude r:= by unfold amplitude; positivity
  apply Ink.raise (Ink.scale (Ink.additions (s:=univ) (fun i _=> he i) hp) _); rw [sum_const,card_univ,nsmul_eq_mul, Real.norm_of_nonneg (inv_nonneg.mpr hg.le), inv_mul_cancel_left₀ (ne_of_gt hg)]
-- No arguments picked, multiplicities genuine.
lemma sew_sub : sew (x-y)=sew x-sew y := by
  unfold sew; simp_rw [show ∀ i, carousel (x-y) i=carousel x i-carousel y i from fun i=>rfl,sum_sub_distrib,smul_sub]
lemma sew_weight (a : ℝ) : sew (a • x)=a • sew x := by unfold sew; simp_rw [show ∀ i,carousel (a • x) i=a • carousel x i from fun _=>rfl, ← Finset.smul_sum,smul_comm a]
lemma sew_map (e : E→L[ℝ] F) : e ∘ sew x=sew (e ∘ x) := by funext b; simp only [comp_apply,sew,carousel,Pi.smul_apply,Finset.sum_apply, _root_.map_smul,_root_.map_sum]

variable [Fintype α]
abbrev rootSong (f : Shale α r) (m : Side) (i : Site m) := Tensor.diagonal (stitch f m i)
private lemma carousel_stitch (h : Summable f) (v : Fin r→PAC α m) (i : Equiv.Perm (Fin r)) (z : Site m) :
    stitch (carousel f i) m z v=stitch f m z (v ∘ i) := by
  rw [stitch_apply (v:=v),stitch_apply h]; swap
  · exact h.comp_injective (permEq i).injective
  rw [← Equiv.tsum_eq (permEq (α:=α) i) (fun j=>f j*rosary (v ∘ i) z j)]
  apply tsum_congr; intro b
  apply congr_arg (f (permEq i b)*·)
  apply Fintype.prod_equiv i.symm _ _
  intro a; change v a _= v (i (i.symm a)) (z+wrap _ (b (i (i.symm a))).1, (b (i (i.symm a))).2); rw [i.apply_symm_apply]; rfl
lemma st_sub (h : Summable f) (g' : Summable g) (z : Site m) : stitch (f-g) m z=stitch f m z-stitch g m z := by
  ext1 v; rw [_root_.sub_apply,stitch_apply h,stitch_apply g',stitch_apply (show Summable (f-g) from h.sub g')]; simp_rw [Pi.sub_apply,sub_mul]; exact (bead_summable _ v h _).tsum_sub (bead_summable _ v g' _)
lemma st_plus (h : Summable f) (g' : Summable g) (z : Site m) : stitch (f+g) m z=stitch f m z+stitch g m z := by
  ext1 v; rw [_root_.add_apply,stitch_apply h,stitch_apply g',stitch_apply (show Summable (f+g) from h.add g')]; simp_rw [Pi.add_apply,add_mul]; exact (bead_summable _ v h _).tsum_add (bead_summable _ v g' _)
lemma st_scale (a : ℝ) (h : Summable f) (z : Site m) : stitch (a • f) m z=a • stitch f m z := by
  ext1 v; rw [_root_.smul_apply,stitch_apply h,stitch_apply (show Summable (a • f) from h.mul_left a)]; simp_rw [Pi.smul_apply, smul_eq_mul,mul_assoc a,tsum_mul_left]
@[simp] lemma st_zero (z : Site m) : stitch (0:Shale α r) m z=0 := by ext1 v; rw [stitch_apply (show Summable (0:Shale α r) from summable_zero)]; simp
lemma st_sums {f : ι→Shale α r} (s : Finset ι) (hp : ∀ i∈s,Summable (f i)) (z : Site m) : stitch (∑ i∈s,f i) m z=∑ i∈s,stitch (f i) m z := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih=>
    have he j hj := hp j (mem_insert_of_mem (s:=s) hj)
    rw [sum_insert hi,sum_insert hi,st_plus (hp _ (mem_insert_self ..)) (shale_total_sum s he), ih he]
lemma sew_diagonal (h : Pens f) (z : Site m) : rootSong (sew f) m z=rootSong f m z := by
  have hp : Summable f := h.of_norm
  funext v
  unfold rootSong Tensor.diagonal sew
  have he s : Summable (carousel f s) := hp.comp_injective (permEq s).injective
  rw [st_scale _ (shale_total_sum _ (fun s _=> he s)), st_sums _ (fun s _=>he s),_root_.smul_apply, _root_.sum_apply]
  simp_rw [carousel_stitch hp]; simp only [comp_def,sum_const,card_univ,nsmul_eq_mul,smul_eq_mul]; rw [inv_mul_cancel_left₀ (show amplitude r≠0 by unfold amplitude; positivity)]
lemma Tidy.sym (h : Tidy f) (z : Site m) : Tensor.Sym (stitch f m z) := by
  intro v t; exact (carousel_stitch h.pens.of_norm v t z).symm.trans (by rw [show carousel f t=f from funext fun b=>h.woven b t])
lemma Tidy.shale_limit (h : Tidy f) {v : Filter ι} (m : ι→Side) (hm : Tendsto (fun i => (m i).val) v atTop) (b) : Tendsto (fun i =>
    stitch f (m i) (0:Site (m i)) (fun k => Pi.single (silks (0:Site (m i)) b k) 1)) v (𝓝 (f b)) := by
  let s (i) (j : Beads α r) := if silks (0:Site (m i)) j=silks (0:Site (m i)) b then f j else 0
  let g (j : Beads α r) := if j=b then f j else 0
  simp_rw [stitch_apply h.pens.of_norm,chord_single]
  have hg i j : f j*(if silks (0:Site (m i)) j=silks (0:Site (m i)) b then 1 else 0)=s i j := by unfold s; split <;> simp
  simp_rw [hg]
  have hu (j) : Tendsto (fun i=>s i j) v (𝓝 (g j)) := by
    by_cases he : j=b
    · rw [he]; simp only [s,g,↓reduceIte]; exact tendsto_const_nhds
    obtain ⟨k,hk⟩ := Function.ne_iff.mp he
    refine EventuallyEq.tendsto ?_
    filter_upwards [eventually_unfold m hm (j k).1,eventually_unfold m hm (b k).1] with i hv hw
    dsimp only [g,s]; rw [if_neg he,if_neg]; intro ht
    apply hk
    have he := congr_fun ht k
    have hp : wrap (m i) (j k).1=wrap (m i) (b k).1 := add_left_cancel (congr_arg Prod.fst he)
    exact Prod.ext ((hv.symm.trans (congr_arg lift hp)).trans hw) (show (silks (0:Site (m i)) j k).2=(silks (0:Site (m i)) b k).2 from congr_arg Prod.snd he)
  have hb (i j) : ‖s i j‖ ≤ ‖f j‖ := by unfold s; split <;> simp
  have he := tendsto_tsum_of_dominated_convergence h.pens hu (.of_forall hb)
  rw [show ∑' j,g j=f b by simp [g]] at he; exact he
lemma Tidy.unicity (h : Tidy f) (hv : Tidy g) {l : Filter ι} [l.NeBot] (m : ι→Side)
    (hm : Tendsto (fun i=> (m i).val) l atTop) (he : ∀ᶠ i in l,rootSong f (m i) 0=rootSong g (m i) 0) : f=g := funext fun p=>
  tendsto_nhds_unique_of_eventuallyEq (h.shale_limit m hm p) (hv.shale_limit m hm p) (he.mono fun i hi=>DFunLike.congr_fun (Tensor.ext_diag _ _ (h.sym (0:Site (m i))) (hv.sym _) hi) _)
lemma Tidy.uniquely (h : Tidy f) (hv : Tidy g) (hp : ∀ m,rootSong f m 0=rootSong g m 0) : f=g :=
  h.unicity hv (fun n : ℕ => (⟨n+1,Nat.succ_pos _⟩:Side)) (tendsto_add_atTop_nat _) (.of_forall fun _=>hp _)
end YM.RG08.Quire
