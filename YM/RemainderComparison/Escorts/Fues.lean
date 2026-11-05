import YM.RemainderComparison.Flues.Ridges
import YM.RemainderComparison.Jolt.Flash
import YM.Push.LOCAL_SPLITTING.Budget
/-!
 # New input attachments of finite footprint pay no extra support exponent

 All capacities Obj.Art fixed; moving roots with periods/seeds allowed. Keep EVERY 
 compulsory address flag through the gluing. For a connected selection with
 one or more plume slots, EACH old support must intersect a new leg. The old
 supports are mutually disjoint (Pellet grammar); no chain through them can
 connect otherwise, even if another root among the plume is far away.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Escorts
open Function Filter Finset Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Push Push.AbsoluteSums PhysicalNext.Repeat
open Merge Mosaic Mosaic.Verse Marker Jolt Flues
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c:Side}{ι κ:Type}{α:Type*}
variable (C:Pipes G c) (i:C.Pellet)

lemma crest (j:Ovens.Label) (a:ℕ) (hj: Ac.chain C.patch i.val (.inl a) j) (he:j≠ .inl a) : ∃ k:ℕ,k∈i.val.toRight ∧ ¬Disjoint (C.kernel a).support (C.softer k):=by
   induction hj with
   | refl=> exact (he rfl).elim
   | @tail x y _ hx I=>
      by_cases hz:x=.inl a
      · subst x
        rcases y with k|k
        · have hp : Disjoint (C.kernel a).support (C.kernel k).support:= i.prop.2.2 (mem_toLeft.mpr hx.1) (mem_toLeft.mpr hx.2.1) (fun h=>he (congr_arg Sum.inl h.symm)); exact ((show ¬ Disjoint (C.kernel a).support (C.kernel k).support from Finset.not_disjoint_iff.mpr hx.2.2) hp).elim -- hp.not?
        exact ⟨k,mem_toRight.mpr hx.2.1, Finset.not_disjoint_iff.mpr hx.2.2⟩
      exact I hz
lemma falls (j:ℕ)(hj:j∈i.val.toLeft)(he:i.val.toRight.Nonempty):¬Disjoint (C.kernel j).support (i.val.toRight.biUnion C.softer):=by
   obtain ⟨k,hk⟩:=he
   have hh:= i.prop.2.1.2 _ (mem_toLeft.mp hj) _ (mem_toRight.mp hk)
   obtain ⟨z,hz,h⟩:= Escorts.crest C i (.inr k) _ hh (by simp)
   exact fun he=> h (he.mono le_rfl (subset_biUnion_of_mem _ hz))
lemma winter (h:i.val.toRight=∅): ∃ j:ℕ,i.val={Sum.inl j}:=by
   obtain ⟨j,hj⟩:= i.prop.1; refine ⟨j,Subset.antisymm ?_ (singleton_subset_iff.mpr (mem_toLeft.mp hj))⟩; intro z hz; apply mem_singleton.mpr; by_contra hn
   obtain ⟨k,hk,-⟩:= Escorts.crest C i z j (i.prop.2.1.2 _ (mem_toLeft.mp hj) _ hz) hn; rw [h] at hk; exact Finset.notMem_empty _ hk

-- graph covers comparable even for interlacing singleton plume placements.
lemma humps (f:ℕ→ℝ)(w:ℕ→ℝ) (p:BudgetPoint) (hf:∀ i,0 ≤ f i)(hw:∀ i,0≤ w i):
     p.mass (C.skin i) ((∏ j∈ i.val.toLeft,f j)*(∏ j∈i.val.toRight,w j)) ≤
            (∏ j∈ i.val.toLeft,p.mass (C.kernel j).support (f j))*(∏ j∈i.val.toRight,p.mass (C.softer j) (w j)):=by
   let u:= Sum.elim f w
   have hp:=Ac.cover C.patch p.B i.prop.2.1
   have he : p.mass (C.skin i) (∏ j∈i.val,u j) ≤ (∏ j∈i.val,p.mass (C.patch j) (u j)):=by
     have hc : 0≤ ∏ j∈i.val,u j:= prod_nonneg fun j _=> j.rec (fun k=>hf _) (fun k=> hw _); unfold BudgetPoint.mass; rw [Finset.prod_mul_distrib,← Real.exp_sum,← mul_sum]; apply mul_le_mul_of_nonneg_right _ hc; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ p.exponent_pos.le; exact_mod_cast hp
   rw [Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight,Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight] at he; exact he

variable {C i}
variable (F:ℕ≃ C.Pellet) (f w:ℕ→ℝ)(p:BudgetPoint) {B d:ℝ}(D:Support c)
set_option quotPrecheck false
local notation "Λ" => (fun i=>if ((F i).val.toRight).Nonempty then (∏ j∈ (F i).val.toLeft, f j)*(∏ j∈ (F i).val.toRight,w j) else 0)
variable (hf:∀ i,0≤ f i)(hw:∀ i, 0≤ w i) (hp:∀ x:Site c,SumBudget (fun i=>if x∈(C.kernel i).support then p.mass (C.kernel i).support (f i) else 0) B)
variable (he: SumBudget (fun i=>p.mass (C.softer i) (w i)) d) (hz:∀ j,w j≠0→C.softer j ⊆ D)
include hf hw he hp hz
lemma tabulated : SumBudget (fun i=>p.mass (C.skin (F i)) (Λ i)) ((Real.exp ((D.card:ℝ)*B)-1)*(Real.exp d-1)):=by
   have hm (i):= mul_nonneg (Real.exp_pos (p.supportExponent * (coverNumber p.B (C.kernel i).support))).le (hf i)
   have hs:= Local.sumBudget_meeting (X:=fun i=>(C.kernel i).support) D hm hp; let K:= fun i:ℕ=> (Finset.sumEquiv ((F i).val) : Finset ℕ × Finset ℕ)
   have hv:= budget_pull K (Finset.sumEquiv.injective.comp (Subtype.val_injective.comp F.injective)) (budget_prod (Local.sumBudget_exponential hs) (Local.sumBudget_exponential he))
   refine budget_mono hv (fun i=>mul_nonneg (Real.exp_pos _).le ?_) (fun i=> ?_)
   · dsimp only; split; exact mul_nonneg (prod_nonneg fun _ _=> hf _) (prod_nonneg fun _ _=> hw _); exact le_rfl
   dsimp only; split
   next hh =>
     by_cases hc:∏ j∈(F i).val.toRight,w j=0
     · rw [hc, mul_zero, BudgetPoint.mass,mul_zero]; exact hv.1 _
     have hr : ((F i).val.toRight.biUnion C.softer) ⊆ D:=by intro z ht; obtain ⟨j,hj,h⟩:=Finset.mem_biUnion.mp ht; exact hz _ (fun e=> hc (prod_eq_zero hj e)) h
     have ha (j) (hj:j∈ (F i).val.toLeft) : ¬Disjoint D (C.kernel j).support := fun hh'=> Escorts.falls _ (F i) _ hj hh (hh'.symm.mono le_rfl hr)
     apply (Escorts.humps _ (F i) f w p hf hw).trans
     change _ ≤ (if (F i).val.toLeft.Nonempty then ∏ j∈ (F i).val.toLeft,(if Disjoint D (C.kernel j).support then 0 else p.mass (C.kernel j).support (f j)) else 0)*(if (F i).val.toRight.Nonempty then _ else 0); rw [if_pos hh,if_pos (show (F i).val.toLeft.Nonempty from (F i).prop.1)]; exact le_of_eq (congr_arg (· * _) (prod_congr rfl fun j hj=> Eq.symm (if_neg (ha _ hj))))
   next=> rw [BudgetPoint.mass,mul_zero]; exact hv.1 _

-- Calendar supply variation: choose real ceiling depending only on the allowed #marks/positions.
omit hf hw he hp hz
end YM.RemainderComparison.Escorts
