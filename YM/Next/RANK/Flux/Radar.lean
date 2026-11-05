import YM.Next.RANK.Flux.Budget
import YM.Next.RANK.Flux.Panels

/-!
# Pointer budget reporting

Root prior to each projection. Here reuse nonrepeating Ac pack; also on ANY
cover grain through growth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory
open scoped BigOperators Classical

variable {V ι κ α β : Type*} {G : Gauge} {n : Side} [DecidableEq V] [Fintype V] {ζ : V→ Site n} {t e y : ℝ}

section single
variable (S : ι→Support n) (f : ι→ℝ) (P : BudgetPoint) [Fintype ι]

def strike (x : ι→ Prop) (v : ℝ) := ∑ i∈ univ.filter x,alarm S f P.B v i
def Hits (σ e : ℝ) := ∀ x : Site n, strike S f P (fun i=>x∈ S i) σ ≤ e
lemma quotas (hf : ∀ i,0≤ f i) (h : Hits S f P e y) : Ac.Hit S P.B f e y:= by
  intro x; refine ⟨fun i=> ?_,(hasSum_fintype _).summable, (tsum_fintype ..).trans_le ?_⟩
  · dsimp only; split_ifs; exact alarm_pos S f _ e hf _; exact le_rfl
  have ht:=h x; unfold strike at ht; rw [sum_filter] at ht; apply le_trans _ ht; exact sum_le_sum fun i _=> by split_ifs<;>exact le_rfl

variable [DecidableEq ι]
local notation "J" => P.B
private lemma on_root (U : Support n) (s : Finset ι) (hf : ∀ i,0 ≤ f i) (h : Hits S f P (e+1) y) (he : ((J+J+1:ℕ):ℝ)^4*y ≤ 1) (hg : 0 ≤ y):
    Ac.film S s U (alarm S f J e) ≤ Real.exp (coverNumber J U) := by
  induction s using Finset.strongInduction generalizing U with
  | H s IH=>
  let b:=alarm S f J e;have hB i:0≤b i:= alarm_pos S f J e hf _
  apply (Ac.lookup S s U b hB).trans; let q:= Ac.buds S s U
  let F:=alarm S f J (e+1)
  calc
    _ ≤ ∏ i∈ q,Real.exp (F i):= by
      apply prod_le_prod; intro j _; apply add_nonneg zero_le_one; exact mul_nonneg (hB _) (Finset.sum_nonneg fun i _=>prod_nonneg fun i _=> hB i)
      intro i hi; rw [add_comm]; apply le_trans _ (Real.add_one_le_exp (F i)); apply add_le_add_left; apply le_trans (mul_le_mul_of_nonneg_left (IH _ (erase_ssubset ((Ac.alive S s U).mp hi).1) _) (hB i))
      unfold b F alarm; rw [add_mul,one_mul,Real.exp_add,mul_assoc]
    _ ≤ _:= by
      rw [← Real.exp_sum];apply Real.exp_monotone; apply (Ac.demand S _ (quotas S f P hf h) U s).trans
      apply (mul_le_mul_of_nonneg_right (show (U.card:ℝ) ≤ coverNumber J U * ((J+J+1:ℕ):ℝ)^4 by exact_mod_cast Corona.pays U J) hg).trans
      rw [mul_assoc]; exact mul_le_of_le_one_right (by positivity) he

lemma anchor_tag (i : ι) (hf : ∀ i,0 ≤ f i) (h : Hits S f P (e+1) y) (ha : 0≤e) (he : ((J+J+1:ℕ):ℝ)^4*y ≤ 1) (hg : 0 ≤ y):
    ∑ s∈ univ.filter (fun s=> Spark S s ∧ i∈s), (∏ j∈s,f j)*Value.charge P e (s.biUnion S) ≤ alarm S f J (e+1) i:= by
  let q:=P.B; let b:=alarm S f q e; let T:= univ.filter fun s=> Spark S s∧ i∈s
  apply le_trans (b:=b i * Ac.film S (univ.erase i) (S i) b)
  · apply le_trans (b:=∑ s∈T,b i * ∏ j∈s.erase i,b j)
    · refine sum_le_sum fun s hs=> ?_; obtain ⟨hv,hx⟩:= (mem_filter.mp hs).2;rw [mul_prod_erase _ b hx]; unfold b alarm; rw [prod_mul_distrib,← Real.exp_sum,←mul_sum]
      apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun i _=> hf _); unfold charge; gcongr; exact_mod_cast Ac.cover S J hv
    rw [← Finset.mul_sum];apply mul_le_mul_of_nonneg_left _ (alarm_pos _ f q e hf _); let A:=T.image fun s=> s.erase i
    have he (s : Finset ι) (h : s∈T): Spark S s ∧ i∈s:= (mem_filter.mp h).2
    have hx: ∑ s∈T, (∏ j∈s.erase i,b j) =∑ s∈A,(∏ j∈s,b j):= Eq.symm (sum_image fun s hs t ht h=> (insert_erase (he s hs|>.2)).symm.trans ((congr_arg (fun s=> insert i s) h).trans (insert_erase (he t ht|>.2))))
    rw [hx];apply sum_le_sum_of_subset_of_nonneg _ fun _ _ _=> prod_nonneg fun i _=> alarm_pos S f q e hf i
    intro s hs; obtain ⟨t,ht,rfl⟩:=mem_image.mp hs
    exact (Ac.op ..).2 ⟨erase_subset_erase i (subset_univ t),Ac.excise S (he t ht|>.1) (he t ht|>.2)⟩
  apply (mul_le_mul_of_nonneg_left (on_root S f P (S i) _ hf h he hg) (alarm_pos S f J e hf _)).trans
  unfold alarm; rw [add_mul,one_mul,Real.exp_add,mul_assoc]
end single

section
variable (S : ι→ Plug G ζ t) (P : κ → Lining G ζ t) [Fintype ι] [Fintype κ] (f : ι⊕κ→ℝ) {b c : ℝ} (A : BudgetPoint)
def panda (p : Party S P) := ∏ i∈p.val, f i
variable (h : ∀ i, 0≤ f i) (hp : Hits (dish S P) f A (b+1) y) (hv : ((A.B+A.B+1:ℕ):ℝ)^4*y ≤ 1) (he : 0≤b) (hy : 0≤y)
omit [Fintype ι] [Fintype κ] in
lemma panda_pos (p) (h : ∀ i,0 ≤ f i) : 0 ≤ panda S P f p:= prod_nonneg fun i _=> h i
include h hp hv he hy
lemma pad : Hits (lamps S P) (panda S P f) A b (Real.exp y -1):= by
  let X := dish S P;let p:= Party S P
  intro x; have ht := Ac.forest X _ he h (quotas _ _ _ h hp) hv hy x
  apply le_trans _ ((tsum_fintype ..).symm.trans_le ht.2.2)
  let Q:= univ.filter fun p:Party S P=> x∈ lamps S P p
  apply le_trans (b:=∑ i∈Q.image Subtype.val, Ac.roots X A.B f b x i)
  · rw [Finset.sum_image Subtype.val_injective.injOn]; let g (x') := alarm (lamps S P) (panda S P f) A.B b x'
    rw [show strike (lamps S P) _ A (fun i=>x∈lamps S P i) b=∑ i∈Q,g i from Finset.sum_congr (Finset.ext fun _=>by simp [Q]) (fun _ _=>rfl)];apply sum_le_sum; intro i hi
    rw [Ac.roots, if_pos (show Spark X i.val∧ x∈i.val.biUnion X from ⟨i.property.1,(mem_filter.mp hi).2⟩)]; exact (mul_comm ..).le
  exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>ht.1 _)

lemma pad_root (R : Finset (Party S P)) (i : ι⊕κ) (hR : ∀ j∈R, i∈j.val) :
    (∑ j∈R,alarm (lamps S P) (panda S P f) A.B b j) ≤ alarm (dish S P) f A.B (b+1) i:= by
  let X:=dish S P; let T:= univ.filter (fun s=> Spark X s∧i∈s);let g:Finset _→ℝ:=fun s=> (∏ j∈s,f j)*Value.charge A b (s.biUnion X)
  apply le_trans _ (anchor_tag X f A i h hp he hv hy); change _ ≤ ∑ j∈T,g j
  apply le_trans (b:=∑ j∈R.image Subtype.val,g j)
  · rw [sum_image Subtype.val_injective.injOn]; exact le_rfl
  apply Finset.sum_le_sum_of_subset_of_nonneg; intro j hj; obtain ⟨j,hjQ,rfl⟩:=mem_image.mp hj; exact mem_filter.mpr ⟨mem_univ _,j.property.1,hR j hjQ⟩; intro j _ _; exact mul_nonneg (prod_nonneg fun i _=>h i) (Real.exp_pos _).le

end
end YM.Next.Rank.Flux
