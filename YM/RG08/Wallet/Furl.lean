import YM.RG08.Ballast.Slide
import YM.RG08.Wallet.Stays

/-! # Linear substitution purchases

Pre/post costs distinguished via Estate and Row width lenders. Inputs varying
index type (gauge etc potentially), not suppressing finite-color counts. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff Classical
variable {r : ℕ}
section test
variable {α β : Type} [Fintype β]
variable {F U : Shale α r} {A B C : Fin r→ Row α β}
private lemma noCharge (h : Summable F) : Glow F 0 (∑' i, ‖F i‖) := by unfold Glow Charge ling; simp only [zero_mul,Real.exp_zero,one_mul]; exact ⟨fun i => norm_nonneg _,h.norm,le_rfl⟩
private lemma noWard {α β : Type} {A : Row α β} (h : Whole A) : ∃ C : ℝ,0≤C ∧ A.strip 0 C := by obtain ⟨w,C,hp,H⟩:=h; exact ⟨max C 0,le_max_right ..,Work.F08.strip_mono H hp.le (le_max_left ..)⟩
private lemma nonraid (h : Summable F) (u : ∀ i, Whole (A i)) : Summable (leads F (flicker A)) := by
  choose C hc H using fun i=> noWard (u i)
  exact (grow_cost _ _ (noCharge h) le_rfl hc H).summable (fun i=> ling_one le_rfl _)
lemma ribbons_sum (h : Summable F) (u : ∀ i,Whole (A i)) : Summable (ribbon F A) := ((nonraid h u).hasSum.tsum_fiberwise fieldsAt).summable
lemma ribbon_eval_all [Fintype α] (h : Summable F) (u : ∀ i,Whole (A i)) (c : Side) (v : Fin r→PAC β c) :
    recital (ribbon F A) c v = recital F c (fun i => (A i).acts c *ᵥ v i) := by
  choose C hc H using fun i=> noWard (u i)
  exact strands _ _ (noCharge h) le_rfl hc H c v
lemma ribbon_less (h : Summable F) (v : Summable U) (hk : ∀ i, Whole (A i)) : ribbon (F-U) A=ribbon F A-ribbon U A := by
  unfold ribbon; rw [leads_minus, pool_minus _ (nonraid h hk) (nonraid v hk)]
-- one changed leg ONLY
lemma noteRibbon (h : Summable F) (hk : ∀ i, Whole (A i)) (hv : ∀ i,Whole (B i)) (z : Fin r) (hq : ∀ j, j≠z → A j=B j) :
    ribbon F (update A z (A z-B z))= ribbon F A-ribbon F B := by
  let X := update A z (A z-B z)
  suffices hp : flicker X=flicker A-flicker B by change ribbon F X=_; unfold ribbon; rw [hp, leads_diff,pool_minus _ (nonraid h hk) (nonraid h hv)]
  ext1 i
  have hx j hj : X j=A j := update_of_ne hj ..
  let q := i.1; let k := i.2
  let f (A : Fin r→Row α β) (s) (_i : Fin r) := ∏ j∈s,A j (q j).2 (k j).2 (k j).1
  change f X univ z= f A univ z- f B univ z
  let s := univ.erase z
  have hp : f X s z=f A s z := prod_congr rfl fun i hi=> by rw [hx i (mem_erase.mp hi).1]
  have he : f B s z=f A s z := prod_congr rfl fun i hi=> by rw [hq i (mem_erase.mp hi).1]
  have hv (C : Fin r→Row α β): f C univ z=C z (q z).2 (k z).2 (k z).1*f C s z := (mul_prod_erase univ _ (mem_univ z)).symm
  rw [hv,hv A,hv B,hp,he,show X z=A z-B z from update_self ..]; exact _root_.sub_mul ..
end test

section variation
variable {I J : Type} {α β : I→Type} [∀ i,Fintype (β i)] {y v w δ : I→ℝ} {x : I→Side}
variable {V T : ∀ i,Shale (α i) r} {C B : ∀ i,Row (α i) (β i)}
lemma Weighed.prod (s : Finset J) {p : J→I→ℝ} (h : ∀ i∈s,Weighed y (p i)) : Weighed y (fun i=> ∏ j∈s,p j i) := by
  induction s using Finset.induction_on with
  | empty => simpa [Set.mem_setOf_eq] using Weighed.constant y zero_le_one
  | insert i s hi ih => simp_rw [prod_insert hi]; exact (h i (mem_insert_self ..)).times (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma Weighed.powers {p : I→ℝ} (h : Weighed y p) (s : ℕ) : Weighed y (fun i=> (p i)^s) := by induction s with | zero => simp only [pow_zero]; exact Weighed.one| succ s ih => simp_rw [pow_succ]; exact ih.times h
private lemma bindR {η : Fin r→I→ℝ} {A : Fin r→ ∀ i, Row (α i) (β i)} (h : 0≤w) (hp : Voucher y δ V w)
    (hq : ∀ i,0 ≤ η i) (hK : ∀ i, SafeRow y (η i) (A i) w) (hv : Weighed y (fun i=> (Fintype.card (β i):ℝ))) :
    Voucher y (fun i=> (∏ j, η j i)*δ i) (fun i=> ribbon (V i) (fun j=> A j i)) w := by
  obtain ⟨b,hb,H⟩:=hp; choose p hP H' using hK
  refine ⟨_, ((hv.powers r).times (Weighed.prod univ fun i _=> hP i)).times hb,fun i=>?_⟩
  apply glow_less (ribbon_price _ _ (H i) (h i) (fun j=> mul_nonneg ((hP j).positive i) (hq j i)) (fun j=> H' j i)) le_rfl
  simp only [Pi.mul_apply,prod_mul_distrib]; exact le_of_eq (by ring)
lemma bind_budget (h : 0≤w) (hp : Voucher y δ V w) {A : Fin r→ ∀ i,Row (α i) (β i)}
    (hK : ∀ i, SafeRow y 1 (A i) w) (hv : Weighed y (fun i=> (Fintype.card (β i):ℝ))) : Voucher y δ (fun i => ribbon (V i) (fun j=> A j i)) w := by
  simpa only [Pi.one_apply,prod_const_one,one_mul] using bindR h hp (fun j i=>show (0:ℝ)≤1 from zero_le_one) hK hv

lemma exchangeR (h : ∀ i, 0<w i) (hg : Audience y) (hδ : 0 ≤ δ) (hv : Voucher y 1 V w) {F H : Fin r→∀ i,Row (α i) (β i)}
    (hf : ∀ i,RowBoth y δ (F i) (H i) w) (hp : Weighed y (fun i=> (Fintype.card (β i):ℝ))) :
    Voucher y δ (fun i=> ribbon (V i) (fun j=> F j i)-ribbon (V i) (fun j=> H j i)) w := by
  let m (s : Finset (Fin r)) (j) := if j∈s then H j else F j
  have hm s j : SafeRow y 1 (m s j) w := by
    by_cases hx:j∈s; · simpa only [m,if_pos hx] using (hf j).again
    simpa only [m,if_neg hx] using (hf j).fresh
  have he (s : Finset (Fin r)) : Voucher y δ (fun i=> ribbon (V i) (fun j=> F j i)-ribbon (V i) (fun j=> m s j i)) w := by
    induction s using Finset.induction_on with
    | empty => simp only [m, notMem_empty, ↓reduceIte,sub_self]; exact Voucher.zero
    | insert a s ha IH=>
      let D (j) := if j=a then F a-H a else m s j
      let W : Fin r→I→ℝ := fun j=> if j=a then δ else 1
      have hx j : SafeRow y (W j) (D j) w := by
        unfold D W; split
        · exact (hf a).moves
        exact hm s j
      have hh : ∀ j,0 ≤ W j := by intro j; unfold W; split; exact hδ; exact fun _=> zero_le_one
      have hk := bindR (show 0≤w from fun i=>(h i).le) hv hh hx hp
      let R i := ribbon (V i) (fun j=> D j i)
      have hz : Voucher y δ R w := hk.raise (fun i=> by
        change _*1 ≤ _; rw [mul_one, prod_eq_single a]; exact Eq.le (by simp [W]); intro b hb hh; simp [W,hh]; simp)
      have ht i : R i=ribbon (V i) (fun j=> m s j i)-ribbon (V i) (fun j=> m (insert a s) j i) := by
        unfold R
        let M j := m s j i; let N j := m (insert a s) j i
        rw [show (fun j=> D j i)=update M a (M a-N a) from funext fun b=> by by_cases hb:b=a <;> simp [hb,D,M,N,m,ha]]
        refine noteRibbon ((hv.choose_spec.2 i).summable (ling_one (h i).le)) (fun j=> (hm s j).status h i) (fun j=> (hm (insert a s) j).status h i) a (fun j hj=> ?_); simp [m,hj]
      have HX : (fun i=> ribbon (V i) (fun j=> F j i)-ribbon (V i) (fun j=> m s j i))+R=(fun i=>ribbon (V i) (fun j=> F j i)-ribbon (V i) (fun j=> m (insert a s) j i)) := (show _ from funext fun i=> (show ribbon (V i) (fun j=> F j i)-ribbon (V i) (fun j=> m s j i)+R i=_ by rw [ht]; abel)) -- lambda specify
      rw [← HX]; exact IH.plus hz hg
  simpa only [m,mem_univ,↓reduceIte] using he univ
end variation
end YM.RG08
