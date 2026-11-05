import YM.SectorNext.RECONNECTED_LOCALITY.Children
import YM.SectorNext.RECONNECTED_LOCALITY.Rose

set_option warningAsError false

/-!
# Local positive tree recursion, for cover-speed integration

 in purpose (bounds for log/marks), alternative proof on
ordered rose trees incl repeats. Marking a counted child needing a hit,
the children series differentiates exponential, we lose *one parent lookup
around the whole child support*, paid exactly by the child's contribution
to parent degree denominator. (No $C B^4$ penalty to the exponent on
each generation!) Works uniform in volume and including winding/infinite
letters, with normalized per-site test as elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect.Rose
open Vouchers RG Lattice Ledger Function Finset
open scoped Classical

variable {ι : Type*} {c : Side} (S : ι → Support c)
  (B : ℕ)

/-- Input test for this recursion (pay d_i at the parent, here exponential
factor `d_i` in the exponent along with possible other costs in v).
-/
structure Climber (v : ι → ℝ) (ε : ℝ) : Prop where
  support : ∀ i, (S i).Nonempty
  fwd : ∀ i,0 ≤ v i
  more : 0 ≤ ε
  room : (Ledger.size B:ℝ)*(2*ε) ≤ 1
  hit : Ac.Hit S B (fun i => (coverNumber B (S i):ℝ)*v i) 1 ε

/-- Positive envelopes truncate only by depth. -/
private def stake (v : ι → ℝ) (m : ℕ) (t : Rose ι) := if t.depth ≤ m then word S B 1 v t else 0

lemma prosperous {v : ι → ℝ} (h : ∀ i,0 ≤ v i) (t : Rose ι) : 0 ≤ word S B 1 v t := by
  induction t using inspect with
  | h i n f IH =>
    rw [spell]; refine div_nonneg (mul_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (h i)) (prod_nonneg (fun i _ => ?_))) (Nat.cast_nonneg _)
    split
    · simpa using IH _
    rfl

private lemma stake0 {v : ι → ℝ} (h : ∀ i,0 ≤ v i) (m : ℕ) (t : Rose ι) : 0 ≤ stake S B v m t := by
  unfold stake; split
  · exact prosperous S B h t
  rfl

private def child (i : ι) (w : Rose ι → ℝ) (t : Rose ι) := if link S i t then w t else 0

/-- Parent's contact cost across the child pool. -/
private lemma child_fee {w : Rose ι → ℝ} {ε : ℝ} (h : Ac.Hit (union S) B w 0 ε) (hW : ∀ i,0 ≤ w i)
    (i : ι) : SumBudget (child S i w) ((S i).card * ε) := by
  refine pinsFromFinite (fun t => ?_) fun s => ?_
  · unfold child; split
    · exact hW _
    rfl
  have he:= Ac.demand (union S) B h (S i) s
  rw [Ac.buds,sum_filter] at he
  simp only [zero_mul,Real.exp_zero,mul_one] at he
  refine le_trans ?_ he; apply sum_le_sum; intro t _
  unfold child; split
  · rename_i hg
    exact le_of_eq (if_pos (Finset.not_disjoint_iff.mp hg)).symm
  split
  · exact hW _
  rfl

private def notice (i : ι) (w : Rose ι → ℝ) (x : Site c) (t : Rose ι) :=
    if x∈union S t then child S i w t / fee S B t else 0

private lemma notice0 {w : Rose ι → ℝ} (hW : ∀ i,0 ≤ w i) (i : ι) (x : Site c) (t : Rose ι) :
    0 ≤ notice S B i w x t := by
  unfold notice child; split_ifs
  · exact div_nonneg (hW t) (Nat.cast_nonneg _)
  · simp
  exact le_rfl

namespace Climber
variable {S B} {v : ι → ℝ} {ε : ℝ} (h : Climber S B v ε)
variable {w : Rose ι → ℝ} (H : Ac.Hit (union S) B w 0 (2*ε)) (hW : ∀ i,0 ≤ w i)

include h
private lemma degree (i : ι) : (1:ℝ) ≤ (coverNumber B (S i):ℝ) := by exact_mod_cast Ledger.cover_pos (B:=B) (h.support i)
private lemma have_fee (t : Rose ι) : (1:ℝ) ≤ (fee S B t:ℝ) := by exact_mod_cast (Nat.le_trans (Rose.exist t) (funds S B h.support t))
private lemma capacity (i : ι) : ((S i).card:ℝ)*(2*ε) ≤ coverNumber B (S i) := by
  calc
    _ ≤ ((coverNumber B (S i):ℕ):ℝ)*(Ledger.size B:ℝ)*(2*ε) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Ledger.rel_size B (S i)) (by have := h.more; positivity)
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_of_le_one_right (Nat.cast_nonneg _) h.room

include H hW
private lemma notice_series (i : ι) (x : Site c) : Summable (notice S B i w x) := by
  refine (child_fee S B H hW i).2.1.of_nonneg_of_le (notice0 S B hW i x) fun t => ?_
  have ht := (child_fee S B H hW i).1 t
  unfold notice; split
  · exact div_le_self ht (h.have_fee t)
  exact ht

-- Paying a parent per encountered child. This sum doesn't erase the
-- D of the child until after exchanging the two hit tests. The Estimate
-- uses C_B*ε and will fit if C_B*2ε ≤ 1.
private theorem reports (x : Site c) :
    SumBudget (fun i => (coverNumber B (S i):ℝ)*v i*Real.exp (coverNumber B (S i)) * ∑' t,notice S B i w x t)
      ((2*ε)*((Ledger.size B:ℝ)*ε)) := by
  let c i := (coverNumber B (S i):ℝ)*v i*Real.exp (coverNumber B (S i))
  have hc i : 0 ≤ c i := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (h.fwd _)) (Real.exp_nonneg _)
  let W (t : Rose ι) := if x∈union S t then w t else 0
  have hbill : SumBudget W (2*ε) := by
    simpa only [W, Ac.Hit,zero_mul,Real.exp_zero,mul_one] using H x
  have hl (q : Finset ι) (t : Rose ι) : ∑ i∈q,c i*notice S B i w x t ≤ ((Ledger.size B:ℝ)*ε) * W t := by
    by_cases hh : x∈union S t
    · have he : ∑ i∈q,(if link S i t then c i else 0) ≤ (union S t).card*ε := by
        have he:=Ac.demand S B h.hit (union S t) q
        rw [Ac.buds, sum_filter] at he
        simp only [one_mul] at he
        refine le_trans (sum_le_sum ?_) he; intro i _
        split
        · rename_i hn; rw [if_pos]
          obtain ⟨a,ha,hb⟩:=Finset.not_disjoint_iff.mp hn
          exact ⟨a,hb,ha⟩
        split
        · exact hc i
        exact le_rfl
      calc
        _ = ∑ i∈q,(if link S i t then c i else 0) * (w t/fee S B t) := by
          refine sum_congr rfl fun i _ => ?_
          unfold notice child; rw [if_pos hh]; split <;> simp
        _ ≤ ((union S t).card*ε)*(w t/fee S B t) := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right he (by have := hW t; positivity)
        _ ≤ ((fee S B t:ℝ)*(Ledger.size B:ℝ)*ε)*(w t/fee S B t) := by
          have he : ((union S t).card:ℝ) ≤ (fee S B t:ℝ)*(Ledger.size B:ℝ) := by exact_mod_cast contained S B t
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he h.more) (by have := hW t; positivity)
        _ = _ := by
          unfold W; rw [if_pos hh]; field_simp [(zero_lt_one.trans_le (h.have_fee t)).ne']
    simp only [notice, if_neg hh,W]; simp
  refine pinsFromFinite (fun i => mul_nonneg (hc i) (tsum_nonneg (notice0 S B hW i x))) fun q => ?_
  change ∑ i∈q,c i* ∑' t,notice S B i w x t ≤ _
  simp_rw [← tsum_mul_left]
  have hs (i) : Summable (fun t => c i * notice S B i w x t) := (h.notice_series H hW i x).mul_left _
  rw [← Summable.tsum_finsetSum (f:=fun i t => c i*notice S B i w x t) (fun i _ => hs i)]
  refine ((summable_sum (s:=q) (f:=fun i t => c i*notice S B i w x t) (fun i _ => hs i)).tsum_le_tsum
    (hl q) (hbill.2.1.mul_left _)).trans ?_
  rw [tsum_mul_left,mul_comm (2*ε)]
  exact mul_le_mul_of_nonneg_left hbill.2.2 (mul_nonneg (Nat.cast_nonneg _) h.more)

/-- Majorants before summing through parents. $f$ graded coefficients here
not raw field functions. First term in `Offer` when parent is at hit;
second term when hit through a particular child (the denominator in `notice`
cancels the incurrence of $|X_{child}|$). -/
private def offer (S : ι → Support c) (B : ℕ) (v : ι → ℝ) (w : Rose ι → ℝ) (x : Site c)
    (i : ι) (p : Row ι) :=
  ((if x∈S i then v i else 0)*issue (child S i w) p) +
    (coverNumber B (S i):ℝ)*v i * invoice (child S i w) (notice S B i w x) p

private lemma limit (x : Site c) :
    SumBudget (fun t : ι × Row ι => offer S B v w x t.1 t.2) (2*ε) := by
  let W i := child S i w; let T i:=notice S B i w x
  let d i := (coverNumber B (S i):ℝ)
  have ht i : 0 ≤ d i := Nat.cast_nonneg _
  let f i := if x∈S i then v i else 0
  let G i := f i * Real.exp (∑' t,W i t) + d i*v i*((∑' t,T i t)*Real.exp (∑' t,W i t))
  have W0 i:=child_fee S B H hW i
  have hf i : 0 ≤ f i := by dsimp [f]; split; exact h.fwd i; rfl
  have hd i := (W0 i).2.2.trans (h.capacity _)
  have hp i : Fee (offer S B v w x i) (G i) := by
    have ha:= (issue_fee (W0 i).2.1 (W0 i).1).scale (hf i)
    have he:= (invoice_fee (W0 i).2.1 (h.notice_series H hW i x) (W0 i).1 (notice0 S B hW i x)).scale
      (mul_nonneg (ht i) (h.fwd i))
    exact ⟨fun t => add_nonneg (ha.pos t) (he.pos t),ha.2.add he.2⟩
  have hn i : 0 ≤ G i := (hp i).paid ▸ tsum_nonneg (hp i).pos
  have hg : SumBudget G (2*ε) := by
    have hw:=h.hit x
    have he:=h.reports H hW x
    apply Ledger.reduce hn _ (Ledger.debit hw he)
    · have hb := h.room; have hm := h.more
      nlinarith
    intro i
    unfold G
    apply add_le_add
    · unfold f; split
      · exact mul_le_mul (le_mul_of_one_le_left (h.fwd _) (h.degree i)) (by rw [one_mul]; exact Real.exp_monotone (hd _))
          (Real.exp_nonneg _) (mul_nonneg (ht _) (h.fwd _))
      simp
    have ht0 : 0 ≤ ∑' t,T i t := tsum_nonneg (notice0 S B hW i x)
    change d i*v i*((∑' t,T i t)*_) ≤ d i*v i*_*(∑' t,T i t)
    rw [mul_comm (∑' t,T i t),← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_monotone (hd _))
      (mul_nonneg (ht _) (h.fwd _))) ht0
  have hfee:= Fee.product (T:=Row ι) (F:=fun i : ι × Row ι => offer S B v w x i.1 i.2) G hp hg.2.1.hasSum
  exact ⟨hfee.pos,hfee.summable,hfee.paid.trans_le hg.2.2⟩

omit H hW in
private lemma advances (m : ℕ) (i : ι) {n : ℕ} (x : Fin n → Rose ι)
    (a : Site c) :
    (if a∈union S (root i x) then stake S B v (m+1) (root i x) else 0) ≤ offer S B v (stake S B v m) a i ⟨n,x⟩ := by
  let P := root i x
  let d (i : ι) := (coverNumber B (S i):ℝ)
  let t j := fee S B (x j)
  let w:=child S i (stake S B v m)
  let W j:=w (x j)
  let b:= if a∈S i then v i else 0
  let r j:=notice S B i (stake S B v m) a (x j)
  have hd : 0 ≤ d i := (h.degree i).trans' zero_le_one
  have hb : 0 ≤ b := by unfold b; split; exact h.fwd _; rfl
  have hw j : 0 ≤ W j := by unfold W w child; split; exact stake0 _ _ h.fwd _ _; rfl
  have hr j : 0 ≤ r j := notice0 S B (stake0 _ _ h.fwd m) i a _
  have hj j k : 0 ≤ if k=j then r k else W k := by split_ifs; exact hr k; exact hw k
  let f:= ((n.factorial:ℕ):ℝ)
  change (if a∈union S P then _ else 0) ≤ b*((∏ j,W j)/f)+d i*v i*((∑ j,∏ k,if k=j then r k else W k)/f)
  have hv : 0 ≤ b*((∏ j,W j)/f) := mul_nonneg hb (div_nonneg (prod_nonneg fun j _ => hw j) (by positivity))
  have hh : 0 ≤ d i*v i*((∑ j,∏ k,if k=j then r k else W k)/f) :=
    mul_nonneg (mul_nonneg hd (h.fwd _)) (div_nonneg (sum_nonneg (fun j _ => prod_nonneg (fun k _ => hj j k))) (by positivity))
  by_cases ha : a∈union S P
  swap; · rw [if_neg ha]; linarith
  rw [if_pos ha]
  unfold stake
  split
  swap; · linarith
  rename_i hd'
  rw [spell]
  have he j : (x j).depth ≤ m := Nat.lt_succ_iff.mp ((climbs i x j).trans_le hd')
  simp_rw [show ∀ j,(if link S i (x j) then 1*word S B 1 v (x j) else 0) = W j from
    fun j => by simp [W,w,child,stake,he]]
  have hparent : d i ≤ (fee S B P:ℝ) := by simp [P,d]; positivity
  have hf' := zero_lt_one.trans_le (h.have_fee P)
  by_cases ht : a∈S i
  · apply le_add_of_le_of_nonneg _ hh
    unfold b; rw [if_pos ht,← mul_div_assoc]
    gcongr
    · exact prod_nonneg fun j _ => hw j
    exact mul_le_of_le_one_left (h.fwd _) ((div_le_one hf').mpr hparent)
  apply le_add_of_nonneg_of_le hv
  have H1 : ∃ j,a∈union S (x j) := by
    simpa [P,ht] using ha
  obtain ⟨j,hj'⟩:=H1
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hden : (t j:ℝ) ≤ (fee S B P:ℝ) := by
    exact_mod_cast le_trans (Finset.single_le_sum (s:=Finset.univ) (fun i _ => Nat.zero_le (t i)) (Finset.mem_univ j))
      (le_trans (Nat.le_add_left _ _) (Nat.le_of_eq (fee_node S B x).symm))
  calc
    _ = (d i/(fee S B P:ℝ))*v i*((∏ k∈univ.erase j,W k)* W j) := by rw [prod_erase_mul _ _ (mem_univ j)]
    _ ≤ (d i/(t j:ℝ))*v i*((∏ k∈univ.erase j,W k)*W j) := by
      have hh := div_le_div_of_nonneg_left hd (show 0<(t j:ℝ) from zero_lt_one.trans_le (h.have_fee (x j))) hden
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (h.fwd _))
        (mul_nonneg (prod_nonneg (fun k _ => hw k)) (hw j))
    _ = d i*v i*∏ k,(if k=j then r k else W k) := by
      rw [← prod_erase_mul univ (fun k => if k=j then r k else W k) (mem_univ j),if_pos rfl,
        prod_congr rfl (g:=W) (fun k hk => if_neg (ne_of_mem_erase hk))]
      unfold r notice; rw [if_pos hj']; change _ = d i*v i*((∏ k∈univ.erase j,W k)*(W j/(t j:ℝ))); ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (single_le_sum (fun j _ => prod_nonneg fun k _ => hj j k) (mem_univ j)) (mul_nonneg hd (h.fwd _))

omit H hW in
private theorem generation (m : ℕ) : Ac.Hit (union S) B (stake S B v m) 0 (2*ε) := by
  induction m with
  | zero =>
    intro x
    suffices hh : SumBudget (fun _ : Rose ι => 0) (2*ε) by
      convert! hh using 1; ext t; unfold stake; simp [show ¬ depth t≤0 from not_le.mpr (depth_pos t)]
    have := h.more
    exact pinsFromFinite (fun _ => le_rfl) fun _ => by simp; assumption
  | succ n IH =>
    intro x
    have hs := Ledger.renamed trunk trunk.injective (h.limit IH (stake0 S B h.fwd n) x)
    refine Ledger.reduce (fun i => ?_) (fun i => ?_) hs le_rfl
    · split
      · exact mul_nonneg (stake0 S B h.fwd ..) (Real.exp_nonneg _)
      exact le_rfl
    obtain ⟨⟨j,n',f⟩,rfl⟩:=trunk.symm.surjective i
    simpa only [root_trunk,comp_apply,trunk_root,zero_mul,Real.exp_zero,mul_one] using
      (show _ from h.advances n j f x)

omit H hW in
/-- No depth dependence in the price. -/
theorem reaches : Ac.Hit (union S) B (word S B 1 v) 0 (2*ε) := by
  intro x
  refine pinsFromFinite (fun i => ?_) fun i => ?_
  · split
    · exact mul_nonneg (prosperous S B h.fwd _) (Real.exp_nonneg _)
    exact le_rfl
  have he:=h.generation (i.sup depth) x
  apply le_trans ?_ ((he.2.1.sum_le_tsum i (fun i _ => he.1 i)).trans he.2.2)
  refine sum_le_sum fun j hj => ?_
  simp [stake,Finset.le_sup (f:=depth) hj]

end Climber
end YM.SectorNext.Reconnect.Rose
