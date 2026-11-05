import YM.Next.MULTISOURCE.Bulk
import YM.Next.MULTISOURCE.Shards
import YM.Next.MULTISOURCE.Spacing
import YM.Next.MULTISOURCE.Tour


/-! Packing estimate to buy an entire indexed set of local responses. -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Marker Lattice Function Finset Filter
open scoped Topology BigOperators
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable {B : ℕ} {n : Side} {f : V → Site n}

namespace Convoy

def paths (p : V) : ℕ → Finset (List V)
  | 0 => {[]}
  | k+1 => insert [] ((univ.erase p).biUnion fun i => (paths i k).image (List.cons i))

lemma carries {p : V} {l : List V} (h : (p::l).Nodup) {k : ℕ} (hk : l.length ≤ k) : l ∈ paths p k := by
  induction k generalizing l p with
  | zero => obtain rfl := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hk); simp [paths]
  | succ k ih =>
    cases l with
    | nil => rw [paths]; exact mem_insert_self ..
    | cons i l =>
      rw [paths]; refine mem_insert_of_mem (mem_biUnion.mpr ⟨i,?_,mem_image_of_mem _ (ih (List.nodup_cons.mp h).2 (by simpa using hk))⟩)
      exact mem_erase.mpr ⟨fun he => (List.nodup_cons.mp h).1 (List.mem_cons.mpr (Or.inl he.symm)),mem_univ _⟩

def rebate (f : V → Site n) (B : ℕ) (p : V) (l : List V) : ℝ := Real.exp (- (miles f p l:ℝ)/(256*B))

lemma clients (hp : ∀ i, (∑ j∈ univ.erase i, linkFare f B i j) ≤ 1/16) (p : V) (k : ℕ) :
    (∑ l ∈ (paths p k), rebate f B p l) ≤ 2 ∧
      (∑ l ∈ (paths p k).erase [], rebate f B p l) ≤ 1/8 := by
  induction k generalizing p with
  | zero => norm_num [paths,rebate,miles]
  | succ k ih =>
    let T (i : V) := (paths i k).image (List.cons i)
    have he : [] ∉ (univ.erase p).biUnion T := by simp [T]
    have hx : (paths p (k+1)).erase []=(univ.erase p).biUnion T := by rw [paths, erase_insert he]
    have hh (i : V) : (∑ l∈ T i, rebate f B p l) ≤ linkFare f B p i*2 := by
      unfold T; rw [sum_image (g:=List.cons i) (fun _ _ _ _ e => (List.cons.inj e).2)]
      simp_rw [rebate,miles,Nat.cast_add, neg_add,add_div,Real.exp_add, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (ih i).1 (Real.exp_pos _).le
    have ht : (∑ l∈(univ.erase p).biUnion T, rebate f B p l) ≤ 1/8 := by
      rw [Finset.sum_biUnion ?_]
      · refine (Finset.sum_le_sum fun i _ => hh i).trans ?_
        rw [← Finset.sum_mul]
        exact (mul_le_mul_of_nonneg_right (hp p) (by norm_num : (0:ℝ) ≤2)).trans_eq (by norm_num)
      intro i hi j hj H; refine disjoint_left.mpr fun x xx xy => H ?_
      obtain ⟨l,hl,rfl⟩ := mem_image.mp xx
      obtain ⟨m,hm,e⟩ := mem_image.mp xy
      exact (List.cons.inj e.symm).1
    rw [hx]; refine ⟨?_,ht⟩
    rw [paths, Finset.sum_insert he, show rebate f B p []=1 by simp [rebate,miles]]
    change 1+(∑ l∈(univ.erase p).biUnion T, rebate f B p l) ≤ 2
    linarith

end Convoy

def partners (R : Census V) (x : V) := (rootAt R x).filter (fun i => 2 ≤ i.sites.card)

def Spot (P : BudgetPoint) : Prop := 8 ≤ P.B ∧ ∀ (V : Type) [Fintype V] [DecidableEq V] (n : Side)
    (f : V → Site n), Spaced f P.B → ∀ p, (∑ i ∈ univ.erase p, Convoy.linkFare f P.B p i) ≤ 1/16

lemma root_campaign (R : Census V) (p : V) (P : BudgetPoint) (h : Spaced f P.B) (H : Spot P) :
    (∑ T∈ partners R p, fare P 1 (T.sites.image f)) ≤ 1/8 := by
  let S := partners R p
  have hl (i) (hi : i ∈ S) := Convoy.routed f i.sites H.1 p (mem_rootAt.mp (mem_filter.mp hi).1)
    (mem_filter.mp hi).2 fun i _ j _ => h i j
  choose! l he hh hw hv using hl
  let F := Convoy.rebate f P.B p
  have hJ : Set.InjOn l S := fun i hi j hj hx => Hot.eq_of_sites (
    (hw i hi).symm.trans ((congrArg (fun x : List V => (p::x).toFinset) hx).trans (hw j hj)))
  let D := Convoy.paths p (Fintype.card V)
  have hb : 0 < P.B := P.B_pos
  calc
    _ ≤ ∑ i∈ S,F (l i) := by
      refine Finset.sum_le_sum fun i hi => Real.exp_monotone ?_
      have H : (Convoy.miles f p (l i):ℝ) ≤ (256*P.B:ℝ)*coverNumber P.B (i.sites.image f) := by exact_mod_cast hv i hi
      apply (le_div_iff₀ (by positivity)).2; linarith
    _ = ∑ i∈S.image l,F i := (sum_image hJ).symm
    _ ≤ ∑ i∈D.erase [],F i := Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => by
        obtain ⟨t,ht,rfl⟩ := mem_image.mp hk
        refine mem_erase.mpr ⟨he _ ht,Convoy.carries (hh _ ht) ?_⟩
        apply le_trans (show (l t).length ≤ (p::l t).length from Nat.le_succ _)
        rw [← List.toFinset_card_of_nodup (hh _ ht)]; exact card_le_univ _)
        (fun i _ _ => (Real.exp_pos _).le)
    _ ≤ 1/8 := (Convoy.clients (H.2 V n f h) ..).2

lemma radius_change (i : Hot R) (hi : 2 ≤ i.sites.card) (P : BudgetPoint) (hB : 8 ≤ P.B)
    (hh : Spaced f P.B) (r : ℝ) (hr : 0 ≤ r) (hx : r ≤ Real.exp (P.B/64 : ℝ)) :
    let X := i.sites.image f
    r^i.sites.card * fare P 2 X ≤ fare P 1 X := by
  intro X
  have hs := Work.I01.answer n V f P.B hB i.sites (fun i _ j _ => hh i j) hi (i.sites.image f) le_rfl
  have he : (P.B:ℝ)*i.sites.card ≤ 64*coverNumber P.B X := by exact_mod_cast hs
  apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr hx _) (Real.exp_pos _).le)
  unfold fare; rw [← Real.exp_nat_mul, ← Real.exp_add]; apply Real.exp_monotone; linarith
end YM.Multi
