import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import YM.Corona.Fill
import YM.RG.History



/-!
# No volume entropy for *compulsory coverage* at a fixed field

Even without positivity of the representation: charge exact flag inventory
at each occurrence on the actual torus. A given flag has a unique owner,
so an induction bounds the (absolute!) sum on a fixed nonempty flag set
by `w`, even across volumes, spending the cover exponent simultaneously
on the number of flagged sites at its proper native rate. Can insert additional
weights per occurrence (e.g. local scalar compensation, exclusion ratio)
if the SAME (possibly remaining) hit predicate is paid. This estimate does
NOT bound the entropy of *choosing* the flag set when integrating/projecting
fields with partial constraints. Nor does it apply to unforced/repeated log
arrays.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open RG Wilson Lattice Lattice.Corona Finset Filter Function
open scoped Matrix.Norms.Frobenius BigOperators Topology Classical
variable {G : Gauge} {n : Side}

/-- Utility when an occurrence really can just be dropped unconditionally,
or budgets not small; weaker extensive estimate. -/
lemma sum_exp_bound {ι : Type*} (v : ι → ℝ) (h : ∀ i, 0 ≤ v i) (hh : Summable v) :
    ∑' s : Finset ι, ∏ i∈s,v i ≤ Real.exp (∑' i,v i) := by
  have ht := summable_finsetProd_of_summable_nonneg h hh
  refine le_of_tendsto ht.hasSum (Eventually.of_forall fun I => ?_)
  let J := I.biUnion id
  calc
    _ ≤ ∑ s∈J.powerset, ∏ i∈s,v i := sum_le_sum_of_subset_of_nonneg
      (fun x hx => mem_powerset.mpr fun i hi => mem_biUnion.mpr ⟨x,hx,hi⟩)
      (fun i _ _ => prod_nonneg fun i _ => h i)
    _ = ∏ i∈J,(1+v i) := (prod_one_add _).symm
    _ ≤ ∏ i∈J,Real.exp (v i) := prod_le_prod (fun i _ => by linarith [h i])
      fun i _ => by linarith [Real.add_one_le_exp (v i)]
    _ = _ := (Real.exp_sum ..).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hh.sum_le_tsum _ fun i _ => h i)



section uniquely
variable {ι J : Type*} 
  (X Z : ι → Finset J)

def accounted (D : Finset J) (s : Finset ι) :=
  (s : Set ι).Pairwise (fun i j => Disjoint (X i) (X j)) ∧ s.biUnion Z = D

lemma minus {D : Finset J} {s : Finset ι} (h : accounted X Z D s)
    (_hZ : ∀ i, Z i ⊆ X i) (i : ι) (hi : i∈s) : Z i ⊆ D := by
  rw [← h.2]; exact fun a ha => mem_biUnion.mpr ⟨i,hi,ha⟩

lemma reaccounts {D : Finset J} {s : Finset ι} (h : accounted X Z D s)
    (hZ : ∀ i, Z i ⊆ X i) (i : ι) (hi : i∈s) : accounted X Z (D \ Z i) (s.erase i) := by
  constructor
  · intro a ha b hb ht
    exact h.1 (mem_of_mem_erase (SetLike.mem_coe.mp ha)) (mem_of_mem_erase (SetLike.mem_coe.mp hb)) ht
  ext k
  simp only [mem_biUnion]
  constructor
  · rintro ⟨j,hj,hh⟩
    have he := (mem_erase.mp hj).1
    have hy := mem_of_mem_erase hj
    refine Finset.mem_sdiff.mpr ⟨minus X Z h hZ j hy hh, fun H => ?_⟩
    exact Finset.disjoint_left.mp (h.1 hy hi he) (hZ j hh) (hZ i H)
  intro hx; obtain ⟨hk,hl⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨j,hj,hh⟩ := mem_biUnion.mp (h.2.symm ▸ hk)
  refine ⟨j,mem_erase.mpr ⟨fun he => ?_,hj⟩,hh⟩
  exact hl (he ▸ hh)

-- cost is exp(rate times counted flags). Hits could pay more via native
-- connected coverNumber; this recursion just needs the consequence for
-- the actual inventory card (also flexible for inflated K bounds).
theorem cover_power {γ w : ℝ} (hZ : ∀ i, Z i ⊆ X i) (hn : ∀ i, (Z i).Nonempty)
    (hw : w ≤ 1) (v : ι → ℝ) (hv : ∀ i, 0≤v i)
    (hit : ∀ x : J, ∀ I : Finset ι, (∑ i∈I, if x∈Z i then v i*Real.exp (γ * (Z i).card) else 0) ≤ w)
    (D : Finset J) (I : Finset ι) :
    (∑ s∈ I.powerset.filter (accounted X Z D), ∏ i∈s,v i) ≤
        (if D=∅ then 1 else w)*Real.exp (-γ * D.card) := by
  induction D using Finset.strongInduction with | H D H
  by_cases he : D.Nonempty
  · rw [if_neg he.ne_empty]
    let x := he.choose
    have hx : x∈D := he.choose_spec
    let F := I.powerset.filter (accounted X Z D)
    let Y := fun (s : Finset ι) => ∏ j∈s,v j
    let owners := I.filter fun i => x∈Z i
    let R := fun i => F.filter fun s => i∈s
    have Q (s : Finset ι) (hs : s∈F) : s⊆I ∧ accounted X Z D s := by simpa [F] using hs
    have hc : F ⊆ owners.biUnion R := by
      intro s hs
      obtain ⟨i,hi,h⟩ := mem_biUnion.mp ((Q s hs).2.2.symm ▸ hx)
      exact mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨(Q s hs).1 hi,h⟩,mem_filter.mpr ⟨hs,hi⟩⟩
    have hf (i : ι) : ((R i).image (fun s => s.erase i)) ⊆ I.powerset.filter (accounted X Z (D \ Z i)) := by
      intro s hs; obtain ⟨t,ht,rfl⟩ := mem_image.mp hs
      obtain ⟨hh,hr⟩ := mem_filter.mp ht
      have h := Q t hh
      exact mem_filter.mpr ⟨mem_powerset.mpr fun j hj => h.1 (mem_of_mem_erase hj), reaccounts X Z h.2 hZ i hr⟩
    have hb (i : ι) (ht : i∈owners) :
        ∑ s∈R i,Y s ≤ v i*Real.exp (γ * (Z i).card) * Real.exp (-γ * D.card) := by
      by_cases ha : (R i).Nonempty
      · obtain ⟨s,hs⟩ := ha
        obtain ⟨hp,hj⟩ := mem_filter.mp hs
        have hh := minus X Z (Q s hp).2 hZ i hj
        have hz := H (D \ Z i) (by
          rw [ssubset_iff_subset_ne]
          refine ⟨sdiff_subset, fun hg => ?_⟩
          have ht := (mem_filter.mp ht).2
          exact (mem_sdiff.mp (hg.symm ▸ hx)).2 ht)
        have ht' : Real.exp (-γ * ↑(D \ Z i).card) = Real.exp (γ * (Z i).card)*Real.exp (-γ * D.card) := by
          have hy := card_sdiff_add_card_eq_card hh
          have hz : ((D \ Z i).card:ℝ)+(Z i).card=D.card := by exact_mod_cast hy
          rw [← Real.exp_add]; congr 1; rw [← hz]; ring
        calc
          _ = v i * ∑ s∈ (R i).image (fun s => s.erase i), Y s := by
            rw [sum_image, mul_sum]
            · refine sum_congr rfl fun t h => ?_
              have hr := (mem_filter.mp h).2; unfold Y
              nth_rw 1 [← insert_erase hr]; rw [prod_insert (notMem_erase _ _)]
            intro a ha b hb hab
            have ka : a∈R i := ha; have kb : b∈R i := hb
            change a.erase i=b.erase i at hab
            rw [← insert_erase (mem_filter.mp ka).2, ← insert_erase (mem_filter.mp kb).2,hab]
          _ ≤ v i * (∑ s∈I.powerset.filter (accounted X Z (D\Z i)),Y s) := by
            apply mul_le_mul_of_nonneg_left _ (hv i)
            exact sum_le_sum_of_subset_of_nonneg (hf _) fun j _ _ => prod_nonneg fun k _ => hv k
          _ ≤ v i * ( (if D\Z i=∅ then 1 else w)*Real.exp (-γ * ↑(D \ Z i).card)) := mul_le_mul_of_nonneg_left hz (hv i)
          _ ≤ v i * Real.exp (-γ * ↑(D \ Z i).card) := by
            apply mul_le_mul_of_nonneg_left _ (hv i); split
            · rw [one_mul]
            exact mul_le_of_le_one_left (Real.exp_pos _).le hw
          _ = _ := by rw [ht']; ring
      rw [not_nonempty_iff_eq_empty.mp ha,sum_empty]
      exact mul_nonneg (mul_nonneg (hv _) (Real.exp_pos _).le) (Real.exp_pos _).le
    change ∑ s∈F,Y s ≤ w*Real.exp _
    -- even have disjoint owners
    calc
      ∑ s∈F,Y s ≤ ∑ s∈owners.biUnion R,Y s := sum_le_sum_of_subset_of_nonneg hc fun s _ _ => prod_nonneg fun k _ => hv k
      _ ≤ ∑ i∈owners, ∑ s∈R i, Y s := by
        apply le_of_eq (Finset.sum_biUnion _)
        intro i hi j hj h
        apply Finset.disjoint_left.mpr
        intro s hs hT
        obtain ⟨hl,hI⟩ := mem_filter.mp (show s∈R i from hs)
        have hJ := (mem_filter.mp (show s∈R j from hT)).2
        exact Finset.disjoint_left.mp ((Q s hl).2.1 hI hJ h)
          (hZ i (mem_filter.mp (show i∈owners from hi)).2)
          (hZ j (mem_filter.mp (show j∈owners from hj)).2)
      _ ≤ ∑ i∈owners, v i * Real.exp (γ * (Z i).card) * Real.exp (-γ * D.card) := sum_le_sum fun i hi => hb i hi
      _ ≤ _ := by
        rw [← Finset.sum_mul,Finset.sum_filter]
        exact mul_le_mul_of_nonneg_right (hit x I) (Real.exp_pos _).le
  rw [not_nonempty_iff_eq_empty.mp he,if_pos rfl]
  have h : I.powerset.filter (accounted X Z ∅) = {∅} := by
    ext s
    simp only [mem_filter,mem_powerset,mem_singleton]
    constructor
    · rintro ⟨h,h'⟩
      by_contra e
      obtain ⟨i,hi⟩ := nonempty_iff_ne_empty.mpr e; obtain ⟨x,hx⟩ := hn i
      have he : x ∈ s.biUnion Z := mem_biUnion.mpr ⟨i,hi,hx⟩; rw [h'.2] at he
      exact notMem_empty x he
    rintro rfl; simp [accounted]
  simp [h]

end uniquely

def flagRate (p : BudgetPoint) := p.supportExponent / (((p.B+p.B+1:ℕ):ℝ)^4)
lemma flagRate_pos (p : BudgetPoint) : 0 < flagRate p := by unfold flagRate; have := p.exponent_pos; push_cast; positivity

lemma inventory_pay (p : BudgetPoint) {X Z : Support n} (h : Z ⊆ X) :
    flagRate p * Z.card ≤ p.supportExponent * coverNumber p.B X := by
  have he : (Z.card:ℝ) ≤ (coverNumber p.B X:ℝ) * (((p.B+p.B+1:ℕ):ℝ)^4) :=
    by exact_mod_cast (card_le_card h).trans (pays X p.B)
  apply le_trans (mul_le_mul_of_nonneg_left he (flagRate_pos p).le)
  apply le_of_eq; unfold flagRate; field_simp

/-- Strong full-coverage bound, not relying on the eligibility predicates
(they may zero more terms). Doesn't even require integrability/measurability
of K here, just the SAME KBound. -/
theorem gas_cover (A : Activities G n) {w : ℝ} {p : BudgetPoint} (hw : w ≤ 1)
    (h : A.KBound p w) (U : Config G n) :
    ∑' i : Finset ℕ, ‖A.gasOccurrence p i U‖ ≤ (if flags p.threshold U = ∅ then 1 else w) *
      Real.exp (- flagRate p * (flags p.threshold U).card) := by
  let D := flags p.threshold U
  let X := fun i => (A.forced i).support
  let Z := fun i => (A.forced i).inventory
  obtain ⟨v,hv,H⟩ := h
  have he := Activities.summable_charge
    (fun i => (A.forced i).inventory_ne.mono (A.forced i).inventory_sup) (fun i => (hv i).1) H
  have hg := summable_finsetProd_of_summable_nonneg (fun i => (hv i).1) he
  let Y := fun (s : Finset ℕ) => ∏ j∈s,v j
  have hm (i : Finset ℕ) : ‖A.gasOccurrence p i U‖ ≤ Y i := by
    unfold Activities.gasOccurrence; split
    · unfold Y; rw [norm_prod]; exact prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => (hv i).2 _
    rw [norm_zero]; exact prod_nonneg fun i _ => (hv i).1
  have hy := hg.of_nonneg_of_le (fun i => norm_nonneg _) hm
  refine hy.tsum_le_of_sum_le ?_
  intro s
  let I := s.biUnion id
  let F := accounted X Z D
  have H' i : Z i ⊆ X i := (A.forced i).inventory_sup
  calc
    _ = ∑ j∈s.filter F, ‖A.gasOccurrence p j U‖ := by
      symm; apply sum_subset (filter_subset ..)
      intro j hj ht
      have hh : ¬ F j := fun hk => ht (mem_filter.mpr ⟨hj,hk⟩)
      have he : ¬ A.admissible p U j := by
        -- simplify subsingleton mismatches via congr!
        rw [show A.admissible p U j = F j by
          unfold Activities.admissible F X Z D accounted; congr!]
        exact hh
      simp [Activities.gasOccurrence,he]
    _ ≤ ∑ i∈I.powerset.filter F, Y i := (sum_le_sum fun i _ => hm i).trans
      (sum_le_sum_of_subset_of_nonneg (fun j hj => by
        obtain ⟨a,b⟩ := mem_filter.mp hj
        exact mem_filter.mpr ⟨mem_powerset.mpr fun i hi => mem_biUnion.mpr ⟨j,a,hi⟩,b⟩)
        (fun i _ _ => prod_nonneg fun k _ => (hv k).1))
    _ ≤ _ := by
      have Hh := cover_power (γ:=flagRate p) X Z H' (fun i => (A.forced i).inventory_ne) hw v (fun i => (hv i).1) ?hit D I
      · apply Hh.trans; apply le_of_eq; congr!
      case hit =>
        intro x l
        apply le_trans _ (((H x).2.1.sum_le_tsum l fun i _ => (H x).1 i).trans (H x).2.2)
        apply sum_le_sum
        intro i _
        split_ifs with he
        · unfold BudgetPoint.mass; rw [mul_comm (Real.exp _)]
          apply mul_le_mul_of_nonneg_left _ (hv i).1; exact Real.exp_le_exp.mpr (inventory_pay p (H' i))
        · exfalso; apply ‹¬ _›; exact H' i he
        · unfold BudgetPoint.mass; exact mul_nonneg (Real.exp_pos _).le (hv _).1
        exact le_rfl

theorem gas_cover_value (A : Activities G n) {w δ : ℝ} {p : BudgetPoint} (hw : w ≤ 1)
    (h : A.Valid p δ w) (U : Config G n) :
    |A.gas p U| ≤ (if flags p.threshold U = ∅ then 1 else w) *
      Real.exp (- flagRate p * (flags p.threshold U).card) := by
  exact (norm_tsum_le_tsum_norm ((Activities.gasSeries h).absolute U)).trans (gas_cover A hw h.boundK U)

lemma gas_le_one (A : Activities G n) {w δ : ℝ} {p : BudgetPoint} (hw : w ≤ 1) (h : A.Valid p δ w)
    (U : Config G n) : |A.gas p U| ≤ 1 := by
  refine (gas_cover_value A hw h U).trans ?_
  apply mul_le_one₀
  · split; exact le_rfl; exact hw
  · exact (Real.exp_pos _).le
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (flagRate_pos p).le) (Nat.cast_nonneg _)

end YM.SectorNext.Vacuum
