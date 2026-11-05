import YM.Ac.Tree
import YM.Next.MULTISOURCE.Cargo

/-!
# Merger bound for cutoff multi-products (volume/copy count independent).
One `κ` paid on the resulting forced source.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Wilson Lattice Finset Function Marker
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {n : Side} {V : Type} [DecidableEq V] [Fintype V] {G : Gauge}

-- support exponent at this point plus two, only required on vacuum at startup
-- no assertion inferred from `Valid`
def Mint (P : Rep G n) (r κ : ℝ) := ∃ f : Pack n → ℝ,
    (∀ i, 0 ≤ f i ∧ ∀ U, ‖incumbent P U i‖ ≤ f i) ∧
    ∀ x : Site n, (∑ i∈ univ.filter (fun i : Pack n => x∈i.zone), burn P.p r i.zone * f i) ≤ κ

namespace Couples

def liftFee (m : ℕ) := 2*((m:ℝ)+1)*Real.exp m

lemma lift_pos (m : ℕ) : 0 < liftFee m := by unfold liftFee; positivity

private lemma replete {ι : Type*} [DecidableEq (Finset ι)] (s : Finset ι) (f : ι→ℝ) (h : ∀ i,0≤ f i) (k m : ℕ)
    (hk : 1 ≤ k) {κ : ℝ} (hh : 0 ≤ κ) (hv : κ ≤ 1) (he : (∑ i∈s,f i) ≤ k*m*κ) :
    (∑ a∈ s.powerset.erase ∅,∏ i∈a,f i) ≤ κ*(liftFee m)^k := by
  let z := (k:ℝ)*m*κ
  have hx : (∏ i∈s,(1+f i)) ≤ Real.exp z := by
    calc
      _ ≤ ∏ i∈s,Real.exp (f i) := prod_le_prod (fun i _ => add_nonneg zero_le_one (h _)) (fun i _ => by
        rw [add_comm]; exact Real.add_one_le_exp _)
      _ ≤ _ := by rw [← Real.exp_sum]; exact Real.exp_monotone he
  have hy : Real.exp z - 1 ≤ z*Real.exp z := by
    have hx := Real.add_one_le_exp (-z)
    rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)] at hx
    linarith
  calc
    _ ≤ Real.exp z-1 := by
      apply le_sub_iff_add_le.mpr
      rw [show (1:ℝ) = ∏ i∈∅,f i from rfl, sum_erase_add _ _ (by simp), ← prod_one_add]; exact hx
    _ ≤ κ*(((k:ℝ)*m)* (Real.exp m)^k) := by
      rw [← Real.exp_nat_mul]
      apply hy.trans
      have hp := Real.exp_monotone (mul_le_of_le_one_right (show (0:ℝ) ≤ (k:ℝ)*m by positivity) hv)
      exact (mul_le_mul_of_nonneg_left hp (show 0≤z from mul_nonneg (by positivity) hh)).trans_eq (by unfold z; ring)
    _ ≤ _ := by
      unfold liftFee; simp only [mul_pow]
      gcongr
      · exact_mod_cast Nat.lt_two_pow_self (n:=k) |>.le
      exact (le_add_of_nonneg_right zero_le_one).trans (le_self_pow₀ (by simp) (by omega))

omit [DecidableEq V] in
private lemma tariff (Y : V → Support n) (F : BudgetPoint) (K : Pack n → ℝ) (p : V→ℝ) {r : ℝ} (hr : 0≤r)
    {j : Recipe n V} (h : j∈ boxes Y) (hk : ∀ i,0≤K i) (hp : ∀ i,0≤p i) :
    burn F r (fused Y j).zone * (∏ i∈j, Sum.elim K p i) ≤
      (∏ i∈j.toLeft, burn F r i.zone*K i)*∏ i∈j.toRight,burn F r (Y i)*p i := by
  have he : burn F r (ground Y j) ≤ ∏ i∈j, burn F r (span Y i) := by
    unfold burn
    rw [← Real.exp_sum]
    apply Real.exp_monotone; rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (add_nonneg F.exponent_pos.le hr)
    exact_mod_cast Ac.cover (span Y) F.B (((owns ..).mp h).2.2)
  rw [merged_zone Y h]
  apply le_trans (mul_le_mul_of_nonneg_right he (Finset.prod_nonneg (fun i _ => by cases i; apply hk; apply hp)))
  rw [← Finset.prod_mul_distrib, split_product j _]; exact le_rfl

private lemma covers_fee {I J : Type*} [DecidableEq J] (D : Finset I) (T : I → Finset J)
    (f : J → ℝ) (hf : ∀ i,0≤f i) : (∑ i∈D.biUnion T,f i) ≤ ∑ i∈ D,∑ j∈T i,f j := by
  let g i j := if j∈T i then f j else 0
  calc
    _ ≤ ∑ j∈ D.biUnion T, ∑ i∈ D,g i j := by
      apply sum_le_sum; intro i hi
      obtain ⟨j,hj,h⟩ := mem_biUnion.mp hi
      refine le_trans (le_of_eq (show f i=g j i from (if_pos h).symm)) (single_le_sum (f:=fun j => g j i) ?_ hj)
      intro j hj; unfold g; split; exact hf _; exact le_rfl
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun i hi => ?_
      unfold g; rw [← sum_filter, show ((D.biUnion T).filter fun j => j∈T i)=T i from ?_]
      ext j; rw [mem_filter]; exact ⟨And.right,fun h => ⟨mem_biUnion.mpr ⟨_,hi,h⟩,h⟩⟩

private lemma allows (Y : V → Support n) (T : Finset V) {m : ℕ} {κ : ℝ}
    (h : ∀ i,(Y i).card ≤ m) (hT : T.Nonempty) (hv : 0 ≤ κ) (hk : κ ≤ 1) (f : Pack n → ℝ)
    (he : ∀ i,0 ≤ f i) (ht : ∀ x : Site n,(∑ i∈univ.filter (fun i : Pack n => x∈ i.zone),f i) ≤ κ) :
    (∑ j∈ boxes Y with j.toRight=T, ∏ i∈j.toLeft,f i) ≤ κ*(liftFee m)^T.card := by
  let B := (boxes Y).filter fun j => j.toRight=T
  let X := T.biUnion Y
  let A := X.biUnion fun x => univ.filter (fun i : Pack n => x∈i.zone)
  have hu : (∑ i∈A,f i) ≤ T.card*m*κ := by
    calc
      _ ≤ ∑ x∈X,∑ i∈univ.filter (fun i : Pack n => x∈i.zone),f i := by
        exact covers_fee X _ f he
      _ ≤ ∑ x∈X, κ := sum_le_sum fun _ _ => ht _
      _ ≤ _ := by
        rw [sum_const,nsmul_eq_mul]; gcongr
        have hh : X.card ≤ T.card*m := card_biUnion_le.trans (by simpa using sum_le_sum (s:=T) (fun j _ => h j))
        exact_mod_cast hh
  have hh : B.image Finset.toLeft ⊆ A.powerset.erase ∅ := by
    intro i hi; obtain ⟨j,hJ,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hb,hj⟩ := mem_filter.mp hJ; refine mem_erase.mpr ⟨((owns ..).mp hb).1.ne_empty, mem_powerset.mpr ?_⟩
    intro i hi; obtain ⟨v,hv,H⟩ := all_hit Y hb (by rwa [hj]) i hi
    obtain ⟨x,hx,ht⟩ := Finset.not_disjoint_iff.mp H
    exact mem_biUnion.mpr ⟨x,Finset.mem_biUnion.mpr ⟨v,hj ▸ hv,hx⟩,mem_filter.mpr ⟨mem_univ _,ht⟩⟩
  apply le_trans _ (replete A f he T.card m (card_pos.mpr hT) hv hk hu)
  refine le_trans (le_of_eq (sum_image (f:=fun s : Finset (Pack n) => ∏ i∈s,f i) ?_).symm)
    (sum_le_sum_of_subset_of_nonneg hh fun i _ _ => prod_nonneg fun j _ => he j)
  intro i hi j hj H; exact (parts_word i).symm.trans (Eq.trans (by rw [H, (mem_filter.mp hi).2,
    (mem_filter.mp hj).2]) (parts_word j))

lemma merge_bound (P : Rep G n) (Y : V → Support n) (T : Finset V) (hT : T.Nonempty)
    {r κ : ℝ} (hr : 0≤r) (hp : 0 ≤ κ) (hk : κ ≤ 1) (hm : Mint P r κ) (m : ℕ) (hX : ∀ i,(Y i).card ≤ m)
    (F : V → Config G n → ℂ) (p : V → ℝ) (h : ∀ i,0≤p i) (H : ∀ i U, ‖F i U‖ ≤ p i) :
    ∃ a : Pack n → ℝ, (∑ i,burn P.p r i.zone * a i) ≤ κ*∏ i∈T,(liftFee m * (burn P.p r (Y i)*p i)) ∧
      ∀ i,0≤a i ∧ ∀ U,‖payload Y P F T i U‖ ≤ a i := by
  obtain ⟨K,hK,hG⟩ := hm
  let D := (boxes Y).filter fun i => i.toRight=T
  let L := Sum.elim K p
  let w (j : Recipe n V) := ∏ i∈j,L i
  have hv i : 0 ≤ w i := prod_nonneg fun j _ => (by cases j; apply (hK _).1; exact h _)
  let a (i : Pack n) := ∑ j∈ D with fused Y j=i, w j
  refine ⟨a,?_,fun i => ⟨sum_nonneg fun j _ => hv j,fun U => ?_⟩⟩
  · let q i := burn P.p r (Pack.zone i)* K i
    let v i := burn P.p r (Y i)*p i
    have he : 0 ≤ ∏ i∈T,v i := prod_nonneg fun i _ => mul_nonneg (burn_pos ..).le (h i)
    calc
      _ = ∑ j∈D,burn P.p r (fused Y j).zone*w j := by
        rw [← sum_fiberwise D (fused Y)]; apply sum_congr rfl; intro i _
        unfold a; rw [Finset.mul_sum]
        exact sum_congr rfl fun j hj => by rw [(mem_filter.mp hj).2]
      _ ≤ ∑ j∈D,(∏ i∈j.toLeft,q i)*(∏ i∈T,v i) := by
        apply sum_le_sum; intro i hi
        rw [← (mem_filter.mp hi).2]; exact tariff Y _ K p hr (mem_filter.mp hi).1 (fun i => (hK i).1) h
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        refine (mul_le_mul_of_nonneg_right (allows Y T hX hT hp hk q (fun i => mul_nonneg (burn_pos ..).le (hK i).1) hG) he).trans_eq ?_
        conv_rhs => rw [prod_mul_distrib,prod_const]
        exact mul_assoc ..
  · unfold payload; apply le_trans (norm_sum_le ..)
    unfold a
    rw [show ((trays Y i).filter fun x => x.toRight=T)=D.filter (fun x => fused Y x=i) by
      ext x; simp only [trays,mem_filter,D,and_right_comm]]
    apply Finset.sum_le_sum
    intro j hi; unfold earning; split
    · rw [norm_prod]; apply Finset.prod_le_prod (fun _ _ => norm_nonneg _); intro x _
      cases x; exact (hK _).2 U; exact H _ U
    rw [norm_zero]; exact hv j
end Couples
end YM.Multi
