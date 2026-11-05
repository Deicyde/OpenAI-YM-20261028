import YM.SectorNext.RECONNECTED_LOCALITY.Optional




set_option warningAsError false

/-!
# Counting ordered child letters with repeats (analog )
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect
namespace Vouchers

open Function Filter Finset

variable {T I : Type*}

def Fee (F : T → ℝ) (r : ℝ) := (∀ i,0 ≤ F i) ∧ HasSum F r

namespace Fee
variable {F : T → ℝ} {r : ℝ}

lemma summable (h : Fee F r) : Summable F := h.2.summable
lemma paid (h : Fee F r) : (∑' i,F i)=r := h.2.tsum_eq
lemma pos (h : Fee F r) (i : T) : 0 ≤ F i := h.1 i
lemma scale (h : Fee F r) {c : ℝ} (hc : 0 ≤ c) : Fee (fun i => c*F i) (c*r) :=
  ⟨fun i => mul_nonneg hc (h.pos i),h.2.mul_left _⟩

lemma sigma {J : I → Type*} {F : Sigma J → ℝ} (g : I → ℝ) {r : ℝ}
    (h : ∀ i,Fee (fun j => F ⟨i,j⟩) (g i)) (he : HasSum g r) : Fee F r := by
  have hf (i : Sigma J) : 0 ≤ F i := (h _).pos i.2
  have hs : Summable F := (summable_sigma_of_nonneg hf).2 ⟨fun i => (h i).summable,by simpa only [fun i => (h i).paid] using he.summable⟩
  exact ⟨hf,hs.hasSum_iff.mpr (hs.tsum_sigma.trans (by simp_rw [fun i => (h i).paid]; exact he.tsum_eq))⟩

lemma product {F : I × T → ℝ} (g : I → ℝ) {r : ℝ}
    (h : ∀ i,Fee (fun j => F (i,j)) (g i)) (he : HasSum g r) : Fee F r := by
  have hf : 0 ≤ F := fun i => (h _).pos i.2
  have hs : Summable F := (summable_prod_of_nonneg hf).2 ⟨fun i => (h _).summable,
    by simpa only [fun i => (h i).paid] using he.summable⟩
  exact ⟨hf,hs.hasSum_iff.mpr (hs.tsum_prod.trans (by simp_rw [fun i => (h i).paid]; exact he.tsum_eq))⟩

lemma notes (s : Finset I) {f : I → T → ℝ} (r : I → ℝ) (h : ∀ i∈s,Fee (f i) (r i)) :
    Fee (fun t => ∑ i∈s,f i t) (∑ i∈s,r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Fee,hasSum_zero]
  | insert i s he IH =>
    have hi := IH (fun j hj => h _ (mem_insert_of_mem hj))
    have hh := h i (by simp)
    simp only [sum_insert he]
    exact ⟨fun j => add_nonneg (hh.pos j) (hi.pos j),hh.2.add hi.2⟩

end Fee

abbrev Line (T : Type*) := Σ n : ℕ,Fin n → T

lemma power {n : ℕ} {f : T → ℝ} (h : Summable f) : HasSum (fun (t : Fin n → T) => ∏ i,f (t i)) ((∑' i,f i)^n) := by
  have he := Optional.series_prod (ι:=Fin n) (E:=fun _ => T) (fun _ i => f i) (fun _ => h)
  simpa only [prod_const,card_univ,Fintype.card_fin] using he

def issue (f : T → ℝ) (x : Line T) := (∏ i,f (x.snd i)) / (x.1.factorial:ℝ)

private lemma e_fee (t : ℝ) : HasSum (fun n : ℕ => t^n/(n.factorial:ℝ)) (Real.exp t) := by
  simpa only [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div] using (Real.summable_pow_div_factorial t).hasSum

lemma issue_fee {f : T → ℝ} (h : Summable f) (he : ∀ i,0 ≤ f i) : Fee (issue f) (Real.exp (∑' i,f i)) := by
  apply Fee.sigma _ _ (e_fee _)
  intro i
  exact ⟨fun _ => div_nonneg (prod_nonneg fun i _ => he _) (by positivity),(power h).div_const _⟩



open scoped Classical in
/-- Mark a child (booked together with the other children at their order / n!). -/
def invoice (f g : T → ℝ) (x : Line T) := (∑ i,∏ j, if j=i then g (x.2 j) else f (x.2 j)) / (x.1.factorial:ℝ)

lemma invoice_fee {f g : T → ℝ} (h : Summable f) (hv : Summable g) (he : ∀ i,0 ≤ f i) (hm : ∀ i,0 ≤ g i) :
    Fee (invoice f g) ((∑' i,g i)*Real.exp (∑' i,f i)) := by
  classical
  let F := ∑' i,f i; let G:=∑' i,g i
  have hi := (e_fee F).mul_left G
  let t : ℕ → ℝ := fun i => if i=0 then 0 else G*(F^(i-1)/((i-1).factorial:ℝ))
  have ht : HasSum t (G*Real.exp F) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [t] using hi
  apply Fee.sigma _ _ ht
  intro n
  cases n with
  | zero =>
    simp [Fee,invoice,t]
  | succ n =>
    let W (i : Fin (n+1)) := fun (p : Fin (n+1) → T) => ∏ j, if j=i then g (p j) else f (p j)
    have hw (i : Fin (n+1)) : Fee (W i) (G*F^n) := by
      refine ⟨fun a => prod_nonneg fun j _ => ?_,?_⟩
      · split_ifs <;> first | exact he _ | exact hm _
      have hg j : (∑' k,if j=i then g k else f k)=if j=i then G else F := by split_ifs with hx <;> simp [F,G]
      have hh := Optional.series_prod (E:=fun _ : Fin (n+1) => T)
        (fun j k => if j=i then g k else f k) (fun j => by
          by_cases hj : j=i
          · simpa only [if_pos hj] using hv
          · simpa only [if_neg hj] using h)
      suffices H : (∏ j, ∑' k, if j=i then g k else f k)=G*F^n by exact H ▸ hh
      simp_rw [hg]
      rw [← prod_erase_mul _ (fun j => if j=i then G else F) (mem_univ i)]
      rw [prod_congr rfl (g:=fun _ => F) (fun j hj => if_neg (ne_of_mem_erase hj)),prod_const]
      simp [mul_comm]
    have hs := Fee.notes univ (fun i : Fin (n+1) => G*F^n) (fun i _ => hw i)
    change Fee (fun p => invoice f g ⟨n+1,p⟩) (t (n+1))
    have hu := hs.scale (c:=((n+1).factorial:ℝ)⁻¹) (by positivity)
    have hx : ((n+1).factorial:ℝ)⁻¹ * (∑ _ : Fin (n+1),G*F^n) = t (n+1) := by
      simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul, t,Nat.add_sub_cancel, Nat.add_eq_zero_iff,
        one_ne_zero,and_false,↓reduceIte,Nat.factorial_succ, Nat.cast_mul]
      field_simp
    rw [← hx]; convert! hu using 1
    funext i; unfold invoice W; simp only [div_eq_mul_inv]; rw [mul_comm]

end Vouchers
end YM.SectorNext.Reconnect
