import YM.WilsonBulk.Transit.Stencil

set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology ENNReal BigOperators Classical
open Lattice Laurent Function Filter Finset RG Pert.Bulk Push.AbsoluteSums
open Work.F08
variable {α β : Type} {n k d : ℕ} {X : Market α} {P : Text α (n+1)}
  {F : Legs ℝ n} {T : Legs (Duct (Market α) (Market β)) n} {s : Finset (Legs (Market β) n)} {p : Legs (Market β) n → ℝ}
  {σ θ M : ℝ} {L : Side}

lemma lot_walk (hL : ∀ i, WalkIn L σ (T i) d (F i)) (hs : 0≤σ) (hp : ∀ v∈s, |p v| ≤ Real.exp (globe L σ X v))
    (t : Legs α n) (l : List (Keys n)) (hl : l.length=d) (v : Slip n) :
    |Taylor.chain (tester T X t s p) l v| ≤ (∏ i,F i)/(L.val:ℝ)^d * Real.exp (σ/L.val*size v) := by
  subst d
  induction l generalizing F T with
  | nil => simpa only [Taylor.chain,pow_zero,div_one,List.length_nil] using test_cost hL hs hp t v
  | cons i l ih=>
    rw [Taylor.chain,dimmer]; simp only [List.length_cons] at hL ⊢
    let H := Function.update F i.1 (F i.1/L.val)
    have hy : ∀ j, WalkIn L σ (Function.update T i.1 (foot i.2 (T i.1)) j) l.length (H j) := by
        intro j; unfold H; by_cases h:j=i.1
        · subst j; simpa using (hL i.1).hop i.2
        simpa [h] using (hL j).less (k:=l.length) (by omega)
    apply (ih hy).trans_eq
    congr 1
    have ht : ∏ j, H j=(∏ j, F j)/(L.val:ℝ) := by
      apply Eq.trans (mul_prod_erase _ _ (mem_univ i.1)).symm
      unfold H; rw [Function.update_self,← mul_prod_erase _ F (mem_univ i.1)]
      have he z (hz:z∈univ.erase i.1) : H z=F z:= Function.update_of_ne (mem_erase.mp hz).1 ..
      rw [prod_congr rfl he]; ring
    rw [ht,pow_succ']; exact div_div ..

lemma grand (hs : 0<θ) (v : Slip n) (d : ℕ) : (1+(size v:ℝ))^d ≤ momentWeight θ d * Real.exp (θ*size v) := polynomial_cost hs (by positivity) d

def moss (L : Side) (F : Legs ℝ n) (θ : ℝ) (d : ℕ) := momentWeight (θ/2) d * (∏ i,F i) /(L.val:ℝ)^d
lemma moss_bound (h : ∀ i,0≤ F i) (hp : 0≤θ) : 0≤moss L F θ d := div_nonneg (mul_nonneg (momentWeight_nonneg (by positivity) _) (prod_nonneg (fun i _=> h i))) (by positivity)
lemma test_past (hL : ∀ i, WalkIn L σ (T i) d (F i)) (hs : 0≤σ) (hp : ∀ v∈s, |p v| ≤ Real.exp (globe L σ X v))
    (ht : 0 < θ) (hh : σ/L.val ≤ θ/2) (v : Slip n) (t : Legs α n) :
    |Taylor.rest d (tester T X t s p) v| ≤ moss L F θ d * Real.exp (θ*size v) := by
  let a: ℝ := (∏ i,F i)/(L.val:ℝ)^d
  have he := (Taylor.envelope d (tester T X t s p) (σ/L.val) a (by positivity) (div_nonneg (prod_nonneg (fun i _=> (hL i).1)) (by positivity)) (lot_walk hL hs hp t) v)
  apply he.trans
  apply (mul_le_mul (grand (show 0<θ/2 by positivity) v d) (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg _))) (div_nonneg (prod_nonneg (fun i _=>(hL i).1)) (by positivity))) (by exact mul_nonneg (div_nonneg (prod_nonneg (fun i _=> (hL i).1)) (by positivity)) (Real.exp_pos _).le) (by unfold momentWeight; positivity)).trans_eq
  rw [show θ*size v=θ/2*size v + θ/2*size v by ring, Real.exp_add]; unfold moss; ring

def TicketNull (d : ℕ) (P : Text α (n+1)) : Prop := ∀ (x : Market α) (t : Legs α n) (v : Formula (Keys n)),v.totalDegree < d → HasSum (fun u : Slip n=> P (hitch x (put x.1 t u)) * Taylor.lineRead u v) 0
lemma TicketNull.removes (h : TicketNull d P) (x : Market α) (t : Legs α n) (v : Slip n→ℝ) :
    HasSum (fun u : Slip n=> P (hitch x (put x.1 t u)) * Taylor.lineRead u (Taylor.abridge d v)) 0 := by
  by_cases he : d=0; · subst d; simp [Taylor.abridge,Taylor.lineRead]
  exact h x t _ (Taylor.total_degree _ _ he)
def draft (P : Text α (n+1)) (x : Market α) (t : Legs α n) : Slip n→ ℝ:= fun v=> P (hitch x (put x.1 t v))
lemma draft_stamp (h : Within (lawn α) θ M P) (x : Market α) (t : Legs α n) : Width θ M (draft P x t) := by
  have hv : Injective (put x.1 t) := fun a b he=> congr_arg Prod.snd ((around (α:=α) (n:=n) x.1).injective (show around (n:=n) x.1 (t,a)=around x.1 (t,b) from he))
  have hh := h.2 0 x; rw [rent_head] at hh
  have hx : SumBudget (fun v => Real.exp (θ*run (lawn α) x v)*|P (hitch x v)|) M:= (globe_pay h.1).2 hh
  have H := budget_pull (put x.1 t) hv hx
  simpa only [typed,draft,Width,Real.norm_eq_abs] using H

lemma draft_past (h : Within (lawn α) θ M P) (hL : ∀ i, WalkIn L σ (T i) d (F i)) (hs : 0≤σ) (hp : ∀ v∈s, |p v| ≤ Real.exp (globe L σ X v))
    (ht : 0< θ) (hk : σ/L.val≤θ/2) (t : Legs α n) :
    SumBudget (fun v : Slip n=> ‖draft P X t v * Taylor.rest d (tester T X t s p) v‖) (moss L F θ d*M) := by
  refine Work.F08.budget_minor (budget_scale (moss_bound (L:=L) (d:=d) (fun i=> (hL i).1) ht.le) (draft_stamp h X t)) (fun _=> norm_nonneg _) (fun a=>?_)
  rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (test_past hL hs hp ht hk a t) (norm_nonneg _)).trans_eq (by ring)
end YM.WilsonBulk.Sheet
