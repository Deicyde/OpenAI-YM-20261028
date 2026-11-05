import YM.WilsonBulk.Transit.JointStep
import YM.WilsonBulk.Grid.PullCost

/-!
# Tensor rank Taylor transfer at fixed head and address types

Full cover positions, NO wrapping. Row estimates with first leg counted
separately. Use finite ℓ1-dual tests on the other legs (one unrestricted
function of ALL the offsets, multilinear along pull). Include nonconstant
width ratio across steps. Here `Blind` generalization via all `Charm`s;
caller supplies on the full initial kernel as in `Keyboard`. No cancellation
across output tags/pruned lists. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical BigOperators ENNReal
open Lattice Laurent Function Finset Filter Pert.Bulk RG
variable {σ θ δ p q M : ℝ} {n k d : ℕ} {α β : Type} {L : Side}

abbrev Keys (n : ℕ) := Fin n×Axis
abbrev Slip (n : ℕ) := Shift (Keys n)
def types (u : Legs (Market α) n) := Prod.snd ∘ u
def deviations (b : Cover) (u : Legs (Market α) n) : Slip n := fun i=> ((u i.1).1-b) i.2
def put (b : Cover) (x : Legs α n) (p : Slip n) : Legs (Market α) n := fun i=> (b+(fun j=> p (i,j)),x i)
def around (b : Cover) : (Legs α n × Slip n) ≃ Legs (Market α) n where
  toFun p:=put b p.1 p.2
  invFun u:=(types u,deviations b u)
  left_inv p:= by
    refine Prod.ext rfl ?_; ext1 ⟨i,j⟩; change b j+p.2 (i,j)-b j=_; ring
  right_inv x:= by ext1 i; refine Prod.ext ?_ rfl; ext1 j; change b j+((x i).1 j-b j)=_; ring
lemma typed (p : Slip n) (b : Market α) (t : Legs α n) : run (lawn α) b (put b.1 t p) = (size p : ℝ) := by
  let f (i : Fin n) : Cover:= fun j=>p (i,j)
  have hh i : (lawn α).cost b (put b.1 t p i)=length (f i) := by
    change sep b.1 (b.1+_)=_; rw [sep_comm,sep, add_sub_cancel_left]
  unfold run; simp_rw [hh,length,Laurent.size,Fintype.sum_prod_type (f:=fun i : Keys n=> _)]; rw [Nat.cast_sum]
lemma put_step (p : Slip n) (b : Cover) (t : Legs α n) (i : Fin n) (j : Axis) : put b t (p+Taylor.notch (i,j)) = Function.update (put b t p) i (((put b t p i).1+step j), t i) := by
  ext1 k; by_cases h : k=i
  · subst i; rw [update_self]; refine Prod.ext ?_ rfl; ext1 w; change b w+(p _+ Taylor.notch (k,j) (k,w))= (b w+p _)+ step j w; rw [add_assoc]; congr 2; simp [Taylor.notch,Pi.single_apply]
  rw [update_of_ne h]; refine Prod.ext ?_ rfl; ext1 w; change b w+(p _+Taylor.notch (i,j) (k,w))= b w +p _; simp [Taylor.notch,h]

section taylor
variable {A : Duct (Market α) (Market β)} {p σ : ℝ}
def walk (A : Duct (Market α) (Market β)) : List Axis → Duct (Market α) (Market β)
| []=>A
| i::l=> walk (foot i A) l
def WalkIn (L : Side) (σ : ℝ) (A : Duct (Market α) (Market β)) (d : ℕ) (p : ℝ) : Prop := 0≤p ∧
  ∀ l:List Axis, l.length ≤ d→∀ x, ∑' y,bill ((walk A l) x y) (spotCost L σ x y) ≤ ENNReal.ofReal (p/(L.val:ℝ)^l.length)
lemma WalkIn.less (h : WalkIn L σ A d p) (hk : k ≤ d) : WalkIn L σ A k p:= ⟨h.1,fun l hl=> h.2 l (hl.trans hk)⟩
lemma WalkIn.hop (h : WalkIn L σ A (d+1) p) (i : Axis) : WalkIn L σ (foot i A) d (p/(L.val:ℝ)) := by
  refine ⟨div_nonneg h.1 (by positivity),fun l hl x=>?_⟩
  have hh := h.2 (i::l) (by simp only [List.length_cons]; omega) x
  rwa [List.length_cons,pow_succ',← div_div] at hh
lemma WalkIn.plain (h : WalkIn L σ A d p) (x : Market α) : ∑' y,bill (A x y) (spotCost L σ x y) ≤ ENNReal.ofReal p := by simpa [walk] using h.2 [] (by simp) x

def globe (L : Side) (σ : ℝ) (x : Market α) (v : Legs (Market β) n) := ∑ i,spotCost L σ x (v i)
def runway (L : Side) (σ : ℝ) (u : Legs (Market α) n) (v : Legs (Market β) n) := ∑ i,spotCost L σ (u i) (v i)
lemma globe_pay {f w : α→ℝ} (hp : 0≤p) : SumBudget (fun x=> Real.exp (w x)*|f x|) p ↔
    ∑'x,bill (f x) (w x) ≤ ENNReal.ofReal p := by
  simp_rw [mul_comm (Real.exp _) _]; constructor
  · exact bill_width_sum
  intro h; have ht := bill_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)
  have he x:0≤ |f x| * Real.exp (w x) := by positivity
  exact ⟨he,ht,ENNReal.ofReal_le_ofReal_iff hp |>.1 ((ENNReal.ofReal_tsum_of_nonneg he ht).le.trans h)⟩
lemma global_cost (u : Legs (Market α) n) (v : Legs (Market β) n) (x: Market α) (hs : 0≤σ) : globe L σ x v ≤ σ/L.val*run (lawn α) x u+runway L σ u v := by
  unfold globe run runway; rw [mul_sum,← sum_add_distrib]; refine sum_le_sum fun i _=>?_
  unfold spotCost; exact (mul_le_mul_of_nonneg_left (delta_fine L x.1 (u i).1 (v i).1) hs).trans_eq (by change _= _*sep ..+_; ring)
variable {T : Legs (Duct (Market α) (Market β)) n} {P : Legs ℝ n} (h : ∀ i, WalkIn L σ (T i) d (P i))
include h
lemma marks (x : Legs (Market α) n) : SumBudget (fun y=> Real.exp (runway L σ x y)*|lot T x y|) (∏ i,P i) := by
  apply (globe_pay (Finset.prod_nonneg (fun i _=> (h i).1))).2
  unfold runway lot; simp_rw [bill_products, all_Δ (a:=fun i (z:Market β)=>bill (T i (x i) z) (spotCost L σ (x i) z)), ENNReal.ofReal_prod_of_nonneg (fun i (_:i∈ (univ:Finset _))=> (h i).1)]
  exact Finset.prod_le_prod' fun i _=>WalkIn.plain (h i) _
omit h

def tester (T : Legs (Duct (Market α) (Market β)) n) (x : Market α) (t : Legs α n)
    (s : Finset (Legs (Market β) n)) (f : Legs (Market β) n→ℝ) (v : Slip n) := ∑ i∈s,lot T (put x.1 t v) i*f i
lemma dimmer {s : Finset (Legs (Market β) n)} {f : Legs (Market β) n→ℝ} {x : Market α} (i : Keys n) (t : Legs α n) :
    Taylor.hop i (tester T x t s f) = tester (Function.update T i.1 (foot i.2 (T i.1))) x t s f := by
  rcases i with ⟨i,j⟩; ext1 v; rw [Taylor.hop, tester,tester,tester,← sum_sub_distrib]; refine sum_congr rfl fun y hy=>?_
  rw [← sub_mul,put_step]; congr 1
  unfold lot; let U:= put x.1 t v
  simp_rw [← mul_prod_erase (s:=univ) _ (mem_univ i), Function.update_self, foot, sub_mul];
  have he := fun a (ha:a∈univ.erase i)=>update_of_ne (mem_erase.mp ha).1 (foot j (T i)) T
  congr 2
  · exact prod_congr rfl fun a ha=> by rw [he a ha,Function.update_of_ne (mem_erase.mp ha).1]
  exact prod_congr rfl fun a ha=> by rw [he a ha]

variable {x : Market α} {s : Finset (Legs (Market β) n)} {f : Legs (Market β) n→ℝ} (hs : 0 ≤ σ) (hf : ∀ y∈s, |f y| ≤ Real.exp (globe L σ x y))
include h hs hf
lemma test_cost (t : Legs α n) (v : Slip n) : |tester T x t s f v| ≤ (∏ i,P i)*Real.exp (σ/L.val*size v) := by
  let g := fun y=> Real.exp (runway L σ (put x.1 t v) y)* |lot T (put x.1 t v) y|
  calc
    _ ≤ ∑ y∈s, |lot T (put x.1 t v) y*f y| := abs_sum_le_sum_abs ..
    _ ≤ ∑ y∈s, g y * Real.exp (σ/L.val*size v) := by
        apply sum_le_sum fun y hy=> ?_; rw [abs_mul]; have he:= global_cost (L:=L) (put x.1 t v) y x hs
        rw [typed] at he; exact (mul_le_mul_of_nonneg_left ((hf y hy).trans (Real.exp_monotone he)) (by positivity)).trans_eq (by rw [Real.exp_add]; unfold g; ring)
    _ ≤ _ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (Push.AbsoluteSums.budget_sum (marks h _) _) (by positivity)

end taylor
end YM.WilsonBulk.Sheet
