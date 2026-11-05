import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Currency
import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Voyage
import YM.Next.FREE_KERNELS.Lifts


/-!
# Compose rooted sup purchases

Post-L calculus within the ACTUAL real balls. Use mixed tolerances retaining path
weights. Doesn't require growth norms used for paying to be ambient analytic chart norms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Estimate Analysis Estimate.Purse
open scoped Topology BigOperators ContDiff
namespace Polish
variable {X Y E F ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Y→E} {g : X→Y} {h : X→F} {x : X} {y : Y} {A C D : ℝ}

/-- No powers in lengths hidden in tolerance. -/
abbrev Ticket (X : Type*) := X → ℝ → Prop
abbrev Menu {n : ℕ} (P : Ticket X) (d : Fin n → X) (c : Fin n →ℝ) := ∀ i,0 ≤ c i ∧ P (d i) (c i)
variable {P : Ticket X} {Q : Ticket Y} {n m u : ℕ}

def Costs (P : Ticket X) (Q : Ticket Y) (g : X→Y) (x : X) (k : ℕ) (C : ℝ) : Prop :=
    ∀ d c, Menu (n:=k) P d c → Q (iteratedFDeriv ℝ k g x d) (C*∏ i, c i)

abbrev budget (X : Type*) [Norm X] : Ticket X := fun x C => ‖x‖ ≤ C
variable {t : Ticket Y}
lemma cheaper (h : Costs P Q g x n C) (hq : ∀ y : Y, ∀ a b,a ≤ b → Q y a → Q y b) (he : C≤D) : Costs P Q g x n D :=
  fun z c hc => hq _ _ _ (mul_le_mul_of_nonneg_right he (Finset.prod_nonneg fun i _ => (hc i).1)) (h z c hc)
lemma Costs.less (h : Costs P (budget Y) g x n C) (he : C ≤ D) : Costs P (budget Y) g x n D :=
    cheaper h (fun _ _ _ he h => h.trans he) he
lemma Costs.change (h : Costs P Q g x n C) {B : Ticket X} (hp : ∀ v c, 0≤c → B v c → P v c) : Costs B Q g x n C :=
    fun j c hh => h j c fun i => ⟨(hh i).1,hp (j i) (c i) (hh i).1 (hh i).2⟩



def indexed (n : ℕ) (c : ℕ → ℝ) : ℝ := ∑ i : Fin (n+1),max 1 (c i)
lemma covers (n i : ℕ) (h : i ≤ n) (c : ℕ → ℝ) : max 1 (c i) ≤ indexed n c :=
    Finset.single_le_sum (f:=fun i : Fin (n+1) => max 1 (c i)) (fun _ _ => zero_le_one.trans (le_max_left ..)) (Finset.mem_univ ⟨i,by omega⟩)
lemma covers_pos (n : ℕ) (c : ℕ → ℝ) : 1 ≤ indexed n c := (le_max_left ..).trans (covers n n le_rfl c)

def counted (n : ℕ) := Fintype.card (OrderedFinpartition n)
def stamped (n : ℕ) (C D : ℝ) := indexed n (fun k => counted k * (C*D^n))
lemma stamp_pos (n : ℕ) (C D) : 1 ≤ stamped n C D := covers_pos ..









lemma paired (hf : ContDiffAt ℝ ω g x) (hg : ContDiffAt ℝ ω h x) (hz : Costs P (budget Y) g x n C) (he : Costs P (budget F) h x n C) :
    Costs P (budget (Y × F)) (fun x=>(g x,h x)) x n C := by
  let f x := (g x,h x)
  have hh : ContDiffAt ℝ ω f x := hf.prodMk hg
  intro d c hc
  have hv := DFunLike.congr_fun ((ContinuousLinearMap.fst ℝ Y F).iteratedFDeriv_comp_left hh le_top) d
  have hk := DFunLike.congr_fun ((ContinuousLinearMap.snd ℝ Y F).iteratedFDeriv_comp_left hh le_top) d
  exact max_le ((show ‖(iteratedFDeriv ℝ n f x d).1‖=‖iteratedFDeriv ℝ n g x d‖ from congr_arg (‖·‖) (id (show iteratedFDeriv ℝ n g x d=_ from hv).symm)).le.trans (hz d c hc))
    ((show ‖(iteratedFDeriv ℝ n f x d).2‖=‖iteratedFDeriv ℝ n h x d‖ from congr_arg (‖·‖) (id (show iteratedFDeriv ℝ n h x d=_ from hk).symm)).le.trans (he d c hc))

lemma fading (A : X→L[ℝ] Y) (x : X) (k : ℕ) (he : 1 < k) : iteratedFDeriv ℝ k (⇑A) x=0 := by
  cases k with
  | zero => omega
  | succ i =>
    ext d; rw [iteratedFDeriv_succ_apply_right, show fderiv ℝ (⇑A)=(fun _=> A) from funext fun _=> A.fderiv, iteratedFDeriv_const_of_ne]
    · rfl
    omega
lemma ordinary (A : X →L[ℝ] Y) (he : ∀ v c, 0 ≤ c → P v c → ‖A v‖≤C*c) (h : 0≤C) (k : ℕ) (hk : 0<k) : Costs P (budget Y) (⇑A) x k C := by
  intro d c hh; unfold budget
  rcases eq_or_lt_of_le (show 1 ≤ k from hk) with hq|hq
  · subst k; rw [iteratedFDeriv_one_apply, A.fderiv,Fin.prod_univ_one]; exact he (d 0) (c 0) (hh 0).1 (hh 0).2
  rw [fading A x k hq, _root_.zero_apply,norm_zero]; exact mul_nonneg h (Finset.prod_nonneg fun i _ => (hh i).1)
end Polish
end YM.AnalyticNext.QuarticMatch.Radius
