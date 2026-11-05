import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Shoot.Criteria

/-! bounded, uniform analytic approximations on fixed parameter patches.
    These lemmas only use one fixed stencil/volume at a time. -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Desk
open MvPolynomial Finset Filter RG
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {I X : Type*} [Fintype I]

section
variable {K : Set X} {A B : X → ℂ} {f g : ℕ → X → ℂ}

-- just norm bounds
def Tint (K : Set X) (A : X → ℂ) := ∃ b : ℝ, ∀ x∈K, ‖A x‖ ≤ b
lemma tint_add (h : Tint K A) (hp : Tint K B) : Tint K fun x => A x+B x := by
  obtain ⟨v,hv⟩ := h; obtain ⟨c,H⟩ := hp
  exact ⟨v+c,fun x hx => (norm_add_le ..).trans (add_le_add (hv x hx) (H x hx))⟩
lemma tint_mul (h : Tint K A) (hp : Tint K B) : Tint K fun x => A x*B x := by
  obtain ⟨v,hv⟩ := h; obtain ⟨c,H⟩ := hp
  exact ⟨v*c,fun x hx => (norm_mul ..).trans_le (mul_le_mul (hv x hx) (H x hx) (norm_nonneg _) ((norm_nonneg _).trans (hv x hx)))⟩
lemma tint_fix (K : Set X) (c : ℂ) : Tint K (fun _ => c) := ⟨‖c‖,fun _ _ => le_rfl⟩
lemma tint_ite (h : Tint K A) (p : X→Prop) [DecidablePred p] : Tint K fun x => if p x then A x else 0 := by
  obtain ⟨B,H⟩ := h; refine ⟨B,fun x hx => ?_⟩
  change ‖if p x then _ else _‖ ≤ B; split; exact H x hx; rw [norm_zero]; exact (norm_nonneg _).trans (H x hx)

variable {J : Type*}
lemma tint_sum (L : Finset J) (F : J → X → ℂ) (h : ∀ i,Tint K (F i)) : Tint K fun x => ∑ i∈L,F i x := by
  classical
  induction L using Finset.induction with
  | empty => simp only [sum_empty]; exact tint_fix ..
  | insert i L hi ih => simp only [sum_insert hi]; exact tint_add (h i) ih
lemma tint_prod (L : Finset J) (F : J → X → ℂ) (h : ∀ i,Tint K (F i)) : Tint K fun x => ∏ i∈L,F i x := by
  classical
  induction L using Finset.induction with
  | empty => simp only [prod_empty]; exact tint_fix ..
  | insert i L hi ih => simp only [prod_insert hi]; exact tint_mul (h i) ih

lemma colors (h : Tint K A) : Tint K (fun x => Complex.exp (A x)) := by
  obtain ⟨C,H⟩ := h; exact ⟨_,fun x hx => by
    rw [Complex.norm_exp]; exact Real.exp_monotone ((Complex.re_le_norm ..).trans (H x hx))⟩

lemma tents (h : Tint K A) (hu : TendstoUniformlyOn f A atTop K) :
    ∃ C : ℝ, 0<C ∧ (∀ x∈K, A x∈ Metric.closedBall 0 C) ∧ ∀ᶠ i in atTop, ∀ x∈K, f i x∈ Metric.closedBall 0 C := by
  obtain ⟨r,hr⟩ := h
  refine ⟨|r|+1,by positivity,fun x hx => ?_,?_⟩
  · rw [Metric.mem_closedBall,dist_zero_right]; linarith [hr x hx, le_abs_self r]
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 zero_lt_one] with i hi x hx
  rw [Metric.mem_closedBall]; apply (dist_triangle (f i x) (A x) (0:ℂ)).trans
  have hv := hi x hx
  rw [dist_comm] at hv
  have hh : dist (f i x) (A x)+ dist (0:ℂ) (A x) ≤ |r|+1 := by
    rw [dist_zero_left]; linarith [hr x hx,le_abs_self r]
  rw [dist_comm (A x)]; exact hh

lemma painting (K : Set X) (c : X→ℂ) : TendstoUniformlyOn (fun _ : ℕ => c) c atTop K :=
  Metric.tendstoUniformlyOn_iff.mpr fun ε he => Eventually.of_forall fun _ _ _ => by simpa using he

lemma uniform_mul (h : Tint K A) (hp : Tint K B) (he : TendstoUniformlyOn f A atTop K)
    (hh : TendstoUniformlyOn g B atTop K) : TendstoUniformlyOn (fun n x => f n x*g n x) (fun x => A x*B x) atTop K := by
  obtain ⟨C,_,Hc,hC⟩ := tents h he; obtain ⟨U,_,HU,hU⟩ := tents hp hh
  let z i x := (f i x,g i x)
  let R x := (A x,B x)
  have ht : TendstoUniformlyOn z R atTop K := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε he' => ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp he _ he',Metric.tendstoUniformlyOn_iff.mp hh _ he'] with i hi hh x hx
    rw [Prod.dist_eq]; exact max_lt (hi x hx) (hh x hx)
  let Z := Set.prod (Metric.closedBall (0:ℂ) C) (Metric.closedBall (0:ℂ) U)
  exact ((show IsCompact Z from (isCompact_closedBall (α:=ℂ) ..).prod (isCompact_closedBall ..)).uniformContinuousOn_of_continuous
    (f:=fun x : ℂ × ℂ => x.1*x.2) continuous_mul.continuousOn).comp_tendstoUniformlyOn_eventually (s:=Z) (f:=R) (F:=z)
    (by filter_upwards [hC,hU] with i hc hi x hx; exact ⟨hc x hx,hi x hx⟩) (fun x hx => ⟨Hc x hx,HU x hx⟩) ht

lemma uniform_sum (L : Finset J) (F : J → X → ℂ) (G : J → ℕ → X → ℂ) (h : ∀ i,TendstoUniformlyOn (G i) (F i) atTop K) :
    TendstoUniformlyOn (fun n x => ∑ i∈L,G i n x) (fun x => ∑ i∈L,F i x) atTop K := by
  classical
  induction L using Finset.induction with
  | empty => simp only [sum_empty]; exact painting K (fun _ => 0)
  | insert i L hi ih => simp only [sum_insert hi]; exact (h i).add ih
lemma uniform_prod (L : Finset J) (F : J → X → ℂ) (G : J → ℕ → X → ℂ)
    (h : ∀ i,TendstoUniformlyOn (G i) (F i) atTop K) (ht : ∀ i,Tint K (F i)) :
    TendstoUniformlyOn (fun n x => ∏ i∈L,G i n x) (fun x => ∏ i∈L,F i x) atTop K := by
  classical
  induction L using Finset.induction with
  | empty => simp only [prod_empty]; exact painting K (fun _ => 1)
  | insert i L hi ih => simp only [prod_insert hi]; exact uniform_mul (ht i) (tint_prod L F ht) (h i) ih
end

def powers (N : ℕ) (z : ℂ) := ∑ i∈ range N,z^i / (i.factorial:ℂ)
lemma kingdoms (r : ℝ) (_h : 0 < r) : TendstoUniformlyOn powers Complex.exp atTop (Metric.closedBall 0 r) := by
  have hp := (NormedSpace.expSeries_div_hasSum_exp r).summable
  have he : TendstoUniformlyOn powers (fun x => ∑' i : ℕ, x^i / (i.factorial:ℂ)) atTop (Metric.closedBall 0 r) := by
    refine tendstoUniformlyOn_tsum_nat hp ?_
    intro n x hx
    have hb : ‖x‖ ≤ r := by simpa using hx
    simp only [norm_div,norm_pow,Complex.norm_natCast]
    gcongr
  rw [show Complex.exp=(fun x => ∑' i : ℕ,x^i / (i.factorial:ℂ)) from funext fun x => by
    rw [Complex.exp_eq_exp_ℂ]; exact (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq.symm]
  exact he

lemma condensate {K : Set X} {A : X→ℂ} {f : ℕ→ X→ ℂ}
    (h : Tint K A) (he : TendstoUniformlyOn f A atTop K) :
    TendstoUniformlyOn (fun n x => powers (n+1) (f n x)) (fun x => Complex.exp (A x)) atTop K := by
  obtain ⟨C,hv,HC,hC⟩ := tents h he
  have ht := ((isCompact_closedBall _ _).uniformContinuousOn_of_continuous Complex.continuous_exp.continuousOn).comp_tendstoUniformlyOn_eventually hC HC he
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hx => ?_
  have hu : ∀ᶠ i in atTop, ∀ x∈Metric.closedBall (0:ℂ) C,dist (Complex.exp x) (powers (i+1) x) < ε/2 :=
    (show Tendsto (fun i : ℕ => i+1) atTop atTop from by refine tendsto_atTop_mono (fun i => i.le_succ) tendsto_id).eventually
    (Metric.tendstoUniformlyOn_iff.mp (kingdoms C hv) _ (half_pos hx))
  filter_upwards [hC,hu, Metric.tendstoUniformlyOn_iff.mp ht _ (half_pos hx)] with i hi hh hn x hx
  exact (dist_triangle _ _ _).trans_lt ((add_lt_add (hn x hx) (hh _ (hi x hx))).trans_eq (add_halves ε))
end YM.Multi.Desk
