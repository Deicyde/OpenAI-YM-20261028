import YM.Next.SCHEDULE.Support

/-!
# Repeatability: input budgets and sufficiency for path charges

No period-dependent constant in the norms. `shoot_change` observes, in
contrast, a fixed-period fact vital for using parameter continuity at these
stages: upgrade the *exponent* in CONTINUITY (finite torus supports). No
claim of uniform moduli, no upgrade of the bounds themselves.

For path encounters: nothing below estimates a root or any Wilson kernel.
IF it has the indicated recurrent costs, these lemmas test the widths, caps,
and overdraw concerns explicitly. The analytic hurdle on emitting the
`emits` width indep of incoming caps/depth remains completely real.
Budget consumes true path lengths in native units, not just locations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling

open Filter RG RG.Supply Shoot Bid Precision Function Finset Lattice
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge}

/-- Payments may be weakened, always retaining absolute summability. -/
lemma smaller {ι : Type*} {f g : ι → ℝ} {c d : ℝ} (hB : SumBudget f c)
    (h : ∀ i,0 ≤ g i ∧ g i ≤ f i) (he : c ≤ d) : SumBudget g d := by
  have hs := hB.2.1.of_nonneg_of_le (fun i => (h i).1) (fun i => (h i).2)
  exact ⟨fun i => (h i).1,hs,(hs.tsum_le_tsum (fun i => (h i).2) hB.2.1).trans (hB.2.2.trans he)⟩





/-- Norm comparison preserving all invariant jets. -/
lemma narrower {a b C D u v : ℝ} {R : PathData G} {p : Clip}
    (h : R.Bounds p a C u) (hp : 0 < b) (hb : b ≤ a) (hC : C ≤ D) (hu : u ≤ v) : R.Bounds p b D v := by
  have hh (x : ℕ) : Real.exp (b * ↑x) ≤ Real.exp (a * ↑x) := Real.exp_monotone (mul_le_mul_of_nonneg_right hb (by positivity))
  have hg {k : ℕ} (A : Atom G k) : 0 ≤ A.budget b ∧ A.budget b ≤ A.budget a := by
    unfold Atom.budget
    have hk : 0 ≤ A.magnitude := by unfold Atom.magnitude; positivity
    exact ⟨by positivity,mul_le_mul_of_nonneg_left (hh _) hk⟩
  exact ⟨hp,fun p => smaller (h.rows p) (fun i => ⟨by positivity, mul_le_mul_of_nonneg_left (hh _) (by positivity)⟩) hC,
    smaller h.two (fun _ => hg _) hu, smaller h.three (fun _ => hg _) hC, smaller h.four (fun _ => hg _) hC,
    h.invariant,h.symTerms,h.metric,h.loopTerms,h.loop_normal⟩

/-- Weighted-moment allowance, pre-L stage if k fixed pre-L. -/
def momentCost (k : ℕ) (w : ℝ) := ∑' t, decay k (w/4) t

variable {s : Survey G} {q : Quote} {e : Exchange} {j i : ℕ} {L : ℝ}

lemma Buy.moments {ι : Type*} (h : Buy s q e j i L) (k : ℕ) (t : ι → ℕ) (F : ι → ℝ)
    (hf : ∀ i,0 ≤ F i) (C : ℝ)
    (H : SumBudget (fun i => F i * Real.exp ((s.melt q j).width * t i)) C) :
    let w:=(s.melt q j).width
    SumBudget (fun i' => F i'*((t i':ℝ)+1)^k * Real.exp ((w/4+q.widths.loads j i/L)*t i'))
      (momentCost k w * C) := by
  intro w
  let d := momentCost k w
  have hs := decay_summable k (w/4) (div_pos (s.melt q j).width_pos (by norm_num : (0:ℝ)<4))
  have he (i) : 0 ≤ decay k (w/4) i := by unfold decay; positivity
  have hd : 0 ≤ d := tsum_nonneg he
  have hw (i) : decay k (w/4) i ≤ d := by simpa only [sum_singleton,d,momentCost] using hs.sum_le_tsum ({i}:Finset ℕ) (fun i _ => he i)
  have hθ : w/4+q.widths.loads j i/L ≤ w-w/4 := by
    have hm : q.widths.loads j i/L ≤ w/2 := h.phase; linarith
  refine smaller (f:=fun i => d*(F i*Real.exp (w*t i))) (c:=d*C) ⟨fun i => mul_nonneg hd (H.1 i), H.2.1.mul_left d,?_⟩ ?_ le_rfl
  · rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left H.2.2 hd
  intro n
  have hn := hf n
  refine ⟨by positivity,?_⟩
  calc
    _ ≤ F n*((t n:ℝ)+1)^k * Real.exp ((w-w/4)*t n) :=
      mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hθ (by positivity))) (by positivity)
    _ = decay k (w/4) (t n) * (F n*Real.exp (w*t n)) := by
      rw [decay,sub_mul,sub_eq_add_neg, Real.exp_add,neg_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hw _) (by positivity)

/-- Encompass example recurrence eq:r34cap.

Use `k/L^2+k/L^4+k²/L^4`
with *incoming* cap k. -/
def classicalFee (L F K : ℝ) := F*(1+K/L^ (2:ℕ)+K/L^ (4:ℕ)+(K/L^ (2:ℕ))^ (2:ℕ))

lemma Buy.fundClassic (h : Buy s q e j i L) (hx : Adj j i) :
    classicalFee L (q.classicalCost.classic j i) (s.melt q j).paths ≤ (s.melt q i).paths := by
  let K := (s.melt q j).paths; let C:=q.classicalCost.classic j i
  have hu : K/L^ (2:ℕ)≤1/8 := h.path
  have hk : 0 < K := (s.melt q j).paths_pos
  have hc : 0 ≤ C := le_trans zero_le_one (q.classicalCost.pos_ij ..)
  have hL := h.block
  have hm : K/L^ (4:ℕ)≤K/L^ (2:ℕ) := by gcongr <;> linarith
  apply le_trans ?_ (q.classicalCost.le_pair hx)
  unfold classicalFee; rw [mul_comm 5]
  apply mul_le_mul_of_nonneg_left _ hc
  have hy : 0 ≤ K/L^ (2:ℕ) := by positivity
  change 1+K/_+K/_+(K/L^ (2:ℕ))^ (2:ℕ) ≤ (5:ℝ)
  nlinarith

lemma fund_top (j : ℕ) {W : PathData G} {p : ℝ} (hp : 0 ≤ p) (s : Survey G) (q : Quote)
    (h : W.Bounds (s.melt q j).clip (q.widths.launch j) (q.classicalCost.beginCost j) 0) :
    W.Bounds (s.melt q j).clip (s.melt q j).width (s.melt q j).paths p :=
  narrower h (q.widths.wp j) (q.widths.le_top j) (q.classicalCost.le_top j) hp

/-- Keep that
factor for uniform recurrence. -/
lemma Buy.keep (h : Buy s q e j i L) (hx : Adj j i) {p p' : ℝ} {W : PathData G}
    (H : W.Bounds (s.melt q i).clip (q.widths.emits j i)
      (classicalFee L (q.classicalCost.classic j i) (s.melt q j).paths)
      (q.finish.loop j i*L^ (4:ℕ)+(q.finish.loop j i/L^ (2:ℕ))*(2*p)))
    (hp : q.finish.loop j i*L^ (4:ℕ) ≤ p') (hP : p ≤ 2*p') (hp0 : 0 ≤ p) :
    W.Bounds (s.melt q i).clip (s.melt q i).width (s.melt q i).paths (2*p') := by
  refine narrower H (q.widths.wp _) (q.widths.le_pair hx) (h.fundClassic hx) ?_
  have he := mul_le_mul_of_nonneg_right h.loop (show 0 ≤ 2*p by positivity)
  linarith
end YM.Next.Scheduling
