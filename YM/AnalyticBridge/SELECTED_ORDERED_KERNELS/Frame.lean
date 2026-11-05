import YM.Next.WARD_BIN.Lies

/-!
# Ordered RG.leftDerivs in real exponential coordinates

E near . The argument to an ordinary derivative will be the
*log of the ordered product* of local Lie increments. The outer derivative
order can be STRICTLY LESS than the length of the list, but every external
slot occurs, in exactly one block. Use true derivatives of chart germs;
hard masks are not given any smoothness by this argument. These are real
polarized derivatives, with no factorial. LEFT here means the project's
exponential on the left of the current link.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels
open Lattice Wilson RG Function Filter Topology WardBin.Lies
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {j k : ℕ}

abbrev Panel (G : Gauge) (j : ℕ) := Fin j → G.Color

/-- In the convention of `leftDerivs` the first list index is the OUTER
operator, thus the exponential nearest to the original base. -/
def chain (G : Gauge) : (j : ℕ) → Panel G j → G.El
  | 0, _ => 1
  | j+1, x => chain G j (Fin.tail x) * G.lieExp (x 0)

@[simp] lemma chain_zero (G : Gauge) (j : ℕ) : chain G j 0 = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => change chain G j 0 * G.lieExp 0 = _; rw [ih,G.mat_lieExp_zero,one_mul]

lemma chain_cont (G : Gauge) (j : ℕ) : Continuous (chain G j) := by
  induction j with
  | zero => exact continuous_const
  | succ j ih =>
    apply (ih.comp (f:=Fin.tail) (continuous_pi fun i => continuous_apply i.succ)).mul (by fun_prop)

lemma chain_smooth (G : Gauge) (j : ℕ) : ContDiff ℝ ω (G.mat ∘ chain G j) := by
  induction j with
  | zero => exact contDiff_const
  | succ j ih =>
    simp only [comp_def,chain,G.mat_mul]
    exact (ih.comp (f:=Fin.tail) (contDiff_pi.mpr fun i => contDiff_apply ℝ G.Color i.succ)).mul
      (G.exp_jet.comp (contDiff_apply ℝ G.Color 0))

lemma chug_apply (V : Config G n) (x : Slab G n j) (e : Edge (Site n)) :
    chug j V x e = chain G j (fun i => x i e) * V e := by
  induction j generalizing V with
  | zero => exact (one_mul _).symm
  | succ j ih => simp only [chug, ih, chain, mul_assoc]; rfl

/-- In the chart with centre the evaluation point (not differentiating a
frozen-coordinate proxy for the NEXT application's direction). -/
def frame (G : Gauge) (j : ℕ) (x : Panel G j) := G.plog (G.mat (chain G j x))
@[simp] lemma frame_zero (G : Gauge) (j : ℕ) : frame G j 0 = 0 := by simp [frame]
lemma frame_smooth (G : Gauge) (j : ℕ) : ContDiffAt ℝ ω (frame G j) 0 := by
  apply ContDiffAt.comp (f:=G.mat ∘ chain G j) (g:=G.plog) _ _ (chain_smooth G j).contDiffAt
  simpa using G.plog_diff

/-- Act separately at *all* physical links. -/
def through (φ : Edge (Site n) → Panel G j → G.Color) (a : Slab G n j) : Directions G n :=
  fun e => φ e (fun i => a i e)

lemma through_smooth {l : ℕ∞ω} {φ : Edge (Site n) → Panel G j → G.Color} (hφ : ∀ e, ContDiffAt ℝ l (φ e) 0) :
    ContDiffAt ℝ l (through φ) 0 := contDiffAt_pi.mpr fun e => (hφ e).comp (0 : Slab G n j)
      (show ContDiffAt ℝ l (fun a : Slab G n j => fun i => a i e) 0 from contDiffAt_pi.mpr fun i =>
        ((contDiff_apply ℝ G.Color e).comp (contDiff_apply ℝ (Directions G n) i)).contDiffAt)

lemma chug_chart (V : Config G n) (j : ℕ) :
    chug j V =ᶠ[𝓝 0] increment V ∘ through (fun _ => frame G j) := by
  have h (e : Edge (Site n)) : ∀ᶠ a : Slab G n j in 𝓝 0,
      G.lieExp (frame G j (fun i => a i e)) = chain G j (fun i => a i e) := by
    apply Filter.Tendsto.eventually _ G.plog_right
    rw [← chain_zero G j]
    exact ((chain_cont G j).comp (continuous_pi fun i =>
      (continuous_apply e).comp (continuous_apply i))).tendsto (0 : Slab G n j)
  filter_upwards [eventually_all.mpr h] with x hx
  exact funext fun e => (chug_apply V x e).trans (congr_arg (· * V e) (hx e).symm)

def term (φ : Edge (Site n) → Panel G j → G.Color) (p : OrderedFinpartition j) (A : Slab G n j)
    (b : Fin p.length) : Directions G n := fun e =>
  iteratedFDeriv ℝ (p.partSize b) (φ e) 0 (fun r => Pi.single (p.emb b r) (A (p.emb b r) e))

private lemma via_term (φ : Edge (Site n) → Panel G j → G.Color) (p : OrderedFinpartition j)
    (A : Slab G n j) (b : Fin p.length) (hφ : ∀ e, ContDiffAt ℝ (p.partSize b) (φ e) 0) :
    iteratedFDeriv ℝ (p.partSize b) (through φ) 0 (fun r => Pi.single (p.emb b r) (A (p.emb b r))) = term φ p A b := by
  funext e
  let L : Directions G n →L[ℝ] G.Color := ContinuousLinearMap.proj e
  let Q : Slab G n j →L[ℝ] Panel G j := ContinuousLinearMap.pi
    (fun i => L.comp (ContinuousLinearMap.proj i))
  have hh i : Q (Pi.single i (A i)) = Pi.single i (A i e) := by
    funext v; change ((Pi.single i (A i) : Slab G n j) v) e = _; by_cases h : v=i <;> simp [h]
  have hx := L.iteratedFDeriv_comp_left (through_smooth hφ) le_rfl
  rw [show (⇑L ∘ through φ)=φ e ∘ Q from rfl, liner Q (by rw [map_zero]; exact hφ e),map_zero] at hx
  symm
  have hr := congr_arg (fun t : Slab G n j [×(p.partSize b)]→L[ℝ] G.Color =>
    t (fun r => Pi.single (p.emb b r) (A (p.emb b r)))) hx
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply] at hr; simp_rw [hh] at hr; exact hr

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Config G n} {F : Config G n → E}

/-- Allow arbitrary link-by-link smooth coordinates on the chug germ. -/
theorem expand_local {f : Directions G n → E} (φ : Edge (Site n) → Panel G j → G.Color)
    (hφ : ∀ e, ContDiffAt ℝ j (φ e) 0) (h : ContDiffAt ℝ j f (through φ 0))
    (he : F ∘ chug j V =ᶠ[𝓝 0] f ∘ through φ) (A : Slab G n j) :
    leftDerivs F (List.ofFn A) V = ∑ p : OrderedFinpartition j, iteratedFDeriv ℝ p.length f (through φ 0) (term φ p A) := by
  have hH := through_smooth hφ
  rw [expand_part A ((h.comp 0 hH).congr_of_eventuallyEq he), mixed_eval,
    (he.iteratedFDeriv ℝ j).eq_of_nhds,iteratedFDeriv_comp h hH le_rfl]
  rw [FormalMultilinearSeries.taylorComp, sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  change iteratedFDeriv ℝ p.length f (through φ 0) (fun b => iteratedFDeriv ℝ (p.partSize b) (through φ) 0
    (fun r => Pi.single (p.emb b r) (A (p.emb b r)))) = _
  rw [funext (fun b => via_term φ p A b fun e => (hφ e).of_le (Nat.cast_le.mpr (p.partSize_le b)))]

/-- Each part contributes a derivative of the log of the entire ordered
path germ at that link. No assertion of symmetry of `leftDerivs`. -/
theorem expand (h : Germ j F V) (A : Slab G n j) :
    leftDerivs F (List.ofFn A) V = ∑ p : OrderedFinpartition j,
      iteratedFDeriv ℝ p.length (F ∘ increment V) 0 (term (fun _ => frame G j) p A) := by
  have hz : through (n:=n) (fun _ => frame G j) 0=0 := funext fun e => frame_zero G j
  exact (expand_local (fun _ => frame G j) (fun e => (frame_smooth G j).of_le le_top)
    (by rw [hz]; exact h) ((chug_chart V j).fun_comp F) A).trans (by rw [hz]; rfl)

/-- Costs are entirely on true *external* fields, not on their total ℓ²
norm. In the centred case the proportionality factors depend just on G
and finite orders, with no period or L in them. -/
theorem term_cost (φ : Edge (Site n) → Panel G j → G.Color) (p : OrderedFinpartition j) (A : Slab G n j)
    (b : Fin p.length) (e : Edge (Site n)) :
    ‖term φ p A b e‖ ≤ ‖iteratedFDeriv ℝ (p.partSize b) (φ e) 0‖ * ∏ r, ‖A (p.emb b r) e‖ := by
  unfold term
  apply ContinuousMultilinearMap.le_opNorm_mul_prod_of_le; intro i; exact (Pi.norm_single _).le

theorem term_zero (φ : Edge (Site n) → Panel G j → G.Color) (p : OrderedFinpartition j) (A : Slab G n j)
    (b : Fin p.length) (e : Edge (Site n)) {i : Fin (p.partSize b)} (h : A (p.emb b i) e=0) :
    term φ p A b e = 0 := (iteratedFDeriv ..).map_coord_zero i (by rw [h, Pi.single_zero])

end YM.SelectedOrderedKernels
