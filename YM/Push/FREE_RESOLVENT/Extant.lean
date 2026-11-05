import YM.Push.FREE_RESOLVENT.Masking
import YM.Push.FREE_RESOLVENT.Reservoir

/-!
# Changing the tree. Prices through the actual positive family

Afford tag-suppressed inverse and window discrepancies via interpolated
completion. Use distinct trees differing at one location. Tags for other
purposes (shared predictor choice, R step etc.) never changed here. All
hypotheses on change of tags given just on physical projection masks, not
coefficient responses. The interpolation an algebra test, not a gauge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice Wilson RG Precision Tree Matrix Mark TestD Bundle Lever Filter Function Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {ι τ X α β E G : Type*}

namespace Lever
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
variable {v : τ → E} {F : E × ℝ → Matrix ι ι ℝ} {a : ι → X} {p : τ → X} {D : Cost X}
variable {γ d t V M : ℝ} {k : ℕ} {x : X}

/-- Pay integrably at the mark. This passage doesn't give a volume factor
*multiplying* the one-tag difference. -/
theorem recovers (l : List τ) (hx : ∀ t ∈ Icc (0:ℝ) 1, ContDiffAt ℝ (↑(l.length+1):ℕ∞ω) F (0,t))
    (ht : ∀ t ∈ Icc (0:ℝ) 1, (park D p d x).Bill D a a (none::l.map some) γ M (jet (guides v) F (none::l.map some) (0,t)))
    (i j) :
    let Z := jet v (fun y => F (y,1)) l 0-jet v (fun y => F (y,0)) l 0
    let B t := D.weight d (a t) x * (positions D p d).pay l (a t)
    B i * (D.weight γ (a i) (a j) * |Z i j|) ≤ M ∧
      B j * (D.weight γ (a j) (a i) * |Z i j|) ≤ M := by
  intro Z B
  let u := l.map (some (α:=τ))
  have hu : u.length=l.length := List.length_map _
  let Y (z : E × ℝ) := jet (guides v) F u z
  have H (t : ℝ) (h : t ∈ Icc (0:ℝ) 1) : HasDerivAt (fun y : ℝ => Y (0,y) i j) (jet (guides v) F (none::u) (0,t) i j) t := by
    have he : ContDiffAt ℝ (↑(u.length+1):ℕ∞ω) F (0,t) := hu.symm ▸ hx t h
    have hg : HasDerivAt (fun r : ℝ => ((0:E),r)) (0,1) t := (hasDerivAt_const t 0).prodMk (hasDerivAt_id _)
    rw [jet_step (guides v) none u he]
    exact (evaluate i j).hasFDerivAt.comp_hasDerivAt _ (((jet_diff _ u he).hasFDerivAt).comp_hasDerivAt t hg)
  have hz (w : ℝ) (hw : 0 ≤ w) (hM : ∀ t ∈ Icc (0:ℝ) 1, w * |jet (guides v) F (none::u) (0,t) i j| ≤ M) :
      w*|Z i j| ≤ M := by
    have h1 : (1:ℝ) ∈ Icc (0:ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
    have h2 : (0:ℝ) ∈ Icc (0:ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
    have h3 := (convex_Icc (0:ℝ) 1 (𝕜:=ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => ((H t ht).const_mul w).hasDerivWithinAt) (fun t ht => by
        rw [Real.norm_eq_abs, abs_mul,abs_of_nonneg hw]; exact hM t ht) h2 h1
    simp only [Y, ← mul_sub, Real.norm_eq_abs, sub_zero,abs_one,mul_one,abs_mul,abs_of_nonneg hw, u,
        restriction v l 1 (smooth_of_le (hx 1 h1) (by omega)),restriction v l 0 (smooth_of_le (hx 0 h2) (by omega))] at h3
    exact h3
  have hB t : 0 ≤ B t := mul_nonneg (D.weight_nn ..) (pay_pos ..).le
  constructor
  · rw [← mul_assoc]; apply hz _ (mul_nonneg (hB i) (D.weight_nn ..))
    intro t h
    have h := (ht t h).row.entry i j
    rw [pay, parks] at h; rw [mul_assoc (B i)]; exact h
  rw [← mul_assoc]; apply hz _ (mul_nonneg (hB j) (D.weight_nn ..))
  intro t h
  have hb := (ht t h).col.entry j i
  rw [pay, parks] at hb
  rw [mul_assoc (B j)]; exact hb
end Lever

namespace Shell
variable [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable {C : Mark τ X} {D : Cost X} {a : ι → X} {M γ : ℝ} (e : α ↪ ι) (f : β ↪ ι)
variable [NormedAddCommGroup E] [NormedSpace ℝ E] {v : τ → E} {F H : E → Matrix ι ι ℝ} {k : ℕ} {x : E}

def clipL (e : α ↪ ι) := ((TestD.times (ι:=ι) (κ:=ι) (μ:=ι)).flip (rim e)) ∘L
  (TestD.times (ι:=ι) (κ:=ι) (μ:=ι) (rim e))

lemma lends (h : Bundle v C D a a F x k γ M) : Bundle v C D a a (slice e ∘ F) x k γ M := by
  refine ⟨(clipL e).contDiff.contDiffAt.comp x h.smooth, fun l hx => ?_⟩
  rw [show jet v (slice e ∘ F) l x=slice e (jet v F l x) from jet_linear v l (clipL e) (smooth_of_le h.smooth hx)]
  apply (h.bound l hx).abs_le; intro i j; rw [slice_test]; split <;> simp

lemma reserves : D.Schur a a γ 1 (off e) := by
  apply Cost.Schur.one.abs_le; intro i j; rw [off_test]; split; next h => rw [h.1]; simp
  simp
lemma padded (h : Bundle v C D a a F x k γ M) : Bundle v C D a a (pad e ∘ F) x k γ (M+1) := by
  have hb : Bundle v C D a a (fun _ : E => off e) x k γ 1 := ⟨contDiffAt_const,fun l h => by
    by_cases ht : l=[]
    · rw [ht,zeroth]; exact Bill.origin _ (reserves e)
    rw [jet_const v l ht]; exact Bill.zero zero_le_one⟩
  exact (lends e h).one_add hb

-- input once on masked domains

def Stable (o : X) (a : ι → X) (e : α ↪ ι) (f : β ↪ ι) : Prop := ∀ i, a i ≠ o → (i∈Set.range e ↔ i ∈ Set.range f)
lemma identical {o : X} (he : Stable o a e f) (F : Matrix ι ι ℝ) (i j : ι) (hx : a i≠o) (hy : a j≠o) :
    pad e F i j = pad f F i j := by
  classical
  rw [pad,pad,Matrix.add_apply, Matrix.add_apply, off_test,off_test,slice_test,slice_test]
  simp_rw [he _ hx,he _ hy]
omit [NormedSpace ℝ E] in
lemma stocks {o : X} (h : Stable o a e f) (F : E → Matrix ι ι ℝ) (x : E) : Alert a o (pad e ∘ F - pad f ∘ F) x :=
  fun i j hx hy => Eventually.of_forall fun z => sub_eq_zero.mpr (identical e f h (F z) i j hx hy)
omit [NormedSpace ℝ E] in
lemma tracks_difference {o : X} (h : Stable o a e f) (F H : E → Matrix ι ι ℝ) (x : E) :
    Alert a o ((pad e ∘ F - pad e ∘ H) - (pad f ∘ F - pad f ∘ H)) x := by
  intro i j hx hy; filter_upwards with w
  change pad e (F w) i j - pad e (H w) i j-(pad f (F w) i j - pad f (H w) i j)=0
  rw [identical e f h _ i j hx hy, identical e f h _ i j hx hy]; ring
lemma pay_sub (h : Bundle v C D a a (fun x => F x-H x) x k γ M) :
    Bundle v C D a a (pad e ∘ F-pad e ∘ H) x k γ M := by
  apply (lends e h).glue (Eventually.of_forall fun i => ?_)
  change slice e (F i-H i)=pad _ _-pad _ _
  unfold pad slice; rw [Matrix.mul_sub,Matrix.sub_mul]; abel
end Shell
end YM.FreeResolvent
