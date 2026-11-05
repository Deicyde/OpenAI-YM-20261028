import YM.Ward.Extreme

/-!
# Continue full Ward VALUES for all labels on walks
-/
set_option autoImplicit false
noncomputable section
namespace YM.Ward
open Metric Function Set Filter Analysis Table OS
open scoped Topology InnerProductSpace ContDiff BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {a : Axis} {n : ℕ}

variable (W : DiffPlan S) (T : SpinRows S) (H : S.Hierarchy) (V : Chamber S a)
include H
lemma channel (P : W.Derivatives S) (Y : Collinear W T) (C : commutes W T) (x : Points n) (k b) (K : Ortho.Skew) (p : Fin n → S.Tag)
    (s : ℝ) (hv : Earliest (cast x k b s) a k ∨ Latest (cast x k b s) a k) : AnalyticAt ℝ (angular W T p K ∘ cast x k b) s := by
  let V := Classical.choice (realization H a)
  have ha (i : Fin n → S.Tag) : ContDiffAt ℝ ω (disc i ∘ cast x k b) s := AnalyticAt.contDiffAt
    (hv.elim (first_adv V H W T P Y C _ _ _ _ _) (last_adv V H W T P Y C _ _ _ _ _))
  apply ContDiffAt.analyticAt
  unfold Function.comp angular
  apply ContDiffAt.sum
  intro i hi; apply (ha _).add (ContDiffAt.sum _)
  intro u hu
  have he : ContDiffAt ℝ ω (cast x k b) s := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  exact ((factor i u K).contDiff.contDiffAt.comp s he).smul (ha _)

omit H in
private lemma unique {f : ℝ → ℂ} {a : ℝ} (h : AnalyticAt ℝ f a) (he : ∀ n, iteratedDeriv n f a=0) :
    f =ᶠ[𝓝 a] 0 := by
  obtain ⟨p,r,hp⟩ := h
  have H n : p n=0 := by
    apply ContinuousMultilinearMap.ext; intro x
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
    have ht := hp.factorial_smul 1 n
    rw [← iteratedDeriv_eq_iteratedFDeriv,he,← Nat.cast_smul_eq_nsmul ℝ] at ht
    have hh : p.coeff n=0 := (smul_eq_zero_iff_right (by positivity : (Nat.factorial n:ℝ)≠0)).mp ht
    rw [hh,smul_zero];rfl
  filter_upwards [eball_mem_nhds a hp.r_pos] with t ht
  have hw := hp.hasSum (y := t-a) (show _ from by
    rw [mem_eball, ← edist_sub_right t a a, sub_self] at ht; exact ht)
  simp only [H,_root_.zero_apply,add_sub_cancel] at hw
  exact hw.unique hasSum_zero

def Still (x : Points n) := ∀ (p : Fin n → S.Tag) K, angular W T p K x=0
omit H in
lemma opened (a : Axis) (j : Fin n) : IsOpen {x : Points n | Earliest x a j ∨ Latest x a j} := by
  have ho : IsOpen {x : Points n| Earliest x a j} := by
    rw [show {x : Points n | Earliest x a j}= conf n ∩ ⋂ i, ⋂ _ : i≠j, {x : Points n | x j a<x i a} by
      ext p; simp [Earliest]]
    refine (conf_open _).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun hi => ?_)
    exact isOpen_lt (by fun_prop) (by fun_prop)
  have hu : IsOpen {x : Points n| Latest x a j} := by
    rw [show {x : Points n | Latest x a j}= conf n ∩ ⋂ i, ⋂ _ : i≠j, {x : Points n | x i a<x j a} by
      ext p; simp [Latest]]
    refine (conf_open _).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun hi => ?_)
    exact isOpen_lt (by fun_prop) (by fun_prop)
  exact ho.union hu

lemma stood (P : W.Derivatives S) (Y : Collinear W T) (C : commutes W T)
    (x : Points n) (k : Fin n) (b) (u v : ℝ) (h : ∀ i∈uIcc u v, Earliest (cast x k b i) a k ∨ Latest (cast x k b i) a k)
    (hp : Still W T (cast x k b v)) : Still W T (cast x k b u) := by
  let z := cast x k b
  have hU := right_mem_uIcc (a := u) (b := v)
  have hv := h _ hU
  have hz : z v∈conf _ := hv.elim And.left And.left
  intro p g
  let f := angular W T p g ∘ z
  have hh : AnalyticOnNhd ℝ f (uIcc u v) := fun i hi => channel W T H P Y C x k b g p i (h _ hi)
  have he := unique (hh v hU) (fun m => jet_line W T H P C g p x k b v hz (fun w => hp w g) m)
  exact (hh.eqOn_zero_of_preconnected_of_eventuallyEq_zero (isPreconnected_uIcc) hU he) left_mem_uIcc

/-- Relation oriented from x to y. Directions and extreme witness *per
segment*, not a claim about the whole path always in one normal. -/
inductive Walk (n : ℕ) : Points n → Points n → Prop
| id (x : Points n) : Walk n x x
| bridge (x : Points n) (i a b s) (h : ∀ t∈uIcc 0 s, Earliest (cast x i b t) a i ∨ Latest (cast x i b t) a i) : Walk n x (cast x i b s)
| transit {x y z} : Walk n x y → Walk n y z → Walk n x z
lemma along (P : W.Derivatives S) (Y : Collinear W T) (C : commutes W T) {x y : Points n} (h : Walk n x y)
    (hy : Still W T y) : Still W T x := by
  induction h with
  | id => exact hy
  | bridge x i a b s hp => simpa only [start] using stood W T H P Y C _ _ _ _ _ hp hy
  | transit _ _ ih im => exact ih (im hy)
end YM.Ward
