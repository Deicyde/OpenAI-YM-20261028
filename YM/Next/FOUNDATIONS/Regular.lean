import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Org.Theatre
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06
import YM.Work.G07.Calculus

/-!
# Pre-mask algebra for combining the purchased columns

Use at *arbitrary* healthy U for `supBounds` compatibility checks, including
flag boundary. A subtlety adding/subtracting regular f: around a healthy U,
when calculating an iterated left derivative, smaller derivatives may be
used even at nearby **nonhealthy** V. Here we check that the actual
`ContDiffAt` condition in `B.Regular` suffices.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Foundations
open Function Filter Lattice Wilson RG
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {G : Gauge} {n : Side}

section Germ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def combine (v : Directions G n × Directions G n) : Directions G n :=
    fun e => G.plog (G.mat (G.lieExp (v.2 e) * G.lieExp (v.1 e)))

private theorem combine_diff : ContDiffAt ℝ ω (combine (G:=G) (n:=n)) 0 := by
  refine contDiffAt_pi.mpr fun e => ?_
  have hg : ContDiff ℝ ω (fun v : Directions G n × Directions G n =>
      G.mat (G.lieExp (v.2 e) * G.lieExp (v.1 e))) :=
    (G.exp_jet.comp ((contDiff_apply ℝ G.Color e).comp contDiff_snd)).mul
      (G.exp_jet.comp ((contDiff_apply ℝ G.Color e).comp contDiff_fst))
  refine ContDiffAt.comp (f:=fun v => _) (g:=G.plog) _ ?_ hg.contDiffAt
  simp only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, G.mat_lieExp_zero, one_mul, G.mat_one]
  exact G.plog_diff

private theorem combine_germ (U : Config G n) :
    (fun x : Directions G n × Directions G n => increment (increment U x.1) x.2) =ᶠ[𝓝 0]
      increment U ∘ combine := by
  suffices hh : ∀ i, ∀ᶠ v : Directions G n × Directions G n in 𝓝 0,
      increment (increment U v.1) v.2 i = increment U (combine v) i by
    filter_upwards [eventually_all.mpr hh] with x hx
    exact funext hx
  intro i
  let f (q : Directions G n × Directions G n) := G.lieExp (q.2 i) * G.lieExp (q.1 i)
  have he : Tendsto f (𝓝 0) (𝓝 1) := by
    rw [← show f 0 = 1 by simp [f]]
    exact (show Continuous f by unfold f; fun_prop).tendsto _
  filter_upwards [he.eventually G.plog_right] with q hq
  unfold increment combine
  rw [← mul_assoc, show G.lieExp _ = f q from hq]

private theorem doubleAt {U : Config G n} {k : WithTop ℕ∞} {f : Config G n → E}
    (h : ContDiffAt ℝ k (f ∘ increment U) 0) :
    ContDiffAt ℝ k (fun q : Directions G n × Directions G n => f (increment (increment U q.1) q.2)) 0 := by
  have hz : combine (0 : Directions G n × Directions G n) = 0 := by funext i; simp [combine]
  apply ((hz.symm ▸ h).comp _ (combine_diff.of_le le_top)).congr_of_eventuallyEq
  exact (combine_germ U).fun_comp f

/-- Smoothness of lower leftDerivs in a moving increment chart, no
flags on those displacements. -/
theorem leftDerivs_chart {U : Config G n} {f : Config G n → E} (l : List (Directions G n))
    (k : ℕ) (h : ContDiffAt ℝ (↑(l.length + k : ℕ)) (f ∘ increment U) 0) :
    ContDiffAt ℝ (k : WithTop ℕ∞) (leftDerivs f l ∘ increment U) 0 := by
  induction l generalizing k with
  | nil => simpa! only [List.length_nil, Nat.zero_add] using h
  | cons A l ih =>
    let V (b : Directions G n) (s : ℝ) := leftDerivs f l (increment (increment U b) (s • A))
    change ContDiffAt ℝ _ (fun b : Directions G n => fderiv ℝ (V b) 0 1) 0
    have he : ContDiffAt ℝ (↑(k+1 : ℕ)) (leftDerivs f l ∘ increment U) 0 :=
      ih (k+1) (by simpa [add_right_comm, add_assoc, add_left_comm, add_comm] using h)
    have hQ : ContDiffAt ℝ (↑(k+1 : ℕ)) (uncurry V) 0 := by
      let m (p : Directions G n × ℝ) := (p.1, p.2 • A)
      have h0 : m 0 = 0 := by simp [m, Prod.zero_eq_mk]
      have hh : ContDiffAt ℝ (↑(k+1 : ℕ))
          (fun q : Directions G n × Directions G n => leftDerivs f l (increment (increment U q.1) q.2)) (m 0) :=
        h0.symm ▸ doubleAt he
      exact hh.comp 0 (f:=m) (by unfold m; fun_prop)
    exact (hQ.fderiv (f:=V) (g:=fun _ => 0) (m:=↑k) contDiffAt_const (by push_cast; rfl)).clm_apply
      (g:=fun _ => (1:ℝ)) contDiffAt_const

/-- In these conventions `ContDiffAt` already supplies the additional
`Regular.hasDerivs` check. -/
theorem left_has {U : Config G n} {f : Config G n → E} {k : ℕ} (A : Directions G n)
    {l : List (Directions G n)} (h : l.length < k) (he : ContDiffAt ℝ k (f ∘ increment U) 0) :
    HasDerivAt (fun t : ℝ => leftDerivs f l (increment U (t • A))) (leftDerivs f (A :: l) U) 0 := by
  have hh : ContDiffAt ℝ (1 : WithTop ℕ∞) (leftDerivs f l ∘ increment U) 0 := by
    simpa only [Nat.cast_one] using leftDerivs_chart l 1 (he.of_le (Nat.cast_le.mpr h))
  have ht : ContDiffAt ℝ (1 : WithTop ℕ∞) (fun t : ℝ => leftDerivs f l (increment U (t • A))) 0 := by
    let q (t : ℝ) := t • A
    exact ((show q 0=0 by simp [q]).symm ▸ hh).comp 0 (f:=q) (by unfold q; fun_prop)
  exact (ht.differentiableAt one_ne_zero).hasDerivAt

/-- Changing base points along a variation. -/
private theorem chart_near {U : Config G n} {f : Config G n → E} {k : ℕ}
    (he : ContDiffAt ℝ k (f ∘ increment U) 0) (A : Directions G n) :
    ∀ᶠ t : ℝ in 𝓝 0, ContDiffAt ℝ k (f ∘ increment (increment U (t • A))) 0 := by
  let q (t : ℝ) := (t • A, (0:Directions G n))
  have ht : Tendsto q (𝓝 0) (𝓝 0) := by
    rw [← show q 0=0 by simp [q, Prod.zero_eq_mk]]
    exact (show Continuous q by unfold q; fun_prop).tendsto _
  filter_upwards [ht.eventually ((doubleAt he).eventually (by simp))] with i hi
  exact hi.comp 0 (f:=fun x => (i • A,x)) (contDiffAt_const.prodMk contDiffAt_id)

private theorem jet_add {U : Config G n} {f g : Config G n → E} {k : ℕ} (l : List (Directions G n))
    (h : ContDiffAt ℝ k (f ∘ increment U) 0) (hg : ContDiffAt ℝ k (g ∘ increment U) 0) (he : l.length ≤ k) :
    leftDerivs (f+g) l U = leftDerivs f l U + leftDerivs g l U := by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih =>
    have hh : l.length < k := he
    refine (((left_has A hh h).add (left_has A hh hg)).congr_of_eventuallyEq (f₁:=fun t =>
      leftDerivs (f+g) l (increment U (t • A))) ?_).deriv
    filter_upwards [chart_near h A, chart_near hg A] with i hi ht
    exact ih hi ht hh.le

end Germ

section Columns

variable {P : BudgetPoint} {o : Site n} {s : Support n} {f g : Config G n → ℂ} {a b : ℝ}

private theorem jet_mult (c : ℂ) (f : Config G n → ℂ) (l : List (Directions G n))
    (U : Config G n) : leftDerivs (c • f) l U = c • leftDerivs f l U := by
  induction l generalizing U with
  | nil => rfl
  | cons A l ih => simp only [leftDerivs, ih]; exact deriv_fun_const_smul_field ..

lemma regular_add (hf : P.Regular s f) (hg : P.Regular s g) : P.Regular s (f+g) := by
  have he : ∀ U : Config G n, Healthy P.threshold s U →
      ContDiffAt ℝ (P.order : WithTop ℕ∞) ((f+g) ∘ increment U) 0 :=
    fun U hu => (hf.smooth U hu).add (hg.smooth U hu)
  refine ⟨?_, hf.borel.add hg.borel, ?_, he, fun U hv A _ h => left_has A h (he U hv)⟩
  · intro U V h
    exact congr_arg₂ (· + ·) (hf.sites U V h) (hg.sites U V h)
  intro T U; exact congr_arg₂ (· + ·) (hf.symmetry _ _) (hg.symmetry _ _)

lemma regular_smul (c : ℂ) (hf : P.Regular s f) : P.Regular s (c • f) := by
  have he : ∀ U : Config G n, Healthy P.threshold s U →
      ContDiffAt ℝ (P.order : WithTop ℕ∞) ((c • f) ∘ increment U) 0 :=
    fun U hu => (hf.smooth U hu).const_smul c
  refine ⟨?_, hf.borel.const_smul _, ?_, he, fun U hv A _ h => left_has A h (he U hv)⟩
  · intro U V h
    exact congr_arg (c • ·) (hf.sites U V h)
  intro T U; exact congr_arg (c • ·) (hf.symmetry _ _)

lemma regular_sub (hf : P.Regular s f) (hg : P.Regular s g) : P.Regular s (f-g) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ g]; exact regular_add hf (regular_smul _ hg)

lemma bound_add (hf : P.Regular s f) (hg : P.Regular s g)
    (h : P.supBounds o s f a) (h' : P.supBounds o s g b) : P.supBounds o s (f+g) (a+b) := by
  refine ⟨add_nonneg h.1 h'.1, fun U hu l hl hD => ?_⟩
  rw [jet_add l (hf.smooth U hu) (hg.smooth U hu) hl]
  exact (norm_add_le ..).trans (add_le_add (h.2 _ hu _ hl hD) (h'.2 _ hu _ hl hD))

lemma bound_smul (c : ℂ) (h : P.supBounds o s f a) : P.supBounds o s (c • f) (‖c‖*a) := by
  refine ⟨mul_nonneg (norm_nonneg _) h.1, fun U hu l hl hD => ?_⟩
  rw [jet_mult, norm_smul]
  exact mul_le_mul_of_nonneg_left (h.2 _ hu _ hl hD) (norm_nonneg _)

lemma bound_sub (hf : P.Regular s f) (hg : P.Regular s g)
    (h : P.supBounds o s f a) (h' : P.supBounds o s g b) : P.supBounds o s (f-g) (a+b) := by
  simpa [sub_eq_add_neg] using bound_add hf (regular_smul (-1) hg) h (bound_smul _ h')

lemma regular_bound_sum {ι : Type*} (I : Finset ι) (u : ι → Config G n → ℂ) (c : ι → ℝ)
    (h : ∀ i ∈ I, P.Regular s (u i) ∧ P.supBounds o s (u i) (c i)) :
    P.Regular s (∑ i ∈ I, u i) ∧ P.supBounds o s (∑ i ∈ I, u i) (∑ i ∈ I, c i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨⟨fun _ _ _ => rfl, measurable_const, fun _ _ => rfl, ?_, ?_⟩, ?_⟩
    · intro U _; exact contDiffAt_const
    · intro U _ A l hl
      exact left_has A hl (f:=0) contDiffAt_const
    refine ⟨le_rfl,fun U hu l hl hd => le_of_eq ?_⟩
    rw [show leftDerivs (0 : Config G n → ℂ) l U = _ from Work.G07.left_const 0 l U]
    simp
  | insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    obtain ⟨hp,hb⟩ := h i (by simp)
    obtain ⟨hx,hX⟩ := ih fun j hj => h j (by simp [hj])
    exact ⟨regular_add hp hx, bound_add hp hx hb hX⟩

lemma regular_larger {u : Support n} (h : P.Regular s f) (hs : s ⊆ u) : P.Regular u f :=
  ⟨fun _ _ hv => h.sites _ _ (agrees_mono hv (Finset.coe_subset.mpr hs)), h.borel,h.symmetry,
    fun U hU => h.smooth U (Finset.disjoint_of_subset_left hs hU),
    fun U hU => h.hasDerivs U (Finset.disjoint_of_subset_left hs hU)⟩

lemma bound_larger {u : Support n} (h : P.supBounds o s f a) (hs : s ⊆ u) : P.supBounds o u f a :=
  ⟨h.1, fun U hU => h.2 U (Finset.disjoint_of_subset_left hs hU)⟩

end Columns
end YM.Next.Foundations
