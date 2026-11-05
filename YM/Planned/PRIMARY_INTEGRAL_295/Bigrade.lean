import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Bid.Fuels
import YM.Next.WARD_BIN.Degree
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07


/-!
# Flat-read toolkit for a graded radial probe

The finite Taylor read of a Snap germ.

We will evaluate a *jet calculation*
from the stationary column this way, not compute that column by continuing
some presumed coherent sources.

The two grades are, respectively, degree in
h (engineering) and ordinary factor degree.

Especially, what it means to
*annihilate* all the mixed derivatives on every list of pure directions is
verified here (cf.

The scaling used here for positions is
`engineered`, not threshold scaling by slot count.

Constant-color gauge
invariance suffices for reading in this calculation; no claiming the flat
logarithmic replacement defines a local gauge invariant field.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Parts
open Function Filter Labels Source Source.Drops Work.G05 WardBin
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {d k l n : ℕ}

lemma engineered_zero (A : Snap G d) : engineered 0 A = 0 := by
  ext1 i; simp [engineered_at]

set_option maxHeartbeats 600000 in
/-- Ordinary Taylor then extract the h-coefficient. Includes order zero. -/
lemma leading_snap_sum {f : Snap G d → ℂ} (hf : ContDiffAt ℝ d f 0) (hk : k ≤ d) (J : Jet G) :
    leading k (fun t => f (engineered t (trunk d J))) =
      ∑ l ∈ Finset.range (d+1), read J (tile (Tensor.coeff f l 0) k) := by
  classical
  let r (t : ℝ) := engineered t (trunk d J)
  have hr : r 0 = 0 := engineered_zero _
  have hd : ContDiffAt ℝ d r 0 := (eng_cont _ _).contDiffAt
  have he := jets_comp hd hd (show ContDiffAt ℝ d f (r 0) by rw [hr]; exact hf)
    (blockTaylor_contDiff d f _|>.contDiffAt) rfl (fun _ _ => rfl)
    (show ∀ l ≤ d, iteratedFDeriv ℝ l f (r 0) = iteratedFDeriv ℝ l (blockTaylor d f) (r 0) from
      fun l hl => hr.symm ▸ (blockTaylor_jets hf l hl).symm) _ hk
  let g l t := Tensor.diagonal (Tensor.coeff f l 0) (r t)
  calc
    leading k (f ∘ r) = leading k (blockTaylor d f ∘ r) := by rw [leading,leading,iteratedDeriv,iteratedDeriv,he]
    _ = leading k (fun t => ∑ l ∈ Finset.range (d+1), g l t) := by
      apply congr_arg (leading k); funext t; simp only [blockTaylor, comp_apply, Finset.sum_apply, g]
    _ = ∑ l ∈ Finset.range (d+1), leading k (g l) := lead_sum _ _ fun l _ =>
      (Tensor.diag_smooth _ k).contDiffAt.comp _ (hd.of_le (by exact_mod_cast hk))
    _ = _ := Finset.sum_congr rfl fun l _ => tile_reads ..

/-- Separates the ordinary factor order at one h order. Do NOT separate
by h degree alone and conclude that a derivative of just one order vanishes. -/
lemma no_tile {f : Snap G d → ℂ} (hf : ContDiffAt ℝ d f 0) (hk : k ≤ d)
    (h : ∀ J : Jet G, leading k (fun t => f (engineered t (trunk d J))) = 0) (hl : l ≤ d) :
    tile (Tensor.coeff f l 0) k=0 := by
  classical
  let p l := tile (Tensor.coeff f l 0) k
  have he : ∑ a ∈ Finset.range (d+1), p a=0 := by
    refine eval_ext _ 0 fun J => ?_
    rw [map_sum,map_zero]; exact (leading_snap_sum hf hk _).symm.trans (h _)
  have H := congr_arg (piece (G:=G) (k,l)) he
  rw [map_sum,map_zero,Finset.sum_eq_single l] at H
  · rwa [MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same
      (show MvPolynomial.IsWeightedHomogeneous bidegree (p l) (k,l) from tile_grade ..)] at H
  · intro b hb hx
    exact MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne (p := p b) (k,l)
      (show MvPolynomial.IsWeightedHomogeneous bidegree (p b) (k,b) from tile_grade ..)
      (fun hh => hx (congr_arg Prod.snd hh).symm)
  intros hh; simp [Nat.lt_succ_of_le hl] at hh

-- Fin rank-one slot projections. Use Fin(d−1), not generation itself as index.
private def tap (i : Fin (d-1)) : Snap G d →L[ℝ] Snap G d :=
    (ContinuousLinearMap.single ℝ (fun j : Fin (d-1) => Taylor G j.val) i).comp
      (ContinuousLinearMap.proj i)

lemma spread_scale (A : Snap G d) (t : ℝ) : engineered t A =
    ∑ i : Fin (d-1), t^(i.val+2) • Pi.single i (A i) := by
  funext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp [engineered_at]
  · intro b _ he
    simp only [Pi.smul_apply, Pi.single_eq_of_ne he.symm, smul_zero]
  simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def rate (b : Fin l → Fin (d-1)) := ∑ i, ((b i).val+2)

private def layer (M : Tensor.T (Snap G d) E l) (n : ℕ) : Tensor.T (Snap G d) E l :=
    ∑ b : Fin l → Fin (d-1) with rate b = n, M.compContinuousLinearMap fun i => tap (b i)

private lemma layer_leads (M : Tensor.T (Snap G d) E l) (n : ℕ) (u : Fin l → Snap G d) :
    leading n (fun t => M (fun i => engineered t (u i)))=layer M n u := by
  classical
  let f (b : Fin l → Fin (d-1)) := M fun i => tap (b i) (u i)
  have hx (t : ℝ) : M (fun i => engineered t (u i)) = ∑ b : Fin l → Fin (d-1), t^(rate b) • f b := by
    simp_rw [spread_scale]
    change M (fun i => ∑ j : Fin (d-1), t^(j.val+2) • tap j (u i)) = _
    rw [M.map_sum (fun i j => t^(j.val+2) • tap j (u i))]
    apply Finset.sum_congr rfl; intro b hb
    rw [M.map_smul_univ, Finset.prod_pow_eq_pow_sum]; rfl
  rw [funext hx, lead_sum (n:=n) Finset.univ (fun b (x : ℝ) => x^(rate b) • f b)]
  · simp_rw [lead_monomial]; unfold layer
    rw [sum_apply]; simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, Finset.sum_filter]
    simp [f,eq_comm]
  intro i _; exact (monoSmooth ..).contDiffAt

private lemma layer_sym (M : Tensor.T (Snap G d) E l) (h : Tensor.Sym M) (n : ℕ) :
    Tensor.Sym (layer M n) := by
  intro u v
  rw [← layer_leads, ← layer_leads]; apply congr_arg (leading n); funext t
  exact h (fun i => engineered t (u i)) v

/-- Null tile is null at all arity-l link-list directions of the given
total engineering weight (right now, on the Snap side). -/
lemma tile_detects (M : Tensor.T (Snap G d) ℂ l) (hs : Tensor.Sym M) (b : Fin l → Fin (d-1))
    (h : tile M (rate b)=0) (X : ∀ i, Taylor G (b i).val) :
    M (fun i => Pi.single (b i) (X i))=0 := by
  let n := rate b
  have hz : layer M n=0 := Tensor.ext_diag _ _ (layer_sym _ hs _) (fun _ _ => rfl) (funext fun A => by
    have he := tile_reads M n (expand d A)
    rw [trunks, show tile M n=0 from h, map_zero] at he
    exact (layer_leads M n (fun _ => A)).symm.trans he)
  let U : Fin l → Snap G d := fun i => Pi.single (b i) (X i)
  have hv (t : ℝ) : M (fun i => engineered t (U i))=t^n • M U := by
    have hy (i : Fin l) : engineered t (U i) = t^((b i).val+2) • U i := by
      funext j
      by_cases he : j=b i
      · rw [he]; rfl
      simp [engineered_at,U,Pi.single_eq_of_ne he]
    simp_rw [hy,M.map_smul_univ,Finset.prod_pow_eq_pow_sum]; rfl
  have he := layer_leads M n U
  rw [funext hv,lead_monomial,if_pos rfl,hz] at he
  exact he

lemma no_derivative {f : Snap G d → ℂ} (hf : ContDiffAt ℝ d f 0) (hl : l ≤ d)
    (b : Fin l → Fin (d-1)) (hb : rate b ≤ d)
    (h : ∀ J : Jet G, leading (rate b) (fun t => f (engineered t (trunk d J))) = 0)
    (X : ∀ i, Taylor G (b i).val) : iteratedFDeriv ℝ l f 0 (fun i => Pi.single (b i) (X i))=0 := by
  have he := tile_detects _ (Tensor.coeff_symm (x:=0) (hf.of_le (show (l:WithTop ℕ∞)≤d from Nat.cast_le.mpr hl))) b (no_tile hf hb h hl) X
  simpa [Tensor.coeff, smul_eq_zero, Nat.factorial_ne_zero] using he


/-! Given a graded input germ, the exact label. This constructor extracts
coordinates through *both* grades. In applications f is already a smooth
jet model. Need invariant only as germs under the constant color action. -/

private lemma cast_scale (v : Snap G d) (u : G.El) (t : ℝ) :
    Cast u (engineered t v)=engineered t (Cast u v) := funext fun _ => map_smul (Taylor.paint u) ..

/-- Only constant colors, not the local gauges. -/
structure Safe (f : Snap G d → ℂ) : Prop where
  smooth : ContDiffAt ℝ d f 0
  invariant : ∀ u : G.El, f ∘ Cast u =ᶠ[𝓝 0] f

private def script (f : Snap G d → ℂ) : Pol G :=
    ∑ k ∈ Finset.range (d+1), ∑ l ∈ Finset.range (d+1), tile (Tensor.coeff f l 0) k

private lemma tile_limited (M : Tensor.T (Snap G d) ℂ l) (h : k ≤ d) : tile M k ∈ limited G d := by
  refine (MvPolynomial.mem_restrictSupport_iff ℂ).mpr ?_
  intro i hi
  have he := tile_grade M k (MvPolynomial.mem_support_iff.mp hi)
  rw [weight_slot] at he
  exact (show height i=k from congr_arg Prod.fst he).trans_le h

private lemma script_limited (f : Snap G d → ℂ) : script f ∈ limited G d := by
  refine Submodule.sum_mem _ fun k hk => Submodule.sum_mem _ fun l _ => ?_
  exact tile_limited _ (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

private lemma script_invariant {f : Snap G d → ℂ} (h : Safe f) : script f ∈ invariantSpace G := by
  intro J u
  unfold script; rw [map_sum,map_sum]; refine Finset.sum_congr rfl fun k hk => ?_
  have hk := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp_rw [map_sum, ← leading_snap_sum h.smooth hk]
  let v (t : ℝ) := engineered t (trunk d J)
  have ht : Tendsto v (𝓝 (0:ℝ)) (𝓝 0) := by
    rw [← engineered_zero (trunk d J)]
    exact (eng_cont (trunk d J) 1).continuous.tendsto _
  have he : (fun t => f (engineered t (trunk d (colored u J)))) =ᶠ[𝓝 (0:ℝ)] (f ∘ v) := by
    filter_upwards [ht.eventually (h.invariant u)] with x hx
    have hu : trunk d (colored u J) = Cast u (trunk d J) := rfl
    rw [hu,← cast_scale]; exact hx
  exact congr_arg (fun z => (k.factorial : ℝ)⁻¹ • z) (he.iteratedDeriv_eq (n:=k))

/-- Truncated label in the *same* label space. -/
def archive {f : Snap G d → ℂ} (h : Safe f) : Label G d := ⟨script f, script_limited f, script_invariant h⟩

lemma capture {f : Snap G d → ℂ} (h : Safe f) (hk : k ≤ d) (hl : l ≤ d) :
    (gradePart (k,l) (archive h)).val=tile (Tensor.coeff f l 0) k := by
  classical
  change piece _ (script _) = _
  unfold script; rw [map_sum, Finset.sum_eq_single k]
  · rw [map_sum, Finset.sum_eq_single l]
    · exact MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same (show
        MvPolynomial.IsWeightedHomogeneous bidegree _ (k,l) from tile_grade ..)
    · intro b _ hb; exact MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne (k,l) (show
        MvPolynomial.IsWeightedHomogeneous bidegree _ (k,b) from tile_grade ..) (fun hh => hb (congr_arg Prod.snd hh).symm)
    intros H; simp [Nat.lt_succ_of_le hl] at H
  · intro b hb hb'
    rw [map_sum]; apply Finset.sum_eq_zero; intro a ha
    exact MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne (k,l) (show
      MvPolynomial.IsWeightedHomogeneous bidegree _ (b,a) from tile_grade ..) (fun hh => hb' (congr_arg Prod.fst hh).symm)
  intros H; simp [Nat.lt_succ_of_le hk] at H

lemma scaled_label_leads (L : Label G d) (hk : k ≤ d) (J : Jet G) :
    leading k (fun t => read (scaleJet J t) L.val)=
      ∑ l ∈ Finset.range (d+1), read J (gradePart (k,l) L).val := by
  classical
  let p i := ∑ l ∈ Finset.range (d+1), read J (gradePart (i,l) L).val
  have ht (t : ℝ) : read (scaleJet J t) L.val=
        ∑ i ∈ Finset.range (d+1), t^i • p i := by
    conv_lhs => rw [← Labels.decompose L]
    simp only [AddSubmonoidClass.coe_finsetSum,map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [show t^i • p i = _ from Finset.smul_sum]; refine Finset.sum_congr rfl fun l _ => ?_
    exact scaled_grade t J _ (gradePart_mem (i,l) L)
  rw [funext ht, lead_sum (n:=k) _ _ (fun i _ => (monoSmooth ..).contDiffAt)]
  simp only [lead_monomial, Finset.sum_ite_eq, Finset.mem_range.mpr (Nat.lt_succ_of_le hk),if_true]; rfl

lemma archive_read {f : Snap G d → ℂ} (h : Safe f) (hk : k ≤ d) (J : Jet G) :
    iteratedDeriv k (fun t => read (scaleJet J t) (archive h).val) 0 =
      iteratedDeriv k (fun t => f (engineered t (trunk d J))) 0 := by
  apply smul_right_injective ℂ (show (k.factorial : ℝ)⁻¹ ≠ 0 from by positivity)
  change leading k _=leading k _; rw [scaled_label_leads _ hk,leading_snap_sum h.smooth hk]
  apply Finset.sum_congr rfl; intro i hi; rw [capture h hk (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]

end YM.Planned.PrimaryIntegral295.Parts
