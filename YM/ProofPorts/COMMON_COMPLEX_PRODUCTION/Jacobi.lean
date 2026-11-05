import YM.Next.UV_STRESS.Fringe
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Slope

/-!
# Score for the normalizer of the COMMON MARGINAL in Pin

Real tables (restricted). Not the relative log-det chain expansion of the
physical global exponent and not differentiating a per-sector precision
prescription! This appearance of log(det) is only a consequence of holding
hard arguments *inside a particular connected component*. Dimension can now
be paid polynomially. Need V-entry jets for THAT marginal and its true
inverse (not principal inverse of the full table); values stay real on the
chosen derivative extension. No analyticity through actual V flag bits used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProofPorts.CommonComplexProduction.Score
open Function Filter Finset Matrix Lattice RG Wilson Precision Multi Multi.Vacuum Next.SectorChange
open MeasureTheory Gaussian Gauss Jets Puff
open scoped Topology BigOperators Classical MatrixOrder ContDiff Matrix.Norms.Frobenius

variable {I : Type} [Fintype I] [DecidableEq I]

private lemma mislay {σ : Equiv.Perm I} (he : σ ≠ 1) (i : I) : (∏ j ∈ univ.erase i,(1 : Gaussian.Table I) (σ j) j) = 0 := by
  obtain ⟨j,hj,hs⟩ : ∃ j, j≠i ∧ σ j ≠ j := by
    by_contra! hf; apply he; ext j
    by_cases ht : j=i
    · subst j; by_contra! h; exact h (σ.injective (hf (σ i) h))
    exact hf _ ht
  exact Finset.prod_eq_zero (mem_erase.mpr ⟨hj,mem_univ _⟩) (by simp [hs])

private lemma det_line {A : ℝ → Gaussian.Table I} {B : Gaussian.Table I} {x : ℝ} (h : A x=1)
    (he : ∀ i j, HasDerivAt (fun t => A t i j) (B i j) x) : HasDerivAt (fun t => (A t).det) (∑ i,B i i) x := by
  let f (σ : Equiv.Perm I) (t : ℝ) := Equiv.Perm.sign σ • ∏ i,A t (σ i) i
  have ht (σ : Equiv.Perm I) : HasDerivAt (f σ) (if σ=1 then ∑ i,B i i else 0) x := by
    have hh := (HasDerivAt.finsetProd (u:=univ) (fun i _ => he (σ i) i)).const_smul (Equiv.Perm.sign σ)
    simp only [h] at hh
    unfold f; by_cases hi : σ=1
    · subst σ; simpa only [Pi.smul_def, Equiv.Perm.sign_one,one_smul,Matrix.one_apply, Equiv.Perm.coe_one,id_eq,↓reduceIte,
        prod_const_one, ← Finset.prod_fn (s:=univ)] using hh
    have hv := mislay hi; simpa only [if_neg hi,hv,zero_smul,sum_const_zero,smul_zero,Pi.smul_def,Finset.prod_apply] using hh
  simp_rw [Matrix.det_apply]; simpa [f] using HasDerivAt.fun_sum (u:=univ) (fun i _ => ht i)

private lemma jacobi {A : ℝ → Gaussian.Table I} {B : Gaussian.Table I} {x : ℝ} (h : IsUnit (A x).det)
    (he : ∀ i j, HasDerivAt (fun t => A t i j) (B i j) x) : HasDerivAt (fun t => Real.log (A t).det)
      (∑ i,((A x)⁻¹ * B) i i) x := by
  let C t := (A x)⁻¹ * A t
  let E := (A x)⁻¹ * B
  have hc : C x=1 := Matrix.nonsing_inv_mul _ h
  have ht : HasDerivAt (fun t => (C t).det) (∑ i,E i i) x := det_line hc fun i j =>
    HasDerivAt.fun_sum (u:=univ) (fun k _ => (he k j).const_mul _)
  have hh (t) : A t=A x*C t := by unfold C; rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h, Matrix.one_mul]
  convert ((ht.const_mul (A x).det).congr_deriv rfl).log (by rw [hc,det_one,mul_one]; exact h.ne_zero) using 1
  · ext t; rw [← Matrix.det_mul, ← hh]
  rw [hc,det_one,mul_one]; unfold E; rw [mul_div_cancel_left₀ _ h.ne_zero]

lemma crest_cast {G : Gauge} {n : Side} {f : Config G n→ℝ} {U k} : Crest k (fun V => (f V : ℂ)) U ↔ Crest k f U := by
  exact ⟨fun h => Puff.into k _ (Complex.reCLM.contDiff.contDiffAt.comp (f:=(fun V => (f V:ℂ)) ∘ increment U) _ h.germ),
    fun h => Puff.into k _ (Complex.ofRealCLM.contDiff.contDiffAt.comp _ h.germ)⟩

lemma crest_tr {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {G : Gauge} {n : Side} {f : Config G n→X} {U k} (h : Crest k f U) : ContinuousAt f U := by
  obtain ⟨g,h,hg⟩:=h
  exact (h.continuousAt.comp Puff.visible.continuousAt).congr hg.symm

namespace Normalizer
variable {G : Gauge} {n : Side} {A : Config G n → Gaussian.Table I}
  {U : Config G n} {k : ℕ}

def entry (A : Config G n → Gaussian.Table I) (i j : I) (V : Config G n) : ℂ := A V i j

def smooth_table (k : ℕ) (A : Config G n → Gaussian.Table I) (U : Config G n) := ∀ i j,Crest k (entry A i j) U

lemma det_smooth (h : smooth_table k A U) : Crest k (fun x => (A x).det) U := by
  apply Puff.into
  simp_rw [comp_def,Matrix.det_apply]
  refine ContDiffAt.sum fun σ _ => ?_
  exact (contDiffAt_prod fun i _ => (crest_cast.mp (h (σ i) i)).germ).const_smul _

lemma cog (h : smooth_table (k+1) A U) (hA : IsUnit (A U).det) (v : Directions G n) :
    leftDerivs (fun W => (Real.log (A W).det:ℂ)) [v] U = ∑ i,∑ j,(((A U)⁻¹ i j:ℝ):ℂ)*leftDerivs (entry A j i) [v] U := by
  let z (t:ℝ) := increment U (t • v)
  have hf := fun i j => ((crest_cast.mp (h i j)).line [] (by simp) v).hasDerivAt
  let B := Matrix.of fun i j => leftDerivs (fun W => A W i j) [v] U
  have hi : A (z 0) = A U := by simp only [z,zero_smul,inc_zero]
  have he := (jacobi (A:=fun t => A (z t)) (B:=B) (hi.symm ▸ hA) hf).ofReal_comp.deriv
  have ht i j : leftDerivs (entry A i j) [v] U = (B i j:ℂ) := (hf i j).ofReal_comp.deriv
  rw [hi] at he
  refine he.trans ?_; simp [mul_apply,ht]

lemma slope {r c d : ℝ} {D : Directions G n → Prop}
    (hr : 0 ≤ r) (hc : 0≤c) (hd : 0≤d)
    (hs : ∀ i j, Slope k D U r d (entry A i j)) (h : ∀ i j, Band k D U r c (entry (fun x => (A x)⁻¹) i j)) (hA : IsUnit (A U).det) :
    Slope k D U (2*r) ((Fintype.card I:ℝ)^2*c*d) (fun W => (Real.log (A W).det : ℂ)) := by
  have he : smooth_table k A U := fun i j => (hs i j).read
  refine Slope.from_core (by positivity) (by positivity) (crest_cast.mpr (into k _ ((det_smooth he).germ.log (by
    change (A (increment U 0)).det ≠ 0; rw [inc_zero]; exact hA.ne_zero)))) ?_
  rintro l rfl v hv
  have h' : ∀ᶠ V in 𝓝 U, smooth_table (l+1) A V := Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => (he i j).near
  let b i j := (entry (fun x => (A x)⁻¹) i j * leftDerivs (entry A j i) [v])
  have hj (i j) : Band l D U (2*r) (c*(d*r)) (b i j) := (show r+r=2*r by ring) ▸ (h i j).crop.multiply ((hs j i).core hv)
  have he := band_comb (s:=univ) (by positivity) (fun i _ => band_comb (s:=univ) (by positivity) (fun j _ => hj i j))
  apply band_move (F:=∑ i,∑ j,b i j) (band_rise he ?_ le_rfl)
  · filter_upwards [h', (crest_tr (det_smooth (A:=A) (k:=l+1) (fun i j => (hs i j).read))).eventually_ne hA.ne_zero] with V he hq
    simpa only [b,Finset.sum_apply,Pi.mul_apply,entry] using cog he (IsUnit.mk0 _ hq) v
  simp only [sum_const,card_univ,nsmul_eq_mul]; nlinarith [mul_nonneg (mul_nonneg (show (0:ℝ)≤(Fintype.card I:ℝ)^2 by positivity) hc) (mul_nonneg hd hr)]
end Normalizer
end YM.ProofPorts.CommonComplexProduction.Score
