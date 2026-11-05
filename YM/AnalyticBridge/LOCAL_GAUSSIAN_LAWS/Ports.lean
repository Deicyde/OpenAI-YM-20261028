import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Margins
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.TotalCost
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay


/-!
# A nonextensive use: any local probes on the active cloud

Standalone likelihood comparison about the **two actual clouds** with b
price already discharged, exact shift, dimension depends only on read set.
No extraneous factor exp(dim) which would kill e^{-c_L B} for local
vol~B^4. Keep weight on inverse difference and logdet sign. Includes
arbitrary subcollections (sets represented by embeddings in measurement
space), not recomputing their C; uses Margins's proved exact projection.
Use before unioning the probes, never claim this permits multiplying as
if independent. Not a bound on scalar *ledger* pressure from the change,
nor on unbounded complements of hard probes; here any bounded Borel (real;
complex separately if needed) at each local read, receiving both licenses.
The caller must prove those hypotheses if feeding in actual factors.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory ProbabilityTheory Matrix
open Bid Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Oriented 
open Next SectorChange SectorChange.Rows SectorChange.Gaussian Wisps
open FreeResolvent
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal
namespace Density
variable {m n α : Type} [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]

section prices
variable {D : Cost α} {p : n→α} {A B : SectorChange.Gaussian.Table n}

/-- If A and B and every requested margin's inverse have Schur budget C,
at sufficiently small e, replacing A by B costs polynomial in that same C
and read dimension (not sites), *even with translations*. This first
states on any one test space (caller then applies to every margin). -/
lemma shift_size {s e C t : ℝ} (hs : 0 ≤ s) (he : 0 ≤ e) (hf : e ≤ 1) (hC : 0 ≤ C)
    (hAC : D.Schur p p s C A⁻¹) (hA : A.PosDef) (hB : B.PosDef)
    (hAQ : D.Schur p p s (C^2*e) (A⁻¹-B⁻¹)) (hD : |Real.log (B.det/A.det)| ≤ Fintype.card n * (2*C*e))
    {u : n→ℝ} (hx : ∀ i, |u i| ≤ e*t) (z : n→ℝ) :
    |Real.log (replace A B u z)| ≤
      e*(C*Fintype.card n*(1+t^2)+(C^2+C)*energy z) := by
  have hi : A⁻¹.IsSymm := Matrix.isHermitian_iff_isSymm.mp hA.inv.isHermitian
  have hm := hAC.mono hs le_rfl
  have h (z u : n→ℝ) : u ⬝ᵥ (A⁻¹ *ᵥ z) = z ⬝ᵥ (A⁻¹ *ᵥ u) := by rw [← hi.eq,Matrix.dotProduct_transpose_mulVec,hi.eq,dotProduct_comm]
  have hg := schur_qf D p (hAQ.mono hs le_rfl) z
  rw [replace_income _ _ hA hB,spice,force,force, Matrix.mulVec_add,add_dotProduct,dotProduct_add,dotProduct_add,h z u]
  apply (abs_add_le ..).trans
  rw [show (z ⬝ᵥ (B⁻¹ *ᵥ z))/2-((z ⬝ᵥ (A⁻¹ *ᵥ z)+z ⬝ᵥ (A⁻¹*ᵥu))+(z ⬝ᵥ (A⁻¹*ᵥu)+u ⬝ᵥ (A⁻¹*ᵥu)))/2=
    -((z ⬝ᵥ ((A⁻¹-B⁻¹)*ᵥ z))/2+z ⬝ᵥ (A⁻¹*ᵥu)+(u ⬝ᵥ (A⁻¹*ᵥu))/2) from (by rw [Matrix.sub_mulVec,dotProduct_sub]; ring),abs_neg]
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  apply le_trans (add_le_add (mul_le_mul_of_nonneg_left hD (by norm_num : (0:ℝ)≤1/2)) (abs_add_le ..))
  apply le_trans (add_le_add_right (add_le_add_left (abs_add_le _ _) _) _)
  rw [abs_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  by_cases h0 : e=0
  · rw [h0] at hg hx ⊢
    have hu : u=0 := funext fun i => abs_eq_zero.mp (le_antisymm ((hx i).trans_eq (zero_mul _)) (abs_nonneg _))
    rw [mul_zero,zero_mul] at hg
    simpa [hu] using div_nonpos_of_nonpos_of_nonneg hg (zero_le_two)
  let v := e⁻¹ • u
  have hu : u=e • v := by unfold v; rw [smul_smul,mul_inv_cancel₀ h0,one_smul]
  have hv i : |v i| ≤ t := by
    change |e⁻¹ * u i| ≤ _
    rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr he)]
    exact (mul_le_mul_of_nonneg_left (hx i) (inv_nonneg.mpr he)).trans_eq (by rw [← mul_assoc,inv_mul_cancel₀ h0,one_mul])
  let N := (Fintype.card n:ℝ)
  have hh : v ⬝ᵥ v ≤ N*t^2 := calc
    _ ≤ ∑ _i : n,t^2 := Finset.sum_le_sum fun i _ => by rw [← sq,← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg (v i)) (hv i) _
    _ = _ := by unfold N; simp
  rw [hu,Matrix.mulVec_smul,dotProduct_smul,smul_dotProduct,dotProduct_smul]; simp only [smul_eq_mul, abs_mul,abs_of_nonneg he]
  have hb := mixed hm z v
  have ht := schur_qf D p hm v
  have hx0 := normSum_nn z
  unfold energy; change 1/2*(N*_) + _ ≤ e*(C*N*_+_)
  calc
    _ ≤ 1/2*(N*(2*C*e)) + (C^2*e*(z ⬝ᵥ z)/2+e*(C*((z ⬝ᵥ z)+(N*t^2))/2)+e*(e*(C*(N*t^2)))/2) := by
      gcongr
      · exact hb.trans (by gcongr)
      · exact ht.trans (by gcongr)
    _ ≤ _ := by
      have hi : 0≤e*C*(N*t^2) := by unfold N; positivity
      have h₁ := mul_le_of_le_one_left hi hf
      have h₂ : 0 ≤ e*((C^2+C)*(z ⬝ᵥ z)) := by positivity
      linarith -- nonlinear

/-- Package local probe estimate with its two exact covariance receipts.
Still supply inverse Schur; follow by deriving it from Closes at *any*
site subset. D covariance-cost not necessarily on Site (native case).
Keep explicit shift from means or from any other priced b on this stencil.
-/
theorem countHeal {s e C t : ℝ} (hs : 0 ≤ s) (he : 0 ≤ e) (hC : 1 ≤ C) (hd : C*e ≤ 1/2)
    (hA : A.PosDef) (hB : B.PosDef)
    (hAQ : D.Schur p p s C A) (hAC : D.Schur p p s C A⁻¹)
    (hBQ : D.Schur p p s C B) (hBC : D.Schur p p s C B⁻¹)
    (hx : D.Schur p p s e (A-B)) (u : n→ℝ) (hk : ∀ i,|u i| ≤ e*t) :
    let N : ℝ := Fintype.card n
    (∀ z, |Real.log (replace A B u z)| ≤ e*(C*N*(1+t^2)+(C^2+C)*energy z)) ∧
      ∀ (T : n → ℝ) (F : (n→ℝ)→ℝ) (M : ℝ), 0 ≤ M → Measurable F → (∀ x, |F x| ≤ M) →
      |(∫ y,F (T+y)∂cloud A) - ∫ y,F (T+u+y)∂cloud B| ≤ e*M*(2*C*N*(1+t^2)+2*(C^2+C)*(N*C)) := by
  intro N
  have hc : 0 ≤ C := zero_le_one.trans hC
  have h0 : e≤1 := by nlinarith
  have fees {A B : SectorChange.Gaussian.Table n} (hA : A.PosDef) (hB : B.PosDef)
      (ha : D.Schur p p s C A⁻¹) (hb : D.Schur p p s C B⁻¹) (h : D.Schur p p s e (A-B)) {u : n→ℝ} (hx : ∀ i, |u i| ≤ e*t) (z) :=
    let hi : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hA.isUnit
    let ht : IsUnit B.det := B.isUnit_iff_isUnit_det.mp hB.isUnit
    have hh : D.Schur p p s (C^2*e) (A⁻¹-B⁻¹) := by
      rw [show A⁻¹-B⁻¹=-(A⁻¹*(A-B)*B⁻¹) from ?_]
      · exact (((ha.mul h hs hc he).mul hb hs (mul_nonneg hc he) hc).neg).mono le_rfl (le_of_eq (by ring))
      rw [Matrix.mul_sub,Matrix.sub_mul,A.nonsing_inv_mul hi,Matrix.one_mul,Matrix.mul_assoc,B.mul_nonsing_inv ht,Matrix.mul_one]; abel
    have hF : D.Schur p p s (C*e) (A⁻¹*B-1) := by
      rw [show A⁻¹*B-1=-(A⁻¹*(A-B)) from ?_]; exact (ha.mul h hs hc he).neg
      rw [Matrix.mul_sub,A.nonsing_inv_mul hi]; abel
    have hL := log_payment hA.inv hB hs (mul_nonneg hc he) hd hF
    have hD : |Real.log (B.det/A.det)| ≤ N*(2*C*e) := by
      rw [Real.log_div hB.det_pos.ne' hA.det_pos.ne']
      rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv,Real.log_inv,← sub_eq_add_neg,← mul_assoc 2] at hL; exact hL
    shift_size hs he h0 hc ha hA hB hh hD hx z
  have hv := fees hA hB hAC hBC hx hk
  refine ⟨hv,fun Y f M hm hf hb => ?_⟩
  let F (z) := f (Y+z)
  have hi : D.Schur p p s e (B-A) := by rw [← neg_sub]; exact hx.neg
  have hl := fees hB hA hBC hAC hi (u:=-u) (fun i => by simpa using hk i)
  have H := contrast A B hA hB u F (hf.comp (by fun_prop : Measurable (fun x : n→ℝ => Y + x))) hm (P:=C*N*(1+t^2)) (T:=C^2+C) (by unfold N; positivity) (by positivity) he (fun i => hb _) hv hl
    (overspend hA hAQ) (overspend hB hBQ)
  simpa only [F,add_comm,add_left_comm,add_assoc,mul_assoc] using! H
end prices

/-- Uniform prices for arbitrary injection of sites (*in this currency*
there is no K^dimension). In particular don't require the chosen set to
be itself a window or contain one, just read entries of same C before
compressing! This is about the corner law, not a resolvent's restriction.
-/
structure Compression (A : SectorChange.Gaussian.Table n) (D : Cost α) (p : n → α) (s C : ℝ) : Prop where
  pos : A.PosDef
  alls {m : Type} [Fintype m] [DecidableEq m] (e : m ↪ n) :
    let H := A.submatrix e e
    let y := p ∘ e
    H.PosDef ∧ D.Schur y y s C H ∧ D.Schur y y s C H⁻¹











lemma billed (e : m ↪ n) {Q : SectorChange.Gaussian.Table n} (hQ : Q.PosSemidef) (f : (m→ℝ)→ℝ) (hf : Measurable f) :
    (∫ z,f (z ∘ e)∂cloud Q)=∫ z,f z∂cloud (Q.submatrix e e) := by
  have H := sample e hQ
  rw [← H.map_eq]
  exact (integral_map H.measurable.aemeasurable hf.aestronglyMeasurable).symm


end Density
end YM.AnalyticBridge.LocalGaussianLaws
