import YM.Next.WARD_BIN.Stencils
import YM.Planned.PRIMARY_INTEGRAL_295.FlatCancel
import YM.Work.G06.Formula


/-!
# The actual unscaled canonical columns

Both bidegrees exact.

The block kernel has
to pay for every other term, including remainders on wrapping supports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Place
open Function Filter Lattice Labels Source Source.Drops RG Wilson WardBin MeasureTheory Next.Foundations
open scoped BigOperators ContDiff Topology Matrix.Norms.Frobenius
variable {G : Gauge} {d n l : ℕ} {F : Labels.Frame G d} {S : Finset Cover}

def copy (F : Labels.Frame G d) (i : F.Index) : F.Coeff := Pi.single i 1

def slant (T : SectionData F) (v : F.Coeff) : Dev T.stencil G → ℂ := T.evaluate v ∘ pore

/-- Unscaled canonical basis address, on logarithmic increments. -/
def column (T : SectionData F) (i : F.Index) : Dev T.stencil G → ℂ := slant T (copy F i)

lemma lead_probe (H : Hol G) (T : SectionData F) (hT : T.Sound H) (i : F.Index) (k : ℕ) (hk : k≤d) (J : Jet G) :
    leading k (fun t => T.evaluate (copy F i) (H.links d J t))=
      if k=(F.grades i).1 then read J (F.basis i).val else 0 := by
  obtain ⟨hX,hY,ht⟩ := hT.projects (copy F i) J
  have hp := ht k hk
  rw [show F.coords.symm (copy F i)=F.basis i from F.coords.injective (by rw [F.coords.apply_symm_apply,F.coords_basis]; rfl)] at hp
  have he (t : ℝ) : read (scaleJet J t) (F.basis i).val=t^(F.grades i).1 • read J (F.basis i).val := scaled_grade t J _ (F.pure i)
  calc leading k _ = leading k (fun t => read (scaleJet J t) (F.basis i).val) := congr_arg ((k.factorial:ℝ)⁻¹ • ·) hp
       _ = _ := by rw [funext he]; exact lead_monomial ..

section Smooth
variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma polynomial_smooth (P : MvPolynomial α ℂ) (f : E→α→ℂ) (hf : ∀ i,ContDiff ℝ ω (fun x=>f x i)) :
    ContDiff ℝ ω fun x => MvPolynomial.aeval (f x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.aeval_C]; exact contDiff_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul,MvPolynomial.aeval_X]; exact hp.mul (hf i)

lemma pore_entry (k : Source.Index G S) : ContDiff ℝ ω (fun w : Dev S G => entry (pore w) k) := by
  rcases k with ⟨⟨p,h⟩,i,j,b⟩
  let v : Spot S := ⟨(⟨p.1,h.1⟩,p.2),h.2⟩
  have he : ContDiff ℝ ω (fun w : Dev S G => G.mat (pore w p) i j) := by
    let L : G.Mat →L[ℝ] ℂ := LinearMap.toContinuousLinearMap { toFun A := A i j, map_add' _ _ := rfl, map_smul' _ _ := rfl }
    have hf : ContDiff ℝ ω (fun w : Dev S G => G.mat (pore w p)) := by
      unfold pore; simp only [dif_pos h]
      exact G.exp_jet.comp (contDiff_apply ℝ G.Color v)
    exact L.contDiff.comp hf
  cases b; · exact he
  exact ((starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff).comp he

lemma entry_poly_smooth {f : CoverConfig G → ℂ} (h : Work.G06.EntryPoly S f) :
    ContDiff ℝ ω (f ∘ pore (S:=S)) := by
  obtain ⟨P,h⟩ := h; rw [← funext h]
  exact polynomial_smooth P (fun x => entry (pore x)) pore_entry

lemma slant_smooth (T : SectionData F) (v : F.Coeff) : ContDiff ℝ ω (slant T v) :=
    entry_poly_smooth (S:=T.stencil) (f:=T.evaluate v) ⟨T.evalC _,fun _ => rfl⟩
lemma column_smooth (T : SectionData F) (i : F.Index) : ContDiff ℝ ω (column T i) := slant_smooth ..

end Smooth

/-- Factor degree here is true vanishing in ordinary link increments. -/
private lemma factor_outer {V : Type} [Fintype V] (P : MvPolynomial V ℂ)
    (H : ∀ m∈P.support,l ≤ m.sum fun _ j => j) (hl : n < l) :
    iteratedFDeriv ℝ n (fun x : V → ℂ => MvPolynomial.aeval x P) 0=0 := by
  classical
  let F (x : V → ℂ) := MvPolynomial.aeval x P
  have hf : ContDiffAt ℝ n F 0 := (polynomial_smooth P (fun a : V → ℂ => a) (fun i => contDiff_apply ℝ ℂ i)).contDiffAt.of_le le_top
  have he (A : V → ℂ) : leading n (fun t : ℝ => F (t • A))=0 := by
    let f (m : V →₀ ℕ) := m.prod (fun i k => (A i)^k)
    let deg (m : V →₀ ℕ) := m.sum fun _ j => j
    have ht (t : ℝ) : F (t • A)=∑ m∈P.support,t^(deg m) • (P.coeff m*f m) := by
      unfold F; rw [MvPolynomial.aeval_def,MvPolynomial.eval₂_eq]; refine Finset.sum_congr rfl fun m _ => ?_
      unfold f deg Finsupp.sum Finsupp.prod
      simp only [Complex.real_smul,Pi.smul_apply,Complex.ofReal_pow,mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
      simp only [Algebra.algebraMap_self,RingHom.id_apply]; ring
    rw [funext ht, lead_sum (n:=n) _ _ (fun _ _ => (monoSmooth ..).contDiffAt)]
    exact Finset.sum_eq_zero fun i hi => by
      rw [lead_monomial, if_neg (show n≠deg i from (hl.trans_le (H i hi)).ne)]
  have h0 : Tensor.coeff F n 0 = 0 := Tensor.ext_diag _ _ (Tensor.coeff_symm hf) (fun _ _ => rfl)
    (funext fun x => (leading_tensor x F hf).symm.trans (he x))
  change iteratedFDeriv ℝ n F 0=0
  simpa [Tensor.coeff,Nat.factorial_ne_zero] using h0

lemma radials_vanish (T : SectionData F) (h : Bid.pop T) (i : F.Index) (k : ℕ) (hk : k < (F.grades i).2) :
    iteratedFDeriv ℝ k (column T i) 0=0 := by
  classical
  obtain ⟨m,B,hB,P,hP,hL⟩ := h i
  let E := (Fin m × G.ColorIndex) → ℂ
  let g (x : E) : ℂ := MvPolynomial.aeval x P
  let Z (w : Dev T.stencil G) : E := fun a => (((B a.1).eval (pore w) a.2 : ℝ) : ℂ)
  have hf : column T i=g ∘ Z := by unfold column slant copy; rw [hP]; rfl
  have hZ : Z 0=0 := by
    funext a
    unfold Z; simp only [pore_zero]
    unfold Slot.eval; rw [show faceValue (1:CoverConfig G) _=1 from Pressure.one _,G.curvature_unit,map_zero]
    simp; rfl
  have hs : ContDiffAt ℝ ω Z 0 := contDiffAt_pi.mpr fun a =>
    (entry_poly_smooth (Work.G06.entryPoly_slot (B a.1) (hB a.1) (G:=G) a.2)).contDiffAt
  have hg : ContDiffAt ℝ ω g (Z 0) := (polynomial_smooth P (id (α:=E)) (fun j => contDiff_apply ℝ ℂ j)).contDiffAt
  ext v
  rw [hf,Cases.compReads hg hs le_top]; apply Finset.sum_eq_zero; intro b _
  rw [Cases.caseRead,hZ,show iteratedFDeriv ℝ b.length g 0=0 from factor_outer P hL (b.length_le.trans_lt hk)]; rfl

/-- Through all Snap engineering qualifications at the actual frame. -/
theorem lower (H : Hol G) (T : SectionData F) (hT : T.Sound H) (i : F.Index) (w : Fin n → ℕ) (hw : ∑ j,w j < (F.grades i).1)
    (u : Fin n → Potential G) (hu : ∀ j,u j∈rangeLt (Axis→G.Color) (w j)) :
    iteratedFDeriv ℝ n (column T i) 0 (fun j => ping _ (u j))=0 := by
  refine cancellation (f:=T.evaluate (copy F i)) (T.cylinder_local _) (hT.gaugeInvariant _) H
    (ContDiffAt.of_le (column_smooth T i).contDiffAt le_top) ?_ ((F.bound i).trans d.le_succ) _ hw u hu
  intro J k hk; rw [lead_probe H T hT i k (hk.le.trans (F.bound i)),if_neg hk.ne]

end YM.Planned.PrimaryIntegral295.Place
