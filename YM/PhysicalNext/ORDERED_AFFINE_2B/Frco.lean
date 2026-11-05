import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Period
import YM.Next.WARD_BIN.Valorem
import YM.PhysicalNext.ORDERED_AFFINE_2B.Fsct
import YM.Push.RELAY_DIFFERENCE.Rolling
import YM.Push.STATIONARY_UNIFORM.Along
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Hosted

/-!
# Issuing Frco's ordered derivatives on the SAME literal sector

After displacement by the physical mean, include BOTH log/ratio terms
(correct signs) in their orientation order. The constant is a SUM of
local squares with all stencil outputs, slip weights and affine columns
at the SAME readout. Identity completion outside Gaussian-charted
coordinates used in stack sends NO independent Haar variables to this
factor. The mean and C are those of this window, not a projection of the
flat-sector Gaussian. Use Literal Receipt signs even if later there are
subtractions not on these stencils. `Frco` paid entries in `Currency` etc
before Z multiplier uses; no polynomial endpoint summation in actual Z
being priced here. Epoch readiness before promoting to global recipes...
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Whole.Frco
open Function Filter Lattice Wilson RG Precision Pressure Exterior Tree
open AnalyticBridge AnalyticBridge.ResetIncome SectorTools.ActualScalar SectorNext.Vacuum
open Next Next.Foundations Next.SectorChange Completion
open ProjectorNext.Equivariance (HasOrderAt)
open Further Further.CurvedGaussianJets Jets ChangeV Tracks MeasureTheory Set
open Push.SectorMeasure Matrix Book
open Footprint.Padded (widen)
open scoped Topology ContDiff InnerProductSpace BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}

section read
variable (T : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (k : S.Choices)
    (χ : Chi) (d g : ℝ) (Y : LinkArray G (Frozen A x F))

def pace (z : Next.SectorChange.Prices G (Active A x F)) (U : Config G c) :=
    (∑ i, Fixed.debit T x A F k χ d Y g U i)+ (Fixed.eta T x A F k χ d Y g U ⬝ᵥ z)+ (z ⬝ᵥ (Fixed.mismatch T x A F k U *ᵥ z))/2

-- vector in active; Gaussian is centered BEFORE calling
abbrev trawl (z : Thing G f → ℝ) : Next.SectorChange.Prices G (Active A x F) := z ∘ enterAt G x A F
end read
variable {A : Stores S} {F : Forest S.ratio} {T : Tube G S} {k : S.Choices}
    {x g s σ d δ M : ℝ} {χ : Chi} {J : Tab} {q n : ℕ} {l : Word G c} {V : Config G c}
    {Y : LinkArray G (Frozen A x F)}





lemma one_pull (v : Next.SectorChange.Prices G (Active A x F)) (z : Thing G f → ℝ) :
    v ⬝ᵥ trawl x A F z = (Footprint.Padded.widen x A F v) ⬝ᵥ z := by
  unfold dotProduct
  conv_rhs => rw [← Equiv.sum_comp (sorted A F (G:=G) (x:=x)), Fintype.sum_sum_type]
  simp_rw [Footprint.Padded.widen_at]; simp

private lemma twice {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (e : α ⊕ β ≃ γ) (z : γ → ℝ) (M C : Gaussian.Table α) :
    let u := z ∘ e ∘ Sum.inl
    u ⬝ᵥ ((C - M) *ᵥ u) = z ⬝ᵥ ((Joint.place e (wide C 1)-Joint.place e (wide M 1)) *ᵥ z) := by
  intro u; change CurvedGaussianJets.quad (C-M) u = CurvedGaussianJets.quad _ z
  let L : Gaussian.Table β:=1
  rw [show Joint.place e (wide C L)-Joint.place e (wide M L)=Joint.place e (Joint.join (C-M) (L-L)) from by
    rw [Joint.join_sub,Joint.place_sub]; rfl,Joint.place_form,Joint.join_form]
  simp [CurvedGaussianJets.quad]; rfl

lemma two_pull (C M : Gaussian.Table (Rows.In x A F (G:=G))) (z : Thing G f→ℝ) :
    let q:=trawl x A F z
    q ⬝ᵥ ((C-M) *ᵥ q)= z ⬝ᵥ ((identityPut x A F C-identityPut x A F M)*ᵥ z) := twice (sorted A F) z M C

section invoices
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : Type} [Fintype ρ]
  (W : Windows ι) (C : Jets.Field G c ι)

def quadResume (l : Word G c) (V : Config G c) (i j : ι) := ∑' d, ∑ p : Run ι (d+2), ends i j p (leftDerivs (pushQuad W C p) l V)
private lemma invoiced {p : CurvedGaussianJets.Prices} {a : ι → Site f} {s : Weights a} {N} {M K} {P : Directions G c → Prop}
    (h : ∀ᶠ U in 𝓝 V, Street p s n P C U M) (hb : W.Includes a N) (hp : Port p s n M K N) (z : ι → ℝ)
    (f : Config G c → ρ → ℝ) (g : Config G c → ι → ℝ) {F : Config G c → ℝ} (hf : ∀ i,Within P n (fun u=> f u i) V)
    (hg : ∀ i, Within P n (fun u=> g u i) V) (he : ∀ᶠ U in 𝓝 V, F U=(∑ i,f U i) + g U ⬝ᵥ z + z ⬝ᵥ (((covariance W C U)⁻¹-C U) *ᵥ z)/2) (hl : l.length≤n) (hL : ∀ i∈l,P i) :
    leftDerivs F l V = (∑ i,leftDerivs (fun u=> f u i) l V) + (∑ i,z i * leftDerivs (fun u=>g u i) l V) +
      ∑ i, ∑ j, (z i*z j/2)*quadResume W C l V i j := by
  have hh := hp.read h hb
  let T := ρ ⊕ ι ⊕ ι × ι
  let X := fun (i : ι × ι) U=> ((covariance W C U)⁻¹-C U) i.1 i.2
  let Gfee : T → ℝ := Sum.elim (fun _=> 1) (Sum.elim z (fun i=> z i.1*z i.2/2))
  let Gentries : T → _ := Sum.elim (fun i u=> f u i) (Sum.elim (fun i u=>g u i) X)
  have he' : F =ᶠ[𝓝 V] fun u=> ∑ i,Gfee i*Gentries i u := he.mono fun u hu=> by
    unfold Gfee Gentries T; rw [hu]; simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,one_mul,Fintype.sum_prod_type]
    rw [←add_assoc]; unfold dotProduct; congr 1
    · simp only [mul_comm]
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mulVec,dotProduct,Finset.mul_sum,Finset.sum_div,X]; exact Finset.sum_congr rfl fun j _=> by ring
  have hU := h.self_of_nhds
  have hk (i : T) : Within P n (Gentries i) V := by
    rcases i with i|i|i; exact hf i; exact hg i
    exact Book.allowed ((((hU.covariance W).inv hh.positive.isUnit).minus hU.good) i.1 i.2)
  rw [Jets.left_on he', Within.coin Gfee Gentries hk hl hL]
  simp only [Gfee,Gentries,T,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type,one_mul]
  have hX i j := (hh.assemble l hl hL i j).2.2
  simp_rw [X, hX]; unfold quadResume; abel
end invoices

section pricing
variable (Y : LinkArray G (Frozen A x F)) (z : Thing G f→ℝ) (hg : 0 < g)
    (h : Fixed.Fees T x A F k χ d V n s δ M) (hp : J.Ships q n σ T F A k x V)

-- report genuine finite-order smoothness as well as enrolling
-- the ordered letters, BEFORE any integration of field ratios.
include h hp hg


theorem epoch (hl : l.length ≤ n) :
    let W:= windows S G x hp.tall; let C:= charter T x A F k
    leftDerivs (pace T x A F k χ d g Y (trawl x A F z)) l V = (∑ i,leftDerivs (fun u=> Fixed.debit T x A F k χ d Y g u i) l V) +
      (∑ i,z i * leftDerivs (fun u=> widen x A F (Fixed.eta T x A F k χ d Y g u) i) l V) + ∑ i, ∑ j,(z i*z j/2)*quadResume W C l V i j := by
  intro W C
  obtain ⟨z₁,hz,hr⟩ := Fsct.any_due S l q
  obtain ⟨h₁,h₂⟩ := (h.quotes Y).2.2.2.2.2 g hg
  refine invoiced W C (hp.street_cost true 0 hz) (spent S G x hp.tall).1 (hp.port 0 hz) z _ _ (fun i=>Book.allowed (h₁ i).smooth)
    (fun i=> Book.allowed ?_) (hp.retained.mono (fun u hu=> ?_)) hl hr
  · obtain ⟨(i|i),rfl⟩ := (sorted A F (G:=G) (x:=x)).surjective i <;> simp_rw [Footprint.Padded.widen_at]
    · exact (h₂ i).smooth
    exact contDiffAt_const
  unfold pace; rw [one_pull]; congr 1
  unfold C W; rw [hu.2.1,plinth]; exact congr_arg (·/2) (two_pull _ _ z)
end pricing
end YM.PhysicalNext.OrderedAffine2B.Whole.Frco
