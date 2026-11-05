import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Selected
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Teller
import YM.AnalyticBridge.RESET_INCOME_PORT.LogQuote
import YM.AnalyticBridge.RESET_INCOME_PORT.Sheen
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.HaarOperators
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.LogAction
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Pattern
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Calendar
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Dissent
import YM.Planned.ATOM_REGULAR_ESTIMATE.Surfaced
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Jacobi
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.After




/-!
# Buying local density-score entry inputs for a physical inherited expectation

Here the actual operator is *restricted covariance*, NOT a precision
minor; on its healthy output stencil we use numerical agreements to charge
with `MarginalInputs`. No derivative of any moving or equality-boundary
flag is used. Uniform post-L entry fees at THIS order with *small t* at
every positive rank and the actual (possibly winding) reanchoring cost
from paying about ONE origin. Not the row-norm target of Book.operator,
and needs the actual alphabet for ALL sizes. Compilation as such physical
marginals & Sewn-sector identification require other suppliers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Vacuum.Jets Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score
    SelectedOrderedKernels SelectedOrderedKernels.Sector FreeResolvent Next.SectorChange.Rows Wisps
open AnalyticBridge.LocalGaussianLaws (gap_positive gapped_iff)
open AnalyticBridge.LocalGaussian (Peak)
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {A : Stores S} {o : Site c} {x t s d γ r g M Y Y' K σ : ℝ} {n R : ℕ}
    {J : Config G c → Matrix ι ι ℝ} {a : ι → Site c} {u : ℕ → ℝ}

def canopy (Z : ℝ) (R b n : ℕ) := Z*((1+(R:ℝ))^b)^n
lemma canopy_one {Z : ℝ} (h : 1≤Z) (R b n : ℕ) : 1 ≤ canopy Z R b n := one_le_mul_of_one_le_of_one_le h (one_le_pow₀ (one_le_pow₀ (by simp)))

-- K ceiling independent of extent; Z includes post-L constants only.
structure Carillon (J : Config G c → Matrix ι ι ℝ) (V : Config G c) (n : ℕ) (P : BudgetPoint) (o : Site c) (K Z t : ℝ) (R : ℕ) : Prop where
  near : ∀ᶠ W in 𝓝 V, (J W).PosDef
  peak : Peak (J V) K
  cov (i j : ι) : Slope n (P.dirBound o) V 1 (t*canopy Z R P.power n) (Normalizer.entry J i j)
  inv (i j : ι) : Slope n (P.dirBound o) V 1 (t*canopy Z R P.power n) (Normalizer.entry (fun W => (J W)⁻¹) i j)
  val (i j : ι) : ‖Normalizer.entry (fun W => (J W)⁻¹) i j V‖ ≤ canopy Z R P.power n

section sector
variable {Z : ℝ} (hZ : 1 ≤ Z) (hh : ∀ j ≤ n,tender G j P.power (s/2) 1 (u j) ≤ Z) (hs : 0<s) (hγ : 0≤γ)
    (h : SelectedOrderedKernels.Book (native c) a a Prod.fst n s γ u J V) (ht : P.threshold ≤ 2*t) (hr : ∀ i, separation (a i) o ≤ R)
include hZ hh hs hγ h ht hr
omit [DecidableEq ι] in
lemma fixed_chimes (i j : ι) : Slope n (P.dirBound o) V 1 (t*canopy Z R P.power n) (Normalizer.entry J i j) ∧ ‖Normalizer.entry J i j V‖ ≤ canopy Z R P.power n := by
  have hT := P.threshold_pos; have ht₀ : 0<t := by linarith
  let L := TestD.evaluate i j
  have hc : ContDiffAt ℝ n ((fun W => J W i j) ∘ increment V) 0 := L.contDiff.contDiffAt.comp (f:=J ∘ increment V) 0 h.smooth
  have he : Multi.Puff.Crest n (Normalizer.entry J i j) V := crest_cast.mpr (Multi.Puff.into _ _ hc)
  have hK := zero_le_one.trans (canopy_one hZ R P.power n)
  have hf (l : List (Directions G c)) (hl : l.length ≤ n) (hv : ∀ B ∈ l,P.dirBound o B) :
      ‖leftDerivs (Normalizer.entry J i j) l V‖ ≤ tender G l.length P.power (s/2) t (u l.length)* ((1+(R:ℝ))^P.power)^l.length := by
    have hh : Normalizer.entry J i j=Complex.ofRealCLM ∘ (fun W => J W i j) := rfl
    have he := (h.entries l hl ht hs hv).1 i
    have hcc := tender_nn (G:=G) (j:=l.length) P.power (half_pos hs) ht₀.le (h.nonneg _ hl)
    have hx := Finset.single_le_sum (s:=Finset.univ) (a:=j) (f:=fun j => Wisps.rate γ (separation (a i) (a j)) * |leftDerivs (fun V => J V i j) l V|) (fun j _=>by have := rate_pos γ (separation (a i) (a j)); positivity) (Finset.mem_univ _)
    rw [hh, Push.Local.left_linear Complex.ofRealCLM l hc hl]; change ‖((leftDerivs (fun W => J W i j) l V:ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real]; refine (le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))).trans (hx.trans (he.trans ?_))
    unfold Mark.hill; change _ * ((1+(separation (a i) o:ℝ))^P.power)^l.length ≤ _; gcongr; exact hr i
  refine ⟨⟨he,zero_le_one,mul_nonneg ht₀.le hK,fun l hl hv hL => ?_⟩,?_⟩
  · refine (hf l hv hL).trans ?_
    let d := tender G l.length P.power (s/2) 1 (u l.length)
    rw [show tender G l.length P.power (s/2) t (u l.length)=t*d by unfold d tender; simp [hl]; ring,one_pow,mul_one]
    have he := mul_le_mul (hh l.length hv) (pow_le_pow_right₀ (one_le_pow₀ (by simp)) hv : ((1+(R:ℝ))^P.power)^l.length ≤ _) (by positivity) (zero_le_one.trans hZ)
    unfold canopy; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left he ht₀.le
  have h0 := hf [] (Nat.zero_le _) (fun _ hj => (List.not_mem_nil hj).elim)
  simp only [List.length_nil,leftDerivs,tender,pow_zero,↓reduceIte,mul_one] at h0
  have hh := hh 0 (Nat.zero_le _); simp only [tender,pow_zero,↓reduceIte,mul_one] at hh
  exact (h0.trans hh).trans (le_mul_of_one_le_right (zero_le_one.trans hZ) (one_le_pow₀ (one_le_pow₀ (by simp))))
end sector

def peal (G : Gauge) (n b : ℕ) (d s M r Y g Y' : ℝ) := ∑ j∈Finset.range (n+1),(|kernelTax G n j b 0 d 1 (covFee G n j M r Y)| + |kernelTax G n j b 0 s 1 (invFee G n j M r Y g Y')|)
def peakCost (G : Gauge) (n : ℕ) (M r Y : ℝ) := 1+|covFee G n 0 M r Y|

lemma ringing (h : MarginalInputs T x A F k V n d M s r Y g Y') (hg : 0<g) (ht : P.threshold=temp x) (e : ι ↪ In x A F (G:=G)) (hr : ∀ i,separation (front A F (e i)) o ≤ R) :
    let Z := 1+peal G n P.power d s M r Y g Y'
    Carillon (eddy T x A F k e) V n P o (peakCost G n M r Y) Z (fiery G x S.patch.L) R := by
  intro Z
  have hc (j) (hj : j ≤ n) := Finset.single_le_sum (s:=Finset.range (n+1)) (a:=j) (f:=fun j => |kernelTax G n j P.power 0 d 1 (covFee G n j M r Y)| + |kernelTax G n j P.power 0 s 1 (invFee G n j M r Y g Y')|) (fun j _ => by positivity) (Finset.mem_range.mpr (by omega))
  simp only [kernelTax,Nat.cast_zero,add_zero,one_pow,mul_one] at hc
  have hZ : 1≤Z := le_add_of_nonneg_right (by unfold peal; positivity)
  have h' := h.priced.C.part e.injective
  have hI := h.priced.slices e e.injective 0 le_rfl; rw [eddy_is] at hI
  have hv : ContinuousAt (eddy T x A F k e) V := crest_tr (Puff.into n _ h'.smooth)
  have hz (V : Config G c) : (eddy T x A F k e V).IsSymm := (show (covariance T x A F k V).IsSymm from by
    unfold SelectedOrderedKernels.Sector.covariance fog Schur.clouded Matrix.IsSymm; rw [transpose_smul,transpose_add,transpose_transpose,add_comm]).submatrix _
  have he := h.ops e e.injective |>.1
  have hp := h'.zeroth; unfold eddy
  have hd := narrow_pos n h.priced.d_pos; have hs := narrow_pos n h.priced.δ_pos;
  refine ⟨?_, (Peak.from_rows (SelectedOrderedKernels.Sector.got_schur hp) (by have := h.priced.d_pos; positivity)).mono ?_,fun i j => ?_,fun i j => ?_,fun i j => ?_⟩
  · filter_upwards [hv.eventually (AnalyticBridge.RelativeLogdet.Differential.holds (A:=id) continuousAt_id he (g/2) (half_lt_self hg) (native c) (front A F ∘ e))] with v hp
    exact gap_positive (hz _) hp (half_pos hg)
  · unfold peakCost covFee; exact (le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)
  all_goals first | refine (fixed_chimes hZ ?_ hd (by have := h.priced.d_pos; positivity) h' (ht.symm ▸ h.scale) hr i j).1 | refine (fixed_chimes hZ ?_ hs (by have := h.priced.δ_pos; positivity) hI (ht.symm ▸ h.scale) hr i j).1 | refine (fixed_chimes hZ ?_ hs (by have := h.priced.δ_pos; positivity) hI (ht.symm ▸ h.scale) hr i j).2
  all_goals intro j hj; have HH := hc j hj; unfold Z peal; simp only [kernelTax,Nat.cast_zero, add_zero, one_pow,mul_one]; first | exact (le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans (HH.trans (le_add_of_nonneg_left zero_le_one))) | exact (le_abs_self _).trans ((le_add_of_nonneg_left (abs_nonneg _)).trans (HH.trans (le_add_of_nonneg_left zero_le_one)))
end YM.PhysicalNext.JointLoad.Heir
