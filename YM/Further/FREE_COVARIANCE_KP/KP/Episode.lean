import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Fuels
import YM.Further.FREE_COVARIANCE_KP.KP.Native
import YM.Next.FREE_KERNELS.Hall
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04


/-!
# Actual periodic ancestry D covariances, KPcol to kper

P_j, : Joint theorem per_cost here (K argument
`k : ℝ`, positive hedge penalty, not weak-stage index). `found` below
has actual unmodified D from Train; at any J≥4, across trains (hence all
applicable earlier areas/repeats/*lengths*), normalized 4D radian
clipped torus as at calibration. Positive axes; no color normalization
inserted here (color-diagonal Deg `Trace.rocket`). Comparing to
Maxwell.bareCurl (two-curl Green out in normalization ;
see YM.Next.MAXWELL.House). For Page/Tags etc using 
all-high cross tests, applies in native units with n at alignment
scale; NOT comparing analytic transfer terms here. Costs ∃C after
J/penalty/orders. Separate debt to buy C for a running regulator.

Proof map of KP:

* Frequency price from Width using the actual p≠0 recipe garnet
  (Gram & strip to punctured Weight): Weight/Plain/Floor/Core/Gem/Alloy.
  Firm brought from Heart in this file, with  equivalence on mesh
  by rotor identities. Elementwise costs. P(0)=0 for torus in use.
* Cut at 5π/4 and telescope, subtract continuum low Maxwell symbol with a
  Gaussian cutoff. Multiplier prices before summing/integrating (ivory).
  See House & Cold. Differences left first / right endpoint opposite lag
  (`Native.spin_lag`).
* Decay of symbol-discrepancy integral: Snow & Hill. Split once at t=1/‖x‖,
  estimate inner ball absolutely & integrate by parts l+5 times outside;
  near overlap and all derivatives estimated with `snow`. Absolute
  integrations, no distributional assertions. This bounds discrepancy with
  continuum regularized retrieval, including BOTH endpoint differences.
* The regularized continuum one itself (including the joint partials):
  Field/Growth/Ride/Petals. Fourier integrate Green with the Gaussian cutoff
  by heat integrals, then differentiate, use normalization on bareCurl; tail
  costs on sphere/outside. No claims on Conf contacts!
* Integration error from true periodic counting after smoothed telescope:
  Tile/Slope. Cost inclusive of clipped at zero gapless. Total Native.k_per
  for KPK; then per_cost using actual installed ancestry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP.Episode
open Filter Set Function Metric Complex MeasureTheory Lattice Bloch Laurent Exterior Matrix Precision Next.Free RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {α Ω η k : ℝ} {j : ℕ} {n : Side}

def arc (k) (v:Train j) (p:Momentum) := symbol 1 p*fieldD 1 k v p*(symbol 1 p)ᴴ
def found (k) (v:Train j) (n:Side) (a b:X2) (x:Cover) := meter n * ∑ t:Site n, mode (mon t) x * arc k v (mon t) a b
lemma zero_harmonic (v:Train j) : arc k v 0=0 := by unfold arc; simp [symbol,wedge,q]

lemma covered_layer (v:Train j) (hk : 0<k) (hj : 4≤j) (f:Firm α Ω η) (hf : f.row=pink k v) (ha : 0<α) (he : 0<η)
    (p:Site n) : garnet f (lit n (lift p))=arc k v (mon p) := by
  by_cases hh : p=0
  · subst p; rw [mon_zero,zero_harmonic]; unfold garnet; simp [lit,Lattice.lift,rcast,tooth,mcast,q,wedge]
  let z := lit n (lift p); let t := mon p
  have ht : t≠0 := by obtain ⟨i,hi⟩ := step_picks p hh; intro h; apply hi; unfold t at h; rw [cell_step,h]; simp
  have hc := mon_mem n p
  have hg : z∈search := by
    refine ⟨fun i => (local_price p i).trans_lt ?_,fun hx => ht ?_⟩
    · unfold earth; linarith [Real.pi_pos]
    change z=0 at hx; rw [show t=mcast z from (lit_mon ..).symm,hx]; ext; simp [mcast]
  let X:=symbol 1 t; let U:= symbol 0 t; let B:= U * Uᴴ; let R:=rotor 1 k v t; let D:=fieldD 1 k v t; let F:=fuel f z
  have hv r : wedge r (tooth z)=symbol r t := by unfold tooth; rw [show mcast z=t from lit_mon ..]; rfl
  have hx (r): mirage 1 r t=(symbol r t)ᴴ := by rw [mirage_herm _ _ hc.1,signal_unit]
  have hF : F=R+B := by
    unfold F fuel R rotor B
    unfold outside
    rw [show mcast z=t from lit_mon .., hv, hv,hx,signal_unit,hf, show (pink k v).read t=pulse k v t from (heart_true k hk hj v).1.echo _ hc]
  have hR : R*D*Xᴴ=Xᴴ := by
    rw [show R*D=_ from rotor_after 1 k hk v (base_subset_realCube zone_pos hc) ht, show Xᴴ=mirage 1 1 t from (hx _).symm, Matrix.sub_mul,Matrix.one_mul, Matrix.mul_assoc,mirage_chain,Matrix.mul_zero,sub_zero]
  have h₀ : X*U=0:=d_d ..
  have hX : X*B=0 := by unfold B; rw [← Matrix.mul_assoc,h₀]; simp
  have h₂ : B*Xᴴ=0 := by have hx := congr_arg Matrix.conjTranspose hX; simp [B] at hx; exact hx
  have HH : R=Xᴴ*pulse k v t*X := by unfold R X rotor; rw [hx,signal_unit]
  have hFB : F*B=B*F := by
    rw [hF, Matrix.add_mul, Matrix.mul_add,HH]
    rw [Matrix.mul_assoc (Xᴴ*_ ) X B,hX,Matrix.mul_zero,← Matrix.mul_assoc B (Xᴴ*pulse k v t) X,← Matrix.mul_assoc B Xᴴ (pulse k v t),h₂]; simp
  have hD : IsUnit F.det := by
    have h:= tank_sealed ha he f z hg; unfold tank at h; rw [Matrix.det_smul] at h; exact isUnit_of_mul_isUnit_right h
  have hE : F⁻¹*F=1:=Matrix.nonsing_inv_mul _ hD; have hO : F*F⁻¹=1:=Matrix.mul_nonsing_inv _ hD
  have hb : F⁻¹*B=B*F⁻¹ := calc
    _ = F⁻¹*(B*(F*F⁻¹)) := by rw [hO,mul_one]
    _ = F⁻¹*(F*B)*F⁻¹ := by rw [← hFB.symm]; simp [Matrix.mul_assoc]
    _ = _ := by rw [← Matrix.mul_assoc F⁻¹,hE,one_mul]
  have hm : X*F⁻¹*B=0:=by rw [Matrix.mul_assoc,hb,← Matrix.mul_assoc,hX,Matrix.zero_mul]
  have heq : X*F⁻¹*F*D*Xᴴ=X*D*Xᴴ := by rw [Matrix.mul_assoc X F⁻¹ F,hE,Matrix.mul_one]
  nth_rw 2 [hF] at heq; rw [Matrix.mul_add,hm,add_zero] at heq
  unfold arc garnet; rw [show lit n (lift p)=z from rfl,hv]; change X*F⁻¹*Xᴴ=X*D*Xᴴ; apply Eq.trans _ heq; nth_rw 1 [← hR]; simp only [Matrix.mul_assoc]

lemma paid (k:ℝ) (hk : 0<k) {j:ℕ} (hj : 4≤j) : ∃ α Ω η:ℝ, 0<α ∧ 0<η ∧ ∀ v:Train j, ∃ f:Firm α Ω η, f.row=pink k v := by
  have hh := (heart_heats k hk hj (@id (Train j))).1; obtain ⟨a,C,ha,hC,h⟩ := hh.stock.uniform; obtain ⟨η,A,hη,hA,H⟩ := hh.funds
  refine ⟨a,max C A,η,ha,hη,fun v => ⟨⟨pink k v,?_,fun n=>?_,?_⟩,rfl⟩⟩
  · have hx : Row.strip (pink k v) a C := by simpa only [id,mul_one] using h v
    exact fun i j=> (hx i j).mono le_rfl (le_max_left ..)
  · have he := (obey_band _ (hh.stock.whole v) (H v) n).2
    intro x
    refine ⟨(he x).1, (he x).2.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (Finset.sum_nonneg ?_))⟩
    intro i _
    exact mul_self_nonneg _
  · rw [show (pink k v).read 0=pulse k v 0 from (heart_true k hk hj v).1.echo _ (show 0 ∈ baseCube from by simpa only [mon_zero] using mon_mem 1 (0:Site 1)),pulse_zero]
lemma bridge (k:ℝ) (hk : 0<k) (hj : 4≤j) (ha : 0<α) (he : 0<η) (v:Train j) (f:Firm α Ω η) (h : f.row=pink k v) (a b:X2) (n:Side) : rock n f a b = found k v n a b := by
  funext x; unfold rock transmits record bill found; simp [covered_layer v hk hj f h ha he]


lemma covering_roots (p:Site n) : ∃ y:Cover, -mon p=mon (-p)+reciprocal y := by
  obtain ⟨v,hv⟩:=lit_alias (n:=n) (-lift p); rw [map_neg,Lattice.wrap_lift] at hv
  refine ⟨v,hv ▸ ?_⟩; rw [← lit_mon]; ext1 i; simp [lit,mcast,rcast]
lemma found_real (hk : 0<k) (v : Train j) (n:Side) (a b:X2) (x:Cover) : conj (found k v n a b x)=found k v n a b x := by
  have he (p:Site n) (r : ℕ) : Next.Free.shade (symbol r (mon p))=symbol r (-mon p) := by
    rw [← signal_unit,← signal_unit]
    exact shade_signal 1 _ (real_frequency p)
  have hh (t:Momentum) (x:Cover) : arc k v (t+reciprocal x)=arc k v t := by unfold arc; simp_rw [← reading,Row.periods,fieldD,fieldD_period]
  let f (p:Site n):=mode (mon p) x*arc k v (mon p) a b
  have hg (p:Site n): conj (f p)= f (-p) := by
    have ht:= mode_adjoint (mon p) x; rw [real_frequency, mode_opposite, ← mode_inverse] at ht
    have hX : Next.Free.shade (arc k v (mon p))=arc k v (-mon p) := by
      have hx := (shade_D 1 k hk v (real_frequency p)).1
      have hu (Z:Matrix X2 X1 ℂ) : Next.Free.shade Zᴴ=(Next.Free.shade Z)ᴴ := by ext i j; rfl
      unfold arc; rw [shade_mul,shade_mul,hx,hu,he]
    obtain ⟨y,hy⟩ := covering_roots p
    rw [hy,hh] at hX
    rw [hy,mode_phase, mode_periodic,mul_one] at ht
    unfold f
    rw [map_mul]
    change star (mode _ _) * star (arc _ _ _ _ _)=_
    rw [ht]
    congr 1
    exact congr_fun (congr_fun hX a) b
  change conj (meter n * ∑ p,f p)=_
  rw [map_mul, map_sum]
  simp_rw [hg]
  rw [show ∑ p:Site n,f (-p)=∑ p,f p from Equiv.sum_comp (Equiv.neg _) f]
  unfold meter found
  simp [meter,f]
lemma wraps {z y:Cover} (v:Train j) (a b:X2) (h : Lattice.wrap n z=Lattice.wrap n y) : found k v n a b z=found k v n a b y := by
  unfold found
  simp_rw [show ∀ p:Site n, mode (mon p) z=mode (mon p) y from fun p => respects _ _ _ h]

-- Target Levels not enlarged or assumed to exist.

end YM.Further.FreeCovariance.KP.Episode
