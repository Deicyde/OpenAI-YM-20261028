import YM.Extra.SOURCE_HISTORIES.Clusters
import YM.Next.FREE_KERNELS.Lifts
import YM.Planned.PRIMARY_INTEGRAL_295.Emits
import YM.Push.LOCAL_SPLITTING.Projection



/-!
# Delivering the jet tests of a true singleton principal term

The lower-level Chart receipt is a *component* (gaussian-regular) and
phase identity obligation taken on the actual address; test using the true
coarse link path. It's for extraction of actual canonical columns, not the
separate problem of regular remainder transport. Need at all requested visits,
all in one account/address bank to use in estimates later. Exposed analytic
input, including moment debt; not claiming implementation. pre-Side `cash`
encloses coat widths, ALL support visits with pricing, and composition and
score constants.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Radical
open Function Filter Set Metric MeasureTheory
open Labels Lattice Source Source.Drops Tones Oval Emits   
open Place  Precision Bloch Next.Free RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
open Wilson
open Push.Local (Probe runProbe)
variable {G : Gauge} {d j t : ℕ} {F : Labels.Frame G d}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {n L : Side}

/-- E Jpr localized receipt remaining from the *actual normalized phase*.
Chart only has to run for unmasked calls incl equality (M.Format).
Need separate M identity incl actual masked correction. One real ledger in
Ω for the Gaussian/no-hole piece (μ,f,rates on entire charts for all
canonical columns; each i common W), not assuming a Markovian history
or a decorrelated coarse trajectory and not providing its prices by
fitting H's derivatives. `Clock` payload independent of H. Caller's
job cannot change β, Raw M or support in between. Ω is Type (finite-
dimensional/choice contractor). Charts may be local versions of integrals;
only certifiable with full exact pointwise *push* obligation, not as a
model. -/
def Gate (T : SectionData F) (L : Side) (Y : F.Index→Config G n→ℂ) (path : E→Config G n) (Q : E→Dev T.stencil G)
    (f : ℝ) (b : ℕ) (R δ : ℝ) : Prop :=
  ∃ (Ω:Type) (_m : MeasurableSpace Ω) (μ:Measure Ω) (W:Ω→E→Dev T.stencil G) (ρ : Ω→E→ℝ) (ε:Ω→ℝ),
    (∀ᵐ z ∂μ, 0≤ρ z 0) ∧ ∀ i, i≠0 →
      let l := (F.grades i).2
      let X := Emits.atom W ρ (Place.column T i) l f
      Emits.Clock μ b l Q W ρ 0 f R ε δ ∧ Ripple.Regales X μ b 0 ∧
        (Y i ∘ path =ᶠ[𝓝 0] (L.val:ℝ)^d • Ripple.value X μ)

namespace Gate

/-- `u` price for predictor path, doesn't need to estimate in μ. Any
R meeting support of clocks with scaled W; don't need R≥1 (will impose in
production budget). -/
lemma consume (T : SectionData F) (i : F.Index) (hi : i≠0) {Y : F.Index→Config G n→ℂ} {path : E →Config G n} {Q}
    {f R R' δ u B : ℝ} {b : ℕ} (h : Gate T L Y path Q f b R δ) (hf : f∈Ioc 0 1) (hR : R≤R') (ht : ContDiffAt ℝ b Q 0)
    (hU : Oval.Envelope 0 b Q u) (hx : ‖f • Q 0‖ ≤ R')
    (hB : Tones.Width (column T i) (b+1) (F.grades i).2 R' B) :
    let Z := (2^b+1)*league b (F.grades i).2 u B
    Fuzz 0 b (Y i ∘ path) ((L.val:ℝ)^d • (tint T i f ∘ Q)) (Z*(L.val:ℝ)^d*δ) := by
  obtain ⟨Ω,M,μ,W,ρ,ε,hP,h⟩:=h
  intro Z
  obtain ⟨hc,hS,H⟩:=h i hi
  let X:=Emits.atom W ρ (column T i) (F.grades i).2 f; let p:=(L.val:ℝ)^d
  have he := forceClock ht (column_smooth T i) hU (hc.radius hR) hS hB hf hx
  let V := Ripple.value X μ; let Q' := tint T i f ∘ Q
  have hp := show 0≤p by unfold p; positivity
  have hy := (mul_nonneg hp he.1)
  obtain ⟨S,hx',hA⟩:=hS
  refine ⟨le_of_le_of_eq hy (by unfold Z p; ring),fun n hn=>?_⟩
  have hN : (n:WithTop ℕ∞) ≤(b:WithTop ℕ∞) := Nat.cast_le.mpr hn
  have hd' : ContDiffAt ℝ n Q' 0 := (show ContDiffAt ℝ b Q' 0 from
    ((coat_smooth (column_smooth T i) ..).contDiffAt.of_le le_top).comp _ ht).of_le hN
  rw [(H.iteratedFDeriv ℝ n).self_of_nhds]; change ‖iteratedFDeriv ℝ n (p • V) 0 - iteratedFDeriv ℝ n (p • Q') 0‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (show ContDiffAt ℝ n V 0 from (hA.flare _ hx').of_le hN),
     iteratedFDeriv_const_smul_apply hd',← smul_sub,norm_smul,Real.norm_of_nonneg hp]
  refine (mul_le_mul_of_nonneg_left (he.2 n hn) hp).trans_eq ?_; unfold p Z; ring
end Gate

/-- Pre price on the arithmetic anticipated parameters -- no `L` or
f dependence. No assuming output costs of the bank to perform this bound. -/
theorem pouch (T : SectionData F) (b : Bid.pop T) (i : F.Index) (k : ℕ) (z R : ℝ) :
    ∃ C:ℝ, 0≤C ∧ ∀ {n L : Side} {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
      (Y : F.Index→Config G n→ℂ) (path : E' → Config G n) Q f δ,
      i≠0 → 0≤δ → Gate T L Y path Q f k R δ → f∈Ioc (0:ℝ) 1 → ContDiffAt ℝ k Q 0 → Oval.Envelope 0 k Q z →
        Fuzz 0 k (Y i ∘ path) ((L.val:ℝ)^d • (tint T i f ∘ Q)) (C*(L.val:ℝ)^d*δ) := by
  obtain ⟨C,H⟩:=columnPrice T b i (k+1) (max z R)
  let Z:=(2^k+1)*league k (F.grades i).2 z C
  refine ⟨max 0 Z,le_max_left ..,fun Y path Q f δ hi hδ h' hf hQ hZ=> ?_⟩
  rename_i n L E _ _
  have hh : ‖f • Q 0‖ ≤ max z R := by
    rw [norm_smul,Real.norm_of_nonneg hf.1.le]; exact (mul_le_of_le_one_left (norm_nonneg (Q 0)) hf.2).trans
      (hZ.value.trans (le_max_left ..))
  have he := Gate.consume T i hi h' hf (le_max_right ..) hQ hZ hh H
  have ht : Z*(L.val:ℝ)^d * δ ≤ max 0 Z*(L.val:ℝ)^d * δ := by gcongr; exact le_max_right ..
  exact ⟨he.1.trans ht,fun i hi=> (he.2 i hi).trans ht⟩
end YM.Planned.PrimaryIntegral295.Radical
