import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Hiring

/-!
# Exact physical single-transition unforced E service upon holding offer

Consumes these SAME Levels and currencies even at constant-stage and first
edges, any certified Tube.

No assumption of a posteriori recursion payments hidden
in estimates.

Certification available at kernel horizon uses below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir.Suite
open Filter Function Set Lattice Wilson Pressure RG Tree Precision Next Next.SectorChange Rows Exterior Bloch
    Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussian Push.PriceCompiler Supply Testing AnalyticBridge.LocalGaussianLaws
    AnalyticBridge.VerifiedReset.Time Push.AbsoluteSums Shoot Bid UVNext.PricedKernels
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {V : Rolls s} {Θ : Protection V} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {a : Levels G} {C : Programs s} {D : ℕ→ℕ→Record} {E t : ℕ→ℕ→ℝ} {r : ℕ→ℕ→ℕ} {m p : ℕ}

abbrev Studio (a : Levels G) (m p : ℕ) := a.clock.op m p
abbrev coarse (a : Levels G) (m : ℕ) := a.clock.J m
abbrev fine (a : Levels G) (m : ℕ) := a.clock.J (m+1)

structure Enabled (s : Sheet G) (K : MapPrices) (C : Programs s) (D : ℕ→ℕ→Record) (E t : ℕ→ℕ→ℝ) (r : ℕ→ℕ→ℕ) (a : Levels G) (m p : ℕ) (T : Tube G (Studio a m p)) : Prop where
  make : let j := fine a m; let i := coarse a m
    Plays (C j i) (D j i) (a.budget m) (a.budget (m+1)) (query s K j i) T (a.clock.hatBeta m)
  pre : let j := fine a m; let i := coarse a m
    Release.accepts (r j i) (a.budget (m+1)).supportExponent (t j i) (a.S.block m) ∧ Release.Quotation (C j i) (a.budget m).power (r j i) (a.budget (m+1)).supportExponent (t j i) (E j i)
  clocks (β : ℝ) : let j := fine a m; let i := coarse a m
    β∈band a (m+1) → 0<coupling β ∧ Lute.Plented (C j i) (D j i) (a.budget m) (a.budget (m+1)) (a.S.block m) (r j i) (a.clock.hatBeta m) (coupling β)
  spare : let j := fine a m; let i := coarse a m
    (E j i / (a.S.block m).val)*a.clock.allowance (m+1) ≤ forecastE a m/8

variable (h : Offers K W C D r) (hv : Earlier s K C E t r) (hp : Paid I a)
    (T : Tube G (Studio a m p)) (ht : Lift.Booth (query s K (fine a m) (coarse a m)) (Studio a m p) T)
    (hT : Seam T (wide K (fine a m) (coarse a m)) (scale K (fine a m) (coarse a m)))
include h hv hp ht hT
lemma enabled : Enabled s K C D E t r a m p T := by
  let j := fine a m; let i := coarse a m; let P:=a.budget m; let B:=a.budget (m+1)
  have h₁ : P.order=(s.profile i).order := congrArg Stage.order (params_eq hp m); have h₂ : P.power=(s.profile i).power := congrArg Stage.power (params_eq hp m)
  have h₃ : B.order=(s.profile j).order := congrArg Stage.order (params_eq hp (m+1)); have h₄ : B.power=(s.profile j).power := congrArg Stage.power (params_eq hp (m+1))
  have he : a.clock.hatBeta (m+1)=betaF G (a.clock.hatBeta m) (V.L j) := beta_eq hp m
  have hg : B.supportExponent = (s.profile j).supportExponent := congrArg Stage.supportExponent (params_eq hp _)
  obtain ⟨hH,hh⟩ := (h j _ (hp.pays m) i (step_paid a m) (first_le hp m)).care P B rfl (congr_arg temp he) (congr_arg radiusB he) h₁ h₃ h₂ h₄
  have hz : a.S.block m=V.L j := block_eq hp m
  refine ⟨hh _ T rfl hz hT ht (by rw [add_comm 1]; exact a.fits.sizeT m p),⟨hz.symm ▸ hg.symm ▸ (hv.gates j i _ (step_paid a m) (V.large j).need).1,h₂.symm ▸ hg.symm ▸ (hv.agrees j i).2.2⟩, fun β hβ => hz.symm ▸ (hH β (he ▸ hβ.1)),?_⟩
  let L : ℝ := (V.L j).val; let M := credit G (s.profile i); let y := a.clock.hatBeta m
  have hl : 1 ≤ L := Nat.one_le_cast.mpr (V.L j).property; have hM : 0<M := credit_pos ..
  have hf : 8*E j i ≤ M*L := (hv.pre j i (step_paid a m)).trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (V.large j).need) hM.le)
  have hF : E j i / L ≤ M/8 := (div_le_iff₀ (zero_lt_one.trans_le hl)).mpr (by linarith)
  have hA : a.clock.allowance (m+1) ≤ a.clock.allowance m := Extra.Iteration.Scales.unforced_mono (zero_lt_one.trans (a.fits.delayed m))
    (he.symm ▸ le_add_of_nonneg_right (Work.E04.shift_nonneg ..))
  have ht' : 0 ≤ a.clock.allowance (m+1) := Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
  change E j i / (a.S.block m).val * _ ≤ _; rw [hz,forecastE,params_eq hp m]; linarith only [mul_le_mul hF hA ht' (show 0≤ M/8 by positivity)]

namespace Enabled
variable {T} (ha : Enabled s K C D E t r a m p T)
omit h hv hp ht hT
include ha



end Enabled
end YM.PhysicalNext.JointLoad.Heir.Suite
