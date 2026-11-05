import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Filaments

/-!
# Backward and forward (coarse-only) tails

Purchase chain estimates with one more true-length expenditure.
Compatible Supports outputs cost via ratio collapse even on plain target.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Calls
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint Paths
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

lemma accent (G : Gauge) (D : Patch) (a C σ r s : ℝ) (L : Side) (ha : 0≤a) (_hr : 0<r) (hs : s<r) (hσ : 0<σ) :
    ∀ᶠ x in atTop, ∀ (c f : Side) (k : Ratio c f) (R : PathData G), k.count=L → Odd k.count.val →
    ∀ φ Λ, R.Bounds φ σ C Λ → Ac.Hit (rib R k x) (radiusB x)
      (fun i => untaxed R i x D r σ) a
      ((Fintype.card Signed:ℝ)*((Fintype.card PlaqAxes:ℝ)*amend G D x s)) := by
  let Z := preCost 120+(10*preCost 120/L.val)*(1+(2:ℕ))
  have hz : 0≤Z := by unfold Z preCost; positivity
  let ε := (σ/8:ℝ); have he : 0<ε := by unfold ε; positivity
  have hC : 0≤C*C := mul_self_nonneg _
  filter_upwards [award G D (L.val^4) 130 (C*C*Real.exp 1) a ε r s Z he (mul_nonneg hC (Real.exp_pos _).le) hs hz,
    -- horizons for k count: old uses same D but call ratio L; actually uses x as coarse availability in this context, even with custom count
    Fees.horizons G L 120 he ha (by unfold ε; linarith : 2*ε<σ/2), Delay.shift_pos G D.L]
    with x hx hp hv c f k R hL hk φ Λ hh
  let B := radiusB x; let H := amend G D x r
  have hM : 0 ≤ Real.exp 1*H := by have he := pos_ac G D x r hv; exact mul_nonneg (Real.exp_pos _).le he.le
  apply many; intro v; apply many; intro j
  let p i := untaxed R (v,j,i) (f:=f) x D r σ; let X (i : Site f × ℕ × ℕ) := enlargement k 120 B (fringe R (v,j,i))
  have hb i : (X i).image v.act = rib R k x (v,j,i) := by
    ext y; rw [mem_image,rib,extent,halo_spec]; constructor
    · rintro ⟨u,hu,rfl⟩; obtain ⟨z,hz,h⟩ := halo_spec.mp hu
      exact ⟨_,mem_image_of_mem v.act hz,(separation_signed ..).trans_le h⟩
    rintro ⟨z,hz,h⟩; obtain ⟨m,hm,rfl⟩ := mem_image.mp hz
    obtain ⟨y,rfl⟩ := (show Surjective (v.act (R:=Per c)) from v.actEquiv.surjective) y
    change separation (v.act m) (v.act y)≤_ at h; rw [separation_signed] at h
    exact ⟨_,halo_spec.mpr ⟨_,hm,h⟩,rfl⟩
  change Ac.Hit (fun i => rib R k x (v,j,i)) _ _ _ _
  simp_rw [← hb]; have hu i : 0≤p i := mul_nonneg hM (laceFee_nonneg ..)
  apply forged v X B p a _ hu ha
  have hl := hp.2.2 _ _ k hL
  intro i
  let w l := mate R j l*Real.exp (σ/2*Paths.length (duplex R j l))
  have hm := Paths.bundle_hit k 120 B _ w (half_pos hσ) (fun i =>
    mul_nonneg (show 0 ≤ mate R j i by unfold mate; positivity) (Real.exp_pos _).le) (gains R j hh) X (fun j => Finset.Subset.refl _) hp.1
      hM hl 0 p hu (fun y => by unfold p untaxed; rw [pow_zero,mul_one]; apply le_rfl) 0 i
  simp only [Nat.zero_le,if_true,pow_zero,mul_one] at hm
  apply budget_loosen hm; rw [show Paths.baseFee (d:=2) k 120 = Z by unfold Paths.baseFee conversion Z; rw [hL],hL]
  apply hx _ (show _ ≤ 130*_ from by unfold Paths.originFee B; omega) _ _ hM hC
  exact le_of_eq (by ring)

-- optional Mayer factors, paid tickets using anchored arrays fixed with actual coefficients
section cap
variable (T : Tube G S) (x r σ : ℝ)


end cap




end YM.AnalyticNext.ConnectedActivity.Calls
