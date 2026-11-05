import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Packets
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Windows

set_option warningAsError false

/-! Fixed-L gap and the complete TestD hypotheses on a uniform germ about
all admissible output V individually. Supplies even nearness of the gap in
Schur on this working neighborhood with tags and tracks held fixed. -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice RG Wilson Pressure Pressure.Tube Precision Exterior Bloch Tree Matrix
open YM.Push.SectorMeasure YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet Schur
open Next.SectorChange.Rows Next.SectorChange.Wisps FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent (native Bundle Cost)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {k n : ℕ} {σ d ε C r : ℝ}
variable {ι κ α : Type} [Fintype ι] [Fintype κ]
variable {p : ι → Site c} {A : Directions G c → Matrix ι ι ℝ}

lemma close_gap {M : Matrix ι ι ℝ} {B : Matrix ι ι ℝ} {ε v : ℝ} (h : (native c).Schur p p 0 v (B-M))
    (hp : Gapped M ε) : Gapped B (ε-v) := by
  intro x
  have ht := FreeResolvent.schur_qf (native c) p h x
  rw [sub_mulVec,dotProduct_sub,← sumSq_dot] at ht
  have hk := hp x; have hl := (abs_le.mp ht).1
  linarith

/-- Shrink once to purchase the same uniform gap on the unmasked chart
readers. No support/curve continuity input for unpriced fields; the gap at
the center `Gapped (A 0)` comes from `SectorChange.Gap` next. -/
lemma nearby_gap (hs : 0 < σ) (hC : 0 ≤ C) (hk : 1 ≤ k) (hs' : 0 < r) {η Z : ℝ} (hZ : 0≤Z)
    (_ : 0<η) (hp : (native c).Volume p (σ/2) Z) (hg : Gapped (A 0) η)
    (h : ∀ b, ‖b‖ ≤ r → RatesPaid p p σ C k A b)
    (B : Directions G c) (hh : ‖B‖ ≤ min r ((η/2)/(1+Z*(sparkCount G (σ/2)*C)))) :
    Gapped (A B) (η/2) := by
  have hv := fluctuate hC hs hk Z Z hp hp 0 B (by simpa using hs'.le) (hh.trans (min_le_left ..)) h
  let U := Z*(sparkCount G (σ/2)*C)
  have hu : 0≤U := mul_nonneg hZ (mul_nonneg (spark_nn ..) hC)
  have hB := (le_div_iff₀ (by linarith : 0<1+U)).mp (hh.trans (min_le_right ..))
  rw [show η/2=η-η/2 from by ring]
  apply close_gap (Cost.Schur.mono hv (half_pos hs).le ?_) hg
  simp only [sub_zero, max_self]
  rw [← mul_assoc]; change U*‖B‖ ≤ _; nlinarith only [hB,norm_nonneg B]

-- evaluation C(x), B window integral called for flags even at boundaries
-- through Handoff. Robust imports (no proof-irrelevance needed on V).
def Trust (G : Gauge) (p : Teller G) (P : Patch) (x C r : ℝ) (k : ℕ) (σ η : ℝ) :=
  ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → p.Funds S T →
    100*(1+radiusB x) ≤ c.val → ∀ (V : Config G c) (t:S.Choices) (A : Stores S) (F : Forest S.ratio),
      A.flags=RG.flags (temp x) V → ∀ B : Directions G c, ‖B‖ ≤ r →
        let g := front (G:=G) A F (x:=x); let H := pilot T A F t x V;
        RatesPaid (down S) g σ C k (scroll T A F t x V) B ∧
          RatesPaid g g σ C k H B ∧ Gapped (H B) η ∧ (H B).PosDef ∧
          (∀ z, z ⬝ᵥ (H B *ᵥ z) ≤ C * sumSq z) ∧
          ∀ (i : Bond c) (s : Signed), curb (shots S x) A F x s (.inr i) →
            ContDiffAt ℝ ω (fun y => G.mat (Press.workQ V s t i y)) (B,0)

lemma pricedUpper (A : Gaussian.Table ι) {p : ι→Site c} (hs : 0≤σ) (h : Pours A p p σ C) :
    ∀ z, z ⬝ᵥ (A *ᵥ z) ≤ C * sumSq z := by
  intro z; have he := le_of_abs_le (estimate (h.weaker hs le_rfl) z z); linarith

/-- *Produced* trust for the authentic data. Price gaps and neighborhood
before choosing the (x,V) input. Consequence is integrable calculus with
TestD, not that the full Gaussian multipliers preserve any prescribed
smoothing widths. -/
theorem trusting (P : Patch) (G : Gauge) (p : Teller G) (hb : P.Branches p.bind G) (k : ℕ) :
    ∃ C r d η : ℝ, 0≤C ∧ 0<r ∧ 0<d ∧ 0<η ∧ ∀ᶠ x : ℝ in atTop, Trust G p P x C r k d η := by
  obtain ⟨C,r,d,hc,hr,hd,h⟩ := bought P G p hb (k+1)
  obtain ⟨η,hη,hE⟩ := Gap.not_flat G P p hb
  obtain ⟨c',r',-,hr',hG⟩ := noise_quote G P p.bind hb k d hd.le
  let Z := geography P G (d/2)
  let W := Z*(sparkCount G (d/2)*C)
  have hz := geography_nn P G (d/2)
  have hp : 0≤W := mul_nonneg hz (mul_nonneg (spark_nn ..) hc)
  let u := min r ((η/2)/(1+W))
  have hu : 0<u := lt_min hr (div_pos (half_pos hη) (by linarith))
  refine ⟨C,min r' u,d,η/2,hc,lt_min hr' hu,hd,half_pos hη,?_⟩
  filter_upwards [h,hE,hG] with x hx hg hp
  intro c f S T hP hT he V t A F hA B hB g H
  have hX b (h : ‖b‖ ≤ r) := hx S T hP hT he V t A F hA b h
  have hU : ‖B‖ ≤ u := hB.trans (min_le_right ..)
  have hv := hX B (hU.trans (min_le_left ..))
  have hG : Gapped (H 0) η := by
    intro z
    unfold H pilot; rw [increment_zero,sumSq_dot]; exact hg S T hP he hT A F t V hA z
  have hZ : (native c).Volume g (d/2) Z := by unfold Z; rw [← hP]; exact (terraced S G A F x _ (half_pos hd)).1
  have hY := nearby_gap hd hc (show 1≤k+1 by omega) hr hz hη hZ hG (fun b h => (hX b h).2) B hU
  refine ⟨reducePay hv.1 le_rfl le_rfl (by omega),reducePay hv.2 le_rfl le_rfl (by omega), hY, ?_,
    pricedUpper _ hd.le (pay_pours hv.2 hc), fun i s h => ?_⟩
  · exact dissolves hY (by unfold H; rw [pilot_eq]; unfold Matrix.IsSymm; rw [transpose_mul, transpose_transpose]) (half_pos hη)
  exact (hp S hP hT.knobs he V A F s t i hA h B (hB.trans (min_le_left ..))).1

-- Bundle proposition -> derivative-only costing on the exact reference
lemma activate {B : Directions G c} (h : RatesPaid p p σ C k A B) (hg : Gapped (A B) ε) {d : ℝ}
    (he : d ≤ σ) : Knew (meterMark G c d) (native c) p atom B k σ C ε 1 A := by
  have hp := Bill.reclaim (h.bound [] (by simp))
  rw [zeroth] at hp
  refine ⟨h.smooth,debut hg,hp,fun l _ hl => ?_⟩
  rw [mul_one]; exact (less_bundle h he le_rfl).bound l hl
end YM.AnalyticBridge.Covariance
