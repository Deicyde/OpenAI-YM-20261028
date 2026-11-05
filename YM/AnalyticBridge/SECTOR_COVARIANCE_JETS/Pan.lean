import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Vista

set_option warningAsError false

/-!
# Panel assembly. The finite-range covariance C(V), not A⁻¹, is the one
used. Symmetrization therefore has a second gap test, produced here also in
the working neighborhood. State error rates distinct from the jump width;
both before any period/field evaluation (both positive and can shrink in use).
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice RG Wilson Pressure Pressure.Tube Precision Exterior Bloch Tree Matrix
open YM.Push.SectorMeasure YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet Schur
open Next.SectorChange.Rows Next.SectorChange.Wisps FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent (native Bundle Cost resolve tagPrice)
open FreeResolvent.Window (Survey)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {k n : ℕ} {σ d r C V η u Y : ℝ}
variable {ι κ α : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] {p : ι → Site c}
  {A F : Directions G c → Matrix ι ι ℝ} {B : Directions G c} {W : ι→Set ι}

structure Installed (p : ι→Site c) (A : Directions G c → Matrix ι ι ℝ) (W : ι→Set ι) (B : Directions G c)
    (d Y C η : ℝ) (k : ℕ) : Prop where
  lens : Vista p A W B d Y C k
  mist : RatesPaid p p d C k (obscure W A) B
  unmask : RatesPaid p p d (Y*C) k (obscure W A-action A 0) B
  spray : RatesPaid p p d (Y*C) k (storm W A) B
  gap : Gapped (obscure W A B) η
  definite : (obscure W A B).PosDef
  upper : ∀ z, z ⬝ᵥ (obscure W A B *ᵥ z) ≤ C*sumSq z
  second : Vista p (obscure W A) W B d Y C k
  precision : RatesPaid p p d (Y*C) k (action (obscure W A) 0-A) B

-- overlap radius to price in radiusB, NOT divided by L again
private lemma anchored (R : ℕ) (h : 120 ≤ R) (k : ℕ) (hu : 0 < u) {b : ℝ} (he : b≤u/120) :
    rateBreak u (R/60) k ≤ rate (-b) R := by
  apply Real.exp_monotone
  have hi : R ≤ 120*(R/60) := by omega
  have hl : (R:ℝ) ≤ 120*↑(R/60) := by exact_mod_cast hi
  have hp : 0 ≤ (↑(R/60) : ℝ) := by positivity
  push_cast; nlinarith only
    [mul_le_mul_of_nonneg_right he (Nat.cast_nonneg R), mul_le_mul_of_nonneg_left hl hu.le,
      mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hu.le) hp]

private lemma circle (hn : 0<u) (k : ℕ) : let z := u/(1+k); 0<z ∧ z + k*z ≤ u ∧ z ≤ u := by
  intro z
  have hp : 0<z := by unfold z; positivity
  have hh : z+k*z=u := by unfold z; field_simp
  exact ⟨hp,hh.le,le_trans (le_add_of_nonneg_right (by positivity)) hh.le⟩

/-- Output uniform in every window containing the pricing ball (not every
finite-range scheme). Compression even for inverse precision of C if needed.
Thence returns to the actual Fog. -/
lemma aperture (P : Patch) (G : Gauge) (hp : 0<σ) (hc : 0≤C) (hz : 0<η) (k : ℕ) :
    ∃ (M d b g : ℝ), 0 < M ∧ C≤M ∧ 0<d ∧ d≤σ ∧ 0 < b ∧ 0 < g ∧ ∀ᶠ x : ℝ in atTop,
    120 ≤ radiusB x ∧ ∀ {c : Side} {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → Site c) (A : Directions G c → Matrix ι ι ℝ) (W : ι → Set ι) (B : Directions G c),
      (∀ t : ℝ, 0<t → (native c).Volume p t (geography P G t)) → (∀ b : Directions G c,(A b).IsSymm) →
      RatesPaid p p σ C k A B → Gapped (A B) η → Bars W p (radiusB x/60) →
      Installed p A W B d (rate (-b) (radiusB x)) M g k := by
  let T := geography P G
  let d := room σ C η k; let V := T d
  let N := tower k C V η
  have hv : Price σ C η d 1 V 1 k := (readyIn G hp hc hz P k).priced
  have hN : 0≤N := tower_nn hv
  obtain ⟨v₀, w₀, g,-,-,hg,hW⟩ := Schur.windows hp hz hc T (geography_nn P G)
  let u := room d N g k; let U := T u
  have hU : Price d N g u 1 U 1 k := (readyIn G hv.pos hN hg P k).priced
  have hu : u≤d := roomLow hU
  let K := tower k N U g
  have hK : 0≤K := tower_nn hU
  let H := tagPrice 1 k C N
  let Z := tagPrice 1 k H K
  let M := C+(N+(K+(H+(Z+1))))
  have hH : 0≤H := FreeResolvent.Affine.tag_nn hc hN
  have hZ : 0≤Z := FreeResolvent.Affine.tag_nn hH hK
  have hm : 0<M := by unfold M; linarith
  have hci : C≤M := by unfold M; linarith
  have hni : N≤M := by unfold M; linarith
  have hki : K≤M := by unfold M; linarith
  have hhi : H≤M := by unfold M; linarith
  have hzi : Z≤M := by unfold M; linarith
  let t := u/(1+k); let r := t/(1+k); let b := u/120
  obtain ⟨htp,ht₁,ht₂⟩ := circle hU.pos k
  obtain ⟨hrp,hr₁,hr₂⟩ := circle htp k
  have hrd : r ≤ d := hr₂.trans (ht₂.trans hu)
  have hb : 0<b := div_pos hU.pos (by norm_num)
  have hR : Tendsto (fun x : ℝ => radiusB x/60) atTop atTop := by
    apply Filter.tendsto_atTop.mpr; intro i
    filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (60*i)] with x hx; omega
  refine ⟨M,r,b,g,hm,hci,hrp,hrd.trans (roomLow hv),hb,hg,?_⟩
  filter_upwards [hR.eventually hW, Work.E01.radiusB_tendsto.eventually_ge_atTop 120] with x hx hα
  refine ⟨hα,?_⟩; intro c ι _ _ p A W B hP hA h hF hB
  let Y := rate (-b) (radiusB x)
  have hy : 0≤Y := (rate_pos ..).le
  have hv₁ := makeVista h hF hv (hP d hv.pos) hB
  have hv₀ : Vista p A W B d Y N k := hv₁.weaken le_rfl le_rfl (mul_le_mul_of_nonneg_right
    (anchored _ hα _ hv.pos (show b≤d/120 from by unfold b; linarith)) hN)
  obtain ⟨hS,hS'⟩ := hv₀.evans hN hA
  have hh : Gapped (obscure W A B) g ∧ (obscure W A B).PosDef :=
    (hx p (A B) W (fun y hy => (hP y hy).bound) (pay_pours h hc) (hA B) hF hB).2
  have hf₁ := makeVista hS hh.1 hU (hP u hU.pos) hB
  have hf₀ : Vista p (obscure W A) W B u Y K k := hf₁.weaken le_rfl le_rfl (mul_le_mul_of_nonneg_right
    (anchored _ hα _ hU.pos le_rfl) hK)
  have hs : RatesPaid p p t (Y*H) k (storm W A) B := by
    have ht := moneyStorm (reducePay h (roomLow hv) le_rfl le_rfl) hS' hc (mul_nonneg hy hN) hF hz htp.le (ht₁.trans hu)
    exact Bundle.mono ht le_rfl (le_of_eq (by unfold H tagPrice; ring))
  have hth : t≤d := ht₂.trans hu
  have hk₁ : RatesPaid p p u K k (action (obscure W A) 0) B := by
    simpa only [drain, add_zero, inv_one, mul_one] using ((hf₀.full _ le_rfl).mild le_rfl hK)
  have hPaid := reducePay hS hrd hni (le_refl k)
  refine ⟨hv₀.weaken hrd hni (mul_le_mul_of_nonneg_left hni hy),hPaid,
    reducePay hS' hrd (mul_le_mul_of_nonneg_left hni hy) le_rfl,
    reducePay hs hr₂ (mul_le_mul_of_nonneg_left hhi hy) le_rfl,hh.1,hh.2,
    pricedUpper _ hrp.le (pay_pours hPaid hm.le),hf₀.weaken (hr₂.trans ht₂) hki (mul_le_mul_of_nonneg_left hki hy),?_⟩
  have hlast := residualInverse hs (mul_nonneg hy hH) hh.1 hg (reducePay hS hth le_rfl le_rfl) hK
    (reducePay hk₁ ht₂ le_rfl le_rfl) hrp.le hr₁
  apply Bundle.mono hlast le_rfl
  exact le_trans (le_of_eq (show tagPrice 1 k (Y*H) K = Y*Z by unfold Z tagPrice; ring)) (mul_le_mul_of_nonneg_left hzi hy)
end YM.AnalyticBridge.Covariance
