import YM.SharpGram.Weak.Bill
import YM.SharpGram.Weak.Compatible
/-!
# Adapt to the actual metric of a common measuring chart

Use cost in operator norm on the real form `glass`. Quantitative estimates
for both exact finite-step inputs and for arbitrary convergent limits in the
true filter. At ties only `detector` used (meaning: the **tilted** grid
positions without projection ties!). Uniform also over charts with bounded
above and below form (includes measured and compatibles thus far). Inlets
and outlets measured with the **exact** engineering normalization using
`C.S.a k` even though station data was pulled up from its closest Interior at
`X.atK k`. They compare to the chart on the physical field space; if using
annual or perturbative reports with further changes of basis those must still
pay their own prices. No numerical claim in this file restricted to just
subsequence of k.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Weak.Portfolio
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank PhysicalNext.RankCovariance
open Org Spec Next.Rank.Station Further.CorrectedLift Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}(U:Final C f S)
variable {D:ℕ}{u:Filter (ℕ×ℕ)}{H:C.Makes} (X : Portfolio C H D u)
local notation "X'"=> standard C
local notation "σ"=> U.room.kernel.spin
local notation "P"=> C.path.levels.clock.hatBeta
local notation "a"=> C.S.a
variable {W r T0} (T : OPE.TableTickets C W r T0) [u.NeBot] (hf : u ≤ f.fuse) (hG:G.Simple)

section algebra
omit [u.NeBot]
-- pay for both maps, including the norm of `model`. No symmetry assumption
lemma realUpper {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (T : RealForm V V) (v : V) :
    T v v ≤ ‖T‖ * ‖v‖^2 := (le_abs_self _).trans ((resid T v v).trans_eq (by ring))
lemma bodyBound {u v c b : ℝ} (hc : 0 < c) (hb : 0≤b) (hu : 0 ≤ u) (hv : 0 ≤ v) (he : c*u^2 ≤ b*v^2) :
    u ≤ Real.sqrt (b/c) * v := by
  apply (sq_le_sq₀ hu (mul_nonneg (Real.sqrt_nonneg _) hv)).mp
  rw [mul_pow,Real.sq_sqrt (div_nonneg hb hc.le),div_mul_eq_mul_div, le_div_iff₀ hc]
  linarith only [he]
lemma normBy {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {P1 Q : RealForm V V}
    {K : ℝ} (hv : ‖P1-Q‖ ≤ K) : ‖P1‖ ≤ K + ‖Q‖ := calc
    _ ≤ ‖P1-Q‖ + ‖Q‖ := by nth_rw 1 [← sub_add_cancel P1 Q]; exact norm_add_le (P1-Q) Q
    _ ≤ _ := add_le_add hv le_rfl

lemma ticketUp {k d : ℕ} (Q : YM.Spin.change S d) (δ K : ℝ)
    (hp : ‖inBasis U X k d Q - model C d‖ ≤ δ) (he : δ ≤ K) :
    ‖inBasis U X k d Q‖ ≤ K + ‖model C d‖ := normBy (hp.trans he)
end algebra

-- `fullChoice`: all slots ≤D, use arbitrary chart, restricted d
include hG T hf H
lemma entry_cap_bill (d : Fin (D+1)) (δ K : ℝ) (he : 0<δ) (hp : 0 ≤ K) (hc : coercive (model C d) δ) :
    ∀ᶠ k : ℕ in atTop,
      ∀ Q : (X').Field d ≃ₗ[ℂ] S.Field d,
        ‖inBasis U X k d Q‖ ≤ K →
          ∀ x : (X').Field d, ∃ v : (X').Field d,
            X.draw S k d v = Q x ∧ ‖v‖ ≤ Real.sqrt (K / (δ/2)) * ‖x‖ ∧
            (∀ N p' : ℕ, k<N →
              quota C d k N p' (microscope C X.aperture (X.atK k) (X.matrix k) d (N,p') (ladder C d v)) ≤ P k^(1+(d.val+1)+1) * a k ^ d.val * ‖x‖) ∧
            Tendsto (fun i=> microscope C X.aperture (X.atK k) (X.matrix k) d i (ladder C d v)) u
              (𝓝 (X.field k d (ladder C d v))) := by
  let p := 1+(d.val+1)
  have hP := zoom_price X T hG d
  let l : ℝ:= Real.sqrt (K/(δ/2))
  filter_upwards [certified U X hG T hf d δ he hc, X.onLevel,
    hP, (Next.Rank.Station.hat_rate _ hG).eventually_ge_atTop (‖ladder C d‖ * l)]
    with k hi ⟨hk,hs,hY,hT⟩ hW hb Q hQ x
  obtain ⟨v,hv⟩:=hi.2.2.2.2 (Q x)
  have hh : ‖v‖ ≤ l*‖x‖ := bodyBound (half_pos he) hp (norm_nonneg _) (norm_nonneg _) (calc
      _ ≤ _ := hi.2.2.1 v
      _ = inBasis U X k d Q x x := by change glass _ _ _ _ (X.draw S k d v) (X.draw S k d v)=glass _ _ _ _ (Q x) (Q x); rw [hv]
      _ ≤ _ := (realUpper _ _).trans (mul_le_mul_of_nonneg_right hQ (sq_nonneg _)))
  refine ⟨v,hv, hh, fun N q hn=>?_,hT d _⟩
  apply (hW N q hn _).trans
  have hL : ‖ladder C d v‖ ≤ P k * ‖x‖ := ((ladder C d).le_opNorm v).trans (le_trans
    (mul_le_mul_of_nonneg_left hh (norm_nonneg _))
    (by rw [← mul_assoc];exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)))
  exact (mul_le_mul_of_nonneg_left hL (mul_nonneg (pow_pos (zero_lt_one.trans (C.path.levels.fits.delayed k)) _|>.le) (pow_pos (C.S.a_pos k) _|>.le))).trans_eq (by rw [pow_succ]; ring)

lemma entry_cap_use (d : Fin (D+1)) (K : ℝ) (hp : 0 ≤ K) :
    ∀ᶠ k : ℕ in atTop,
      ∀ Q : (X').Field d ≃ₗ[ℂ] S.Field d,
        ‖inBasis U X k d Q‖ ≤ K →
          ∀ x : S.Field d,
            ∃ (y : C.label d)(q:ℕ×ℕ → C.label d), S.project d y=x ∧ Tendsto q u (𝓝 y) ∧
            ∀ᶠ i in u, quota C d k i.1 i.2 (q i) ≤ P k^(1+(d.val+1)+1) * a k ^ d.val * ‖Q.symm x‖ := by
  obtain ⟨δ,he,hc⟩ := freely (C:=C) d
  have hP := entry_cap_bill U X T hf hG d δ K he hp hc
  filter_upwards [hP] with k hk Q hQ x
  obtain ⟨v,hv,_,hY,H⟩:= hk Q hQ (Q.symm x)
  exact ⟨X.field k d (ladder C d v),_,hv.trans (Q.apply_symm_apply _),H,
    (((Push.RelayDifference.cutoff_grows f).mono_left hf).eventually_gt_atTop k).mono fun i hi=> hY _ _ hi⟩

lemma entryBill (d : Fin (D+1)) (δ K : ℝ) (he : 0<δ) (hp : 0 ≤ K) (hc : coercive (model C d) δ) :
    ∃ p : ℕ, ∀ᶠ k : ℕ in atTop,
      ∀ Q : (X').Field d ≃ₗ[ℂ] S.Field d,
        ‖inBasis U X k d Q‖ ≤ K →
          ∀ x : (X').Field d, ∃ v : (X').Field d,
            X.draw S k d v = Q x ∧ ‖v‖ ≤ Real.sqrt (K / (δ/2)) * ‖x‖ ∧
            (∀ N p' : ℕ, k<N →
              quota C d k N p' (microscope C X.aperture (X.atK k) (X.matrix k) d (N,p') (ladder C d v)) ≤ P k^p * a k ^ d.val * ‖x‖) ∧
            Tendsto (fun i=> microscope C X.aperture (X.atK k) (X.matrix k) d i (ladder C d v)) u
              (𝓝 (X.field k d (ladder C d v))) := 
  ⟨_, entry_cap_bill U X T hf hG d δ K he hp hc⟩

lemma entryUse (d : Fin (D+1)) (K : ℝ) (hp : 0 ≤ K) :
    ∃ p : ℕ, ∀ᶠ k : ℕ in atTop,
      ∀ Q : (X').Field d ≃ₗ[ℂ] S.Field d,
        ‖inBasis U X k d Q‖ ≤ K →
          ∀ x : S.Field d,
            ∃ (y : C.label d)(q:ℕ×ℕ → C.label d), S.project d y=x ∧ Tendsto q u (𝓝 y) ∧
            ∀ᶠ i in u, quota C d k i.1 i.2 (q i) ≤ P k^p * a k ^ d.val * ‖Q.symm x‖ := 
  ⟨_, entry_cap_use U X T hf hG d K hp⟩

-- May use our `enlarged`, whose coercivity has NOT been asserted
lemma departBill (d : Fin (D+1))(δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, ∀ Q : (X').Field d ≃ₗ[ℂ] S.Field d,
      coercive (inBasis U X k d Q) δ →
        ∀ x : C.label d, ‖Q.symm (X.visible S k d x)‖ ≤ Real.sqrt ((1+‖modelFull C d‖) / δ) * ‖x‖ := by
  filter_upwards [SharpGram.stayNear (X.detectorAll U hG T hf d) zero_lt_one] with k hk Q hQ x
  let y:= X.visible S k d x
  apply bodyBound hδ (by positivity) (norm_nonneg _) (norm_nonneg _)
  calc
    _ ≤ _ := hQ (Q.symm y)
    _ = enlarged U X k d x x := by change glass _ _ _ _ (Q (Q.symm y)) (Q (Q.symm y))=glass _ _ _ _ y y; rw [Q.apply_symm_apply]
    _ ≤ _ := (realUpper ..).trans (mul_le_mul_of_nonneg_right (normBy hk) (sq_nonneg _))

-- phase/state untouched; exact filter quantifiers for departure. Arbitrary
-- finer subfilter! If `u` is our chosen ultra then necessarily same; but
-- argument works generally with the same data. Use compactness on `y`.
lemma departUse (d : Fin (D+1))(δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, ∀ Q : (X').Field d ≃ₗ[ℂ] S.Field d,
      coercive (inBasis U X k d Q) δ →
        ∀ (v : Filter (ℕ×ℕ)) [v.NeBot], v ≤ u →
          ∀ (q : ℕ×ℕ → C.label d)(x : C.label d)(z:ℝ),
            (∀ᶠ i in v, quota C d k i.1 i.2 (q i) ≤ z) → Tendsto q v (𝓝 x) →
            ‖Q.symm (S.project d x)‖ ≤ Real.sqrt ((1+‖modelFull C d‖) / δ) * 2 / a k ^ d.val * z := by
  filter_upwards [X.onLevel,X.unzoom T hG d,X.departBill U T hf hG d δ hδ] with k ⟨hk,hs,hY,hT⟩ he hp Q hQ v hv hc q x z hA hB
  let Z' i (x:C.label d) := microscope C X.aperture (X.atK k) (X.matrix k) d i x
  let c : ℝ:= 2/a k^d.val*z
  have ht : ∀ᶠ i : ℕ×ℕ in v, ∃ y, ‖y‖ ≤ c ∧ Z' i y=q i := by
    filter_upwards [hA, ((Push.RelayDifference.cutoff_grows f).mono_left (hc.trans hf)).eventually_gt_atTop k] with i hi hj
    obtain ⟨y,he,hx⟩:= he _ _ hj (q i)
    exact ⟨y,hx.trans (mul_le_mul_of_nonneg_left hi (div_nonneg zero_le_two (pow_pos (C.S.a_pos k) _|>.le))),he⟩
  let y (i : ℕ×ℕ) := if h:∃ y, ‖y‖ ≤ c ∧ Z' i y=q i then h.choose else 0
  have hr : ∀ᶠ i in v, ‖y i‖ ≤ c ∧ Z' i (y i)=q i := ht.mono fun i hi=> by rw [show y i=_ from dif_pos hi]; exact hi.choose_spec
  obtain ⟨w,hw,ha,Y,hX⟩ := finite_extract y c (hr.mono fun i hi=>hi.1)
  have he : X.field k d Y=x := tendsto_nhds_unique_of_eventuallyEq (Dash.arcing ((Dash.fit_plane _ _
    (hT d)).mono_left (hw.trans hc)) hX) (hB.mono_left hw) ((hr.mono fun i hi=> hi.2).filter_mono hw)
  let b := Real.sqrt ((1+‖modelFull C d‖)/δ)
  rw [← he]; change ‖Q.symm (X.visible S k d Y)‖ ≤ _
  exact (hp Q hQ Y).trans ((mul_le_mul_of_nonneg_left
    (show ‖Y‖ ≤ c from le_of_tendsto hX.norm ((hr.filter_mono hw).mono fun i hi=> hi.1)) (show 0≤ b from Real.sqrt_nonneg _)).trans_eq
    (by unfold b c; ring))
end YM.SharpGram.Weak.Portfolio
