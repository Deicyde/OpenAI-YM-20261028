import YM.Push.GRID_APPROXIMATION.Joint

/-!
# Sufficient signed many-source estimate for one rooted discrepancy

Thus a quite different type of estimate from assuming
that pairs of far cutoff correlations are approximable.

Needs genuine
agreement and bounds BEFORE integrating/cancelling denominator.

Address
and scale tests use the actual histories and cutoffs.

Compare
 (already propagated to ℓ).

That production, including what
would justify the estimates from exponential gaps, lies largely outside
current verified knowledge; no claim of its truth here.

Sufficiency proof goes from this many-source signed bound to the h-centered
microscopic `rootTest`, cancelling the actual denominator (including its
volume cost). Radius W must be large at the stop for this to pay. This is
marker radius **after** `a_r^d` encoding. Doesn't discuss other, less
costly, sufficient conditions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox.Joint
open RG Lattice Wilson MeasureTheory Filter Function Marker Overlay Cells
open scoped Topology BigOperators

variable {G : Gauge} (H : History G) (N p : ℕ) {h k r : ℕ}
variable (hk : h ≤ k) (hN : k ≤ N)
variable (O : Config G (H.S.side N p) → ℂ) (F : Config G (H.S.side k p) → ℂ)

/-- Needs the vacuum rep with actual address set; no inferred
freedom to add/merge histories from inequalities on unmarked reps.
Expect W > 0, u,c,d',b bounded constants at fixed stop (specified in
consuming estimates). `d'` the forced cost parameter, NOT the d of
scaling. `a` not reconstructed from a cutoff limiting measure. All
Mode slots from distinct cells. -/
def Receipt (hh : h ≤ r) (hr : r ≤ k) (d : ℕ) (W u c d' b : ℝ) :=
    ∃ a : Bands (Markers H h p) (H.rep N p r), a.Active ∧
      a.Radial (fun _ => W) u c d' b ∧ (∀ i, a.origins i = anchor H.S p hh i) ∧
      ∀ s : (Markers H h p).Mode, (fun V => (a.density V).part s) = scaled H N p hk hN O F hr d s

variable {O F}

/-- Per-root numerator after charging stop-volume constants (still divide
by W). -/
def cost (H : History G) (h r d : ℕ) (u c d' b : ℝ) :=
    Real.exp ((H.S.a h / H.S.a r)^4 * Vac.treasury H.levels r + (u+c+d'*b)) / (H.S.a r)^d

lemma cost_pos (h r d) (u c d' b) : 0 < cost H h r d u c d' b :=
  div_pos (Real.exp_pos _) (pow_pos (H.S.a_pos r) _)

lemma receipt_power (hS : H.Selected) (hO : Envelope O) (w : ℕ) (hF : Interior (window 0 w) F)
    (hRoom : room H.levels h k w) (hh : h ≤ r) (hr : r ≤ k)
    (d : ℕ) (W u c d' b : ℝ) (ht : Receipt H N p hk hN O F hh hr d W u c d' b) (s : (Markers H h p).Mode) :
    ‖Ride.bump (H.S.a r) s (fun _ => d)‖ *
      ‖moment (H.β N p N) (cutoff H N p hk hN O F s.val)‖ * Poly.toll (fun _ => W) s ≤
        Real.exp (Fintype.card (Site (H.S.side h p)) *
          ((H.S.a h / H.S.a r)^4 * Vac.treasury H.levels r + (u+c+d'*b))) := by
  obtain ⟨a,ha,hR,hp,hD⟩ := ht
  let n := Fintype.card (Site (H.S.side h p))
  let C := H.levels.clock
  have hAd := hr.trans hN
  have he := hS.represents N p r hAd
  have hh' : 0 < C.hatCoupling r :=
    inv_pos.mpr (Real.sqrt_pos.2 (lt_trans zero_lt_one (H.levels.fits.delayed r)))
  have hv : C.hatCoupling r ≤ (H.rep N p r).p.threshold := by
    rw [he.vac]; change _ ≤ C.hatCoupling r * Real.exp _
    exact le_mul_of_one_le_right hh'.le (Real.one_le_exp (sq_nonneg _))
  have hu := a.total ha hR he.good (Overlay.beta_positive hS hAd).le _ hh' hv (H.nonnegative hS N p r hAd) s
  have hE := restore_scaled H N p hk hN hO w hF hRoom hr d s
  have hZ : 0 < partition G (H.S.side N p) (H.β N p N) := partition_pos _
  have hj := hu.trans (Real.exp_monotone (Vac.suffices_bill hS hAd n ..))
  have hz : (∫ U,(a.density U).part s ∂prior G _) = _ := Eq.trans (congr_arg (fun f => ∫ U, f U ∂prior G (H.S.side r p)) (hD s)) hE
  rw [hz,H.partition_eq hS N p r hAd,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hZ.le] at hj
  let v := ‖Ride.bump (H.S.a r) s (fun _ => d)‖
  let y := ‖moment (H.β N p N) (cutoff H N p hk hN O F s.val)‖
  change v*(partition G _ _ * y) / partition G _ _ * Poly.toll _ _ ≤ Real.exp
    ((Fintype.card (Site (H.S.side r p)):ℝ)*_ + n * _) at hj
  rw [show v*(partition G _ _ * y) / partition G _ _ = v*y by field_simp, Stock.tallies H.S h r p] at hj
  refine hj.trans_eq ?_; congr 1; unfold n; ring

lemma receipt_root (hS : H.Selected) (hO : Envelope O) (w : ℕ) (hF : Interior (window 0 w) F)
    (hRoom : room H.levels h k w) (hh : h ≤ r) (hr : r ≤ k)
    (d : ℕ) (W u c d' b : ℝ) (hW : 0<W) (ht : Receipt H N p hk hN O F hh hr d W u c d' b) :
    (tilesAt H.S p (hk.trans hN)).rootTest (H.β N p N) (difference H N p hN O F) ≤ cost H h r d u c d' b / W := by
  let T := Site (H.S.side h p)
  let s := Stock.final T
  let n := Fintype.card T
  let m := ‖moment (H.β N p N) (cutoff H N p hk hN O F s.val)‖
  let e := ((H.S.a h / H.S.a r)^4 * Vac.treasury H.levels r + (u+c+d'*b))
  have hj := receipt_power H N p hk hN hS hO w hF hRoom hh hr d W u c d' b ht s
  have hp : ‖Ride.bump (H.S.a r) s (fun _ => d)‖ = ((H.S.a r)^d)^n := by
    unfold Ride.bump s Stock.final
    simp_rw [norm_prod,norm_pow,Complex.norm_real,Real.norm_of_nonneg (H.S.a_pos r).le,
      Finset.prod_const,Finset.card_univ]; rfl
  have he : Poly.toll (fun _ => W) s = W^n := by simp [Poly.toll,n,s,Stock.final]
  have ht' : m*((H.S.a r)^d*W)^n ≤ Real.exp (n*e) := by
    rw [hp,he] at hj
    change ((H.S.a r)^d)^n * m * W^n ≤ Real.exp (n*e) at hj
    rw [mul_pow]; ring_nf at *; exact hj
  change m^((n:ℝ)⁻¹) ≤ _
  refine (Stock.spacer m e _ n (norm_nonneg _) (mul_pos (pow_pos (H.S.a_pos _) _) hW) Fintype.card_pos ht').trans_eq ?_
  exact (div_div (Real.exp e) ..).symm
end YM.Push.GridApprox.Joint
