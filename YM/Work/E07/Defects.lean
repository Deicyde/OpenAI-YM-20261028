import YM.Work.E07.Local

/-!
# Estimates on the two departure rows (L,D)

Sum tested Bool slots. D needs no stencil savings at all. For L, retain
possible wide-column costs for small fine terms (post-L), but only multiply
the fine excess by the pre-priced *row* rate `a/L²`. Do the analogous noise
charge and allow an input bill for coarse toll excess.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.E07
open Lattice RG Wilson Pressure Pressure.Stores Precision Exterior Bloch Finset Bid
open scoped Topology InnerProductSpace BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {x W a d : ℝ}
variable {T : Tube G S} {U : Config G f} {Q V : Config G c} {k : S.Choices}

def dCost (a d : ℝ) := d * (d + a*d + a*d + a*(a*d))

lemma workD_ge (ha : 0 ≤ a) (hd : 0 ≤ d) (hw : Allowance a T x V)
    (hm : Maximum d T x V) (p : Cell c) :
    -(dCost a d * (fiery G x S.patch.L)^2) ≤ T.workD (till x) V (temp x) p := by
  let l : ℝ := S.patch.L.val
  let t := fiery G x S.patch.L
  let v := T.vision (till x) (temp x) V
  let uf := unzip (T.Φ (till x) V) (T.Mv (till x) (temp x) V)
  let un := unzip (T.Φ' (till x) V) (T.Mw (till x) (temp x) V)
  let z := zip (T.N (till x) V) v
  let uz := unzip (T.N (till x) V) z
  have ht : 0 ≤ t := temp_nonneg _
  have hl : 0 < l := by unfold l; positivity
  have hz (j) : ‖z j‖ ≤ a * (d*t) := zip_uniform _ _ j (hw.tight.rows j) (by positivity) hm.up
  have h (j : Twin c) : ‖v j - (uf j + un j + uz j)‖ ≤ (d + a*d + a*d + a*(a*d)) * t := by
    have hf : ‖uf j‖ ≤ (a*l^2) * (d/l^2*t) :=
      unzip_uniform _ _ _ (hw.wide.columns j) (by positivity) hm.phi
    have hn : ‖un j‖ ≤ a * (d*t) :=
      unzip_uniform _ _ _ (hw.narrow.columns j) (by positivity) hm.hot
    have hj : ‖uz j‖ ≤ a * (a * (d*t)) :=
      unzip_uniform _ _ _ (hw.tight.columns j) (by positivity) hz
    have hh : (a*l^2) * (d/l^2*t) = a*d*t := by field_simp
    rw [hh] at hf
    apply (norm_sub_le _ _).trans
    apply (add_le_add (show ‖v j‖ ≤ d*t from hm.up _) ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add hf hn)) hj))).trans_eq
    ring
  have H (i : Bool) : let j : Twin c := (p, i);
      -(dCost a d * t^2) / 2 ≤ inner ℝ (v j) (v j - (uf j + un j + uz j)) / 2 := by
    intro j
    gcongr
    have hs : ‖v j‖ ≤ d*t := hm.up _
    have hi : ‖v j‖ * ‖v j - (uf j + un j + uz j)‖ ≤ dCost a d * t^2 :=
      (mul_le_mul hs (h j) (norm_nonneg _) (by positivity)).trans_eq (by unfold dCost; ring)
    exact (neg_le_neg hi).trans (abs_le.mp (abs_real_inner_le_norm _ _)).1
  have he := sum_le_sum (s := (univ : Finset Bool)) (fun i _ => H i)
  change -(dCost a d * t^2) ≤ _
  refine le_trans ?_ he
  rw [sum_const, card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat]
  apply le_of_eq; ring

/-- Summation transfer into L, for the named set of tested faces. -/
lemma workL_total (U : Config G f) (Q : Config G c) (hm : Maximum d T x V)
    (hd : 0 ≤ d) (s : Finset (Cell c)) {r b z : ℝ}
    (hf : ∑ j ∈ s ×ˢ (univ : Finset Bool), ‖unzip (T.Φ (till x) V) (T.Xf (till x) U) j‖ ≤ r)
    (hb : ∑ j ∈ s ×ˢ (univ : Finset Bool), ‖unzip (T.Φ' (till x) V) (Tube.Z S Q V) j‖ ≤ b)
    (hz : ∑ j ∈ s ×ˢ (univ : Finset Bool), ‖T.Xn (till x) V j‖ ≤ z) :
    -(d * fiery G x S.patch.L * (r + b + z)) ≤
      ∑ p ∈ s, T.workL (till x) U Q V (temp x) p := by
  let F := unzip (T.Φ (till x) V) (T.Xf (till x) U)
  let B := unzip (T.Φ' (till x) V) (Tube.Z S Q V)
  let X := T.Xn (till x) V
  let W := T.vision (till x) (temp x) V
  let t := fiery G x S.patch.L
  let ls := s ×ˢ (univ : Finset Bool)
  have ht : 0 ≤ t := temp_nonneg _
  have hh (j : Twin c) : -(d*t * (‖F j‖ + ‖B j‖ + ‖X j‖)) ≤ inner ℝ (W j) (F j + B j - X j) := by
    have he : ‖W j‖ ≤ d*t := hm.up j
    refine le_trans (neg_le_neg ?_) (abs_le.mp (abs_real_inner_le_norm (W j) _)).1
    exact mul_le_mul he ((norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _))
      (norm_nonneg _) (by positivity)
  calc
    _ ≤ -(d*t * ∑ j ∈ ls, (‖F j‖ + ‖B j‖ + ‖X j‖)) := by
      apply neg_le_neg; gcongr
      simp_rw [sum_add_distrib]; exact add_le_add (add_le_add hf hb) hz
    _ = ∑ j ∈ ls, -(d*t * (‖F j‖ + ‖B j‖ + ‖X j‖)) := by rw [sum_neg_distrib, ← Finset.mul_sum]
    _ ≤ ∑ j ∈ ls, inner ℝ (W j) (F j + B j - X j) := sum_le_sum fun j _ => hh j
    _ = _ := by unfold ls; rw [sum_product]; rfl

lemma fine_total {E : Cell f → ℝ} {bill : ℝ} (U : Config G f)
    (hA : Allowance a T x V) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hL : LaneCounts T.up x (fiery G x S.patch.L) T.high d 1 S.ratio.parent)
    (hE : ∀ p, 0 ≤ E p) (hbill : (∑ p, E p) / (S.patch.L.val : ℝ)^2 ≤ bill)
    (s : Finset (Twin c)) (hh : ∀ i ∈ s, tagged i ∈ A.dome (2 * radiusB x))
    (hU : ∀ p : Cell f, S.ratio.parent p.1 ∈ A.dome (5 * radiusB x) →
      toll U p ≤ fiery G x S.patch.L + E p) :
    let u := (Real.sqrt T.high.direct + d)
    ∑ p ∈ s, ‖unzip (T.Φ (till x) V) (T.Xf (till x) U) p‖ ≤
      (s.card : ℝ) * (a * (S.patch.L.val : ℝ)^2 * (u * fiery G x S.patch.L)) +
        a * (2 * u) * bill := by
  let X (i : Twin f) := plottedExcess T.up T.high x 1 E i.1
  intro u
  let t := fiery G x S.patch.L
  have hu : 0 ≤ u := by unfold u; positivity
  refine (unzip_total _ s _ (g := X) (fun _ => plottedExcess_nonneg hL hE _)
    hA.wide.rows hA.wide.columns (mul_nonneg hu (show 0 ≤ t from temp_nonneg _)) ?_).trans ?_
  · intro j hj i hi
    have he : separation (tagged j) (S.ratio.parent (tagged i)) ≤ radiusB x / 50 :=
      (separation_comm ..).symm ▸ (hA.wide.stencil i j hi)
    have hv : S.ratio.parent i.1.1 ∈ A.dome (3 * radiusB x) :=
      dome_extend (hh _ hj) he (by omega)
    exact plotted_le hL U hE i hd (show 0 ≤ t from temp_nonneg _) fun z hz =>
      hU z (dome_extend hv hz (by omega))
  · apply add_le_add_right
    calc
      _ ≤ a / (S.patch.L.val : ℝ)^2 * (2 * u * ∑ i, E i) :=
        mul_le_mul_of_nonneg_left (plottedExcess_total hL hE) (by positivity)
      _ = a * (2 * u) * ((∑ i, E i) / (S.patch.L.val : ℝ)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbill (by positivity)

lemma noise_total (Q : Config G c) {E : Bond c → ℝ} {bill u : ℝ}
    (hA : Allowance a T x V) (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hE : ∀ p, 0 ≤ E p) (hbill : ∑ p, E p ≤ bill)
    (s : Finset (Twin c)) (hh : ∀ i ∈ s, tagged i ∈ A.dome (2 * radiusB x))
    (hQ : ∀ p : Bond c, p.1 ∈ A.dome (5 * radiusB x) → wire Q V p ≤ u + E p) :
    let g := Real.sqrt S.kernel.penalty
    ∑ p ∈ s, ‖unzip (T.Φ' (till x) V) (Tube.Z S Q V) p‖ ≤
      (s.card : ℝ) * (a * (g * u)) + a * g * bill := by
  intro g
  have hg : 0 ≤ g := Real.sqrt_nonneg _
  refine (unzip_total _ s _ (g := fun i => g * E i) (fun i => mul_nonneg hg (hE i))
    hA.narrow.rows hA.narrow.columns (mul_nonneg hg hu) ?_).trans ?_
  · intro j hj i hi
    have he : separation (tagged j) i.1 ≤ radiusB x / 50 :=
      (separation_comm ..).symm ▸ (hA.narrow.stencil i j hi)
    have ht := hQ i (dome_extend (hh _ hj) he (by omega))
    unfold Tube.Z
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), ← mul_add]
    exact mul_le_mul_of_nonneg_left ((G.curvature_norm _).trans ht) hg
  rw [← Finset.mul_sum, mul_assoc a g]
  gcongr

lemma coarse_total {E : Cell c → ℝ} {u bill : ℝ}
    (hL : LaneCounts T.down x (temp x) T.low d S.patch.L.val (id : Site c → Site c))
    (hd : 0 ≤ d) (hu : 0 ≤ u) (s : Finset (Twin c))
    (hE : ∀ p, 0 ≤ E p) (hbill : ∑ p, E p ≤ bill)
    (hh : ∀ i ∈ s, tagged i ∈ A.dome (2 * radiusB x))
    (hV : ∀ p : Cell c, p.1 ∈ A.dome (3 * radiusB x) → toll V p ≤ u + E p) :
    let g := Real.sqrt T.low.direct + d
    ∑ p ∈ s, ‖T.Xn (till x) V p‖ ≤ (s.card : ℝ) * (g * u) + 2 * g * bill := by
  intro g
  refine (plotted_total hL V s hE hd hu (fun p hp z hz =>
    hV _ (dome_extend (hh _ hp) (show separation (tagged p) z.1 ≤ radiusB x / 50 from hz) (by omega)))).trans ?_
  unfold g; gcongr

end YM.Work.E07
