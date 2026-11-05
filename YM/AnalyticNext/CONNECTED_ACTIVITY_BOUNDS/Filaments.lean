import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Hair

/-!
# Inherited row tails, before estimating the hitting cost

E at the pinned `R`, choose per (i,j) path-pair exponent once; include
all old orientation and complete mask dependence. RHS outgoing SHIELD is
*full coarse base* (not loop terms). `crown` from Energy receipt is thus
on BOTH scales cut. When subtract and peel, coarse tails return with
positive sign in the exponent. Need true dual support for these as
well. No support computed by actual nonzero read.
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

-- charges with count=1 for outbound, uses actual coarse radius via d. leg geometry in its own native units.
def plain (c : Side) : Ratio c c := ⟨1,by simp⟩
lemma collar (i : Site c) : (plain c).parent i=i := by
  have hv : (plain c).embed i=i := by simp [Ratio.embed,plain]
  simpa only [hv] using (plain c).embed_parent i

abbrev Buttons (f : Side) := Signed × (PlaqAxes × (Site f × (ℕ × ℕ)))

section defs
variable (R : PathData G)

def fringe (b : Buttons f) := Paths.bundle b.2.2.1 (Paths.duplex R b.2.1 b.2.2.2)

def partWay (k : Ratio c f) (b : Buttons f) := ((fringe R b).image k.parent).image b.1.act

def rib (k : Ratio c f) (x : ℝ) (b : Buttons f) := Calls.extent 120 (partWay R k b) x

def strip (i : PlaqAxes) (v d : ℕ) (k : ℕ) := (R.row i k).2.length*d ≤ v

def drain (L : Clip) (p : Cell f) (i j : ℕ) (v d : ℕ) (s : ℝ) (U : Config G f) :=
    if PathData.kept L s p.1 U ∧ ¬(strip R p.2 v d i ∧ strip R p.2 v d j) then
      inner ℝ (R.ellTerms p i U) (R.ellTerms p j U)/2 else 0

def chiffon (L : Clip) (h : Buttons f) (v d : ℕ) (s : ℝ) (U : Config G f) :=
    drain R L (h.2.2.1,h.2.1) h.2.2.2.1 h.2.2.2.2 v d s (pull h.1 0 U)

-- keep all stencils near `partWay`, incl e-ticket PSC reads, covers full kept query even on robe envelope

def cuts (b : Buttons f) (R : Rep G f) (Y : Mint T F A x) (a : ArrayR G f) := -R.beta*Aff.weight *
    guards Y (partWay R.path S.ratio b) a * chiffon R.path R.clip b (till x) 1 R.p.threshold (Y.build a)

def reset (b : Buttons c) (x β : ℝ) (T : Tube G S) (V : Config G c) := β*Aff.weight *
    chiffon T.down T.low b (till x) S.patch.L.val (temp x) V

def laceFee (b : Buttons f) (σ : ℝ) := mate R b.2.1 b.2.2.2 * Real.exp ((σ/2)*Paths.length (duplex R b.2.1 b.2.2.2))

def untaxed (b : Buttons f) (x : ℝ) (D : Patch) (r σ : ℝ) := Real.exp 1 * amend G D x r*laceFee R b σ

lemma gains (i : PlaqAxes) {φ : Clip} {σ C Λ : ℝ} (hx : R.Bounds φ σ C Λ) :
    SumBudget (fun b : ℕ×ℕ => (mate R i b*Real.exp ((σ/2)*Paths.length (duplex R i b))) *
      Real.exp ((σ/2)*Paths.length (duplex R i b))) (C*C) := by
  convert budget_prod (hx.rows i) (hx.rows i) using 1; ext b
  rw [mul_assoc,← Real.exp_add, show σ/2 * _ + _ = σ*Paths.length (duplex R i b) from by ring,
    duplex_price,Nat.cast_add,mul_add,Real.exp_add]
  unfold mate; ring
lemma laceFee_nonneg (i : Buttons f) (σ : ℝ) : 0 ≤ laceFee R i σ := by unfold laceFee mate; positivity
lemma remnants (i : Buttons f) {φ : Clip} {σ C Λ : ℝ} (hx : R.Bounds φ σ C Λ) : laceFee R i σ ≤ C*C := by
  have he := budget_single (gains R i.2.1 hx) i.2.2.2
  apply le_trans _ he
  exact le_mul_of_one_le_right (laceFee_nonneg R ..) (Real.one_le_exp (mul_nonneg (half_pos hx.width).le (by positivity)))
end defs

-- exp(σ/2 ℓ) pays any powers. d in lengths actual native scaling; choice post-L.
lemma long_paid (G : Gauge) (D : Patch) (σ r : ℝ) (hp : 0 < σ) (hr : 0 < r) (d : ℕ) (hd : 0 < d) : ∀ᶠ x in atTop,
    ∀ β : ℝ, OnBand G D x β → ∀ n : ℕ,till x < n*d → β*Aff.weight*2 ≤
      amend G D x r * Real.exp ((σ/2)*n) := by
  let s := σ/2/d
  have hs : 0<s := div_pos (half_pos hp) (by positivity)
  filter_upwards [Delay.shift_pos G D.L, Fees.route_tail_decay G D.L hs (by linarith : 0<r+2),
    instills G D (4*Aff.weight*2) (r+1) (r+2) 0 (by have he := weight_pos; positivity) (by linarith)]
    with x hx hh he β hβ n hn
  let t := betaF G x D.L
  have ht : 0 < t := hx
  let y := σ/2*n
  have hg : Real.exp (-y) ≤ amend G D x (r+2) := by
    apply le_trans _ hh; apply Real.exp_monotone
    unfold s y; have hv : ((till x:ℕ):ℝ) ≤ n*(d:ℝ) := by exact_mod_cast hn.le
    calc
      _ = -(σ/2/ (d:ℝ))*(n*(d:ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonpos_left hv (by linarith only [show 0<s from hs])
  apply le_of_mul_le_mul_right _ (Real.exp_pos (-y))
  calc
    _ ≤ ((4*t)*Aff.weight*2)*Real.exp (-y) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβ.2 weight_pos.le) (by norm_num)) (Real.exp_pos _).le
    _ ≤ ((4*t)*Aff.weight*2)*amend G D x (r+2) := mul_le_mul_of_nonneg_left hg (by have ht := weight_pos; positivity)
    _ = (4*Aff.weight*2*amend G D x (r+2))*t := by ring
    _ ≤ amend G D x (r+1) * t := by gcongr; simpa using he
    _ = amend G D x r := by unfold amend; rw [neg_add, Real.rpow_add hx, Real.rpow_neg_one]; unfold t; field_simp
    _ = _ := by rw [mul_assoc,← Real.exp_add]; unfold y; rw [add_neg_cancel,Real.exp_zero,mul_one]

-- Basic cannon: length toll for ANY oriented determinant tail pair
lemma outerPay (G : Gauge) (D : Patch) (σ r C : ℝ) (d : ℕ) (hd : 0<d) (hp : 0<σ) (hr : 0<r) : ∀ᶠ x in atTop,
    ∀ β,OnBand G D x β → ∀ (n : Side) (R : PathData G) (φ : Clip) (Λ s : ℝ), R.Bounds φ σ C Λ →
    ∀ (p : Buttons n) (U : Config G n), |β*Aff.weight*chiffon R φ p (till x) d s U| ≤
      amend G D x r * laceFee R p σ ∧ amend G D x r * laceFee R p σ ≤ 1 := by
  have hm : Tendsto (fun x => C*C*amend G D x r) atTop (nhds 0) := by
    simpa using! ((tendsto_rpow_neg_atTop hr).comp (Work.E09.betaF_growth G D.L)).const_mul (C*C)
  filter_upwards [long_paid G D σ r hp hr d hd, Delay.shift_pos G D.L,
    hm.eventually (ge_mem_nhds zero_lt_one)] with x hx ht hw β hβ n R φ Λ s h p U
  have hs := (pos_ac G D x r ht).le; let Z := amend G D x r
  have hb : 0≤β := (by have H := hβ.1; linarith)
  refine ⟨?_,(mul_le_mul_of_nonneg_left (remnants R p h) hs).trans (by rw [mul_comm]; exact hw)⟩
  unfold chiffon drain; split
  next he =>
    let T := (p.2.2.1,p.2.1)
    let i := p.2.2.2
    let v r := R.row p.2.1 r
    let W := pull p.1 0 U
    have hf j : ‖R.ellTerms T j W‖ ≤ |(v j).1| * 2 := by
      unfold PathData.ellTerms; rw [norm_smul]; apply mul_le_mul_of_nonneg_left (Slot.eval_norm ..) (abs_nonneg _)
    let H := Paths.length (duplex R p.2.1 i)
    have hv := hx β hβ H (by
      unfold H; rw [duplex_price]; have hh := he.2; unfold strip at hh; push Not at hh
      by_contra! hg; apply he.2; refine ⟨?_,?_⟩ <;> unfold strip <;> unfold i at hg <;> nlinarith)
    have H' : 0 ≤ (mate R p.2.1 i) := by unfold mate; positivity
    let L := mate R p.2.1 i
    rw [abs_mul,abs_of_nonneg (mul_nonneg hb weight_pos.le)]
    apply le_trans (mul_le_mul_of_nonneg_left (show |inner ℝ (R.ellTerms T i.1 W) (R.ellTerms T i.2 W)/2| ≤ 2*L from ?_)
      (show 0 ≤ β*Aff.weight from mul_nonneg hb weight_pos.le))
    · rw [← mul_assoc]; apply le_trans (mul_le_mul_of_nonneg_right hv H'); unfold laceFee H; exact le_of_eq (by unfold i; ring)
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    apply le_trans (div_le_div_of_nonneg_right ((abs_real_inner_le_norm ..).trans
      (mul_le_mul (hf i.1) (hf i.2) (norm_nonneg _) (by positivity))) (by norm_num)); exact le_of_eq (by unfold v L mate; ring)
  next => rw [mul_zero,abs_zero]; exact mul_nonneg hs (laceFee_nonneg ..)
end YM.AnalyticNext.ConnectedActivity.Calls
