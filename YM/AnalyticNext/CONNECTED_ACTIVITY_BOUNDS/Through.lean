import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Bedrock
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Mint
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Odometer
import YM.Progress.STATIONARY_SCENES.Entrance
import YM.Work.A03
import YM.Work.A04

/-!
# Remote no-hole prediction from the curved precision

Proof on literal `Mint` above full-sector data. `Y, C` context uses
arbitrary off-patch formal seeds (frozen geometry) and the actual V.
Uses NO inverse bound with moved projection. . Links and
paths wrapping included. Scalar-vector differences not paid from another
gauge. Can integrate on the one Z across cumulative supports later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Filter Win Rates Green Mint Win.Promise
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

section projected
variable (F : Forest S.ratio) (A : Stores S) (x : ℝ)

def unit (T : Tube G S) (z : Site c → G.El) (b : LogField G c) :=
  mute F A x (real (rotateG (attempt T F b) (fun i => (z (S.ratio.parent i))⁻¹)))

lemma unit_pars (T : Tube G S) (z : Site c→G.El) (b : LogField G c) (p : Bond f) (r : ℝ) (hr : 0≤r)
    (he : ‖attempt T F b p‖ ≤ r) (j : G.ColorIndex) :
    |unit F A x T z b (p,j)| ≤ r := by
  unfold unit mute; split
  · unfold real rotateG; exact (piece_cost ..).trans ((G.norm_adjoint ..).trans_le he)
  rw [abs_zero]; exact hr

lemma on_way (T : Tube G S) (z : Site c→G.El) (b : LogField G c) (p : Bond f)
    (he : p∈ F.trunks ∨ p∈ activeB A F (radiusB x)) :
    rotateG (lie (unit F A x T z b)) (z ∘ S.ratio.parent) p=attempt T F b p := by
  rcases he with he|he
  · have ht := attempt_root T F b p he; rw [ht]; unfold rotateG
    have hs : p∉ activeB A F (radiusB x) := fun h => (mem_filter.mp h).2.1 he
    have hv : lie (unit F A x T z b) p=(0:G.Color) := by ext; exact if_neg hs
    rw [hv,map_zero]
  have hv : lie (unit F A x T z b) p=rotateG (attempt T F b) (fun i => (z (S.ratio.parent i))⁻¹) p := by ext; exact if_pos he
  unfold rotateG; rw [hv]; unfold rotateG; dsimp only [Function.comp_apply]; rw [← G.adjoint_mul,mul_inv_cancel,G.adjoint_one]

lemma environs (p : Bond f) (r : ℕ) (v : Site c) (hv : v∉A.dome r) (he : separation v (home S p)+1+10*radiusB x≤r) :
    p∈ F.trunks ∨ p∈ activeB A F (radiusB x) := by
  by_cases h : p∈F.trunks
  · exact Or.inl h
  refine Or.inr (mem_filter.mpr ⟨mem_univ p,h,Finset.disjoint_left.mpr ?_⟩)
  intro j hj hk; refine exclude A _ _ _ _ hv ?_ hk
  have hx := pin_radius _ _ hj
  have hi := separation_triangle v (home S p) j; omega
end projected

section row
variable (P : Teller G) (C : ℝ) (he : Reserve P C) (D : Patch) (hD : D.Branches P.bind G)
include he hD

/-- Frame patch chooses over actual V. It need only fit the read halo
through $6B$. Completeness of footprint still uses any farther query
(e.g. to `10B` for freezing). Using $\nu$ UNrotated back to actual
fields even outside, fully projected for the estimate. No sector mask
handoff. This is BEFORE derivative tests.
-/
theorem pre_center : ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch=D →
    ∀ (H K : Bed), Alongside H K T → ∀ (F : Forest S.ratio) (A : Stores S) (Y : Mint T F A x), cert S x A Y.V →
      let B := radiusB x
      ∀ (o : Site c) (_ht : o∉A.dome (20*B)) (z : Site c → G.El) (b : LogField G c),
        ‖b‖ ≤ allowance G D x 1 7 → AgreeNear id o (6*B) (gauge z Y.V) (represent b) →
        let v := unit F A x T z b
        ∀ i : Ix G S, separation o (drow S i)≤5*B →
          |Y.actions v i| ≤ allowance G D x 2 24 := by
  filter_upwards [unfrozen P C he D hD 7, prepare D, Rates.grow G D (Real.sqrt weight)
    (by decide : 7+7+9 < 24) 2] with x h ht hr c f S T hT hS H K hK F A Y hA B o hl z b hb hc v i hi
  have hx : ‖derivative T (till x) i.1 (gauge z Y.V) (rotateG (lie v) (z∘S.ratio.parent))‖ =
      ‖derivative T (till x) i.1 Y.V (lie v)‖ := by rw [derivative_gauge T _ _ _ _ _ hT, G.norm_adjoint]
  -- `sh` and active rule agree ONLY on those stencils
  have hh : i.1∈choosing A B := mem_filter.mpr
    ⟨mem_univ _,exclude A _ _ _ _ hl (show separation o (drow S i)+_≤20*B by omega)⟩
  have hy (e : Bond f) (he : separation (base S i.1) (home S e) ≤ stencilD S.patch (till x)) :
      e∈F.trunks ∨ e∈activeB A F B := by
    apply environs F A x e _ o hl; apply le_trans (Nat.add_le_add_right (Nat.add_le_add_right
      (le_trans (separation_triangle _ (drow S i) _) (Nat.add_le_add hi he)) _) _)
    have hu : 4*stencilD D (till x)+10≤B/4 := ht.1
    rw [hS]; change 5*B+_+1+10*B ≤ 20*B; omega
  have hv := derivative_range T (till x) i.1 (gauge z Y.V) (funds_branch hT) (rotateG (lie v) (z∘S.ratio.parent))
    (attempt T F b) (fun i h => on_way F A x T z b i (hy i h))
  have hg : (scale T x Y.V *ᵥ Y.sh) i=0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h' : separation (base S i.1) (home S j.1) ≤ stencilD S.patch (till x)
    · rcases hy _ h' with H|H
      · simp [sh,fixed,real,H]
      simp only [show Y.sh j=0 from plateau_zero _ _ _ _ _ _ _ _ j H,mul_zero]
    dsimp only; rw [tangent_support T hT x Y.V i j (lt_of_not_ge h'),zero_mul]
  have h1 : AgreeNear id (base S i.1) B (gauge z Y.V) (represent b) := hc.shrink (le_trans
    (Nat.add_le_add_right hi B) (Nat.le_of_eq (by omega)))
  have h2 j (he : separation (base S i.1) j ≤ B) : j∉flags (temp x) (gauge z Y.V) := by
    rw [gauge_flags]; apply vacancy x A Y.V (20*B) hA.2 hl
    apply le_trans (separation_triangle _ (drow S i) _); exact (Nat.add_le_add hi he).trans (by omega)
  let U := target T (till x) (temp x) i.1 Y.k Y.V (replica S.ratio Y.V)
  let W := derivative T (till x) i.1 Y.V (lie v)
  have he : ‖U+W‖ ≤ allowance G D x 2 (7+7+9) := by
    have hp := h _ _ S T (gauge z Y.V) F Y.k hS hA.1 hT H K hK b i.1 hb h1 h2
    dsimp only at hp; rw [← hv, derivative_gauge T (till x) _ _ _ z hT] at hp
    rw [← copied S.ratio S.patch.odd_side Y.V z, constantGauge, target_gauge P hT] at hp
    rw [← map_add,G.norm_adjoint] at hp; exact hp
  let s := Real.sqrt weight
  have hf : (Y.D *ᵥ v) i = s* W i.2 := by
    have hm (j : Vars G f) (he : j.1∉activeB A F B) : v j = 0 := if_neg he
    calc _ = descend (Y.D *ᵥ v) i.1 i.2 := rfl
         _ = _ := by rw [summit _ _ _ _ _ _ _ hT hh hm]; rfl
  have hp : Y.actions v i = s*(U+W) i.2 := by
    unfold actions origin zeroed; rw [Pi.add_apply,if_pos hh,hf,hg]
    change s*W i.2 + (s*U i.2+0)= s*(U i.2+W i.2); ring
  rw [hp,abs_mul,abs_of_nonneg (show 0 ≤ s from Real.sqrt_nonneg _)]
  exact ((mul_le_mul_of_nonneg_left ((piece_cost ..).trans he) (Real.sqrt_nonneg _)).trans hr)
end row
end YM.AnalyticNext.ConnectedActivity.Aff
