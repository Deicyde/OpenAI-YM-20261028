import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Monitors
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Stint


/-!
# Central chart guards buy trigger disappearance (values)

Ticket spent on coordinate tiles. Shared between rotated or central
frames. Include all *possible* indices, even inactive; for each word
prove the expense sparse in `occupied`. Shrink on direction, doesn't
require a strict equality price between β and a real previous trajectory.
ε tested once after fixed thresholds (post-L). Values only here;
e.g. doesn't delete a U derivative by using equality without proving a
margin.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Jewels
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint  Wages
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

def pulls (S : StepData c f) (d : ℕ) (i : Site c) : Finset (Bond f) := reaches (home S) d i

def Awake (S : StepData c f) (d : ℕ) (i : Site c) (z : ArrayR G f) (K : ℝ) :=
    ∀ j : Vars G f, j.1∈pulls S d i → |z j| ≤ K

def cashB (Y : Mint T F A x) (β : ℝ) (z : ArrayR G f) := Y.μ+power β • z



def maxParts (G : Gauge) := Real.sqrt (Fintype.card G.ColorIndex)
lemma max_unit {r : ℝ} (hr : 0≤r) (a : G.Color) (h : ∀ i,|a i|≤r) : ‖a‖ ≤ maxParts G*r := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (show 0 ≤ maxParts G from Real.sqrt_nonneg _) hr)).mp
  rw [EuclideanSpace.real_norm_sq_eq,mul_pow, maxParts,Real.sq_sqrt (by positivity)]
  apply le_trans (sum_le_sum (g:=fun _ => r^2) (fun i _ => ?_)); simp
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i) _

lemma guard_broad (P : Teller G) (C : ℝ) (hc : Reserve P C) (D : Patch) (hb : D.Branches P.bind G) (ε : ℝ) (_hp : 0 ≤ ε)
    (X : Turns) : ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch=D → ∀ (A : Stores S) (F : Forest S.ratio)
      (Y : Mint T F A x), cert S x A Y.V → X.Takes (eyes S G (radiusB x)) Y.sheet (dcol S) (paceR x) →
      Y.u=holdSize G D x → ∀ z : ArrayR G f, ∀ i : Bond f, (∀ j : G.ColorIndex,|z (i,j)|≤ ε*fiery G x D.L) →
        ‖lie (Y.μ+z) i‖ ≤ chartSize G D x := by
  filter_upwards [towers_source P C hc D hb 1 X,pos_size G D,
    Rates.grow G D ε (show 0<13 by decide) 1, Rates.grow G D (maxParts G*2) (show 13<17 by decide) 1]
    with x hh he hx hv c f S T hT hS A F Y h hr hu z i hz
  have hg : 0 ≤ 2 * allowance G D x 1 13 := mul_nonneg (by norm_num) (allowance_nn ..)
  have hy := hh c f S T hS hT A F Y h (hu.symm ▸ he.2.1) hu.le hr
  have hp j : |lie (Y.μ+z) i j| ≤ 2*allowance G D x 1 13 := by
    have ht : ε*fiery G x D.L ≤ allowance G D x 1 13 := by simpa [allowance,pieces] using hx
    rw [two_mul]
    exact (abs_add_le ..).trans (add_le_add (hy.2.2 _) ((hz j).trans ht))
  rw [mul_assoc] at hv
  exact (max_unit hg _ hp).trans hv

lemma broad_stops (Y : Mint T F A x) (a : ArrayR G f) (i : Site c) (d : ℕ) (ht : 0 < radiusB x)
    (hD : d≤2*radiusB x) (he : i∉ A.dome (20*radiusB x)) {p : ℝ} (hp : 0≤p)
    (hy : ∀ j∈ activeB A F (radiusB x), separation i (home S j)≤d → ‖lie a j‖ ≤ p) :
    Stops S (Y.road a) Y.V (Y.build a) i d p := by
  have hv (e : Bond f) (hz : separation i (home S e)≤d) : ‖Y.road a e‖≤p ∧
      Y.build a e=increment (replica S.ratio Y.V) (Y.road a) e := by
    rcases environs F A x e _ _ he (by omega) with hk|hk
    · obtain ⟨h1,h2⟩ := Y.on_trunk a e hk; exact ⟨by rw [h1,norm_zero]; exact hp,h2⟩
    obtain ⟨h1,h2⟩ := Y.on_active a e hk; unfold increment; rw [h1]; exact ⟨hy _ hk hz,h2⟩
  exact ⟨fun j hj => (hv j hj).1,fun j hj => (hv j hj).2⟩

lemma guard_stops (P : Teller G) (C : ℝ) (hc : Reserve P C) (D : Patch) (hb : D.Branches P.bind G) (ε : ℝ) (hp : 0 ≤ ε)
    (X : Turns) : ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch=D → ∀ (A : Stores S) (F : Forest S.ratio)
      (Y : Mint T F A x), cert S x A Y.V → X.Takes (eyes S G (radiusB x)) Y.sheet (dcol S) (paceR x) →
      Y.u=holdSize G D x → ∀ (z : ArrayR G f) (i : Site c), let B := radiusB x; let a := Y.μ+z
      i∉A.dome (20*B) → Awake S B i z (ε*fiery G x D.L) → Stops S (Y.road a) Y.V (Y.build a) i B (chartSize G D x) := by
  filter_upwards [guard_broad P C hc D hb ε hp X,pos_size G D, Work.E01.radiusB_tendsto.eventually_ge_atTop 1]
    with x hx hp hh c f S T hT hS A F Y h hr hu z i B a he hz
  exact broad_stops Y a i B hh (by omega) he (hp.2.1.trans_le hp.2.2).le fun j _ he =>
    hx c f S T hT hS A F Y h hr hu z j (fun k => hz (j,k) (mem_filter.mpr ⟨mem_univ _,he⟩))

/-- Given δ (along positive root) buy ε on same read. Does not stipulate
truncated source to be centered enough: earned in Stint. -/
lemma guard_δ (P : Teller G) (C : ℝ) (hc : Reserve P C) (D : Patch) (hb : D.Branches P.bind G)
    (X : Turns) (δ : ℝ) (hd : 0<δ) : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch=D →
    ∀ (A : Stores S) (F : Forest S.ratio) (Y : Mint T F A x), cert S x A Y.V → ∀ J K, Alongside J K T →
    X.Takes (eyes S G (radiusB x)) Y.sheet (dcol S) (paceR x) → Y.u=holdSize G D x →
    ∀ (o : Pos S) (z : ArrayR G f), let B := radiusB x; let b := Y.μ+z; let i := base S o
    i∉ A.dome (20*B) → Awake S B i z (ε*fiery G x D.L) →
      ‖target T (till x) (temp x) o Y.k Y.V (Y.build b)‖ ≤ δ*fiery G x D.L := by
  obtain ⟨W,hW,H⟩ := gram_budget P D hb
  let v := maxParts G
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  let s := Real.sqrt weight; have hs : 0<s := Real.sqrt_pos.mpr weight_pos
  let ε := δ*s/(4*(1+v)*W)
  have hε : 0<ε := by unfold ε; positivity
  refine ⟨ε,hε,?_⟩
  filter_upwards [guard_stops P C hc D hb ε hε.le X,
    arc_bill P C hc D hb 17 (by norm_num), shifted P C hc D hb X, prepare D,
    burn G D 1 40 1 (δ/2) (by positivity), burn G D 1 29 1 (W*ε) (by positivity),pos_size G D]
    with x hx ht he hp hh hf hb c f S T hT hS A F Y hY K L hK hr hu o z B b i h hh'
  let t := fiery G x D.L
  have ht' : 0<t := hb.1
  let g := Y.road b
  have hw j : |Y.actions b (o,j)| ≤ 2*W*ε*t := by
    have hy : ∀ k : Vars G f,Y.D (o,j) k ≠0 → |z k| ≤ ε*t := by
      intro k hk
      apply hh'; refine mem_filter.mpr ⟨mem_univ _,?_⟩
      apply le_trans (spring Y (o,j) k hk hT); rw [hS]; omega
    have hm : |(Y.D *ᵥ z) (o,j)| ≤ W*(ε*t) := row_ball _ _ _ (H c f S T hT hS F A Y.V x).affine.1
      (half_pos P.top.width_pos).le z (by positivity) (o,j) hy
    have hz : |Y.actions Y.μ (o,j)| ≤ allowance G D x 2 29 := he c f S T hT hS K L hK F A Y hY hr _ h
    have hx : allowance G D x 2 29 ≤ W*ε*t := by
      simpa only [show allowance G D x 1 0=t from by simp [allowance,pieces,t],one_mul] using hf
    rw [show Y.actions b=Y.actions Y.μ + Y.D *ᵥ z by unfold actions b; rw [mulVec_add]; abel]
    exact ((abs_add_le ..).trans (add_le_add (hz.trans hx) hm)).trans_eq (by ring)
  let u := target T (till x) (temp x) o Y.k Y.V (replica S.ratio Y.V) + derivative T (till x) o Y.V g
  have hm : ‖u‖ ≤ (δ/2)*t := by
    apply le_of_mul_le_mul_left _ hs
    have hh : s*‖u‖≤v*(2*W*ε*t) := calc
      _ = ‖descend (Y.actions b) o‖ := by rw [Y.roads b o (mem_filter.mpr ⟨mem_univ _,
              fun he => h (placed A _ _ (by omega) he)⟩) hT,norm_smul, Real.norm_of_nonneg hs.le]
      _ ≤ _ := max_unit (a:=descend (Y.actions b) o) (show 0≤ 2*W*ε*t by positivity) hw
    apply hh.trans
    apply le_trans (mul_le_mul_of_nonneg_right (by linarith only [] : v≤1+v) (show 0 ≤ 2*W*ε*t by positivity))
    exact le_of_eq (by unfold ε; field_simp; ring)
  have ha : ‖target T (till x) (temp x) o Y.k Y.V (Y.build b)-u‖ ≤ allowance G D x 2 40 :=
    (ht c f S T hS hT Y.V A F hY Y.k (Y.build b) o g (fun he => h (placed A _ _ (by omega) he))
      (hx c f S T hT hS A F Y hY hr hu z _ h hh')).2
  have hh : allowance G D x 2 40 ≤ (δ/2)*t := by
    simpa only [show allowance G D x 1 0=t from by simp [allowance,pieces,t],one_mul] using hh
  exact (norm_le_norm_sub_add _ u).trans ((add_le_add (ha.trans hh) hm).trans_eq (by unfold t; ring))
end YM.AnalyticNext.ConnectedActivity.Jewels
