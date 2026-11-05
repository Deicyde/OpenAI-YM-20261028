import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Draught
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Ground

/-!
# The real small chord expenses on a chart stencil

The bridge to the Z estimate on the minimizing branch. No copy of S at
another normalization. Includes potential turns; estimate uses the same
vocabulary in two possibly different patch gauges. Nothing here forbids
another operation using a nonminimizing tag at a different site.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Rates
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

-- in row coordinates
def Lit (S : StepData c f) (V : Config G c) (U : Config G f) (p : Site c)
    (R : ℕ) (h : ℝ) (z : Site c→G.El) :=
    (∀ i : Bond c,separation p i.1≤R → G.chord (gauge z V i) ≤ h) ∧
      (∀ i : Bond f, separation p (S.ratio.parent i.1) ≤ R → G.chord (gauge (z ∘ S.ratio.parent) U i) ≤ h)

lemma shine (G : Gauge) (D : Patch) (p : ℕ) (hp : 7 ≤ p) : ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (U : Config G f) (V : Config G c) (A : Stores S) (w : Directions G f),
    S.patch=D → cert S x A V → let B := radiusB x
    ∀ (s : Signed) (y : Site c), s.act y∉A.dome (2*B) → Stops S w V U (s.act y) B (allowance G D x 1 p) →
    ∃ z, Lit S (pull s 0 V) (pull s 0 U) y (B/2) (allowance G D x 1 (p+2)) z := by
  filter_upwards [remote_frame G D 1 (by norm_num), Work.E01.radiusB_tendsto.eventually_ge_atTop 2,
    pressing G D p, Rates.widen G D 1 hp, chord_price G D (p+1),
    Rates.widen G D 1 (show p≤p+1 by omega)] with x hx hv he hb hp hm c f S U V A w hS hV B s y hy hw
  obtain ⟨z,b,ha,h⟩ := hx c f S hS A V hV _ hy
  let u := z∘s.act (R:=Per c)
  have hu : (z∘S.ratio.parent)∘s.act=u∘ S.ratio.parent := by funext i; rw [Function.comp_apply,
    Function.comp_apply,S.ratio.parent_signed S.patch.odd_side]; rfl
  refine ⟨u,?_⟩
  rw [one_mul] at h
  obtain ⟨a,ht,hq,hd⟩ := in_scene S (s.act y) w V U z B _ (allowance_nn ..) hw b h
  obtain ⟨r,h1,h2,_⟩ := he f a _ ht ((shadow_copy S.ratio b).2.trans (ha.trans hb))
  rw [(shadow_copy S.ratio b).1,h1] at hd
  have hc {n : Side} (W : Config G n) (t : Bond n) : G.chord (pull s 0 W t)=G.chord (W (edgeP s t)) := by
    rw [step_transport]; split
    next => rw [G.chord_inv]
    next => rfl
  constructor
  · intro i hi
    have he : separation (s.act y) (edgeP s i).1≤ B := (directed_climb s y i).trans (by change _≤B; omega)
    unfold u; rw [← gauge_pulled,hc,h _ he]; exact hp c b ((ha.trans hb).trans hm) _
  intro i hi
  have he : separation (s.act y) (home S (edgeP s i))≤ B := (along_home s y S i).trans (by unfold home; omega)
  rw [← hu,← gauge_pulled,hc,hd _ he]; exact hp f r h2 _

lemma centering (z : Site c→G.El) (b : Bond c) (k : S.Choices) (U : Config G f) (V : Config G c)
    (h : S.patch.Branches S.kernel G) : wire (S.prediction (gauge (z∘S.ratio.parent) U) k) (gauge z V) b =
    wire (S.prediction U k) V b := by
  rw [(choice_gauge h U k _).2, show (z∘ S.ratio.parent) ∘ S.ratio.embed = z from by
    funext; simp [Function.comp_def,S.ratio.embed_parent],wire_gauge]

lemma face_pays (G : Gauge) (D : Patch) (p : ℕ) : ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (a : Cell f) (V : Config G c) (U : Config G f) (z : Site c→G.El),
    Lit S V U (S.ratio.parent a.1) (radiusB x/2) (allowance G D x 1 p) z → toll U a ≤ allowance G D x 1 (p+1) := by
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 8,
    grow G D 4 (show p<p+1 by omega) 1] with x hx ht c f S a V U z h
  let W := gauge (z ∘ S.ratio.parent) U
  let v (i : Bond f) := if separation (S.ratio.parent a.1) (home S i) ≤ radiusB x/2 then W i else 1
  have hv i : G.chord (v i) ≤ allowance G D x 1 p := by
    unfold v; split
    next he => exact h.2 i he
    next => rw [G.chord_one]; exact allowance_nn ..
  have he : toll W a = toll v a := by
    unfold toll faceValue
    rw [travel_near S.ratio.parent (Work.E03.parent_step S) W v a.1 _ (radiusB x/2) ?_ ?_]
    · exacts [show 4≤_ by omega]
    exact fun j hj => (if_pos hj).symm
  rw [← show toll W a = toll U a from toll_gauge ..,he]
  exact (travel_chord v (square ..) a.1 _ hv).trans ht

-- Tag masses (individual normalized, shared through each spun packet).
def αSite (U : Config G f) (i : Site c) (k : S.Choices) := (Fintype.card S.patch.FrameTag : ℝ)*
    S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) U) (k.1 i)

def αBond (U : Config G f) (b : Bond c) (k : S.Choices) := (Fintype.card S.patch.Points : ℝ)*
    S.patch.predictorMass S.kernel (S.connector U k.1 b) (k.2 b)

lemma symmetric_mass (U : Config G f) (i : Bond c) (k : S.Choices) (h : S.patch.Branches S.kernel G)
    (z : Site f→G.El) : αSite (gauge z U) i.1 k = αSite U i.1 k ∧ αBond (gauge z U) i k=αBond U i k := by
  constructor
  · unfold αSite; rw [expandAt_gauge,(S.patch.frame_gauged h ..).1]
  unfold αBond; rw [S.updateGauged h,(S.patch.bond_gauge (h:=h) ..).1]

/-- The small-chord receipt (before using that small-chord branch to
turn Z estimate into quantitative wire payment). -/
lemma cordF (D : Patch) (K : KernelChoices) (hd : D.Branches K G) (p : ℕ) (r : ℝ) (hr : 0<r) :
    ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (i : Bond c) (V : Config G c)
      (U : Config G f) (z : Site c→G.El) (k : S.Choices), S.patch=D → S.kernel=K →
      Lit S V U i.1 (radiusB x/2) (allowance G D x 1 p) z →
      wire (S.prediction U k) V i < r ∧ αSite U i.1 k=1 ∧ αBond U i k=1 := by
  filter_upwards [tap_open D K hd p (r/2) (by positivity),
    (vanishes G D p).eventually (ge_mem_nhds (show 0<r/2 by positivity))]
    with x ht hx c f S i V U z k hS hK he
  let W := z∘ S.ratio.parent; let Q := S.prediction (gauge W U) k
  have hf := ht S hS hK _ k i he.2
  have hd : S.patch.Branches S.kernel G := by rw [hS,hK]; assumption
  rw [← centering z i k U V hd]
  refine ⟨?_,?_,?_⟩
  · let X := gauge z V
    have hm : G.chord (X i) ≤ r/2 := (he.1 i (by simp)).trans hx
    apply lt_of_le_of_lt (G.chord_triangle ..); rw [G.chord_inv]
    exact (add_lt_add_of_le_of_lt hm hf.2.2).trans_eq (by ring)
  · rw [← (symmetric_mass U i k hd W).1,αSite, Patch.frameMass, if_pos]
    · exact mul_inv_cancel₀ (show (Fintype.card S.patch.FrameTag:ℝ)≠0 from by positivity)
    rw [hK]; exact hf.1
  rw [← (symmetric_mass U i k hd W).2, αBond, Patch.predictorMass, if_pos]
  · exact mul_inv_cancel₀ (show (Fintype.card S.patch.Points:ℝ)≠0 from by positivity)
  rw [hK]; exact hf.2.1
end YM.AnalyticNext.ConnectedActivity.Aff
