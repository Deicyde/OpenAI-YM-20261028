import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Through
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Warsaw

/-!
# Real no-hole payment for the shift obstruction

A seed halo not required to be disjoint from the support e.g. of the
K-bearing word. Only check flags/projections where using the stencil.
Specifically this concerns the first term of E \\eqref(Frco),
the extensive correction after completing the global square. No
payment for its FIELD-dependence by interpreting it as global scalar.
Split per row on the same chosen record: each term separately small on
the remote (not-in-packet-core); on the packet use its own sign.
Then estimates on the actual physical trigger tests can exploit this
forecast. Doesn't use ticket quantities coming from core activities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Filter Win Rates Green Mint Win.Promise
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {S' : Teller G} {c f : Side} {S : StepData c f}
  {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {x : ℝ}

lemma spring (Y : Mint T F A x) (i : Ix G S) (j : Vars G f) (h : Y.D i j≠0) (hT : S'.Funds S T) :
    separation (drow S i) (dcol S j) ≤ stencilD S.patch (till x) := by
  apply le_of_not_gt; intro H
  apply h; simp only [Mint.D, Dmat, Matrix.of_apply,tangent_support _ hT _ _ i j H,ite_self]

lemma absence (Y : Mint T F A x) (v : ArrayR G f) (h : ∀ i : Vars G f,i.1∉activeB A F (radiusB x) → v i=0) :
    Y.sheet *ᵥ v+Y.source=Y.D.transpose *ᵥ (Y.actions v) := by
  unfold sheet gram actions Mint.D source
  rw [Matrix.mulVec_add, add_mulVec, Matrix.mulVec_mulVec]
  have he : Matrix.diagonal (fun j : Vars G f => if j.1 ∉ activeB A F (radiusB x) then 1 else 0) *ᵥ v=0 := by
    funext i
    rw [Matrix.mulVec_diagonal]; split
    next ht => rw [h i ht,mul_zero]; rfl
    next => rw [zero_mul]; rfl
  rw [he,add_zero]

-- `u` about here germ chart radii not used, so works at all real offpatch extensions.
theorem velocity (P : Teller G) (C : ℝ) (he : Reserve P C) (D : Patch) (hD : D.Branches P.bind G) (q : Turns) : ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch=D →
    ∀ (H K : Bed), Alongside H K T → ∀ (F : Forest S.ratio) (A : Stores S) (Y : Mint T F A x), cert S x A Y.V →
      let B := radiusB x
      q.Takes (eyes S G B) Y.sheet (dcol S) (paceR x) →
      ∀ (o : Site c) (_ht : o∉A.dome (20*B)) (z : Site c → G.El) (b : LogField G c),
        ‖b‖ ≤ allowance G D x 1 7 → AgreeNear id o (6*B) (gauge z Y.V) (represent b) →
        let v := unit F A x T z b
        ∀ i : Vars G f, separation o (dcol S i)≤2*B →
          |(Y.μ - v) i| ≤ allowance G D x 2 27 := by
  obtain ⟨W,hW,H⟩ := gram_budget P D hD
  filter_upwards [pre_center P C he D hD, shot_budget P 7 D,
    prepare D, Work.E01.radiusB_tendsto.eventually_ge_atTop 8,
    shrink_pace q G D 1 1 zero_le_one,Rates.widen G D 2 (show 0+(7+2)≤24 by norm_num),
    Rates.grow G D W (by decide : 24<25) 2,Rates.widen G D 2 (by omega : 24≤26),
    Rates.grow G D q.base (by decide : 25<26) 2,Rates.grow G D 2 (by decide : 26<27) 2]
    with x hx hs hp hM hz hc hK hl hq hm c f S T hT hS M L hL F A Y hY B hV o hA z b hb hv v i hi
  let E := eyes S G B
  have he : stencilD S.patch (till x) ≤ B := by rw [hS]; unfold B; omega
  have hr i : |v i| ≤ allowance G D x 1 (7+2) := unit_pars F A x T z b i.1 _ (allowance_nn ..)
    (hs c f S T F b hS hT hb i.1) i.2
  have hf : ∀ j,separation o (dcol S j) ≤ 4*B → |(Y.sheet *ᵥ v+Y.source) j| ≤ allowance G D x 2 25 := by
    intro j hj
    rw [absence Y v (fun _ hr => if_neg hr)]
    have hh := (H c f S T hT hS F A Y.V x).affine.2
    apply le_trans (row_ball _ _ _ hh (half_pos P.top.width_pos).le _
      (allowance_nn G D x 2 24) j (fun k hh => ?_)) hK
    apply hx c f S T hT hS M L hL F A Y hY o hA z b hb hv
    apply le_trans (separation_triangle _ (dcol S j) _); rw [separation_comm (dcol S j)]
    have hh : Y.D k j≠0 := hh
    exact (Nat.add_le_add hj ((spring Y k j hh hT).trans he)).trans (by omega)
  let N := Y.sheet *ᵥ v + Y.source
  let Pz := E.within Y.sheet; let D' := E.error Y.sheet
  obtain ⟨hg,hrm⟩ := span q T F A _ hV
  have hh : |(D'.transpose *ᵥ v) i| ≤ allowance G D x 2 26 := by
    apply le_trans (row_ball _ _ _ hrm.2 q.wide.le _ (allowance_nn G D x 1 (7+2)) i fun j _ => hr j)
    rw [one_mul] at hz
    calc
      _ ≤ allowance G D x 1 0 * allowance G D x 1 (7+2) := mul_le_mul_of_nonneg_right hz (allowance_nn ..)
      _ ≤ _ := (exchange ..).le.trans (hc.trans hl)
  have hy : |(Pz.transpose *ᵥ N) i| ≤ allowance G D x 2 26 := by
    apply le_trans (row_ball _ _ _ hg.2 q.wide.le N (allowance_nn G D x 2 25) i fun j hh => ?_) hq
    apply hf; apply le_trans (separation_triangle _ (dcol S i) _)
    apply (Nat.add_le_add hi ?_).trans (show 2*B+(B/4+2)≤4*B by unfold B; omega)
    rw [separation_comm]
    apply travelB
    by_contra hn
    apply hh; change (Win.Windows.within E Y.sheet) j i=0
    unfold Windows.within; rw [Matrix.of_apply,dif_neg hn]
  rw [takes_sub Y]; change |((-(Pz.transpose)) *ᵥ N + D'.transpose *ᵥ v) i| ≤ _
  rw [neg_mulVec, Pi.add_apply, Pi.neg_apply]
  have hw : |-((Pz.transpose *ᵥ N) i)| ≤ allowance G D x 2 26 := by rw [abs_neg]; exact hy
  exact ((abs_add_le ..).trans (add_le_add hw hh)).trans
    (by linarith)

/-- The requested C^0 remainder from the actual selected Gaussian shift remote from geometry changes. -/
theorem shifted (P : Teller G) (C : ℝ) (he : Reserve P C) (D : Patch) (hD : D.Branches P.bind G) (q : Turns) : ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch=D →
    ∀ (H K : Bed), Alongside H K T → ∀ (F : Forest S.ratio) (A : Stores S) (Y : Mint T F A x), cert S x A Y.V →
      let B := radiusB x
      q.Takes (eyes S G B) Y.sheet (dcol S) (paceR x) →
      ∀ i : Ix G S,drow S i∉A.dome (20*B) → |Y.actions Y.μ i| ≤ allowance G D x 2 29 := by
  obtain ⟨W,hW,H⟩ := gram_budget P D hD
  filter_upwards [velocity P C he D hD q,Rates.widen G D 2 (show 24≤28 by decide),
    remote_frame G D 6 (by norm_num), pre_center P C he D hD,
    Rates.grow G D W (show 27<28 by decide) 2, Rates.grow G D 2 (show 28<29 by decide) 2,
    prepare D] with x hu ht hh hr hm hq hv c f S T hT hS M L he F A Y hY B h i hi
  let o := drow S i
  obtain ⟨z,b,hb,hp⟩ := hh c f S hS A Y.V hY o (fun he => hi (placed A _ _ (by omega) he))
  let v := unit F A x T z b
  have hz : Y.actions Y.μ=Y.actions v+Y.D *ᵥ (Y.μ-v) := by unfold actions; rw [Matrix.mulVec_sub]; abel
  rw [hz,Pi.add_apply]; apply le_trans ((abs_add_le ..).trans (add_le_add ?_ ?_))
    (by simpa only [two_mul] using hq)
  · exact (hr c f S T hT hS M L he F A Y hY o hi z b hb hp i (by unfold o; simp)).trans ht
  apply le_trans (row_ball _ _ _ (H c f S T hT hS F A Y.V x).affine.1 (half_pos P.top.width_pos).le _
    (allowance_nn G D x 2 27) i (fun j hj => ?_)) hm
  apply hu c f S T hT hS M L he F A Y hY h o hi z b hb hp
  apply le_trans (spring Y _ j hj hT); rw [hS]; omega
end YM.AnalyticNext.ConnectedActivity.Aff
