import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Curtain

/-!
# Local expenses even on broad regular and frozen shell stencils

Quantitative, no cost of inverse heat divided out yet. Key
`Aff.arc_bill`. Extension not by enforcing good `U` outside the patch.
Selections shared with all roots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Rates
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

def Stops (S : StepData c f) (a : Directions G f) (V : Config G c) (U : Config G f) (i : Site c)
    (R : ℕ) (w : ℝ) :=
    (∀ j : Bond f,separation i (home S j) ≤ R → ‖a j‖ ≤ w) ∧
      AgreeNear S.ratio.parent i R U (increment (replica S.ratio V) a)

lemma in_scene (S : StepData c f) (x : Site c) (s : Directions G f) (V : Config G c) (U : Config G f)
    (z : Site c → G.El) (R : ℕ) (w : ℝ) (he : 0 ≤ w) (h : Stops S s V U x R w)
    (b : LogField G c) (hp : AgreeNear id x R (gauge z V) (represent b)) :
    ∃ a : Directions G f,(∀ j, ‖a j‖≤w) ∧
    (∀ j : Bond f, separation x (home S j) ≤ R → rotateG s (z ∘ S.ratio.parent) j = a j) ∧
      AgreeNear S.ratio.parent x R (gauge (z ∘ S.ratio.parent) U) (increment (replica S.ratio (represent b)) a) := by
  let a (j : Bond f) := if separation x (home S j)≤ R then rotateG s (z∘S.ratio.parent) j else 0
  have hh i (he : separation x (home S i) ≤ R) : a i = rotateG s (z∘S.ratio.parent) i := if_pos he
  refine ⟨a,fun j => ?_,fun j he => (hh j he).symm,shadows b s a hp h.2 fun i h => (hh i h).symm⟩
  dsimp only [a]; split
  next hi => rw [rotateG, G.norm_adjoint]; exact h.1 j hi
  next => rwa [norm_zero]

lemma quadratic_forecast (P : Teller G) (D : Patch) (hd : D.Branches P.bind G) (p : ℕ) : ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (a : LogField G f) (y : Pos S),
      S.patch=D → P.Funds S T → ‖a‖≤allowance G D x 2 p → ‖forecast T y a 0‖ ≤ allowance G D x 2 (p+1) := by
  obtain ⟨C,τ,r,hC,_,hr,h⟩ := ordered_cost P D hd
  filter_upwards [(vanishes G D 0).eventually (ge_mem_nhds hr),grow G D C (by omega : p<p+1) 2,
    burn G D 1 p 1 1 (by norm_num)] with x hx hp hv c f S T a y hD hT he
  let H := allowance G D x 2 p
  rw [one_mul,one_mul] at hv
  exact ((h c f S T hT hD a 0 H (hv.trans hx) he (by rw [norm_zero]; exact allowance_nn ..) 0
    Classical.ofNonempty).2 y).1.trans hp

/-- Uniform **pointwise in sector** affine error bound on real weak
patch. Allow rough V elsewhere, no mask on U retained in conclusions
here. r uses `t` unit of fine scale. -/
theorem arc_bill (P : Teller G) (C : ℝ) (he : Reserve P C) (D : Patch) (hD : D.Branches P.bind G)
    (p : ℕ) (hp : 7 ≤ p) : ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
      S.patch=D → P.Funds S T → ∀ (V : Config G c) (A : Stores S) (_F : Forest S.ratio), cert S x A V →
      ∀ (k : S.Choices) (U : Config G f) (a : Pos S) (s : Directions G f), let B := radiusB x
      base S a ∉ A.dome (2*B) → Stops S s V U (base S a) B (allowance G D x 1 p) → let R := till x; let t := temp x
      ‖target T R t a k V U‖ ≤ allowance G D x 1 (p+4) ∧
      ‖target T R t a k V U- (target T R t a k V (replica S.ratio V) + derivative T R a V s)‖ ≤
        allowance G D x 2 (p+p+6) := by
  filter_upwards [remote_frame G D 1 (by norm_num), first_bill P C he D hD p, Rates.widen G D 1 hp,
    pressing G D p, prepare D, late_cost P D hD (p+1), he.receipt D.L,
    residual_cost P D hD (p+1) p, quadratic_forecast P D hD (p+p+1),
    burn G D 1 (p+1+(p+1)+3) 1 1 (by norm_num), chord_price G D p,
    Rates.widen G D 1 (show p≤p+1 by omega), Rates.widen G D 1 (show 0≤p+1+1 by omega),
    grow G D 2 (show p+1+1<p+4 by omega) 1, Rates.widen G D 2 (show p+p+3≤p+1+(p+1)+3 by omega),
    Rates.widen G D 2 (show p+p+1+1≤p+1+(p+1)+3 by omega),
    Rates.widen G D 2 (show p+1+p+4≤p+1+(p+1)+3 by omega),
    grow G D 4 (show p+1+(p+1)+3<p+p+6 by omega) 2]
    with x hx hu hp ht hH hy hm hh hf hd hK hv hl hz hi hq hG hX c f S T hS hT V A F hL k U a s B hA hw R t
  let Y := allowance G D x 1 p; let Z := allowance G D x 2 (p+1+(p+1)+3)
  let o := base S a
  obtain ⟨z,b,hb,hc⟩ := hx c f S hS A V hL o hA
  have hb : ‖b‖ ≤ Y := hb.trans hp
  let W := gauge z V; let X := z∘S.ratio.parent
  have ha : ∀ v,separation (base S a) v≤B → v∉ RG.flags (temp x) W := fun v h => by
    unfold W; rw [gauge_flags]; apply vacancy x A V (2*B) hL.2 hA; omega
  rw [one_mul] at hc
  let c' := form (linearCopy S.ratio (collect G b))
  let u := target T R t a k V U
  let w := target T R t a k V (replica S.ratio V)
  let d := derivative T R a V s
  let F' := forecast T a c' b
  have he : ‖G.adjoint (z o) w-F'‖ ≤ Z := by
    have h := (hu c f S T W F hT hS hL.1 k a b hb hc ha).2
    unfold w
    rw [show z o=z (base S a) from rfl,← target_gauge P hT]
    apply le_trans _ hi
    rw [show gauge (z ∘ S.ratio.parent) (replica S.ratio V)=replica S.ratio W from copied S.ratio S.patch.odd_side V z]
    exact h
  obtain ⟨r,hr,hV,hU⟩ := in_scene S o s V U z B Y (allowance_nn ..) hw b hc
  obtain ⟨a',h1,h2⟩ := ht _ r c' hr ((shadow_copy S.ratio b).2.trans hb)
  let g := forecast T a a' b; let y := forecast T a (form r) 0
  have hkey : G.adjoint (z o) u = primal T R a k (represent b) (represent a') := by
    have hT' := (hm c _ S T hT (congr_arg Patch.L hS) hL.1 F W).2.1
    rw [(shadow_copy S.ratio b).1,h1] at hU
    rw [← show target T R t a k W (gauge X U) = G.adjoint (z o) u from target_gauge P hT ..,
      target_unveiled T x _ _ _ _ hT' ha]
    have hv : radial R S.patch ≤ B := by rw [hS]; apply hH.2.trans (Nat.div_le_self ..)
    exact primal_local T R _ _ (funds_branch hT) (hU.shrink (show separation o o + radial R S.patch ≤ B by simpa))
      (hc.shrink (show separation o o + radial R S.patch ≤ B by simpa))
  obtain ⟨h1,h3⟩ := (hy c _ S T hT hS a' b h2.1 (hb.trans hv)).2 k a
  have h3 : ‖G.adjoint (z o) u - g‖ ≤ Z := by rw [hkey]; exact h3
  constructor
  · have ht := norm_le_norm_sub_add (G.adjoint (z o) u) g
    change ‖u‖ ≤ _; rw [← G.norm_adjoint (z o) u]
    change ‖g‖≤_ at h1; change 1*Z≤1*_ at hd
    linarith only [h1,h3,ht,hd,hz,hl]
  have hd : ‖y-G.adjoint (z o) d‖ ≤ Z := by
    unfold d
    rw [show z o=z (base S a) from rfl, ← derivative_gauge T R a V s z hT, derivative_range T R a W (funds_branch hT) _ r ?_]
    apply le_trans _ hG
    apply hh c _ S T hS hT a W r _ hr
    · intro j hj
      unfold W; rw [hc j (show separation o j.1≤radiusB x by change _≤_ at hj; unfold o; omega)]
      exact hK _ b hb j
    intro i hi
    apply hV; unfold R at hi; rw [hS] at hi; unfold o B; omega
  have hk : ‖g-(F'+y)‖ ≤ Z := by
    let j := a' - (c'+form r)
    have h : ‖forecast T a j 0‖ ≤ Z := (hf c _ S T j _ hS hT h2.2).trans hq
    have he : a'=(c'+form r)+j := by unfold j; abel
    have hy : g=F'+y+forecast T a j 0 := by unfold g; conv_lhs => rw [he,forecast_step hT,forecast_step hT]
    rwa [hy, add_sub_cancel_left]
  change ‖u-(w+d)‖ ≤ _
  rw [← G.norm_adjoint (z o) (u-(w+d)),map_sub,map_add]
  apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ g _)
  apply le_trans (add_le_add h3 (le_trans (norm_sub_le_norm_sub_add_norm_sub g (F'+y) _)
      (add_le_add hk ?_))) (show Z+(Z+(Z+Z))≤_ from by convert hX using 1; unfold Z; ring)
  let t := G.adjoint (z o) w; let v := G.adjoint (z o) d
  change ‖(F'+y)-(t+v)‖≤_
  rw [show F'+y-(t+v)=y-v-(t-F') by abel]; exact (norm_sub_le ..).trans (add_le_add hd he)
end YM.AnalyticNext.ConnectedActivity.Aff
