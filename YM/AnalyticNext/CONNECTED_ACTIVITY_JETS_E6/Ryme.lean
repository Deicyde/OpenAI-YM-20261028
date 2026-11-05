import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Clods
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Facility
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Stove
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.StreamsCost
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Zest

/-!
# R-Sector at a Probe. Enough actual analyticity to pass to nearby parameters
 post-S. Not on an imaginary globally good neighborhood. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine  Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art  Poll Pond   
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:E}
variable {j n : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {X : Coat T F} {I : Finset (Bond f)} {η r Q q Y a β b p v d t w σ : ℝ} {C : E → Config G c}

lemma widen_mode (h : Mode C x j v) (hv : v<w) : ∀ᶠ y in 𝓝 x,Mode C y j w := by
  have hp i (k : ℕ) (he : 0<k) (hk : k≤j) : ∀ᶠ y in 𝓝 x, normJ k (fun j=> G.mat (C j i)) y ≤ royalty G*w^k := by
    have hZ := (h.atLink i)
    have hh := (hZ.order k hk).trans_lt (mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hv h.pos he.ne') (zero_lt_one.trans_le (royalty_ge G)))
    have hf := hZ.smooth.continuousAt_iteratedFDeriv (k:=k) (Nat.cast_le.mpr hk)
    filter_upwards [hf.norm.eventually (gt_mem_nhds hh)] with i hi; exact le_of_lt hi
  have hh i : ∀ᶠ y in 𝓝 x, Brush j (royalty G) w (fun j=> G.mat (C j i)) y := by
    filter_upwards [(Finset.eventually_all (Finset.Icc 1 j)).mpr (fun k hk=> hp i k (mem_Icc.mp hk).1 (mem_Icc.mp hk).2),
      (h.atLink i).smooth.eventually (by simp)] with y he hT
    refine ⟨hT,h.pos.trans hv.le,?_⟩; rintro (_|k) hk
    · unfold normJ; rw [pow_zero,mul_one,norm_iteratedFDeriv_zero]; exact (Gauge.unitary_frob (G.mat_mul_star _)).le
    exact he (k+1) (mem_Icc.mpr ⟨by omega,hk⟩)
  filter_upwards [eventually_all.mpr hh] with y hy using ⟨h.pos.trans hv.le,hy⟩

structure Glass (P : Teller G) (X : Coat T F) (C:E→ Config G c) (x:E) (j : ℕ) (W : ℝ) : Prop where
  lifts : C x=X.V
  sails : ∃ v:ℝ, Mode C x j v
  vest (i : Tubular f G) (k) : ContDiffAt ℝ (↑j) (fun y=> (vary X (C y)).plate i k) x
  winter : (X.relating).PosDef
  minted : ∀ i, IsUnit (X.shutter.principal X.plate i).det
  scroll (s i) : X.selected s (spot S i) → ContDiffAt ℝ (↑j : WithTop ℕ∞)
    (fun y=> Scroll.freely T X.x (pull s 0 (C y)) (choice s X.k) i) x
  figures (i : Mention c f) (u : Tubular f G) (b : G.ColorIndex) : ContDiffAt ℝ (↑j : WithTop ℕ∞)
    (fun y=> (vary X (C y)).form (i,b) u) x
  gracious : ∀ i, ContDiffAt ℝ (↑j) (fun y=>ArmA X.shutter (vary X (C y)).plate i) x
  tenuous : ∀ i, ContDiffAt ℝ (↑j) (fun y=>ArmS X.shutter (vary X (C y)).plate i) x
  condiment : ∀ i, ContDiffAt ℝ (↑j) (fun y=> (vary X (C y)).condensation i) x
  weather : Zest (fun Y y=> (drive X (C y) Y).saved) x j
  canopy (t : Signed) (i : Spot c f) : Zest (fun U y=> Scroll.loft T X.x U (choice t X.k) (pull t 0 (C y)) false i) x j ∧
      Zest (fun U y=> Scroll.loft T X.x U (choice t X.k) (pull t 0 (C y)) true i) x j

namespace Glass
lemma portal (P : Teller G) (D : Patch) (L : Side) (hD : D.Branches P.bind G) (j : ℕ) (χ : Chi) {f : ℝ→ℝ} (hp : Rate G L (-(1/2)) f)
    (hf : ∀ᶠ x in atTop, 0≤f x) (K γ W : ℝ) {η r Q : ℝ} (Y : ℝ) (ht : Torch η r Q) : ∀ᶠ x : ℝ in atTop,
    ∀ (c f':Side) (S: StepData c f') (T: Tube G S), S.patch=D → Works P L x S T → ShellAccess S G x W K γ →
      ∀ (F:Forest S.ratio) (X: Coat T F), X.width=K → X.χ=χ → X.x=x → Port P L η r Q Y X →
        ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (U:E→ Config G c) (z:E), U z=X.V →
        Mode U z j (f x) → Glass P X U z j W := by
  let g x:= f x+Pressure.fiery G x L
  have hg : Rate G L (-(1/2)) g := hp.add Rate.flame
  obtain ⟨B,hB,hV⟩:= Vine.signals G L W γ K j χ (v:=g) hg
  obtain ⟨A,hA,hY⟩:= hearthLift P L j hg
  obtain ⟨F,hF,hQ⟩:= certifiedBranch P L D hD j hp hf
  obtain ⟨C,hC,H⟩:= Vine.enlighten P L D hD 4 j le_rfl ht (-1) 1 1 (by norm_num) zero_le_one hp
  obtain ⟨R',p',hR,hp',hT⟩:= Vine.mistropy P L D hD j Y ht hp
  obtain ⟨E,hE,hΓ⟩:=bounded_stencils P D hD
  filter_upwards [hV,hY,hQ,H,hT] with x hx h hO H hD' c f' S T hS hP hv F' X hk hy ht hR F _ _ _ U z hX hm
  obtain ⟨a,b,ha,hb,hΨ⟩:= H _ _ S T hS hP
  subst x
  have hr : P.Funds S T:=hP.funds; have he : Port P L η r Q Y (vary X (U z)) := by rw [hX]; exact hR
  have hp:=hR.sails; have h':= hΨ F F' X U z rfl hm he.sails.scale
  have hy' : 0≤g X.x:= add_nonneg hm.pos (temp_nonneg _)
  have hH:= hΓ _ _ S T hS hr
  have hω : ∀ᶠ y in 𝓝 z,Mode U y j (g X.x) := widen_mode hm (lt_add_of_pos_right _ (by
    rw [← hP.length_eq]; exact hp.room.fiery))
  refine ⟨hX,⟨_,hm⟩,?_,hp.fullC,?_,?_,?_,fun i=> (h'.1 i).smooth,fun i=> (h'.2 i).smooth,?_,?_,?_⟩
  · exact fun i f=> ((Gate.plates X _ hS hP.length_eq hp.room hm E hE hH (le_refl 0) P.top.width_pos).singular i f).smooth
  · exact fun i=>Matrix.isUnit_det_of_right_inverse (hp.scale.sub (Embedding.subtype (fun j=>j∈ X.shutter.take i))).initial.1
  · intro s i hs; refine (hO _ _ S T hS hP _ _ F (fun t=>pull s 0 (U t)) z (Blaze.turn hm s) ?_).smooth
    rw [hX]; exact safe_hull X hR.placed s i hs
  · intro i j k; exact ((Gate.replicaM X _ hS hP.length_eq hp.room hm E hE hH (le_refl 0) P.top.width_pos).singular (i,k) j).smooth
  · intro i; exact ((hD' _ _ S T F' X F U z hS hP.length_eq rfl he hm i).1).smooth
  · refine ⟨|B X.x|,abs_nonneg _,hω.mono (fun y hy' Y=> Brush.fold zero_le_one (abs_nonneg _) (fun i=>?_))⟩
    exact hx c f' S T hP.length_eq hv F F' (X.wrapY Y) U y hy rfl hk hy' i
  intro s i
  let f y:= pull s 0 (U y); let K:= choice s X.k
  refine ⟨⟨|A X.x|,abs_nonneg _, hω.mono fun y hh Z=> (h c f' S T hP F Z K f y (Blaze.turn hh s) i).climb (le_abs_self _) le_rfl⟩,?_⟩
  let C:=scaleQ P L (till X.x)*(1+feeQ P (till X.x) (g X.x))^j
  refine ⟨|C|,abs_nonneg C,hω.mono (fun y hh Z=> ?_)⟩
  exact ((wild (k:=j) hr hP.length_eq (U:=fun _:F=> Z) ⟨hy',fun i=> a_oneB G (Z i) hy'⟩ (Blaze.turn hh s) K
    ⟨hy',fun i=> a_oneB G (S.prediction Z K i) hy'⟩ i X.x).trim).climb (le_abs_self _) le_rfl
end Glass
end YM.ConnectedActivityE6.Blaze
