import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Throne

/-!
# The accompanying short rows L/D/N/C, all rotations

Real predictor and thinned input retained here, no analytic-at-germs
assumption on backed `w`; hence ready to add each item independently to
optional price tests. No redistributing out to selected/unselected
neighbors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Rates
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

lemma flag_turn (U : Config G n) (s : Signed) (v) (y) (h : y ∈ RG.flags v (pull s 0 U)) : s.act y ∈ RG.flags v U := by
  rw [← Work.H03.flags_send s 0 v U]; exact mem_image.mpr ⟨y,h,add_zero _⟩

lemma normC (T : Tube G S) (W : Config G c) (p : Cell c) (R : ℕ) (t : ℝ) (he : toll W p ≤ t) :
    T.workC R W t p = -(T.low.direct/2*missed G (faceValue W p)) := by
  rw [Work.E05.workC_eq, PathData.clipped, if_pos he]
  have h : (if toll W p=0 then 1 else min 1 (t / toll W p))=1 := by
    split
    next => rfl
    next h =>
      rw [min_eq_left]; rw [le_div_iff₀ (lt_of_le_of_ne (show 0≤toll W p from G.chord_nonneg _) (Ne.symm h)),one_mul]; exact he
  rw [h]; unfold missed toll; ring

lemma earnsC (P : Teller G) (D : Patch) : ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (V : Config G c) (A : Stores S), P.Funds S T → cert S x A V →
    ∀ (s : Signed) (p : Cell c), s.act p.1 ∉ A.dome (2*radiusB x) →
    |T.workC (till x) (pull s 0 V) (temp x) p| ≤ allowance G D x 4 5 := by
  filter_upwards [currency (G:=G) (P.below.clip.direct/2) D 1, grow G D 2 (by decide : 0<1) 1,
    closer G D] with x hx hv he c f S T V A hT hA s p hp
  have hh := he.1.trans (show 2 * fiery G x D.L ≤ allowance G D x 1 1 by simpa [allowance,pieces] using hv)
  have hs : toll (pull s 0 V) p ≤ temp x := honor fun hs => vacancy x A V _ hA.2 hp _ (by simp) (flag_turn V s _ _ hs)
  rw [normC T _ _ _ _ hs,hT.low,abs_neg]
  exact hx _ (hs.trans hh)

lemma lends (D : Patch) (G : Gauge) (p : ℕ) (τ : ℝ) (ht : 0<τ) : ∀ᶠ x : ℝ in atTop,
    Next.Fluctuations.widen (till x) (allowance G D x 1 p) τ ≤ allowance G D x 1 (p+2) := by
  filter_upwards [decay G D ht 1 0 1,Rates.widen G D 1 (show 0 ≤ p+1 by omega),
    Work.E01.radiusB_tendsto.eventually_ge_atTop 2,grow G D 2 (show p+1<p+2 by omega) 1] with x hh hx hv hp
  apply le_trans _ hp
  unfold Next.Fluctuations.widen; rw [two_mul]
  apply add_le_add _ (le_trans (by simpa [pieces] using hh) hx)
  have ht : 1+(till x:ℝ) ≤ (radiusB x:ℝ) := by exact_mod_cast (show 1+till x ≤ _ by unfold till; omega)
  calc
    _ ≤ (radiusB x:ℝ)*_ := mul_le_mul_of_nonneg_right ht (allowance_nn ..)
    _ = _ := by unfold allowance pieces; ring

lemma earnsN (P : Teller G) (C : ℝ) (he : Reserve P C) (D : Patch) (hd : D.Branches P.bind G) : ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (V : Config G c) (A : Stores S) (_F : Forest S.ratio),
      S.patch=D → P.Funds S T → cert S x A V → ∀ K H, Alongside K H T →
    ∀ (s : Signed) (p : Co c Gain), s.act p.1 ∉ A.dome (2*radiusB x) →
      T.workN (till x) (pull s 0 V) (temp x) p ≤ allowance G D x 4 34 := by
  filter_upwards [prepare D,remote_frame G D 1 (by norm_num), late_cost P D hd 7, he.receipt D.L,
    Work.E01.radiusB_tendsto.eventually_ge_atTop 10] with x hx hh ht hp hv c f S T V A F hS hT he K H hA s p hk
  let V' := pull s 0 V; let y := s.act p.1; let B := radiusB x; let R := till x
  obtain ⟨z,b,hb,h⟩ := hh c f S hS A V he _ hk
  let w := z∘s.act (R:=Per c); let X := gauge w V'; let a := orient s b
  have hr : AgreeNear id p.1 (B/2) X (represent a) := by
    rw [one_mul] at h
    unfold X V' a; rw [orient_represents]; unfold w; rw [← gauge_pulled]; apply pull_agreesCoarse
    apply h.shrink; simp; omega
  have hV u (hy : separation p.1 u ≤ B) : u ∉ RG.flags (temp x) X := by
    unfold X; rw [gauge_flags]; intro hf
    apply vacancy x A V _ he.2 hk _ _ (flag_turn V s _ _ hf); rw [separation_signed]; omega
  let t := temp x
  let m := zip (T.N R X) (T.vision R t X) p
  have hu : 2*R+4 ≤ B/2 := by unfold R B; unfold radial at hx; omega
  have hm : m=primalN T R (represent a) p := by
    rw [← primalN_local T R p X (represent a) (hr.shrink (by rw [separation_self,zero_add]; exact hu))]
    apply Unseen.pay _ _ _ (i:=p) (laneSight T.R.o S.patch.L.val R S.patch.L.property id mesh) (fun _ _ => rfl)
    intro j hj
    exact veil T x X j (hp c f S T hT (congr_arg Patch.L hS) he.1 F X).2.1
      fun q he => hV q ((separation_triangle _ (mesh j).1 _).trans ((Nat.add_le_add
        (show separation p.1 (mesh j).1≤R from hj) he).trans (by omega)))
  have hA' : ‖a‖ ≤ allowance G D x 1 7 := (orient_norm ..).trans hb
  have hz := (ht c f S T hT hS 0 a (by rw [norm_zero]; exact allowance_nn ..) hA').1 p
  rw [gain_zero T hA hT a p] at hz; simp only [sub_zero] at hz
  have hm' : G.adjoint (w p.1) (zip (T.N R V') (T.vision R t V') p) = m := (congr_fun (movers P hT R V' w t).2.2.2 _).symm
  unfold Tube.workN; rw [← show V'=pull s 0 V from rfl]
  rw [← G.norm_adjoint (w p.1),hm',hm]
  apply le_trans (half_le_self (sq_nonneg _))
  apply le_trans (pow_le_pow_left₀ (norm_nonneg _) hz.2 2); rw [pow_two,exchange]

lemma earnsLD (P : Teller G) (C : ℝ) (he : Reserve P C) (D : Patch) (hD : D.Branches P.bind G) (p : ℕ) (hp : 7≤p) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
      S.patch=D → P.Funds S T → ∀ (V : Config G c) (A : Stores S) (_F : Forest S.ratio), cert S x A V →
      ∀ (k : S.Choices) (U : Config G f) (i : Cell c) (s : Signed) (w : Directions G f), let B := radiusB x
      let o := s.act i.1
      o∉A.dome (2*B) → Stops S w V U o B (allowance G D x 1 p) →
      let W := pull s 0 V; let U' := pull s 0 U; let Q := S.prediction U' (choice s k); let t := temp x; let R := till x
      |T.workL R U' Q W t i| + |T.workD R W t i| ≤ allowance G D x 3 (p+p+9) := by
  obtain ⟨K,τ,r,hK,hτ,hr,H⟩ := interior_cost P D hD
  filter_upwards [(vanishes G D (p+2)).eventually (ge_mem_nhds hr),lends D G (p+2) τ hτ, he.receipt D.L,
    shine G D p hp, Rates.widen G D 1 (show 1≤p+2 by omega), grow G D C (by decide : 0<1) 1,
    prepare D, grow G D (4*K) (show p+p+7<p+p+9 by omega) 3] with x hx hv ht hh hp hC hq hB c f S T hS hT V A F he k U i s w B o hA hw W U' Q t R
  obtain ⟨z,hz⟩ := hh _ _ S U V A w hS he s i.1 hA hw
  let X := allowance G D x 1 (p+2); let E := allowance G D x 1 (p+2+2)
  let Y := allowance G D x 1 1
  let Z := K * allowance G D x 2 (p+p+6)
  have he' (j : Twin c) : ‖T.vision R t W j‖ ≤ Y := by
    have hh := (ht c f S T hT (congr_arg Patch.L hS) he.1 F W).2.2.up j
    rw [hS] at hh; exact hh.trans (by simpa [allowance,pieces,Y] using hC)
  have hi : 0 ≤ X := allowance_nn ..
  have hy j := (he' j).trans hp
  have hg : K*X*Next.Fluctuations.widen R X τ ≤ Z := by
    apply le_trans (mul_le_mul_of_nonneg_left (show Next.Fluctuations.widen R X τ≤E from hv) (show 0≤K*X by positivity))
    rw [mul_assoc]; unfold X E; rw [exchange,show p+2+(p+2+2)=p+p+6 by omega]
  have hf j : ‖lGap T R U' Q W (i,j)‖ ≤ Z ∧ ‖dGap T R W (T.vision R t W) (i,j)‖ ≤ Z := by
    obtain ⟨hl,hd⟩ := H c f S T hS hT (choice s k) R (B/2) (by rw [hS]; unfold R B; unfold stencilD radial at hq; omega)
      U' W _ hi hx (i,j) z hz.2 hz.1
    exact ⟨hl.trans hg,(hd _ X hi hy).trans hg⟩
  have hu {u v : Bool→ G.Color} (m : ℝ) (hm : 1≤m) (he : ∀ i, ‖u i‖ ≤ Y) (ht : ∀ i, ‖v i‖≤Z) :
      |∑ i,inner ℝ (u i) (v i)/m| ≤ 2*(Y*Z) := by
    rw [Fintype.sum_bool]; apply le_trans (abs_add_le ..)
    have hh i : |inner ℝ (u i) (v i)/m| ≤ Y*Z := by
      rw [abs_div, abs_of_nonneg (zero_le_one.trans hm)]
      apply le_trans (div_le_self (abs_nonneg _) hm)
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (he i) (ht i) (norm_nonneg _) (allowance_nn ..))
    rw [two_mul]; exact add_le_add (hh _) (hh _)
  rw [workL_gap,workD_gap]; apply le_trans (add_le_add (b:=2*(Y*Z))
      (by simpa only [div_one] using!
        (hu (u:=fun j => T.vision R t W (i,j)) (v:=fun j => lGap T R U' Q W (i,j)) 1 le_rfl (fun j => he' _) fun j => (hf j).1))
      (hu 2 (by norm_num) (fun _ => he' _) fun j => (hf j).2))
  apply le_trans _ hB; rw [show 2*(Y*Z)+2*(Y*Z)=4*K*(Y*allowance G D x 2 (p+p+6)) by unfold Z; ring]
  unfold Y; rw [exchange,show 1+(p+p+6)=p+p+7 by omega]
end YM.AnalyticNext.ConnectedActivity.Aff
