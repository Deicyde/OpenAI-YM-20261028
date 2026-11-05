import YM.Next.FLUCTUATIONS.Kernel
import YM.Next.FLUCTUATIONS.Linear
import YM.Next.FLUCTUATIONS.Prediction
import YM.Next.FLUCTUATIONS.Slots
import YM.Work.E07.Columns





/-!
# Uniform real small-log estimates on the full torus

Winding allowed. Cut already in L,D terms, but use the *uncut* matrix
identities, paying for both transport and cut differences in `NearFlat`.
Orientation-local. In another module will apply even on a halo using a
small extension off it and comparing the SAME defect at a given anchor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Fluctuations
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {c f : Side} {S : StepData c f}

section estimate
variable {X Y : Type*} [Fintype X] [Fintype Y]

private def InputCost (f l : X → G.Color) (C h b : ℝ) : Prop :=
  ∀ i, ‖l i‖ ≤ C*h ∧ ‖f i - l i‖ ≤ C*h*b

omit [Fintype X] in
private lemma InputCost.mono {f l : X → G.Color} {C h b D u : ℝ}
    (hx : InputCost f l C h b) (hh : 0≤h) (hv : 0≤b) (hD : 0≤D)
    (ht : C≤D) (hu : b≤u) : InputCost f l D h u := fun i => by
  obtain ⟨he,hw⟩ := hx i
  exact ⟨he.trans (by gcongr), hw.trans (by gcongr)⟩

variable {F E : X → Y → Pay G} {C h b : ℝ} (hC : 0≤C) (hb : 0≤b) (hf : NearFlat F E C b) (hh : 0 ≤ h)
include hC hb hf hh

private lemma unzip_cost {f t : X → G.Color} (ht : InputCost f t C h b) (i : Y) :
    ‖unzip F f i - unzip E t i‖ ≤ 2*C^2*h*b := by
  have he : unzip F f i - unzip E t i = unzip F (f-t) i + unzip (F-E) t i := by
    unfold unzip; simp only [Pi.sub_apply,map_sub,sub_apply,sum_sub_distrib]; abel
  have hF := Work.E07.unzip_uniform F (f-t) i (hf.cut.cols _) (show 0 ≤ C*h*b by positivity)
    (fun j => (ht j).2)
  have hE := Work.E07.unzip_uniform (F-E) t i (hf.close.cols _) (show 0 ≤ C*h by positivity)
    (fun j => (ht j).1)
  rw [he]; exact (norm_add_le _ _).trans ((add_le_add hF hE).trans_eq (by ring))

private lemma unzip_zip_cost (w : Y → G.Color) (ht : ∀ i, ‖w i‖ ≤ h) (i : Y) :
    ‖unzip F (zip F w) i - unzip E (zip E w) i‖ ≤ 2*C^2*h*b := by
  apply unzip_cost hC hb hf hh ?_ i
  intro j
  refine ⟨Work.E07.zip_uniform E w j (hf.full.rows j) hh ht,?_⟩
  have he : zip F w j - zip E w j = zip (F-E) w j := by
    unfold zip; simp only [Pi.sub_apply,sub_apply,sum_sub_distrib]
  rw [he]; exact (Work.E07.zip_uniform _ w j (hf.close.rows j) hh ht).trans_eq (by ring)
end estimate

private lemma l_three (a b c x y z : G.Color) (u v w : ℝ) (hl : x+y-z=0)
    (ha : ‖a-x‖ ≤ u) (hb : ‖b-y‖ ≤ v) (hc : ‖c-z‖ ≤ w) : ‖a+b-c‖ ≤ u+v+w := by
  have he : a+b-c = (a-x)+(b-y)-(c-z) := by rw [← sub_eq_zero.mp hl]; abel
  rw [he]; exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ha hb)) hc)

private lemma d_three (t a b c x y z : G.Color) (u : ℝ) (hl : t-(x+y+z)=0)
    (ha : ‖a-x‖ ≤ u) (hb : ‖b-y‖ ≤ u) (hc : ‖c-z‖ ≤ u) : ‖t-(a+b+c)‖ ≤ u+u+u := by
  have he : t-(a+b+c) = -((a-x)+(b-y)+(c-z)) := by rw [sub_eq_zero.mp hl]; abel
  rw [he,norm_neg]; exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ha hb)) hc)

/-- Post-L, branch-certified log prices for both defects; `b` the actual
coarse log field, not clamped here. Testing dyad D permits arbitrary
bounded input (will use on thinned data). Uniform including cuts down to zero.
The cost `h` counts both fine and coarse links. -/
lemma global_chart_cost (P : Teller G) (D : Patch) (hp : D.Branches P.bind G) :
    ∃ C τ r : ℝ, 0<C ∧ 0<τ ∧ 0<r ∧
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → P.Funds S T →
    ∀ (k : S.Choices) (R : ℕ) (a : LogField G f) (b : LogField G c) (h : ℝ),
        ‖a‖ ≤ h → ‖b‖ ≤ h → h ≤ r →
    let U := represent a; let V := represent b
    ∀ i : Twin c, ‖lGap T R U (S.prediction U k) V i‖ ≤ C * h * widen R h τ ∧
      ∀ (w : Twin c → G.Color) (q : ℝ), 0≤q → (∀ j, ‖w j‖ ≤ q) →
        ‖dGap T R V w i‖ ≤ C*q*widen R h τ := by
  obtain ⟨C₁,r₁,h1,h1r,hf⟩ := x_chart_cost G P.top 1 (by decide)
  obtain ⟨C₂,r₂,h2,h2r,hg⟩ := x_chart_cost G P.below D.L.val D.L.property
  obtain ⟨C₃,r₃,h3,h3r,hz⟩ := z_chart_cost D P.bind G hp
  obtain ⟨C₄,τ,r₄,h4,hτ,h4r,hK⟩ := kernel_chart_cost G D.L P.η P.C P.width
  let C := max (max C₁ C₂) (max C₃ C₄)
  have hc1 : C₁ ≤ C := le_max_of_le_left (le_max_left _ _)
  have hc2 : C₂ ≤ C := le_max_of_le_left (le_max_right _ _)
  have hc3 : C₃ ≤ C := le_max_of_le_right (le_max_left _ _)
  have hc4 : C₄ ≤ C := le_max_of_le_right (le_max_right _ _)
  have hC := h1.trans_le hc1
  let r := min (min r₁ r₂) (min r₃ r₄)
  let p := min τ (min P.top.width (P.below.width/D.L.val))
  have hv : 0 < P.below.width / D.L.val := div_pos P.below.width_pos (side_pos D.L)
  refine ⟨6*C^2+C,p,r,by positivity, lt_min hτ (lt_min P.top.width_pos hv),
    lt_min (lt_min h1r h2r) (lt_min h3r h4r),?_⟩
  intro c f S T hl hh k R a b h ha hb hw U V i
  let m := widen R h p
  let Q := S.prediction U k
  have hn : 0≤h := (norm_nonneg _).trans ha
  have hs τ : 0 ≤ widen R h τ := widen_nonneg _ hn
  -- first kernels
  obtain ⟨A,B,H⟩ := hK S T (congr_arg Patch.L hl) ⟨_,hh.crosses⟩ R b h hb
    (hw.trans ((min_le_right ..).trans (min_le_right ..)))
  have he : NearFlat (T.Φ R V) (flatF T) C m :=
    A.mono hC.le (hs τ) hc4 (widen_anti R h (min_le_left _ _))
  have hu : NearFlat (T.Φ' R V) (flatI T) C m :=
    B.mono hC.le (hs τ) hc4 (widen_anti R h (min_le_left _ _))
  have hy : NearFlat (T.N R V) (flatN T) C m :=
    H.mono hC.le (hs τ) hc4 (widen_anti R h (min_le_left _ _))
  obtain ⟨Λ,Λ',hΛ,hΛ'⟩ := hh.feeds
  have hs1 : InputCost (T.Xf R U) (xLin T.high T.up a) C₁ h (widen R h P.top.width) := by
    intro i; unfold Tube.Xf; rw [hh.high]
    simpa only [Nat.cast_one,div_one] using hf f T.up Λ hΛ R a h ha
      (hw.trans ((min_le_left ..).trans (min_le_left ..))) i
  have hs2 : InputCost (T.Xn R V) (xLin T.low T.down b) C₂ h (widen R h (P.below.width/D.L.val)) := by
    intro i; unfold Tube.Xn; rw [hh.low,hl]
    exact hg c T.down Λ' hΛ' R b h hb (hw.trans ((min_le_left ..).trans (min_le_right ..))) i
  have hs3 : InputCost (Z S Q V) (zLin S a b) C₃ h h := by
    intro e
    obtain ⟨hv,hy⟩ := hz c f S hl hh.knobs k e (a,b)
    have ht : ‖(a,b)‖ ≤ h := max_le ha hb
    refine ⟨hv.trans (mul_le_mul_of_nonneg_left ht h3.le),?_⟩
    apply (hy (ht.trans (hw.trans ((min_le_right ..).trans (min_le_left ..))))).trans
    rw [mul_assoc, ← sq]
    gcongr
  have hf' : InputCost (T.Xf R U) (xLin T.high T.up a) C h m :=
    hs1.mono hn (hs _) hC.le hc1 (widen_anti R h ((min_le_right ..).trans (min_le_left ..)))
  have hg' : InputCost (T.Xn R V) (xLin T.low T.down b) C h m :=
    hs2.mono hn (hs _) hC.le hc2 (widen_anti R h ((min_le_right ..).trans (min_le_right ..)))
  have hz' := hs3.mono hn hn hC.le hc3 (le_widen (τ:=p) R hn)
  obtain ⟨X,Y,hX,hY,hJ⟩ := hh.tilts
  rw [← hh.high] at hΛ
  rw [← hh.low] at hΛ'
  constructor
  · refine (l_three _ _ _ _ _ _ _ _ _ (roll_l T hJ hΛ hΛ' hX hY a b i)
      (unzip_cost hC.le (hs p) he hn hf' i) (unzip_cost hC.le (hs p) hu hn hz' i) ((hg' i).2)).trans ?_
    have ht : 0 ≤ C^2*h*widen R h p := mul_nonneg (mul_nonneg (by positivity) hn) (hs _)
    unfold m; linarith
  intro w q hq hl
  refine (d_three _ _ _ _ _ _ _ _ (roll_d T hJ w i)
    (unzip_zip_cost hC.le (hs p) he hq w hl i) (unzip_zip_cost hC.le (hs p) hu hq w hl i)
    (unzip_zip_cost hC.le (hs p) hy hq w hl i)).trans ?_
  have ht : 0 ≤ C*q*widen R h p := mul_nonneg (mul_nonneg hC.le hq) (hs _)
  linarith
end YM.Next.Fluctuations
