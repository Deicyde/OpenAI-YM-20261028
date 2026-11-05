import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Windows
import YM.Next.EXTRACTION.Base
import YM.Next.FREE_KERNELS.Priced
import YM.Next.SCHEDULE.Stadium

/-!
# Windows: before-phase pricing

At ANY step and *every* formal sector receiving these physical kernel
estimates. Earn width and window ratio from fixed-$L$ affine receipts
before seeing the actual volume and patterns. Uses `Green`'s spectral
estimates and actual principal restrictions, not ignoring the boundary.
Does not claim analyticity in directions here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Win
open Progress.StationaryScenes Matrix Filter Lattice ResolventVolume
open Green
open scoped Topology BigOperators Matrix.Norms.Frobenius

structure Promise where
  mass : ℝ
  bottom : ℝ
  alpha : ℝ
  types : ℝ
  mass_pos : 0<mass
  bottom_pos : 0<bottom
  alpha_pos : 0<alpha
  types_pos : 0<types

namespace Promise
variable {n : Type*} {c : Side} [Fintype n] [DecidableEq n] (Y : Promise)

/-- Hypothesis on the *selected affine precision*, not sector charges. -/
def Served (A : Matrix n n ℝ) (d : n → Site c) : Prop :=
  A.IsHermitian ∧ Bottom A Y.bottom ∧ governs d Y.types ∧ Both d d A Y.alpha Y.mass Y.mass

def flows (A : Matrix n n ℝ) (t : ℝ) := graph 1 (A-1) t

omit [Fintype n] in
private lemma flow_pick (A : Matrix n n ℝ) (t : ℝ) : flows A t = t • A + (1-t) • 1 := by
  unfold flows graph; rw [smul_sub,sub_smul,one_smul]; abel

lemma flow_income (A : Matrix n n ℝ) (d : n → Site c) (h : Y.Served A d) (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    let F := flows A t; let r := min Y.bottom 1
    F.IsHermitian ∧ Both d d F Y.alpha (Y.mass+2) (Y.mass+2) ∧ Bottom F r := by
  intro F r
  have he := ht.1; have hq := ht.2; have hw := sub_nonneg.mpr hq
  have hu := (plusBoth h.2.2.2 (negBoth (identities d Y.alpha)))
  rw [← sub_eq_add_neg A 1] at hu
  refine ⟨?_, ?_, ?_⟩
  ·
    dsimp only [F]; rw [flow_pick,Matrix.IsHermitian, conjTranspose_add,conjTranspose_smul,conjTranspose_smul,h.1.eq]
    simp
  · have H := plusBoth (identities d Y.alpha) (smulBoth hu t)
    have hb : 1 + |t| * (Y.mass+1) ≤ Y.mass+2 := by
      rw [abs_of_nonneg he]; have hY := Y.mass_pos
      linarith [mul_le_of_le_one_left (show 0≤Y.mass+1 by linarith) hq]
    exact monoBoth H le_rfl hb hb
  intro x
  have hu := Centered.dot_nonneg x
  have hA : r*dotProduct x x ≤ dotProduct x (A *ᵥ x) :=
    (mul_le_mul_of_nonneg_right (min_le_left ..) hu).trans (h.2.1 x)
  have hI : r*dotProduct x x ≤ dotProduct x x := mul_le_of_le_one_left hu (min_le_right ..)
  dsimp only [F]; rw [flow_pick, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
    dotProduct_smul, dotProduct_smul,smul_eq_mul,smul_eq_mul]
  linarith [mul_le_mul_of_nonneg_left hA he,mul_le_mul_of_nonneg_left hI hw]

/-- Prices needed even for later-continuum headers on these entries. -/
structure Turns where
  expense : ℝ
  exp_width : ℝ
  win : ℝ
  base : ℝ
  z : ℝ
  foot : ℝ
  bought : 0 < expense
  wide : 0 < exp_width
  wins : 0 < win
  holds : 0 < base
  carries : 0 < z
  feet : 0 < foot

namespace Turns

def pace (B : Turns) (R : ℕ) := B.expense * Real.exp (-B.win*R)

lemma pace_pos (B : Turns) (R : ℕ) : 0 < B.pace R := mul_pos B.bought (Real.exp_pos _)

structure Takes (B : Turns) (P : Windows n) (A : Matrix n n ℝ) (d : n → Site c) (R : ℕ) : Prop where
  greens t : t ∈ Set.Icc (0:ℝ) 1 →
    let F := flows A t; let s := B.pace R; let e := B.exp_width
    Both d d F⁻¹ e B.base B.base ∧ Both d d (P.within F) e B.base B.base ∧
      Both d d (P.error F) e s s ∧ Both d d (P.within F-F⁻¹) e s s
  ascent :
    let s := B.pace R; let e := B.exp_width
    Both d d (P.cov A) e B.base B.base ∧ Both d d (P.cov A-A⁻¹) e s s ∧
      Both d d (P.untuned A) e s s
  precision :
    Bottom (P.cov A) B.foot ∧ Bottom (P.cov A)⁻¹ B.z
end Turns

open Windows Turns

lemma receive (Y : Promise) : ∃ B : Turns, B.exp_width ≤ Y.alpha ∧
    ∀ᶠ R : ℕ in atTop, pace B R < 1 ∧
      ∀ (c : Side) (n : Type) [Fintype n] [DecidableEq n] (d : n → Site c),
      ∀ (P : Windows n), P.Room d R → ∀ A : Matrix n n ℝ, Y.Served A d → B.Takes P A d R := by
  let r := min Y.bottom 1
  let V := Y.mass+2
  let θ := min 1 (r/(2*V))
  have hm := Y.mass_pos
  have hr : 0<r := lt_min Y.bottom_pos zero_lt_one
  have hV : 0<V := by unfold V; linarith
  have hy : 0<θ := lt_min zero_lt_one (by positivity)
  have hw : θ ≤ 1 := min_le_left ..
  have hh : θ*V ≤ r/2 := calc
    _ ≤ r/(2*V)*V := mul_le_mul_of_nonneg_right (min_le_right ..) hV.le
    _ = _ := by field_simp
  let ν := θ*Y.alpha/2; let μ := ν/2
  have hn : 0<ν := half_pos (mul_pos hy Y.alpha_pos)
  have hU : 0<μ := half_pos hn
  have hp : μ < ν := half_lt_self hn
  have hx : ν < θ*Y.alpha := half_lt_self (mul_pos hy Y.alpha_pos)
  let D := planePrice Y.types (θ*Y.alpha-ν)*(min 1 (r/2))⁻¹
  have hD : 0 ≤ D := mul_nonneg (planePrice_nn Y.types_pos.le (sub_pos.mpr hx))
    (inv_nonneg.mpr ((lt_min zero_lt_one (half_pos hr)).le))
  let w := ν-μ
  let E := V*D+1
  let k := Y.mass⁻¹/2
  let z := (D+1)⁻¹
  have he : 0<w := sub_pos.mpr hp
  have hE : 0<E := by unfold E; positivity
  have hk : 0<k := by unfold k; positivity
  have hz : 0<z := by unfold z; positivity
  let G := E * (1+D+Y.mass*D)
  let B : Turns := ⟨G,μ,w,D+1,z,k,by unfold G; positivity,hU,he,by positivity,hz,hk⟩
  have ht : μ ≤ Y.alpha := hp.le.trans (hx.le.trans (mul_le_of_le_one_left Y.alpha_pos.le hw))
  have hd : D ≤ D+1 := le_add_of_nonneg_right (by norm_num)
  let s (R : ℕ) := Real.exp (-w*R)*E
  have hs (R : ℕ) : 0 ≤ s R := mul_nonneg (Real.exp_pos _).le hE.le
  have hW : Tendsto (fun R : ℕ => Real.exp (-w*R)) atTop (𝓝 0) := by
    have h : Real.exp (-w)<1 := Real.exp_lt_one_iff.mpr (by linarith)
    simpa only [← Real.exp_nat_mul, mul_comm (-w)] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-w)).le h
  have h1 : Tendsto B.pace atTop (𝓝 0) := by
    change Tendsto (fun R : ℕ => G * Real.exp (-w*R)) _ _; simpa only [mul_zero] using hW.const_mul G
  have h2 : Tendsto (fun R => D * s R) atTop (𝓝 0) := by
    simpa only [s,mul_zero,zero_mul] using
        (hW.mul_const E).const_mul D
  refine ⟨B,ht, ?_⟩
  filter_upwards [h1.eventually (gt_mem_nhds zero_lt_one), h2.eventually (gt_mem_nhds hk)] with R hR hp'
  refine ⟨hR,fun c n _ _ d P hP A hA => ?_⟩
  have ht (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : let F := flows A t
      Both d d F⁻¹ μ D D ∧ Both d d (P.within F) μ D D ∧ Both d d (P.error F) μ (s R) (s R) ∧
      Both d d (P.within F-F⁻¹) μ (D*s R) (D*s R) := by
    intro F
    obtain ⟨h1,h2,h3⟩ := flow_income Y A d hA t ht
    exact P.window_price d F Y.alpha_pos hy hw hh hr hx hA.2.2.1 Y.types_pos.le hU.le hp R hP hV.le
      h2 h1 h3
  have hl : s R ≤ B.pace R ∧ D*s R ≤ B.pace R ∧ Y.mass*(D*s R) ≤ B.pace R := by
    have hf : B.pace R = (1+D+Y.mass*D)*s R := by unfold pace B G s; ring
    rw [hf]; have hs := hs R; have hc := mul_nonneg hm.le hD
    refine ⟨le_mul_of_one_le_left hs (by linarith),mul_le_mul_of_nonneg_right (by linarith) hs,
      by rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right (by linarith) hs⟩
  obtain ⟨i1,i2,i3,i4⟩ := ht 1 ⟨zero_le_one,le_rfl⟩
  rw [show flows A 1 = A by rw [flow_pick]; simp] at i1 i2 i3 i4
  have hm' : μ ≤ Y.alpha := hp.le.trans (hx.le.trans (mul_le_of_le_one_left Y.alpha_pos.le hw))
  have hv := Centered.symmetric_bottom Y.bottom_pos hA.2.1 hA.1
  obtain ⟨c1,c2,c3⟩ := P.covariance_price d A hv hA.2.2.2 hm.le hU.le hm' i2 (mul_nonneg hD (hs R)) i4
  have ha' := monoBoth c1 le_rfl hd hd
  refine ⟨fun t H => ?_, ⟨ha',monoBoth c2 le_rfl hl.2.1 hl.2.1,monoBoth c3 le_rfl hl.2.2 hl.2.2⟩,?_⟩
  · obtain ⟨h1,h2,h3,h4⟩ := ht _ H
    exact ⟨monoBoth h1 le_rfl hd hd,monoBoth h2 le_rfl hd hd,
      monoBoth h3 le_rfl hl.1 hl.1,monoBoth h4 le_rfl hl.2.1 hl.2.1⟩
  exact P.covariance_floor d A hv hA.2.2.2 hm hU.le hm' ha' B.holds c2
    (show D*s R < k from hp').le
end Promise
end YM.AnalyticNext.ConnectedActivity.Win
