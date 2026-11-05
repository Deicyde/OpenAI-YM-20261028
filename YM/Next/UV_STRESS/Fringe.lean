import YM.Next.UV_STRESS.Focus
import YM.Next.UV_STRESS.Gate


/-!
# Zoomed comparison on aligned points plus two-cost cells

`Spots` is the primitive pricing target here. Uses finite **basis lists** when
requested below. No bounds on point/gradient of S assumed. Aligned numerical
comparison can be requested only away from projection ties.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Metric Analysis Extraction Table Ward Climb Cells Lattice
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order} {n D : ℕ}

structure Wheel (C : Family G) (D : ℕ) extends Station C D where
  grid : ℕ
  /-- stripe parameter (normalized units) -/
  σ : ℝ
  stripe : 0<σ

namespace Wheel
variable (X : Wheel C D) {R : ℝ} {t : Caps n}
def spacing := C.S.a X.grid / X.r
lemma space : 0<X.spacing := div_pos (C.S.a_pos _) X.rad

def tones (h : ∀ i, t i ≤ D) (w : Ribbon (Bel C.book) t) (u : ℕ×ℕ) (i : Fin n) : C.book.Ref (t i) :=
    X.atCut u ⟨t i,Nat.lt_succ_of_le (h i)⟩ (w i)

def inspection (F : Extraction.Order) (e : ℝ) (W : Set (Points n)) (h : ∀ i, t i ≤ D) (w : Ribbon (Bel C.book) t) : Prop :=
    ∀ x : Fin n → Cover, tag X.spacing x∈W → tag X.spacing x∈generic n →
    F.upper (fun N p => ‖C.numeric N p (ripped (t:=t) (C:=C) (X.tones h w (N,p)))
      (location C.S X.grid N p ∘ x) - disc (hang t w) (tag X.spacing x)‖) e

structure Spots (F : Extraction.Order) (R e A B : ℝ) (h : ∀ i, t i ≤ D) (w : Ribbon (Bel C.book) t) : Prop where
  compare : X.inspection F e (Scaling.window (2*R) n) h w
  crude : ∃ m k : ℕ, C.S.a m < X.r/(2*R) ∧ m≤k ∧ (n:ℝ)*(2*(3*C.S.a k)) < C.S.a m ∧
    bulk (C:=C) (t:=t) (X.tones h w) F A k
  slab : ∃ j : ℕ,C.S.a j < X.r*X.σ ∧ generous (C:=C) (t:=t) (X.tones h w) F B j

lemma covers_tag (x : Fin n → Cover) : X.r • tag X.spacing x=tag (C.S.a X.grid) x := by
  ext i a; change X.r*(C.S.a X.grid/X.r * _) = _
  rw [← mul_assoc, mul_div_cancel₀ _ X.rad.ne']; rfl

lemma spots_upon {A B e : ℝ} {h} {w : Ribbon (Bel C.book) t} (hA : X.Spots F R e A B h w) (f : Extraction.Order) :
    X.Spots (F.refine f) R e A B h w := by
  obtain ⟨H,⟨m,k,he,hb,hg,hc⟩,j,hj,hD⟩:=hA
  exact ⟨fun x hx hv ε hε => F.late_refine f (H x hx hv _ hε),
    ⟨m,k,he,hb,hg,fun i j => F.late_refine f (hc i j)⟩,⟨j,hj,F.late_refine f (A:=fun N p => Difference.Permit (C:=C) (ripped (t:=t) (C:=C) (X.tones h w (N,p))) B j N p) hD⟩⟩
end Wheel

section cushions

lemma scales_wild {r : ℝ} (hr : 0<r) (x : Points n) (hx : x∈generic n) : r•x∈generic n := by
  intro a i j hij; exact hx a (mul_left_cancel₀ hr.ne' hij)

lemma centered_in {R r : ℝ} (hR : 0<R) (hr : 0<r) (x : Points n) (hx : x∈Scaling.window R n) :
    r•x ∈ airy n (r/(2*R)) := by
  intro i j hij
  have he : cubedist ((r • x) i) ((r • x) j)= r * cubedist (x i) (x j) := by
    unfold cubedist
    simp only [PiLp.smul_apply, WithLp.ofLp_smul]
    rw [dist_eq_norm,dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  rw [he,div_eq_mul_inv]
  exact mul_lt_mul_of_pos_left ((inv_lt_inv₀ (by positivity) hR).mpr (by linarith) |>.trans_le (hx.1 i j hij)) hr

lemma strict_thin {r σ : ℝ} (hr : 0<r) (x : Points n) (hx : x∈openFilm n (4*σ)) : r•x∈openFilm n (4*(r*σ)) := by
  intro i j hij a
  have he : Gaps.distances (r • x) i j a=r*Gaps.distances x i j a := by
    unfold Gaps.distances; rw [mul_sub]; rfl
  rw [he, abs_mul, abs_of_pos hr]; have hh := mul_lt_mul_of_pos_left (hx i j hij a) hr
  linarith

lemma closed_thin {σ : ℝ} (hs : 0≤σ) (x : Points n) (hx : x∈openFilm n (8*σ)) :
    closedBall x σ ⊆ openFilm n (4*σ) := by
  intro y hy i j hij a
  have he : dist x y ≤ σ := by rw [dist_comm]; exact hy
  rw [dist_eq_norm] at he
  have hh (i : Fin n) : |x i a-y i a| ≤ σ :=
    ((PiLp.norm_apply_le ((x-y) i) a).trans ((PiLp.norm_apply_le (x-y) i).trans he))
  have hh' : |Gaps.distances x i j a| ≤ |Gaps.distances y i j a| + 2*σ := by
    rw [show Gaps.distances x i j a = Gaps.distances y i j a + ((x j a-y j a)-(x i a-y i a)) by unfold Gaps.distances; abel]
    apply (abs_add_le ..).trans; apply add_le_add_right
    exact (abs_sub _ _).trans (by linarith [hh i, hh j])
  linarith [hx i j hij a]

lemma upgrade_window (R : ℝ) (hr : 0<R) : ∃ σ : ℝ,0<σ ∧ cthickening σ (Scaling.window R n) ⊆ Scaling.window (2*R) n := by
  let A := ball (0:Points n) (2*R) ∩ airy n (2*R)⁻¹
  have he : Scaling.window R n ⊆ A := by
    rintro x ⟨hx,h⟩
    exact ⟨mem_ball_zero_iff.mpr (h.trans_lt (by linarith)), fun i j hij =>
      ((inv_lt_inv₀ (by positivity) hr).mpr (by linarith)).trans_le (hx i j hij)⟩
  obtain ⟨σ,hσ,hA⟩ := (window_closed R n).exists_cthickening_subset_open (show IsOpen A from isOpen_ball.inter (airy_open _)) he
  exact ⟨σ,hσ,fun x hx => ⟨fun i j hij => ((hA hx).2 i j hij).le,(mem_ball_zero_iff.mp (hA hx).1).le⟩⟩
end cushions

section fringe
variable (X : Wheel C D) (𝓛 : Filter (ℕ×ℕ)) [𝓛.NeBot] (hp : 𝓛≤F.fuse)
variable {t : Caps n} (w : Ribbon (Bel C.book) t) {Y : Bud C t} (P : C.Makes) (H : F.PointLimits C S) (h : S.Smooth)
variable {R A B e : ℝ} {u : ∀ i,t i ≤ D}

def glow (S : Table C.book) (Y : Bud C t) (x : Points n) : ℂ := S.value t (X.r • x) Y
lemma glow_smooth (h : S.Smooth) (Y : Bud C t) : ContDiffOn ℝ ∞ (glow X S Y) (conf n) :=
    (S.smooth_read h (ripped (C:=C) (t:=t) Y)).comp (show ContDiffOn ℝ ∞ (fun x : Points n => X.r • x) (conf n) by fun_prop)
      (fun x hx => (enlarged X.rad x).1 hx)
include H hp

lemma match_phase (ha : Tendsto (X.tones u w) 𝓛 (𝓝 Y)) (hx : X.Spots F R e A B u w) (x : Fin n → Cover)
    (hu : tag X.spacing x∈Scaling.window (2*R) n) (hw : tag X.spacing x∈generic n) :
    ‖glow X S Y (tag X.spacing x)-disc (hang t w) (tag X.spacing x)‖ ≤ e := by
  have he : tag (C.S.a X.grid) x∈generic n := by rw [← X.covers_tag]; exact scales_wild X.rad _ hw
  rw [glow,X.covers_tag]
  apply le_of_forall_pos_le_add
  intro ε hε
  let V := disc (hang t w) (tag X.spacing x)
  have ht : ∀ᶠ i in F.fuse, ‖C.numeric i.1 i.2 (ripped (C:=C) (t:=t) (X.tones u w i))
      (location C.S X.grid i.1 i.2 ∘ x)-V‖ ≤ e+ε := hx.compare x hu hw ε hε
  exact le_of_tendsto (((paid_point (X.tones u w) Y ha hp H X.grid x he).sub_const V).norm) (ht.filter_mono hp)

include P h
lemma covers_cost (hr : 0<R) (ha : Tendsto (X.tones u w) 𝓛 (𝓝 Y)) (hx : X.Spots F R e A B u w)
    (x : Points n) (hh : x∈Scaling.window R n) : ‖glow X S Y x‖ ≤ A^n := by
  obtain ⟨m,k,hm,hv,hw,hA⟩:=hx.crude
  exact large_gate P h H 𝓛 hp (X.tones u w) Y ha (div_pos X.rad (by positivity)) m k hm hv hw hA _ (centered_in hr X.rad x hh)

lemma pays_gradient (ha : Tendsto (X.tones u w) 𝓛 (𝓝 Y)) (hx : X.Spots F R e A B u w) (hB : 0 ≤ B)
    (x : Points n) (hh : x∈openFilm _ (4*X.σ)) : ‖fderiv ℝ (glow X S Y) x‖ ≤ (n:ℝ)*4*(B^n/X.σ) := by
  obtain ⟨j,hj,HT⟩ := hx.slab
  apply (Work.B10.norm_le_direction_sum ..).trans
  let r := X.r
  have hr : 0<r := X.rad
  have hi := X.stripe
  have hz := strict_thin hr x hh
  have hs := generic_conf _ (open_fit _ (by positivity) hz)
  let U (x : Points n) := S.value t x Y
  have hD : DifferentiableAt ℝ U (X.r • x) :=
    (((S.smooth_read h (ripped (C:=C) (t:=t) Y)) _ hs).contDiffAt ((conf_open _).mem_nhds hs)).differentiableAt (by simp)
  calc
    _ ≤ ∑ _ : Fin n × Axis,B^n/X.σ := by
      apply Finset.sum_le_sum; rintro ⟨k,a⟩ _
      have hh := Work.A04.gradient_scaled r U x hD k a
      change ‖Points.gradient k a (fun x => U (r • x)) x‖ ≤ _
      rw [hh,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      refine (mul_le_mul_of_nonneg_left (slope_gate P H h (X.tones u w) 𝓛 hp Y ha j B _ hB (by positivity)
        HT hj k a _ hz) hr.le).trans_eq ?_
      field_simp
      change r * B^n / r = B^n; field_simp
    _ = _ := by simp [Axis]

lemma glide (ha : Tendsto (X.tones u w) 𝓛 (𝓝 Y)) (hx : X.Spots F R e A B u w) (hB : 0 ≤ B)
    (x : Points n) (hh : x∈openFilm _ (8*X.σ)) (hw : (4*n:ℝ)*X.spacing ≤ X.σ) :
    dist (glow X S Y (tag X.spacing (address X.spacing x))) (glow X S Y x) ≤
      ((n:ℝ)*4*(B^n/X.σ))*((4*n:ℝ)*X.spacing) := by
  let U := closedBall x X.σ
  have hs := X.stripe
  have hk : U ⊆ openFilm _ (4*X.σ) := closed_thin hs.le x hh
  have hy (y) (hx' : y ∈ U) : DifferentiableAt ℝ (glow X S Y) y := by
    have he := generic_conf _ (open_fit _ (by positivity) (hk hx'))
    exact (((glow_smooth X h Y) y he).contDiffAt ((conf_open _).mem_nhds he)).differentiableAt (by simp)
  let y := tag X.spacing (address X.spacing x)
  have ht := approximate X.space x
  have he := (convex_closedBall x X.σ).norm_image_sub_le_of_norm_fderiv_le hy
    (fun y hy => pays_gradient X 𝓛 hp w P H h ha hx hB y (hk hy)) (mem_closedBall_self hs.le) (show y∈U from ht.trans hw)
  rw [dist_eq_norm] at ht ⊢; exact he.trans (mul_le_mul_of_nonneg_left ht (by positivity))
end fringe
end YM.Next.UVStress
