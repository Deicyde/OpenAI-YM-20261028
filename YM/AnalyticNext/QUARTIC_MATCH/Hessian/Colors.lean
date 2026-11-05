import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Sojourn

/-!
# Install the mixed response invoice on the actual Color charts

Acceleration estimates for centered branch. Quantities on the SAME stationarity
jet; use signed exponential weights, including the tilt of input scratch probes.
Pre-L. No p dependence of these rates/costs. Not a uniform IFT at neighborhoods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Hessian
open Filter Function Lattice Laurent Bloch Exterior Matrix Precision RG Work.F03
open Joint Pre.Centered YM.Next.Free YM.Progress.StationaryScenes Wilson Bid Tree
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ComplexConjugate InnerProductSpace

namespace Tracks
open Green (wt)
variable {G : Gauge} {c f : Side} (S : StepData c f)
local notation "X" => LieSpin G f
local notation "Y" => Vertical G c f
local notation "Z" => Dir G c

def guard (y : Y) (i : G.ColorIndex) := tariff S (parts G 1 y.1 i) (sitePart y.2 i)
abbrev Chest (G : Gauge) (f : Side) := EuclideanSpace ℝ (G.ColorIndex × Body 0 f)

def cop : Y→L[ℝ] Chest G f := LinearMap.toContinuousLinearMap {
    toFun := fun x => WithLp.toLp 2 (fun i => guard S x i.1 i.2)
    map_add' := fun x y => by apply PiLp.ext; rintro ⟨a,i⟩; exact congr_fun (show guard S (x+y) a=guard S x a+guard S y a from tariff_add ..) i
    map_smul' := fun s x => by apply PiLp.ext; rintro ⟨a,i⟩; exact congr_fun (show guard S (s • x) a=s • guard S x a from tariff_smul ..) i }

lemma remit_exists : Surjective (cop S ∘ depart S (G:=G)) := by
  intro x; let b (i : G.ColorIndex) (j : Body 0 f) := x (i,j)
  choose a ha using (fun i => given S (b i))
  let z : X := fun j => WithLp.toLp 2 (fun i => a i (j,vac))
  refine ⟨z,?_⟩
  apply PiLp.ext; rintro ⟨i,q⟩
  have he : sitePart z i=a i := by funext ⟨x,k⟩; rw [vac_only k]; rfl
  have hv : sitePart (remit S z) i=palette S *ᵥ a i := by rw [← he]; funext ⟨x,k⟩; rw [vac_only k]; rfl
  change tariff S (-(parts G 1 (gradient z) i)) (-(sitePart (remit S z) i)) q = _
  rw [parts_grad,he,hv, ha]

def bankCredit (H : Precision.Bed) (x y : Y) := second S H (0,x) (0,y) + inner ℝ (cop S x) (cop S y)
lemma reform (H : Precision.Bed) (x y : Y) : bankCredit S H x y = ∑ i : G.ColorIndex,
    baseline S H (parts G 1 x.1 i) (parts G 1 y.1 i) (sitePart x.2 i) (sitePart y.2 i) := by
  unfold bankCredit; rw [pairs]
  simp_rw [flatBill, Finset.sum_add_distrib]; congr 1
  let a (v : Y) (j : G.ColorIndex × Body 0 f) := guard S v j.1 j.2
  change inner ℝ (WithLp.toLp 2 (a x)) (WithLp.toLp 2 (a y)) = _
  rw [real_area,dotProduct,Fintype.sum_prod_type]; rfl

def stake (x : Y) (i : G.ColorIndex) := gain S (parts G 1 x.1 i) (sitePart x.2 i)
def shares (x : Y) := Real.sqrt (∑ i, stake S x i^2)

lemma stake_nonneg (x : Y) (i : G.ColorIndex) : 0 ≤ stake S x i := positive_gain ..
lemma shares_nonneg (x : Y) : 0 ≤ shares S x := Real.sqrt_nonneg _
lemma share_count (x : Y) : ∑ i, stake S x i^2=shares S x^2 := (Real.sq_sqrt (by positivity)).symm
lemma share_positive {x : Y} (h : x≠0) : 0 < shares S x := by
  have he : ∃ i, stake S x i ≠ 0 := by
    by_contra! hv
    have hh (i) : parts G 1 x.1 i = 0 ∧ sitePart x.2 i=0 := by by_contra! H; exact (enter S (parts G 1 x.1 i) (sitePart x.2 i) (by tauto)).ne' (hv i)
    apply h; apply Prod.ext
    · funext k; apply PiLp.ext; intro i
      exact congr_fun (hh i).1 k
    funext k; apply PiLp.ext; intro i
    exact congr_fun (hh i).2 (k,vac)
  obtain ⟨i,hi⟩ := he
  exact Real.sqrt_pos.mpr ((sq_pos_of_ne_zero hi).trans_le (Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ _)))


local notation "L" => (S.patch.L.val:ℝ)

def polar (t : ℝ) (z : Site f) (x : Y) : Y := (fun i => wt (t/L) i.1 z • x.1 i, fun i => wt (t/L) (S.ratio.embed i) z • x.2 i)
lemma cancels (t : ℝ) (z : Site f) (x : Y) : polar S (-t) z (polar S t z x)=x := by
  apply Prod.ext <;> funext i
  · change wt _ _ _ • (wt _ _ _ • x.1 i)=_
    rw [smul_smul,neg_div,lefties, inv_mul_cancel₀ (Green.wt_pos ..).ne',one_smul]
  change wt _ _ _ • (wt _ _ _ • x.2 i)=_
  rw [smul_smul,neg_div,lefties, inv_mul_cancel₀ (Green.wt_pos ..).ne',one_smul]

variable {p : Clip} {u a : ℝ} {H : Precision.Bed} (ha : 0<a) (h : Floor H p f a u)
include ha h
local notation "α" => reserve S.patch.J a S.kernel.penalty
lemma vested (v : Y) : α*shares S v ^ 2 ≤ bankCredit S H v v := by
  rw [reform S,← share_count,Finset.mul_sum]
  exact Finset.sum_le_sum fun _ _ => wins S h ha _ _
lemma tilted {t η C : ℝ} (ht : |t| ≤ Tracks.purchase S.patch.J a η C S.kernel.penalty) (he : 0<η) (hw : H.metric.strip η C)
    (z : Site f) (v : Y) : α/2*shares S v ^ 2 ≤ bankCredit S H (polar S (-t) z v) (polar S t z v) := by
  rw [reform S,← share_count,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => sojourn S he hw ha h ht z (parts G 1 v.1 i) (sitePart v.2 i)

section
variable {T : Forest S.ratio} {W : PathData G} {b : Dir G c→AxisChart G T} {σ C Λ η : ℝ}
    (hP : W.Bounds p σ C Λ) (hb : Critical T p W b) (ht : Attached H W) (hs : Sworn H f G)
    (θ : S.Choices) (hp : S.patch.Branches S.kernel G) {B : Bed} {U : Matrix (Body 1 f) (Body 1 c) ℝ} (hk : Inputs S U (H.metric.acts f) (B.metric.acts c))
    (hv : Comptroller T H p W) (he : 0 < η) (hq : PriceGap T p W η)
include hP hb ht hs hp hk hv he hq

theorem procure : ∃ d : Z→Y, d 0=0 ∧ OnShell (cash S θ p W) d 0 ∧
    fderiv ℝ d 0=stance U ∧ (∀ u w, cop S (D2 d 0 u w)=0) ∧ cash S θ p W ∘ arc d =ᶠ[𝓝 0] Joint.value T θ p W b :=
    Pre.Centered.purchase S θ hp hP hb ht h hs hk hv he hq (cop S)
    (fun i hi => (mul_pos (reserve_pos _ _ _ ha S.kernel.penalty_pos)
        (pow_pos (share_positive S hi) _)).trans_le (vested S ha h i)) (remit_exists S)
end
section
variable {σ C Λ : ℝ} {W : PathData G} (hP : W.Bounds p σ C Λ) (ht : Attached H W) (hs : Sworn H f G)
    (θ : S.Choices) (hp : S.patch.Branches S.kernel G) {b : Dir G c→Vertical G c f} (hb : b 0=0) (hx : OnShell (cash S θ p W) b 0)
include hP ht hs hp hb hx

/-- How to use with tested estimates on actual exchange legs. Mixed; holds for
any such b and matching cop condition on those directions. -/
theorem flight (u' v : Z) {r η Q E} (he : 0<η) (hr : |r| ≤ Tracks.purchase S.patch.J a η Q S.kernel.penalty)
    (hQ : H.metric.strip η Q) (hE : 0 ≤ E) (hl : cop S (D2 b 0 u' v) = 0)
    (z : Site f) :
    let l := leg (cash S θ p W) 0 (tangent b 0 u') (tangent b 0 v)
    (∀ y, |l (polar S r z y)| ≤ E*shares S y) →
      α/2*shares S (polar S r z (D2 b 0 u' v)) ≤ E := by
  intro l hq
  let P := D2 b 0 u' v
  let Wx := polar S r z P
  have he' : arc b 0=0 := Prod.ext rfl hb
  have hu (w : Y) := hx.equation u' v w; rw [he'] at hu
  have hd (w : Y) : bankCredit S H P w= -l w := by
    have hy := hu w
    rw [← D2_jet,(reveals S θ hp hP ht h hs (he' ▸ hx.action)).2.2] at hy
    rw [bankCredit, show cop S P=0 from hl, inner_zero_left,add_zero]; exact eq_neg_of_add_eq_zero_left hy
  have hh := tilted S ha h hr he hQ z Wx
  rw [show polar S (-r) z Wx=P from cancels .., hd] at hh
  have hZ := hh.trans ((neg_le_abs _).trans (hq Wx)); rcases eq_or_lt_of_le (shares_nonneg S Wx) with hv|hv
  · change α/2 * shares S Wx ≤ E; rw [← hv, mul_zero]; exact hE
  rw [pow_two, ← mul_assoc] at hZ; exact le_of_mul_le_mul_right hZ hv
end
end Tracks
end YM.AnalyticNext.QuarticMatch.Hessian
