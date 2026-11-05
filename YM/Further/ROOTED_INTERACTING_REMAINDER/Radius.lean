import YM.Next.EXTRACTION.Tails
import YM.Next.FREE_KERNELS.Signal
import YM.Push.CORRECTED_COLUMNS.Tree
import YM.Work.E01
import YM.Work.E04
import YM.Work.E09.Scales

/-!
# The halo toll for holes in the intact normalized estimate

Not a forecast: includes proof that share income from points_grant (even
a fraction) is sufficient for our elimination, once stationed. In
particular at next height, must still buy along with other delays so no
Program advance estimated by imposing this on a finished calendar.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder.Levy
open Filter Function Lattice RG RG.Patch Axial Wilson Finset Precision Tree Exterior Bloch Laurent
open Pressure Pressure.Stores Pressure.Teller Pressure.Tube Bid 
open Vac.Numbers
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

lemma nucleated (S : StepData c f) (C : Stores S) (r : ℕ) :
    (C.dome r).card ≤ 4 * C.shares * (r+r+1)^4 :=
  (Lattice.Corona.halo_size C.place _).trans (Nat.mul_le_mul_right _ (Work.E01.place_card C))

lemma covers_intern (S : StepData c f) (C : Stores S) (x : ℝ) :
    (C.intern x).card ≤ 4*4*(2*radiusB x+2*radiusB x+1)^4*C.shares := by
  let r := 2*radiusB x
  calc
    _ ≤ (C.dome r ×ˢ (univ : Finset Axis)).card := Finset.card_le_card (t:=C.dome r ×ˢ (univ : Finset Axis)) (fun i hi=>mem_product.mpr ⟨(mem_filter.mp hi).2,mem_univ _⟩)
    _ ≤ (4 * C.shares * (r+r+1)^4)*Fintype.card Axis := by
      rw [Finset.card_product,Finset.card_univ]; exact Nat.mul_le_mul_right _ (nucleated ..)
    _ = _ := by rw [show Fintype.card Axis = 4 by decide]; unfold r; ring

lemma covers_limit (S : StepData c f) (C : Stores S) (x : ℝ) :
    (C.limit x).card ≤ Work.E01.volumePrice (2*radiusB x)*C.shares*S.patch.L.val^4 := by
  let r := 2*radiusB x
  let P := C.limit x
  let Y := C.dome r
  let T := Site S.patch.L × PlaqAxes
  let e (i : Cell f) : Site c × T := (S.ratio.parent i.1,S.ratio.residue i.1, i.2)
  have hi : Function.Injective e := by
    intro i j H; have hy := Prod.mk.inj H
    have he : S.ratio.splitSites i.1 = S.ratio.splitSites j.1 := by rw [← S.ratio.unpack,←S.ratio.unpack,hy.1, (Prod.mk.inj hy.2).1]
    exact Prod.ext (S.ratio.splitSites.injective he) (Prod.mk.inj hy.2).2
  have he : P.image e ⊆ (Y ×ˢ (univ : Finset T)) := by
    intro u h; obtain ⟨i,hi,rfl⟩ := mem_image.mp h; exact mem_product.mpr ⟨(mem_filter.mp hi).2,mem_univ _⟩
  change P.card ≤ _
  rw [← Finset.card_image_of_injective _ hi]
  calc
    _ ≤ _ := Finset.card_le_card he
    _ = Y.card * (S.patch.L.val^4*Fintype.card PlaqAxes) := by simp [T,site_card]
    _ ≤ _ := Nat.mul_le_mul_right _ (nucleated S C r)
    _ = _ := by unfold Work.E01.volumePrice r; ring

-- holes for both coins for THIS Store count
def density (L : Side) (x : ℝ) : ℕ :=
    (4*4+4*(Fintype.card PlaqAxes)*L.val^4)*(5*(1+radiusB x))^4
lemma unit_density (S : StepData c f) (C : Stores S) (x : ℝ) :
    (C.limit x).card+(C.intern x).card ≤ density S.patch.L x*C.shares := by
  apply (Nat.add_le_add (covers_limit S C x) (covers_intern S C x)).trans
  unfold Work.E01.volumePrice density
  have he : (2*radiusB x+2*radiusB x+1)^4 ≤ (5*(1+radiusB x))^4 := by gcongr; omega
  calc
    _ ≤ _ := Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 he))))
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left (4*4) he))
    _ = _ := by ring

open Work.E09
-- Power any. `β.shape²` compared at same hat variable b on both levels.
private lemma monitor_cover (i : ℕ) (L : Side) :
    Tendsto (fun x : ℝ => (1+Real.log (betaF G x L))^i / Vac.Numbers.P (betaF G x L)) atTop (𝓝 0) := by
  have h : Tendsto (fun v : ℝ => (1+Real.log v)^i/P v) atTop (𝓝 0) := by
    let y := fun v : ℝ=> Real.log (Real.log v)
    have he : Tendsto y atTop atTop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
    have hg : Tendsto (fun v => 2^i * Real.exp (-(y v))) atTop (𝓝 0) := by
      have hx := (Real.tendsto_exp_neg_atTop_nhds_zero.comp he).const_mul ((2:ℝ)^i)
      simpa using hx
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [eventually_gt_atTop 1] with v hv; have := Real.log_pos hv; have hp : 0<P v := Real.exp_pos _; positivity
    filter_upwards [he.eventually_ge_atTop ((i:ℝ)+1),Real.tendsto_log_atTop.eventually_ge_atTop 1] with v hh hv
    let a:=y v
    have ht : 0<Real.log v := zero_lt_one.trans_le hv
    change (i:ℝ)+1≤a at hh
    unfold P
    calc
      _ ≤ (2*Real.exp a)^i/Real.exp (a^2) := by rw [Real.exp_log ht]; gcongr; linarith
      _ = 2^i*Real.exp ((i:ℝ)*a - a^2) := by rw [mul_pow,←Real.exp_nat_mul,mul_div_assoc,Real.exp_sub]
      _ ≤ _ := by
        change (2:ℝ)^i * _ ≤ (2:ℝ)^i*_
        gcongr; change (i:ℝ)*a - a^2 ≤ -a; nlinarith [Nat.cast_nonneg (α:=ℝ) i]
  exact h.comp (betaF_growth G L)

private lemma halo_toll (L : Side) (d : ℕ) :
    Tendsto (fun x => (density L x : ℝ)*d*(1+Real.log (betaF G x L)) / (Vac.Numbers.P (betaF G x L))) atTop (𝓝 0) := by
  let v := fun x => betaF G x L
  let C : ℕ := (4*4+4*Fintype.card PlaqAxes*L.val^4)*5^4*3^4
  -- B≈log²; 1+B≤3(log v+1)^2
  have ht (x : ℝ) (hx : 1≤x) : (density L x:ℝ) ≤ C * (1+Real.log (v x))^8 := by
    have hb : (radiusB x:ℝ) ≤ (Real.log x)^2 + 1 := (Nat.ceil_lt_add_one (sq_nonneg _)).le
    have hx' : x ≤ v x := le_add_of_nonneg_right (Work.E04.shift_nonneg G L)
    have hL : 0≤Real.log x := Real.log_nonneg hx
    have he := Real.log_le_log (by linarith only [hx]) hx'
    have hy : (1:ℝ)+radiusB x ≤ 3*(1+Real.log (v x))^2 := by nlinarith only [hb,hL,he]
    unfold C density; push_cast
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (show (0:ℝ)≤5*(1+(radiusB x:ℝ)) by positivity) (mul_le_mul_of_nonneg_left hy (a:= (5:ℝ)) (by norm_num)) 4) (by positivity)
      _ = _ := by ring
  have hg : Tendsto (fun x => (C:ℝ)*d*((1+Real.log (v x))^9/P (v x))) atTop (𝓝 0) := by
    have hb := (monitor_cover (G:=G) 9 L).const_mul ((C:ℝ)*d)
    simpa only [mul_zero] using hb
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [(betaF_growth G L).eventually_ge_atTop 1] with x hx
    have := Real.log_nonneg hx; have hP := Real.exp_pos ((Real.log (Real.log (v x)))^2)
    change 0 ≤ _*(1+Real.log (betaF G x L)) / Real.exp _; positivity
  filter_upwards [(betaF_growth G L).eventually_ge_atTop 1,eventually_ge_atTop (1:ℝ)] with x hx he
  let y := 1+Real.log (v x)
  have hy : 0≤y := by dsimp only [y,v]; linarith [Real.log_nonneg hx]
  calc
    _ ≤ (C:ℝ)*y^8*d*y/P (v x) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (ht x he) (Nat.cast_nonneg _)) hy) (Real.exp_pos _).le
    _ = _ := by change _ ≤ _ at hy; unfold y v; ring

/-- Restoring even all the lost halo links (per seed, conservative count),
out of same grant on intact. -/
theorem buy_halos (G : Gauge) (δ : ℕ) (L : Side) (κ : ℝ) (hκ : 0<κ) :
    ∀ᶠ x : ℝ in atTop, ∀ β : ℝ,betaF G x L/2 ≤ β → β≤2*betaF G x L →
      let v := fiery G x L
      let τ := Real.sqrt β
      Real.exp (-(κ/2)*(β*v^2))*(τ^δ)^density L x ≤ 1 := by
  filter_upwards [(halo_toll (G:=G) L (δ)).eventually (ge_mem_nhds (show 0<(κ/4) by positivity)),
    (betaF_growth G L).eventually_ge_atTop 4] with x hx he
  intro β h hB v τ
  let b := betaF G x L
  have h4 : 4≤b := he
  have hp : 0<β := by change b/2 ≤ β at h; linarith
  have ht : 0<τ := Real.sqrt_pos.mpr hp
  let p := P b
  have hP : 1≤p := Real.one_le_exp (sq_nonneg _)
  have hτ : τ ≤ b := by change β ≤ 2*b at hB; nlinarith only [Real.sq_sqrt hp.le,hB,h4,ht]
  have hy : Real.log τ ≤ Real.log b := Real.log_le_log ht hτ
  let d := (δ)
  let n := density L x
  rw [show (τ^d)^n=Real.exp (n*(d*Real.log τ)) by rw [Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_log ht],← Real.exp_add]
  apply Real.exp_le_one_iff.mpr
  have hv : b*v^2=p^2 := by
    unfold v fiery temp; rw [mul_pow,inv_pow,Real.sq_sqrt (show 0≤betaF G x L by linarith only [he]),←mul_assoc, show (betaF G x L)=b by rfl,mul_inv_cancel₀ (by linarith),one_mul]; rfl
  have he : (density L x:ℝ)*d*(1+Real.log b) ≤ κ/4*p := (div_le_iff₀ (zero_lt_one.trans_le hP)).mp hx
  have hd : 0 ≤ (density L x:ℝ)*d := by positivity
  change b/2 ≤ β at h
  have hT := mul_le_mul_of_nonneg_right h (sq_nonneg v)
  unfold n
  linarith only [mul_le_mul_of_nonneg_left (show Real.log τ≤1+Real.log b by linarith only [hy]) hd,he,
    mul_le_mul_of_nonneg_left (show p≤p^2 by nlinarith only [hP]) hκ.le, mul_le_mul_of_nonneg_left hT hκ.le,
    show κ*(b*v^2)=κ*p^2 by rw [hv]]

theorem cash_holes (G : Gauge) (L : Side) (κ : ℝ) (hκ : 0<κ) :
    ∀ᶠ x : ℝ in atTop, ∀ β : ℝ,betaF G x L/2 ≤ β → β≤2*betaF G x L →
      let v := fiery G x L
      let τ := Real.sqrt β
      Real.exp (-(κ/2)*(β*v^2))*(τ^Module.finrank ℝ G.Color)^density L x ≤ 1 :=
  buy_halos G _ L κ hκ

end YM.Further.RootedInteractingRemainder.Levy
