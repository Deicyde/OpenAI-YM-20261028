import YM.ProjectorNext.PROJECTOR_CALIBRATION.Equation
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Picks

/-!
# Cash the finite stencil estimates at regulator or in precomputation

Compute by smooth laws on 2 parameters at each d.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice RG Wilson Source Source.Drops Labels Work Function Filter Next.Foundations Push.CutoffProjectors Coupon
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ}
namespace Machine
variable (M : Machine H d) (F : Labels.Frame G d)

/-- Value of each basis contribution on scaled native jets through order d. -/
def calendar (i : F.Index) (k : Lens G d) (θ χ : ℝ) : ℂ :=
    let f (t : ℝ) := course (d:=d) k.1 t
    iteratedDeriv (k.2:ℕ) (fun t =>
      (∑ w : M.Outlet, daylight (shade F i) M.U d (M.first w) θ (f t)) -
      ∑ w : M.Outlet, ∑ j : G.ColorIndex, evening (shade F i) M.U d (M.second w j) θ χ (f t)) 0

set_option maxHeartbeats 500000 in
lemma smooth_calendar (i : F.Index) (k : Lens G d) : ContDiff ℝ ω (uncurry (M.calendar F i k)) := by
  refine varies k.2.val (X:=ℝ × ℝ) (Y:=ℂ) (f:=fun (p : (ℝ × ℝ) × ℝ) =>
    (∑ w : M.Outlet, daylight (shade F i) M.U d (M.first w) p.1.1 (course k.1 p.2)) -
      ∑ w : M.Outlet, ∑ j : G.ColorIndex, evening (shade F i) M.U d (M.second w j) p.1.1 p.1.2 (course k.1 p.2)) ?_
  let f (p : (ℝ × ℝ) × ℝ) : Snap G d := course k.1 p.2
  have hh : ContDiff ℝ ω f := (course_smooth k.1).comp contDiff_snd
  apply ContDiff.sub
  · refine ContDiff.sum fun w _ => (day_smooth (shade F i) M.U d (M.first w)).comp (f:=fun p : (ℝ × ℝ) × ℝ => (p.1.1,f p)) (contDiff_fst.fst.prodMk hh)
  exact ContDiff.sum fun w _ => ContDiff.sum fun j _ =>
    (eve_smooth (shade F i) M.U d (M.second w j)).comp (f:=fun p : (ℝ × ℝ) × ℝ => (p.1.1,p.1.2,f p))
      (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk hh))

/-- The limiting law on all the coefficient slots of interest to triangles. -/
lemma as_recorded (i : F.Index) (k : Lens G d) :
    M.calendar F i k 0 0 = iteratedDeriv k.2.val
      (fun t => Cross.mix (shade F i) M.U (course k.1 t) (M.liftAll (course k.1 t))) 0 := by
  unfold calendar
  simp_rw [day_value,M.init_first,evening,zero_smul ℝ, Finset.sum_const_zero,sub_zero]
  apply congr_arg (fun f => iteratedDeriv k.2.val f 0)
  funext t
  simp_rw [← _root_.map_sum, M.complete] -- continuouslinear map sum

private def stencilInput (i : F.Index) (k : Lens G d) (θ β t : ℝ) :=
    let U := H.links d (θ • k.1) t
    θ⁻¹^(F.grades i).2 • (M.energyLeg F i U - β⁻¹ • M.divLeg F i U)

private lemma joint {I J : Type*} [Fintype I] [Fintype J] (k : ℕ) {Y : I → ℝ → ℂ} {D : I → J → ℝ → ℂ}
    (hy : ∀ i, ContDiffAt ℝ (k:WithTop ℕ∞) (Y i) 0) (hd : ∀ i j, ContDiffAt ℝ (k:WithTop ℕ∞) (D i j) 0) :
    iteratedDeriv k (fun t => (∑ i,Y i t) - ∑ i, ∑ j,D i j t) 0 = (∑ i, iteratedDeriv k (Y i) 0) - ∑ i,∑ j,iteratedDeriv k (D i j) 0 := by
  rw [iteratedDeriv_fun_sub (ContDiffAt.sum fun i _ => hy i) (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => hd i j),iteratedDeriv_fun_sum (fun i _ => hy i), iteratedDeriv_fun_sum (fun i _ => ContDiffAt.sum fun j _ => hd i j)]
  simp_rw [iteratedDeriv_fun_sum (fun i _ => hd _ i)]

set_option maxHeartbeats 500000 in
private lemma raw_law (i : F.Index) (k : Lens G d) (θ β : ℝ) (ht : θ≠0) :
    iteratedDeriv k.2.val (M.stencilInput F i k θ β) 0 = M.calendar F i k θ (β⁻¹/θ^2) ∧
    ContDiffAt ℝ (k.2.val:WithTop ℕ∞) (M.stencilInput F i k θ β) 0 := by
  let χ := β⁻¹ /θ^2
  let f (t : ℝ) : Snap G d := course k.1 t
  let T := θ⁻¹^(F.grades i).2
  have hβ : β⁻¹=χ*θ^2 := (div_mul_cancel₀ _ (pow_ne_zero 2 ht)).symm
  let Y (w : M.Outlet) (t : ℝ) : ℂ := T • raw (shade F i) M.U (M.first w (θ • f t))
  let Z (w : M.Outlet) (j : G.ColorIndex) (t : ℝ) : ℂ := T • ((χ*θ^2) • marked (shade F i) M.U (M.second w j (θ • f t)))
  have he : M.stencilInput F i k θ β = fun t => (∑ w,Y w t)-∑ w,∑ j,Z w j t := by
    funext t; unfold stencilInput; simp_rw [energyLeg,divLeg,smul_sub,Finset.smul_sum,course_pays, diagnostic,differentiated, hβ]; rfl
  rw [he]; unfold calendar
  let n : WithTop ℕ∞ := k.2.val
  let J := k.1
  have hy (w) : ContDiffAt ℝ n (Y w) 0 := ((contDiffAt_const (c:=T)).smul
    (sensed θ (smooth_first M w) (raw_smooth (shade F i) M.U) (course_smooth J) (course_zero J))).of_le (show n≤ω from le_top)
  have hz (w j) : ContDiffAt ℝ n (Z w j) 0 := ((contDiffAt_const (c:=T)).smul ((contDiffAt_const (c:=χ*θ^2)).smul
    (sensed θ (smooth_second M w j) (marked_smooth (shade F i) M.U) (course_smooth J) (course_zero J)))).of_le (show n≤ω from le_top)
  refine ⟨?_, (ContDiffAt.sum fun w _ => hy w).sub (ContDiffAt.sum fun w _ => ContDiffAt.sum fun j _ => hz w j)⟩
  let L (w : M.Outlet) (t : ℝ) := daylight (shade F i) M.U d (M.first w) θ (f t)
  let V (w : M.Outlet) (j : G.ColorIndex) (t : ℝ) := evening (shade F i) M.U d (M.second w j) θ χ (f t)
  have hL (w : M.Outlet) : ContDiffAt ℝ n (L w) 0 := ((day_smooth (shade F i) M.U d (M.first w)).comp (f:=fun t => (θ,f t))
    (contDiff_const.prodMk (course_smooth J))).contDiffAt.of_le le_top
  have hV (w j) : ContDiffAt ℝ n (V w j) 0 := ((eve_smooth (shade F i) M.U d (M.second w j)).comp (f:=fun t => (θ,χ,f t))
    (contDiff_const.prodMk (contDiff_const.prodMk (course_smooth J)))).contDiffAt.of_le le_top
  rw [joint _ hy hz, joint _ hL hV] -- definal D funcs?
  have hk := k.2.isLt.le
  simp_rw [show ∀ w, iteratedDeriv k.2.val (Y w) 0=iteratedDeriv k.2.val (L w) 0 from fun w => cash (shade F i) M.U d _ hk (smooth_first M w) (first_zero M w) (course_smooth J) (course_zero J) ht,
    show ∀ w j, iteratedDeriv k.2.val (Z w j) 0=iteratedDeriv k.2.val (V w j) 0 from fun w j => cash_div (shade F i) M.U d _ hk (smooth_second M w j) (second_zero M w j) (course_smooth J) (course_zero J) ht]

variable {C : Family G} (M₀ : Machine C.params d) {N p : ℕ} (E : Packet C d N p)

theorem calendar_eq {s : Finset Cover} (h : M₀.Release s) (hn : ∀ x∈s,∀ a : Axis, 20*((x a).natAbs+1)≤(C.side N p).val)
    (he : M₀.lined E) (x : equationSpace (C.labels.level d)) (k : Lens G d) :
    E.amount x k = let F := C.labels.level d; let θ := C.path.levels.clock.threshold N
      ∑ i : F.Index, x.val i * M₀.calendar F i k θ ((C.beta N p)⁻¹/θ^2) := by
  dsimp only
  rw [amount_eq M₀ E h hn he]; dsimp only
  let F := C.labels.level d
  let θ := C.path.levels.clock.threshold N
  let β := C.beta N p
  have ht : θ≠0 := (C.path.levels.budget N).threshold_pos.ne'
  let f (i : F.Index) := M₀.stencilInput F i k θ β
  have hh i := raw_law M₀ F i k θ β ht
  have hd (t : ℝ) (i : F.Index) :
      (↑(θ⁻¹ ^ (F.grades i).2) : ℂ)* (x.val i) *
        (M₀.energyLeg F i (C.params.links d (θ • k.1) t) - (↑β : ℂ)⁻¹ * M₀.divLeg F i (C.params.links d (θ • k.1) t)) =
      x.val i * f i t := by simp only [f,stencilInput,Complex.real_smul,Complex.ofReal_inv]; ring
  let R (i : F.Index) (t : ℝ) := (↑(θ⁻¹ ^ (F.grades i).2) : ℂ)* (x.val i) *
        (M₀.energyLeg F i (C.params.links d (θ • k.1) t)-(↑β : ℂ)⁻¹*M₀.divLeg F i (C.params.links d (θ • k.1) t))
  change iteratedDeriv k.2.val (fun t => ∑ i : F.Index, R i t) 0 = _
  have hR (i t) : R i t=x.val i * f i t := hd ..
  simp_rw [hR]
  rw [iteratedDeriv_fun_sum (fun i _ => contDiffAt_const.mul (hh i).2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_const_mul _ (hh i).2]; exact congr_arg _ (hh i).1

end Machine
end YM.ProjectorNext.Calibration
