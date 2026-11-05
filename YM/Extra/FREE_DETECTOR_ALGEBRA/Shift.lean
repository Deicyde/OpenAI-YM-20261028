import YM.Extra.FREE_DETECTOR_ALGEBRA.LegAct
import YM.Extra.FREE_DETECTOR_ALGEBRA.Translation

set_option warningAsError false

/-!
# Shift-triangular diagonalization of the physical single leg

Recenter at the inversion of a noncoincident separation. Statement
still about either-side Taylor tests on the *same* kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {x y : E4} {j k : ℕ}

def shifts (j k : ℕ) (x : E4) : Sol F j →ₗ[ℝ] Sol F k :=
    (strength j / strength k) • towards j k (-inversePoint x)

@[simp] theorem shifts_self (P : Sol F j) (x : E4) : shifts j j x P = P := by simp [shifts, strength_ne]

theorem field_smul (c : ℝ) (Q : Sol F k) (i m : Axis) (y : E4) : Sol.field (c • Q) i m y = c • Q.field i m y := rfl

theorem fields_shift (P : Sol F j) (x y : E4) (i m : Axis) :
    ∑ k : Fin (j+1), strength k.val • Sol.field (shifts _ k.val x P) i m y =
      strength j • P.field i m (y-inversePoint x) := by
  have he (k : Fin (j+1)) : strength k.val • Sol.field (shifts _ k.val x P) i m y =
      strength j • Sol.field (towards _ k.val (-inversePoint x) P) i m y := by rw [shifts,LinearMap.smul_apply,field_smul,smul_smul,mul_comm,div_mul_cancel₀ _ (strength_ne _)]
  simp_rw [he,← Finset.smul_sum,field_expands,add_comm (-inversePoint x),sub_eq_add_neg]

/-- Blow-up increment for inversion on the test line. `scaleVector`
remains smooth through zero line parameter (given fixed basepoint x nonzero).
-/
def scaleVector (x v : E4) (t : ℝ) : E4 := rr (x + t • v) •
    (mov (face x) v - (t * ‖v‖^2) • inversePoint x)

theorem invert_line (hx : x ∈ away) (v : E4) (t : ℝ) (hv : x + t • v ∈ away) :
    inversePoint (x+t • v) - inversePoint x = t • scaleVector x v t := by
  have he (x : E4) (hx : x ∈ away) : rr x*‖x‖^2=1 := inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  let A := rr x
  let B := rr (x+t • v)
  have hz : ‖x + t • v‖^2 = ‖x‖^2 + 2*t*⟪x,v⟫ + t^2*‖v‖^2 := by
    simp only [← real_inner_self_eq_norm_sq,inner_add_left,inner_add_right,real_inner_smul_left,
      real_inner_smul_right]; rw [real_inner_comm x v]; ring
  have ht : B * (‖x‖^2 + 2*t*⟪x,v⟫ + t^2*‖v‖^2)=1 := hz ▸ he _ hv
  have hc : B-A = -(A*B)*(2*t*⟪x,v⟫ + t^2*‖v‖^2) := by
    have hA : A*‖x‖^2=1 := he _ hx
    linear_combination A*ht - B*hA
  unfold inversePoint scaleVector
  rw [mov_apply,face_apply]
  change B • (x+t • v) - A • x = t • B • (v - (2*A*⟪x,v⟫) • x - (t*‖v‖^2) • A • x)
  rw [smul_add,add_sub_right_comm, ← sub_smul,hc]
  module

variable {G : Gauge}

/-- Left response for the shifted probe. Here `x` denotes intended
separation fixed in advance; evaluation argument still ranges (even for
taking right derivatives). -/
def signal (P : Sol G.Color j) (x : E4) : Maxwell.Field G.Color := fun i m y =>
    ∑ k : Fin (j+1), reply (G:=G) (shifts _ k.val x P) i m y

theorem signal_wave (P : Sol G.Color j) (x : E4) : WaveOn away (signal (G:=G) P x) := superpose fun _ => replied _

theorem signal_kelvin (P : Sol G.Color j) (x : E4) (hy : y ∈ away) :
    (fun i m => signal (G:=G) P x i m y) = rr y ^ 2 • bi (face y).val
      (fun a b => strength j • P.field a b (inversePoint y-inversePoint x)) := by
  let Q (k : Fin (j+1)) := shifts _ k.val x P
  let f (k : Fin (j+1)) (a b : Axis) := (Q k).field a b (inversePoint y)
  have he (k : Fin (j+1)) : (fun i m => reply (G:=G) (Q k) i m y) =
      rr y ^ 2 • bi (face y).val (strength k.val • f k) := by
    rw [reply_radial _ hy, _root_.map_smul,mul_comm (strength _), mul_smul]
  have ht : ∑ k, strength k.val • f k = fun a b => strength j • P.field a b (inversePoint y-inversePoint x) := by
    funext a b; rw [Finset.sum_apply, Finset.sum_apply]; exact fields_shift ..
  rw [← ht,_root_.map_sum, Finset.smul_sum]
  ext1 i; ext1 m
  rw [Finset.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => congr_fun (congr_fun (he k) i) m

private def onLine (P : Sol G.Color j) (x v : E4) (i m : Axis) (t : ℝ) : G.Color :=
    let y := x+t • v
    rr y ^ 2 • bi (face y).val (fun a b => strength j • P.field a b (scaleVector x v t)) i m

private lemma line_eq (P : Sol G.Color j) (hx : x ∈ away) (v : E4) (i m : Axis) :
    (fun t : ℝ => signal (G:=G) P x i m (x+t • v)) =ᶠ[𝓝 0]
      fun t : ℝ => t^j • onLine P x v i m t := by
  let g := fun t : ℝ => x+t • v
  have hc : Continuous g := by unfold g; fun_prop
  have hb : g 0 ∈ away := by simpa [g] using hx
  filter_upwards [(hc.continuousAt (x:=0)).preimage_mem_nhds (open_away.mem_nhds hb)] with t ht
  rw [show signal (G:=G) P x i m (x+t • v) = _ from congr_fun (congr_fun (signal_kelvin P x (show g t ∈ away from ht)) i) m]
  have hu : (fun a b => strength j • P.field a b (inversePoint (g t)-inversePoint x)) =
      t^j • fun a b => strength j • P.field a b (scaleVector x v t) := by
    funext a b
    rw [invert_line hx v t ht,Sol.field,homogeneous, smul_comm]; rfl
  rw [hu,_root_.map_smul]; simp only [Pi.smul_apply]; rw [smul_comm]; rfl

private theorem line_diff (P : Sol G.Color j) (hx : x ∈ away) (v : E4) (i m : Axis) :
    ContDiffAt ℝ ∞ (onLine P x v i m) 0 := by
  let g := fun t : ℝ => x + t • v
  have hg : ContDiffAt ℝ ∞ g 0 := contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have hr : ContDiffAt ℝ ∞ (fun t => rr (g t)) 0 := ((rr_smooth (show g 0 ∈ away by simpa [g] using hx))).comp 0 hg
  have ht : ContDiffAt ℝ ∞ (scaleVector x v) 0 :=
    hr.smul (contDiffAt_const.sub ((contDiffAt_id.mul contDiffAt_const).smul contDiffAt_const))
  have hm a b : ContDiffAt ℝ ∞ (fun t => (face (g t)).val a b) 0 := by
    have hc a : ContDiffAt ℝ ∞ (fun t => g t a) 0 := (compAxis a).contDiff.contDiffAt.comp 0 hg
    exact contDiffAt_const.sub (((contDiffAt_const.mul hr).mul (hc a)).mul (hc b))
  have hs a b : ContDiffAt ℝ ∞ (fun t => P.field a b (scaleVector x v t)) 0 := (P.smooth a b _).comp 0 ht
  exact (hr.pow 2).smul (show ContDiffAt ℝ ∞ (fun t => ∑ a : Axis, ∑ b : Axis, (face (g t)).val i a •
    (face (g t)).val m b • strength j • P.field a b (scaleVector x v t)) 0 from ContDiffAt.sum fun a _ =>
      ContDiffAt.sum fun b _ => (hm i a).smul ((hm m b).smul ((contDiffAt_const (c:=strength j)).smul (hs a b))))

private theorem line_zero (P : Sol G.Color j) (x v : E4) (i m : Axis) :
    onLine P x v i m 0 = (strength j * rr x ^ (j+2)) • Sol.field (solO (face x) P) i m v := by
  let f := fun a b => P.field a b (mov (face x) v)
  have he : (fun a b => strength j • P.field a b (scaleVector x v 0)) = (strength j * rr x ^ j) • f := by
    funext a b
    rw [scaleVector,zero_smul,add_zero,zero_mul,zero_smul,sub_zero,Sol.field,homogeneous,mul_smul]; rfl
  rw [field_solO, reel]; dsimp only [ onLine]; rw [he,_root_.map_smul]
  simp only [Pi.smul_apply,zero_smul, add_zero,face_inv]; simp only [smul_smul, pow_add]; unfold f; congr 1; ring

private theorem signal_diag (P : Sol G.Color j) (hx : x ∈ away) (v : E4) (i m : Axis) (hk : k ≤ j) :
    diagonal (WaveOn.nth (signal (G:=G) P x) k x i m) v =
    if k=j then (strength j * rr x ^ (j+2)) • Sol.field (solO (face x) P) i m v else 0 := by
  have ht : (↑k : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  rw [WaveOn.nth,along (((signal_wave P x).smooth i m x hx).of_le ht),
    (line_eq P hx v i m).iteratedDeriv_eq,deriv_power ((line_diff P hx v i m).of_le ht) hk]
  split
  · rw [smul_smul,inv_mul_cancel₀ (by positivity),one_smul,line_zero]
  rw [smul_zero]

theorem signal_lower (P : Sol G.Color j) (hx : x ∈ away) (hk : k < j) : WaveOn.nth (signal (G:=G) P x) k x = 0 := by
  ext1 i; ext1 m
  refine ext_diag _ _ (((signal_wave P x).jets open_away hx).1.coeffSym i m) ?_ ?_
  · intro v σ; rfl
  funext v; rw [signal_diag P hx v i m hk.le,if_neg hk.ne]; rfl

theorem signal_top (P : Sol G.Color j) (hx : x ∈ away) : WaveOn.nth (signal (G:=G) P x) j x =
    (strength j * rr x ^ (j+2)) • (solO (face x) P).val := by
  ext1 i; ext1 m
  let Q : Sol G.Color j := (strength j*rr x^(j+2)) • solO (face x) P
  change _ = Q.val i m
  refine ext_diag _ _ (((signal_wave P x).jets open_away hx).1.coeffSym i m) (Q.closed.coeffSym i m) ?_
  funext v; exact (signal_diag P hx v i m (show j≤j from le_rfl)).trans (if_pos rfl)
end YM.Extra.FD
