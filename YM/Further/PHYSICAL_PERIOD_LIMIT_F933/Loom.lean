import YM.Extra.ITERATION_NO_LOSS.Atoms
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Shingle

/-! # Exponential license between any matching systems of two tori

Accounting lock at floor side N, LENGTH in absolute distance; from universal geometry & symmetry
of actual unmarked functions, not a hypothesis on their loop answers. Last task here
before proving those geometry statements. Small/full external directions can be any
unit position profiles (sup norm, incl all real waves) supplied jointly. int normalization
one trace, not full intensive normalized determinant itself.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Loom
open Jacobi Polytrace     Shingle Push.Uniform
open Function Lattice Gauge RG Tree Matrix Finset Precision Filter Exterior Bid Wilson Set Metric
open scoped Topology ContDiff BigOperators
variable {β α ι : Type} [Fintype β] [Fintype α] [Fintype ι] {s : Side} {X : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X]

variable [DecidableEq β] [DecidableEq α]
def statement {ι : Type} [Fintype ι] [DecidableEq ι] (F : X → Matrix ι ι ℝ) (a : X→ℝ) (x : X) := (1/2:ℝ)*Real.log (F x).det - a x

lemma jet_lock {F : X → Matrix β β ℝ} {b : X → ℝ} (v w : X) (hf : Faces F 0) (hb : ContDiffAt ℝ ω b 0) (he : (F 0).det≠0) :
    mixed v w (statement F b) 0 =
      (1/2:ℝ)*(Matrix.trace ((F 0)⁻¹*delta v (delta w F) 0) - Matrix.trace (((F 0)⁻¹*delta v F 0)*((F 0)⁻¹*delta w F 0))) - mixed v w b 0 := by
  let h x := Real.log (F x).det; let f x := (1/2:ℝ)*h x
  have ht := (face_det hf).log he
  have he : ContDiffAt ℝ ω f 0 := contDiffAt_const.mul ht
  have hz (j : X) (hh : ContDiffAt ℝ ω h j) (hb : ContDiffAt ℝ ω b j) :
      blade w (statement F b) j = (1/2:ℝ)*blade w h j - blade w b j := by
    change fderiv ℝ (f-b) _ _ = _
    rw [fderiv_sub (f:=f) ((contDiffAt_const.mul hh).differentiableAt (by simp)) (hb.differentiableAt (by simp))]
    change blade w f j - _ = _; rw [product (f:=fun _=> (1/2:ℝ)) w contDiffAt_const hh, blade_const,mul_zero,add_zero]; rfl
  let L (j : X) := (1/2:ℝ)*blade w h j - blade w b j
  have hh : blade w (statement F b) =ᶠ[𝓝 0] L := by
    filter_upwards [ht.eventually (by simp), hb.eventually (by simp)] with x hf hb; exact hz x hf hb
  have hU := smooth w ht; have hd := smooth w hb
  unfold mixed; rw [show blade v (blade w _) 0 = blade v L 0 from congr_arg (fun l:X→L[ℝ]ℝ=>l v) hh.fderiv_eq]
  change fderiv ℝ ((fun j=>(1/2:ℝ)*blade w h j) - blade w b) 0 v = _
  rw [fderiv_sub ((contDiffAt_const (c:=(1/2:ℝ))).mul (show ContDiffAt ℝ ω (blade w h) 0 from hU) |>.differentiableAt (by simp)) (hd.differentiableAt (by simp))]
  change blade _ (fun j=>(1/2:ℝ)*blade w h j) _ - blade v (blade w b) 0 = _
  rw [product _ contDiffAt_const hU,blade_const,mul_zero,add_zero]
  congr 2
  rw [show blade v _ _= _ from tranche v w hf ‹_›,← Matrix.mul_assoc]

lemma mixed_scale {g b : X → ℝ} (hb : ContDiffAt ℝ ω b 0) (m : ℝ) (he : g=ᶠ[𝓝 0] fun x => m*b x) (v w : X) :
    mixed v w g 0=m*mixed v w b 0 := by
  have ht : blade w g =ᶠ[𝓝 0] fun x=>m*blade w b x := by
    filter_upwards [hb.eventually (by simp),eventually_eventually_nhds.mpr he] with x hx h
    rw [show blade w g x=blade w (fun j=>m*b j) x from congr_arg (fun L : X →L[ℝ] ℝ=>L w) (show g =ᶠ[𝓝 x] fun x=>m*b x from h).fderiv_eq,product _ contDiffAt_const hx, blade_const,mul_zero,add_zero]
  unfold mixed; rw [show blade v (blade w _) _=blade v (fun x=>m*blade w b x) 0 from congr_arg (fun L : X→L[ℝ] ℝ=> L v) ht.fderiv_eq,product _ contDiffAt_const (smooth _ hb), blade_const,mul_zero, add_zero]

variable {T Q B d : ℝ}
-- Sufficient total amount before converting from all indices on big to cost per site
-- no half required
def spending (K : ℕ) (T Q B d : ℝ) :=
  let H := (B*T*space K (d/2)); (B*Q*space K (d/4)+H*H*space K (d/4))*space K (d/4/2)
lemma disburse (K : ℕ) (ht : 0 ≤ T) (hq : 0≤ Q) (hb : 0 ≤ B) (hp : 0<d) : 0 ≤ spending K T Q B d := by
  have he := space_pos K (half_pos hp); have h : 0 < d/4 := by positivity
  have := space_pos K h; have := space_pos K (half_pos h); unfold spending; dsimp only; positivity

/-- Tail estimate directly for M times SMALL minus LARGE; no ratios per true spectral eigenvalue.
Both Haar answered in same direction. M copies and raw price of #beta. -/
theorem spinning {π : β→α} {K M N : ℕ} {l : β→Site s} (hL : Multiplicity l K) (hF : Fold π M) (he : Reserved l π N)
    (hp : 0 < d) (ht : 0 ≤ T) (hq : 0 ≤ Q) (hb : 0≤B)
    {F : X → Matrix β β ℝ} {G : X → Matrix α α ℝ} {y z : X → ℝ} (hf : Faces F 0) (hg : Faces G 0)
    (hx : (F 0).det≠0) (hU : (G 0).det≠0) (hG : ∀ᶠ x in 𝓝 0, Every π (F x) (G x))
    (hP : ContDiffAt ℝ ω y 0) (hQ : ContDiffAt ℝ ω z 0) (hh : y =ᶠ[𝓝 0] fun x => (M:ℝ)*z x)
    (hl : Sealed l d (F 0)⁻¹ B)
    (u v : X) (hu : Sealed l d (delta u F 0) T) (hv : Sealed l d (delta v F 0) T)
    (hs : Sealed l d (delta u (delta v F) 0) Q) :
    |(M:ℝ)*mixed u v (statement G z) 0 - mixed u v (statement F y) 0| ≤
      (Fintype.card β : ℝ)*spending K T Q B d*Real.exp (-(d/4/2)*N) := by
  classical
  let I := (F 0)⁻¹; let i := (G 0)⁻¹
  have hh0 : Every π (F 0) (G 0) := @Filter.Eventually.self_of_nhds X _ 0 (fun x=>Every π (F x) (G x)) hG
  have hZ : Every π I i := Shingle.flip hh0 hx hU
  have hg w : Every π (delta w F 0) (delta w G 0) := (pay w (faces_near hf) (faces_near hg) hG).self_of_nhds
  let D := d/4; let P := space K D; let R := space K (d/2)
  have hD : 0<D := by unfold D; positivity
  have h₁ : D+D ≤ d := by unfold D; linarith
  have h₂ : D+D ≤ d/2 := by unfold D; linarith
  -- products in actual hessian formula
  have h1 := deficit hD (mul_nonneg (mul_nonneg hb hq) (space_pos K hD)) hL hF he (premium hl hs hb hq hL h₁ hD) (Shingle.square hZ (spray u v hf ‹Faces G 0› hG))
  let H := B*T*R
  have h w (hw : Sealed l d w T) : Sealed l (d/2) (I*w) H := premium hl hw hb ht hL (add_halves d).le (half_pos hp)
  have hy : 0≤H := mul_nonneg (mul_nonneg hb ht) (space_pos _ (half_pos hp))
  have h2 := deficit hD (mul_nonneg (mul_nonneg hy hy) (space_pos K hD)) hL hF he (premium (h _ hu) (h _ hv) hy hy hL h₂ hD) (Shingle.square (Shingle.square hZ (hg u)) (Shingle.square hZ (hg v)))
  let Lw := (Fintype.card β:ℝ)
  let a := Real.exp (-(d/4/2)*N); let charge := spending K T Q B d
  let f₁ := (I*delta u (delta v F) 0).trace; let f₂ := ((I*delta u F 0)*(I*delta v F 0)).trace
  let g₁ := (i*delta u (delta v G) 0).trace; let g₂ := ((i*delta u G 0)*(i*delta v G 0)).trace
  have hw := mixed_scale hQ _ hh u v
  rw [jet_lock _ _ ‹Faces G 0› hQ hU,jet_lock _ _ hf hP hx,hw]
  let x := (M:ℝ)*g₁-f₁; let y := (M:ℝ)*g₂-f₂
  change |(M:ℝ)*(1/2*(g₁-g₂)-_)-(1/2*(f₁-f₂)-_)| ≤ Lw*charge*a
  have HC : 0 ≤ Lw*charge*a := by have hi : 0≤charge:=disburse _ ht hq hb hp; unfold Lw a; positivity
  rw [show (M:ℝ)*(1/2*(g₁-g₂)-mixed u v z 0)-(1/2*(f₁-f₂)-(M:ℝ)*mixed u v z 0)=(1/2)*(x-y) by unfold x y; ring,abs_mul]
  apply (mul_le_mul_of_nonneg_left (abs_sub ..) (abs_nonneg _)).trans -- abs_sub_le?
  apply (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (abs_nonneg _)).trans
  norm_num1 -- lowers abs
  apply le_trans _ (show _ ≤ Lw*charge*a from mul_le_of_le_one_left HC (by norm_num : (1/2:ℝ)≤1))
  unfold charge spending H R a Lw; unfold D; dsimp only; exact le_of_eq (by ring)
end YM.Further.PhysicalPeriodLimitF933.Loom
