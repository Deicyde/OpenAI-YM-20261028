import YM.Further.CURVED_GAUSSIAN_JETS.Colors
import YM.Further.CURVED_GAUSSIAN_JETS.WeightsD

/-! # The actual cut transported ell factor as a real color map -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Shape
open Function Filter Matrix Gauge Lattice Wilson Tree RG Precision Pressure Exterior Bid SectorNext.Vacuum FlatTree Progress.StationaryScenes Work
open Green (wt wt_pos Both)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {f : Side} (W : PathData G) (N : ℕ)
local notation "Key" => Shape.Page G f 2
local notation "basis" => EuclideanSpace.basisFun G.ColorIndex ℝ

def amp (U : Config G f) (x : Cell f) (k : ℕ) := G.adjoint (travel U x.1 (W.row x.2 k).2.walk)
def trace (U : Config G f) (k : ℕ) (x y : Key) := let a := (Cut.turn f).symm x.1; let b := (Cut.turn f).symm y.1
  Cut.tick W N a b k * ((amp W U a k) (basis y.2)).ofLp x.2

def ell (U : Config G f) : Table Key := Matrix.of fun x y => ∑' k, Shape.trace W N U k x y
lemma bounded (U : Config G f) (s : Signed) {w σ : ℝ} (h : 0≤w) (hs : 2*w ≤ σ) (k : ℕ) (x y : Key) :
    wt (2*w) (fineSite s x) (fineSite s y)* |Shape.trace W N U k x y| ≤ E04.rich W σ ((Cut.turn f).symm x.1).2 k := by
  rcases x with ⟨x,i⟩; rcases y with ⟨y,j⟩
  obtain ⟨a,rfl⟩ := (Cut.turn f).surjective x; obtain ⟨b,rfl⟩ := (Cut.turn f).surjective y
  simp only [Shape.trace,Cut.tick,fineSite,wt,separation_signed,Equiv.symm_apply_apply]; split <;> rename_i hh
  · obtain ⟨h1,rfl⟩ := hh
    have he : ‖amp W U a k (basis j)‖ = 1 := (G.norm_adjoint ..).trans (OrthonormalBasis.norm_eq_one ..)
    rw [abs_mul]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg _) ((coord_paid ..).trans_eq he)) (Real.exp_pos _).le)
    rw [mul_comm]; unfold E04.rich; gcongr
    · linarith only [h, hs]
    exact_mod_cast E04.slot_separation (W.row a.2 k).2 a.1
  unfold E04.rich; rw [zero_mul,abs_zero,mul_zero]; positivity

variable {W} {p : Clip} {σ C Λ : ℝ} (hb : W.Bounds p σ C Λ)
include hb
lemma summable_trace (U : Config G f) (x y : Key) : Summable fun k => Shape.trace W N U k x y := by
  refine Summable.of_norm_bounded (g:=E04.rich W σ ((Cut.turn f).symm x.1).2) (hb.rows _).2.1 (fun k=>?_)
  simpa [wt] using bounded W N U 1 (w:=0) le_rfl (by linarith [hb.width] : 2*(0:ℝ)≤σ) k x y
lemma ell_price (U : Config G f) (s : Signed) {w : ℝ} (hw : 0<w) (hs : 2*w≤σ) : let L := C*(crowd G * Push.Uniform.countCost w)
    Both (fineSite s) (fineSite s) (Shape.ell W N U) w L L := by
  intro L
  refine both_pay (fine_count s) (fine_count s) hw (Cut.pos_cost hb) (fun i j=>?_)
  have he := bounded W N U s hw.le hs
  have ht := (summable_trace N hb U i j).norm
  let e := wt (2*w) (fineSite s i) (fineSite s j)
  calc
    _ ≤ e*∑' k, |Shape.trace W N U k i j| := mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm ht) (wt_pos ..).le
    _ ≤ _ := by rw [←tsum_mul_left]; exact ((ht.mul_left e).tsum_le_tsum (g:=fun k => E04.rich ..) (fun k => he k i j) (hb.rows _).2.1).trans (hb.rows _).2.2

/-- Equality of the physical table with pathwise cut operation, not
just same adjoint norm. Direction colors ordinary Lie components. -/
lemma applied (U : Config G f) (v : Body 2 f → G.Color) (x : Key) : let a := (Cut.turn f).symm x.1
    HasSum (fun k => if (W.row a.2 k).2.length ≤ N then
        ((((W.row a.2 k).1) • amp W U a k (v (Cut.turn f (E04.landing (W.row a.2 k).2 a.1)))).ofLp x.2)
        else 0)
      ((Shape.ell W N U *ᵥ fun i:Key=> (v i.1).ofLp i.2) x) := by
  intro a
  apply (hasSum_sum (s:=Finset.univ) (fun i _ => ((summable_trace N hb U x i).hasSum.mul_right ((v i.1).ofLp i.2)))).congr_fun
  intro k
  rw [Fintype.sum_prod_type]; let b := E04.landing (W.row a.2 k).2 a.1
  have he y : b=(Cut.turn f).symm y ↔ y=Cut.turn f b := by rw [← (Cut.turn f).injective.eq_iff,Equiv.apply_symm_apply,eq_comm]
  unfold Shape.trace Cut.tick
  symm
  change ∑ i : Body 2 f, ∑ j, ((if (W.row a.2 k).2.length ≤ N ∧ b=(Cut.turn f).symm i then (W.row a.2 k).1 else 0)*_) * (v i).ofLp j = _
  split <;> rename_i hh
  · simp [hh,he,ite_mul]
    let L : G.Color →ₗ[ℝ] ℝ := (EuclideanSpace.proj x.2).toLinearMap.comp (amp W U a k)
    let u := v (Cut.turn f b)
    change ∑ j,(W.row a.2 k).1 * L (EuclideanSpace.single j 1) * u.ofLp j = _*L u
    have heq : ∑ j,(u.ofLp j) • (basis j) = u := (EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr u
    simp only [EuclideanSpace.basisFun_apply] at heq; nth_rw 2 [← heq]; rw [map_sum,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> ?_; rw [map_smul,smul_eq_mul]; ring
  simp [hh]
omit hb in
lemma ell_flat : Shape.ell W N (1:Config G f)=Tint.row G.ColorIndex (Cut.short W N f) := by
  ext i j
  simp only [Shape.ell,Matrix.of_apply, Shape.trace,amp, Tint.row_apply]
  have h k := G.adjoint_one (basis k)
  have ht (x : Cell f) (k : ℕ) : travel (1:Config G f) x.1 (W.row x.2 k).2.walk = 1 := by rw [← Precision.link_one]; exact Push.stroll_zero ..
  simp_rw [ht,h]; split <;> rename_i he
  · simp [EuclideanSpace.basisFun_apply,he,Cut.short]
  simp [EuclideanSpace.basisFun_apply,he]
end YM.Further.CurvedGaussianJets.Shape
