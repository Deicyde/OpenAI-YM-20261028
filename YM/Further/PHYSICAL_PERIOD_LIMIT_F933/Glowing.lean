import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.LocalLedger
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Rainy
import YM.SectorNext.VACUUM_NORMALIZATION.Plaques

/-!
# Real error inspectors for alpha ancestry identity

Brute loss on p (even powers of period) OK ONLY at this call
(comparing prices with exponential surplus); no implications for
price planning. Works without Hilbert symbol estimates at non-stationary fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Glowing
open Gauge Filter Jacobi Macrame Macrame.Lace Polytrace Withdrawal Liquid Enamel Loom Function Lattice RG Tree Matrix Finset Precision Exterior Bid Wilson Set Metric Push.Uniform Push Shingle Pitch Extra.Iteration Extra.Iteration.Calibration Bloch
open scoped Topology ContDiff BigOperators Classical

variable {G : Gauge} {n : Side}
abbrev bill := TypeFace 1→ G.ColorIndex→ℂ
def unitSize (σ : bill (G:=G)) := ∀ x i, ‖σ x i‖ ≤ 1

-- real chips in joint fieldDir (not positions), unit Size on entire type
abbrev ticket := Primary n G

def coin (q : ticket (G:=G) (n:=n)) (i : Site n) : bill (G:=G) := fun x j=> if x=q.1.2 ∧ j=q.2 then (cell i q.1.1)⁻¹ else 0
lemma orig (q : ticket) (i : Site n) : unitSize (coin (G:=G) q i) := by intro x j; unfold coin; split<;>simp [Inflation.norm_atom]

lemma cash (q : ticket) : (Fintype.card (Site n):ℝ)⁻¹ • ∑ p : Site n,wave p (coin (G:=G) q p) = tint G _ (bolt q) := by
  funext x; ext1 j
  let m : ℝ:=Fintype.card (Site n)
  rw [Pi.smul_apply,Finset.sum_apply,PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply]
  change m⁻¹ * (∑ i : Site n, (cell i x.1 * (if x.2=q.1.2 ∧ j=q.2 then (cell i q.1.1)⁻¹ else 0)).re) = bolt q (x,j)
  by_cases h:x.2=q.1.2 ∧ j=q.2
  · simp_rw [if_pos h]; have ht := orthogonal x.1 q.1.1; simp_rw [cell_duality _ x.1,cell_duality _ q.1.1]
    let L := Complex.reCLM; change _*(∑ i:Site n, L (cell x.1 i*(cell q.1.1 i)⁻¹))=_; rw [← map_sum,ht]; split
    next he => have hi : (x,j)=q := Prod.ext (Prod.ext he h.1) h.2; rw [hi,]; simp only [bolt,Pi.single_eq_same]; have hm : m=(n.val:ℝ)^4 := by unfold m; rw [site_card]; push_cast; rfl
               rw [hm]; change ((n.val:ℝ)^4)⁻¹*(↑(n.val)^4:ℂ).re=1; rw [← Complex.ofReal_natCast,← Complex.ofReal_pow,Complex.ofReal_re,inv_mul_cancel₀]; positivity [n.pos]
    next he => simp [bolt,show (x,j)≠q from fun e=>he (congr_arg (fun z:ticket=>z.1.1) e)]
  simp [h,bolt,show (x,j)≠q from fun p=> h ⟨congr_arg (fun z:ticket=>z.1.2) p,congr_arg Prod.snd p⟩]

-- inspect ||χ|| per physical component, not inappropriate Complex product norm
lemma component (x : Dir G n) (i : ticket (n:=n) (G:=G)) : |x i.1 i.2| ≤ ‖x‖ :=
  le_trans (by simpa only [EuclideanSpace.basisFun_inner,OrthonormalBasis.norm_eq_one,one_mul] using
    abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i.2) (x i.1)) (norm_le_pi_norm x _)

-- on any true quadratic comparison. Retain p in β-free profile.
lemma confer (Y : Dir G n →L[ℝ] Dir G n→L[ℝ] ℝ) {b c : ℝ} (he : ∀ p q : Site n, ∀ σ τ, unitSize σ → unitSize τ →
    |Y (wave p σ) (wave q τ)| ≤ c) (x y : Dir G n) (hx : ‖x‖ ≤ b) (hy : ‖y‖≤b) :
    |Y x y| ≤ (Fintype.card (ticket (n:=n) (G:=G)):ℝ)^2*b^2*c := by
  let S := Fintype.card (Site n)
  have hS : 0<(S:ℝ) := by unfold S; positivity
  have hb := (norm_nonneg _).trans hx
  let I (j : ticket (n:=n) (G:=G)) := tint G _ (bolt j)
  have ha (i j : ticket) : |Y (I i) (I j)| ≤ c := by
    unfold I; rw [← cash,← cash]; simp only [map_smul,map_sum,_root_.sum_apply, _root_.smul_apply]
    simp only [smul_eq_mul, abs_mul]
    suffices hh : |∑ p:Site n,∑ r:Site n,Y (wave p (coin i p)) (wave r (coin j r))| ≤ (S:ℝ)*((S:ℝ)*c) by
      rw [← Finset.mul_sum] -- perhaps outer than abs_mul
      rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hS.le)]
      rw [Finset.sum_comm]; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (show 0 ≤ (S:ℝ)⁻¹ by positivity)) (show 0≤ (S:ℝ)⁻¹ by positivity)).trans_eq ?_; field_simp
    apply ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs ..)).trans
    apply (Finset.sum_le_sum fun _ _=> Finset.sum_le_sum fun _ _=>he _ _ _ _ (orig _ _) (orig _ _)).trans_eq
    simp [S]
  let J := tint G (Body 1 n)
  let v (i : ticket (G:=G) (n:=n)) := x i.1 i.2
  have ht (z : Dir G n) : z= ∑ i:ticket,z i.1 i.2 • I i := by
    have hz := congr_arg J (combine (J.symm z)); simp only [map_sum,map_smul,J.apply_symm_apply] at hz
    exact hz.symm
  conv_lhs => rw [ht x, ht y]
  simp only [map_sum,map_smul,_root_.sum_apply, _root_.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun _ _=> Finset.abs_sum_le_sum_abs ..)).trans
  apply (Finset.sum_le_sum fun j (_:j∈(Finset.univ:Finset (ticket (G:=G) (n:=n))))=>Finset.sum_le_sum fun i _=>
    (show |y j.1 j.2 * (x i.1 i.2 * Y (I i) (I j))| ≤ b*(b*c) from by
      simp only [abs_mul]; exact mul_le_mul ((component _ j).trans hy) (mul_le_mul ((component _ _).trans hx) (ha _ _) (abs_nonneg _) hb) (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hb)).trans_eq ?_
  simp; ring

section tangent
variable {c f : Side} {S : StepData c f} {F : Forest S.ratio}
variable {R T : PathData G} {p : Clip} {η C Λ : ℝ} {u : Push.In G c→AxisChart G F}

-- physical hessian kernel for the loop insertion itself


open Work.F03






end tangent
end YM.Further.PhysicalPeriodLimitF933.Glowing
