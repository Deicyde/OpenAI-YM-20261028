import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Fuels
import YM.Next.FREE_KERNELS.Signal
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B06
import YM.Work.F08.Rows

/-!
# Absolute counts of the kernels in finite-volume distance

Optional release: retain the *stronger* on-cover `Width` costs through
`Rack`, here project abs values onto torus for concrete matrix applications.
Kernel evaluation, exponent and indices in same Scale. Cross distances to
coarse bond uses distance to the embedded site divided by the factor L.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid
open scoped Topology BigOperators ComplexConjugate
variable {c f L : Side} {m n : Type*}

lemma below_wrap (L : Side) (x : Cover) (i : Axis) : (lift (wrap L x) i).natAbs ≤ (x i).natAbs := by
  let y := lift (wrap L x)
  have he := lift_centers (wrap L x) i
  have ht : y i=(lift (wrap L x)) i := rfl
  obtain ⟨z,hz⟩ := cover_of_eq y x (wrap_lift _)
  have hh := congr_fun hz i
  simp [nsmul_eq_mul] at hh
  by_cases h : z i=0
  · rw [← ht]; rw [h, mul_zero,add_zero] at hh; rw [hh]
  have hL : (0:ℤ)<L.val := by exact_mod_cast L.property
  change -(↑L.val:ℤ)<2*y i ∧ 2*y i≤L.val at he
  rw [← ht]
  rcases lt_or_gt_of_ne h with h|h
  · have hq : z i ≤ -1 := by omega
    have hb : (L.val:ℤ)*z i ≤ -L.val := by nlinarith
    omega
  have hh' : 1 ≤ z i := by omega
  have hb : (L.val:ℤ) ≤ L.val*(z i) := by nlinarith
  omega

lemma within_size (i : Cover) (L : Side) : pdist (wrap L i) ≤ size i := by
  unfold pdist; apply Finset.sup_le; intro a _
  exact (below_wrap L i a).trans (Finset.single_le_sum (f:=fun a => (i a).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
lemma row_sprawl [Fintype n] {R : Row m n} {η C : ℝ} (he : 0≤η) (h : R.strip η C) (L : Side) (i : Co L m) :
    ∑ j : Co L n, Real.exp (η*separation i.1 j.1) * ‖R.acts L i j‖ ≤ Fintype.card n * C := by
  let v (y : Site L) := Real.exp (η*separation i.1 y)
  have hh (a : n) : (∑ y : Site L,v y * ‖R.acts L i (y,a)‖) ≤ C := by
    let f := R i.2 a
    have hS := ((h i.2 a).unweighted he).2.1
    have hf (x : Cover) : v (i.1+wrap L x)*‖f x‖ ≤ Real.exp (η*size x)*‖f x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); unfold v; apply Real.exp_le_exp.mpr; apply mul_le_mul_of_nonneg_left _ he
      rw [separation_comm, separation, add_sub_cancel_left]; exact_mod_cast within_size x L
    let H (y : Site L) (x : Cover) := if y=i.1+wrap L x then R i.2 a x else 0
    have hb (y : Site L) : Summable fun x => ‖H y x‖ := by
      apply Summable.norm; exact Work.F08.summable_sift hS.of_norm _ _
    have hk : RG.SumBudget (fun x => v (i.1+wrap L x)*‖f x‖) C := Work.F08.budget_minor (h i.2 a) (fun _ => by unfold v; positivity) hf
    calc
      _ ≤ ∑ y, v y * ∑' x, ‖H y x‖ := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hb y)) (Real.exp_pos _).le
      _ = ∑' x, ∑ y, v y * ‖H y x‖ := by simp_rw [← tsum_mul_left]; rw [Summable.tsum_finsetSum]; exact fun y _ => (hb y).mul_left _
      _ ≤ C := (show (∑' x, ∑ y, v y * ‖H y x‖)=(∑' x, v (i.1+wrap L x)*‖f x‖) from by
        refine tsum_congr fun x => ?_; unfold H; rw [Finset.sum_eq_single (i.1+wrap L x),if_pos rfl]; intro b _ h; rw [if_neg h,norm_zero,mul_zero]; simp).trans_le hk.2.2
  rw [Fintype.sum_prod_type,Finset.sum_comm]; exact (Finset.sum_le_sum (g:=fun _ => C) (fun a _ => hh a)).trans_eq (by simp)
lemma col_sprawl [Fintype m] {R : Row m n} {η C : ℝ} (he : 0≤η) (h : R.strip η C) (L : Side) (i : Co L n) :
    ∑ j : Co L m, Real.exp (η*separation i.1 j.1) * ‖R.acts L j i‖ ≤ Fintype.card m * C := by
  have hh := row_sprawl he (strip_trans h) L i; rwa [acts_trans] at hh

lemma scaled_root (g : Ratio c f) (x y : Site c) : separation (g.embed x) (g.embed y) ≤ g.count.val * separation x y := by
  unfold separation
  rw [← g.root_embed, ← g.root_embed, ← map_sub, g.root_embed]
  unfold pdist; apply Finset.sup_le; intro i _; rw [g.lift_embed, Pi.smul_apply,nsmul_eq_mul]
  simp only [Int.natAbs_mul,Int.natAbs_natCast]; exact Nat.mul_le_mul_left g.count.val (component_le ..)
lemma scaled_dist (g : Ratio c f) (x : Site f) (y : Site c) :
    (separation x (g.embed y):ℝ)/(g.count.val:ℝ) ≤ 1+separation (g.parent x) y := by
  have hL := side_pos g.count
  rw [div_le_iff₀ hL]
  have hb : separation x (g.embed (g.parent x)) ≤ g.count.val := by
    unfold separation
    rw [show x-g.embed (g.parent x)=wrap f (lift (g.residue x)) by
      conv_lhs => lhs; rw [← g.unpack_at x]
      abel]
    unfold pdist; apply Finset.sup_le; intro i _
    apply (below_wrap f _ i).trans; have hh := lift_centers (g.residue x) i; omega
  have hh := (separation_triangle x (g.embed (g.parent x)) (g.embed y)).trans (Nat.add_le_add hb (scaled_root g (g.parent x) y))
  exact (by exact_mod_cast ((by rw [add_mul,one_mul,mul_comm]; exact hh) : separation x (g.embed y) ≤ (1+ separation (g.parent x) y)*g.count.val))

def crossW (g : Ratio c f) (η : ℝ) (x : Site f) (y : Site c) := Real.exp (η*((separation x (g.embed y):ℝ)/(g.count.val:ℝ)))
lemma toll_cross (g : Ratio c f) {η : ℝ} (he : 0 ≤ η) (x : Site f) (y : Site c) :
    crossW g η x y ≤ Real.exp η*Real.exp (η*separation (g.parent x) y) := by
  unfold crossW; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; have hm := scaled_dist g x y; nlinarith

lemma cross_sprawl [Fintype n] (g : Ratio c f) {R : Cross g.count m n} {η C : ℝ} (he : 0≤η) (h : R.strip η C) (x : Co f m) :
    ∑ y : Co c n,crossW g η x.1 y.1 * ‖installed g R x y‖ ≤ Real.exp η*(Fintype.card n*C) := by
  have hh := row_sprawl he h c (splitCo g m x)
  apply le_trans _ (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le); rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  unfold installed; rw [Matrix.submatrix_apply,id_eq, ← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [split_co]; exact toll_cross g he _ _

lemma crossColumns [Fintype m] (g : Ratio c f) {R : Cross g.count m n} {η C : ℝ} (he : 0≤η) (h : R.strip η C) (y : Co c n) :
    ∑ x : Co f m,crossW g η x.1 y.1 * ‖installed g R x y‖ ≤ Real.exp η*(g.count.val^4*(Fintype.card m*C)) := by
  have hh := col_sprawl he h c y
  rw [show Real.exp η*(g.count.val^4*(Fintype.card m*C))=Real.exp η*(Fintype.card (Co g.count m)*C) by rw [← mul_assoc ((g.count.val:ℝ)^4), show Fintype.card (Co g.count m)=g.count.val^4 * Fintype.card m by unfold Co; rw [Fintype.card_prod,site_card]]; push_cast; rfl]
  apply le_trans _ (mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le); rw [Finset.mul_sum]
  let s := splitCo g m
  rw [← Equiv.sum_comp s]; apply Finset.sum_le_sum; intro x _
  unfold installed; rw [Matrix.submatrix_apply,id_eq]
  rw [← mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); unfold s; rw [split_co, separation_comm]; exact toll_cross g he x.1 y.1
end YM.Next.Free
