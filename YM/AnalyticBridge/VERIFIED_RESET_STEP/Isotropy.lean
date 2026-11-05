import YM.AnalyticBridge.VERIFIED_RESET_STEP.Projection
import YM.Push.STRESS_FLUX.Orbits

/-!
# Same-volume, same-label kinetic coefficient

Sum the actual (chargeable) bilinear projections at one anchor. Orbits of
label addresses yield exact symmetries BEFORE dropping indicators. `identity`
is for replacing on a single common clover indicator per site.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical
variable {G : Gauge} {n : Side} {p : BudgetPoint}

namespace Averaging
variable {A : Activities G n} {c : ℝ}
structure Projects (A : Activities G n) (p : BudgetPoint) (c : ℝ) : Prop where
  regular (i : ℕ) : p.Regular (A.reg i).support (A.E i)
  bound : A.EBound p c

lemma Projects.series (hG : G.Simple) (h : Projects A p c) (a b : PlaqAxes) : Summable fun i => projection (A.reg i) (A.E i) a b := by
  obtain ⟨k,hk,h⟩ := A.E_total h.bound
  have hp := sq_pos_of_pos p.threshold_pos
  refine Summable.of_norm_bounded ((hk.mul_left 3).div_const (p.threshold^2)) (fun i => (le_div_iff₀ hp).mpr ?_)
  rw [mul_comm]; exact projection_bound _ hG (Projects.regular ‹Projects A p c› i) (h i) _ _

def censusAt (A : Activities G n) (o : Site n) (a b : PlaqAxes) (i : ℕ) :=
    if (A.reg i).site = o then projection (A.reg i) (A.E i) a b else 0
lemma Projects.seriesAt (hG : G.Simple) (h : Projects A p c) (a b : PlaqAxes) (o : Site n) : Summable (censusAt A o a b) :=
  Summable.of_norm_bounded (h.series hG a b).norm fun i => by unfold censusAt; split <;> simp

def total (A : Activities G n) (o : Site n) (a b : PlaqAxes) := ∑' i, censusAt A o a b i
lemma quad_total (hG : G.Simple) (h : Projects A p c) (o : Site n) (w z : Flux G) :
    quad (total A o) w z = ∑' i, if (A.reg i).site = o then quad (projection (A.reg i) (A.E i)) w z else 0 := by
  let f a b i := censusAt A o a b i * inner ℝ (w a) (z b)
  have hi (i) : ∑ a, ∑ b, f a b i = if (A.reg i).site = o then quad (projection (A.reg i) (A.E i)) w z else 0 := by
    by_cases ho : (A.reg i).site=o <;> simp [ho, f, quad,censusAt]
  have hf a b : Summable (f a b) := (h.seriesAt hG a b o).mul_right _
  rw [← funext hi,Summable.tsum_finsetSum fun a _ => summable_sum fun b _ => hf a b]
  simp_rw [Summable.tsum_finsetSum (fun _ _ => hf _ _), f, tsum_mul_right, quad,total]

lemma total_turn (hG : G.Simple) (h : Projects A p c) (hn : 4 ≤ n.val) (o b : Site n) (s : Signed) (M : A.Moves s b) (w z : Flux G) :
    quad (total A (affine s b o)) w z = quad (total A o) (reframe w s) (reframe z s) := by
  rw [quad_total hG h, quad_total hG h, ← M.ep.tsum_eq (fun i : ℕ => if (A.reg i).site = affine s b o then quad (projection (A.reg i) (A.E i)) w z else 0)]
  apply tsum_congr; intro i
  rw [M.reg_site]; simp only [affine,add_left_inj,s.act_injective.eq_iff]
  rw [quad_moves s b hn (M.reg_support i) (M.reg_site i) hG (h.regular i) (h.regular _) (funext (M.valuesE i))]

def ray (b : PlaqAxes) : Flux G := fun a => if a=b then spike G else 0
private lemma reframe_ray (p q : PlaqAxes) (s : Signed) (hs : s.perm p.val.1 = q.val.1) (ht : s.perm p.val.2 = q.val.2) :
    reframe (ray q (G:=G)) s = (sign s p.val.1 * sign s p.val.2) • ray p := by
  ext1 j
  simp only [reframe,ray,orderedDir,Pi.smul_apply]
  by_cases hp : j=p
  · subst j; simp [hs,ht,q.property,not_lt_of_gt q.property]
  have h₁ : (s.perm j.val.1, s.perm j.val.2) ≠ q.val := fun h => hp (by
    have := s.perm.injective; apply Subtype.ext; apply Prod.ext <;> apply this <;> grind)
  have h₂ : (s.perm j.val.2, s.perm j.val.1) ≠ q.val := fun h => by
    have ha : j.val.1 = p.val.2 := s.perm.injective (by grind)
    have hb : j.val.2 = p.val.1 := s.perm.injective (by grind)
    exact lt_asymm p.property (show p.val.2 < p.val.1 by rw [← ha,← hb]; exact j.property)
  simp only [Subtype.ext_iff]; split_ifs <;> simp_all
private lemma tests_quad (q : PlaqAxes → PlaqAxes → ℝ) (hG : G.Simple) (a b : PlaqAxes) (u v : ℝ) :
    quad q (u • (ray a (G:=G))) (v • ray b) = q a b * (u*v) := by
  rw [quad, Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]; swap
  · intro x _ hx; simp [ray,hx]
  rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ _)]; swap
  · intro y _ hy; simp [ray,hy]
  simp [ray,real_inner_smul_left,real_inner_smul_right,spike_norm hG,mul_comm v u]

def axes01 : PlaqAxes := ⟨(0,1),by decide⟩
def delta (A : Activities G n) := total A 0 axes01 axes01

lemma isotropic (hG : G.Simple) (h : Projects A p c) (hn : 4 ≤ n.val) (o : Site n) (hm : ∀ s b, Nonempty (A.Moves s b)) (a b : PlaqAxes) :
    total A o a b = if a=b then delta A else 0 := by
  have he (x y : Site n) (d e i j : PlaqAxes) (s : Signed) (hd : s.perm i.val.1=d.val.1 ∧ s.perm i.val.2=d.val.2)
      (he : s.perm j.val.1=e.val.1 ∧ s.perm j.val.2=e.val.2) :
      total A y d e = total A x i j * ((sign s i.val.1 * sign s i.val.2) * (sign s j.val.1 * sign s j.val.2)) := by
    obtain ⟨M⟩ := hm s (y - s.act x)
    have h := total_turn hG h hn x _ s M (ray d) (ray e)
    rw [show affine s (y-s.act x) x = y by simp [affine],reframe_ray _ _ s hd.1 hd.2,reframe_ray _ _ s he.1 he.2,tests_quad _ hG] at h
    simpa [h] using (tests_quad (total A y) hG d e 1 1).symm
  split
  next h => subst b; obtain ⟨t,ha,hb⟩ := extend_two a.val.1 a.val.2 a.property.ne
            simpa only [sign,Bool.false_eq_true,if_false,mul_one, delta] using he 0 o a a axes01 axes01 ⟨t,fun _ => false⟩ ⟨ha,hb⟩ ⟨ha,hb⟩
  next hn =>
    have H (x : Axis) := he o o a b a b (Signed.mirror x) ⟨rfl,rfl⟩ ⟨rfl,rfl⟩
    simp only [sign,Signed.mirror,decide_eq_true_eq] at H
    have ha := H a.val.1; have hb := H a.val.2
    have H1 := a.property; have H2 := b.property
    have he : a.val.1 ≠ b.val.1 ∨ a.val.2 ≠ b.val.2 := by grind
    simp only [↓reduceIte,if_neg H1.ne,if_neg (Ne.symm H1.ne),one_mul,mul_one] at ha hb
    rcases (show (a.val.1 ≠ b.val.1 ∧ a.val.1 ≠ b.val.2) ∨ (a.val.2 ≠ b.val.1 ∧ a.val.2 ≠ b.val.2) by grind) with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
    · simp only [if_neg h₁,if_neg h₂,mul_one,mul_neg] at ha; linarith
    simp only [if_neg h₁,if_neg h₂,mul_one,mul_neg] at hb; linarith

lemma identity (hG : G.Simple) (h : Projects A p c) (hn : 4 ≤ n.val) (o : Site n) (hm : ∀ s b, Nonempty (A.Moves s b)) (w : Flux G) :
    (∑' i, if (A.reg i).site = o then quad (projection (A.reg i) (A.E i)) w w else 0) = delta A * ∑ b, ‖w b‖^2 := by
  rw [← quad_total hG h,quad]; simp [isotropic hG h hn o hm,ite_mul,Finset.mul_sum]
lemma delta_bound (hG : G.Simple) (h : Projects A p c) : p.threshold^2 * |delta A| ≤ c := by
  obtain ⟨k,hk,ho⟩ := h.bound
  let f i := p.threshold^2 * censusAt A 0 axes01 axes01 i
  have hf := ((h.seriesAt hG axes01 axes01 0).mul_left (p.threshold^2)).norm
  unfold delta total; rw [← abs_of_nonneg (sq_nonneg p.threshold),← abs_mul,← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm (f:=f) hf).trans ((hf.tsum_le_tsum (fun i => ?_) (ho 0).2.1).trans (ho 0).2.2)
  change ‖f i‖ ≤ _; unfold f censusAt; split_ifs with hi
  · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg p.threshold)]
    exact (projection_diag _ hG (h.regular i) (hk i) _).trans (p.loMass _ _ (hk i).1)
  simp
end Averaging
end YM.AnalyticBridge.VerifiedReset
