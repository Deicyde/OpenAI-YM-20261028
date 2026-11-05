import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Widow
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Height.Span
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration   
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ} {F : Tree.Forest S.ratio}
    {χ : Chi} {H : Cash W s μ L Q o α T R}
section second
variable (H)
def acme (z : H.fragrances) := ∑ i,pins S (z.2 i).val

def degree (z : H.fragrances) := acme H z + breadth H z
def depth (z : H.fragrances) := ∑ i,H.shapeW (z.2 i).val

def beacon (z : H.fragrances) := grow G L s^degree H z * Real.exp (Q.mark L μ s*overlap H z)* Real.exp (Q.ε*depth H z)
def tired (z : H.fragrances) := 3≤degree H z ∨ 1≤overlap H z ∨ Pressure.Stores.till s ≤ depth H z
variable {H}
variable (N : Captain H j C' d v Y A b r B q k χ) (hd : 1 ≤ grow G L s) (hh' : Heavy N.conduit)
lemma wield (z : H.fragrances) : clusters H.seam (fun u:H.ThinP=> stronger H u.val*N.stone u) z.2 = beacon H z*N.design z := by
  unfold Captain.design clusters stronger gust
  unfold beacon degree acme breadth depth overlap
  simp only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Nat.cast_sum,pow_add,mul_sum,Real.exp_sum]
  ring

variable (n : ℕ) (ht : Armada Q L μ a s i B j k)
include N ht hd hh'
lemma completed (hc : grow G L s^3 ≤ Real.exp (Q.mark L μ s)) (hcc : grow G L s^3≤Real.exp (Q.ε*Pressure.Stores.till s))
    (hs : degreePrice (radiusB s) (grow G L s*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2) (hp : degreePrice (radiusB s) (grow G L s*salary Q L μ B s j k) i ≤ 1/2) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=>if tired H z then N.markΦ z n else 0) a
        ((grow G L s^3)⁻¹*collars G i s j n*(grow G L s*salary Q L μ B s j k*(1-1/2)⁻¹)) := by
  intro x
  let D:=grow G L s
  have hD:0<D:=zero_lt_one.trans_le hd
  let m (z:H.fragrances):= beacon H z
  have hy:= log_hit_tail _ _ _ H.testS (stable N hd hh' i a ht.delta ht.little ht.earned hs hp) (add_nonneg ht.gain ht.delta.le) 0 x
  simp only [pow_zero,mul_one] at hy
  let v:= collars G i s j n
  have he:0 ≤ shiftG s:=by unfold shiftG; positivity
  have hv:0 ≤ v:=by unfold v collars Reserves.polyPrice; have he := ht.delta; positivity
  have hz z : 0 ≤ N.markΦ z n:= mul_nonneg (pow_nonneg (by positivity) _) (N.pvc _)
  have hh:= budget_scale (show 0 ≤  (D^3)⁻¹*v by positivity) hy
  refine budget_mono hh (fun z=> ?_) fun z=> ?_
  · dsimp only; split_ifs
    next => exact mul_nonneg (hz z) (Real.exp_pos _).le
    next => simp
    exact le_rfl
  dsimp only; split
  next hx=>
    by_cases he' : tired H z
    · let K:= reachability (H:=H) z
      rw [if_pos he', if_pos (show 0 ≤ z.fst ∧ x∈unionOf H.smallAt z.snd from ⟨Nat.zero_le _,hx⟩),wield N]
      let c:ℝ:=coverNumber (radiusB s) K; have hg:0 ≤ c:= Nat.cast_nonneg _
      have hPos:1 ≤ Real.exp (Q.ε*depth H z) := Real.one_le_exp (mul_nonneg Q.usable.le
        (sum_nonneg fun i _=> H.positive_volume _))
      have ht':0≤Q.mark L μ s:= H.laws.acquired.marked
      have hM:1≤Real.exp (Q.mark L μ s*overlap H z):=Real.one_le_exp (mul_nonneg ht' (Nat.cast_nonneg _))
      have hu : D^3 ≤ m z := by
        rcases he' with h|h|h
        · exact (pow_le_pow_right₀ hd h).trans ((le_mul_of_one_le_right (by positivity) hM).trans
          (le_mul_of_one_le_right (by positivity) hPos))
        · exact hc.trans ((Real.exp_monotone (le_mul_of_one_le_right ht' (show (1:ℝ)≤ overlap H z by exact_mod_cast h))).trans ((le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ hd)).trans (le_mul_of_one_le_right (by positivity) hPos)))
        exact hcc.trans ((Real.exp_monotone (mul_le_mul_of_nonneg_left h Q.usable.le)).trans
          (le_mul_of_one_le_left (Real.exp_pos _).le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd) hM)))
      change (shiftG s*(1+c))^(n*j)*N.design z *Real.exp (a*c) ≤ ((D^3)⁻¹*v)*(m z*N.design z*Real.exp ((a+i)*c))
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu (N.pvc _)) (Real.exp_pos _).le) (by positivity))
      rw [mul_pow]; unfold v collars
      rw [add_mul a i c, Real.exp_add]
      apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (polynomial_cost ht.delta hg _) (pow_nonneg he _)) (N.pvc z)) (Real.exp_pos _).le)
      apply le_of_eq; unfold Reserves.polyPrice; field_simp
    rw [if_neg he',zero_mul]; exact hh.1 z
  exact hh.1 z
end second
end YM.PhysicalNext.Repeat.Height
