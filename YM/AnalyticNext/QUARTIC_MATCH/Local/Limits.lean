import YM.AnalyticNext.QUARTIC_MATCH.Local.Direction
import YM.AnalyticNext.QUARTIC_MATCH.Local.Stipple
import YM.Push.PRICE_COMPILER.Post

/-!
# Distance on output kernels

Extensive estimates. Not requiring external length below the period. Feed literal
entries into unfolding proof, retaining exponent at true pre-L scale.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Local
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08 Pre.Centered
open Joint Estimate Estimate.Purse Estimate.Logfee Estimate.Depot BoxChain Premium Evoke 
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
namespace Wages
variable {G : Gauge} {n l c f : Side} (S : StepData c f)
open Green (wt)
variable {ι : Type} [Fintype ι] [DecidableEq ι] {u : ℝ} {k m : ℕ}

def boom (v : ℝ) := 4*v
def rate (v : ℝ) := v/2
lemma booms (hp : 0 < u) : 0<boom u := mul_pos (by norm_num) hp
lemma after (hp : 0<u) : 0 < rate u := half_pos hp
lemma wt_le {η θ : ℝ} (he : θ ≤ η) (x y : Site n) : wt θ x y ≤ wt η x y := Real.exp_monotone (mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ (separation x y:ℝ)))
lemma wt_ge {η : ℝ} (he : 0 ≤ η) (x y : Site n) : 1 ≤ wt η x y := Real.one_le_exp (by positivity)

def span (v : ℝ) (z : Site l) (x : ι → Site l) := ∏ i, wt v z (x i)
omit [DecidableEq ι] in
lemma span_pos (v : ℝ) (z : Site l) (x : ι → Site l) : 0 < span v z x := Finset.prod_pos fun _ _ => Green.wt_pos ..
lemma pass_pair {v : ℝ} (he : 0 ≤ v) (z : Site l) (x : ι → Site l) (i j : ι) : wt v (x i) (x j) ≤ span v z x := by
  by_cases h : i=j
  · rw [h,wt,separation_self]; simp only [Nat.cast_zero,mul_zero,Real.exp_zero]; exact Finset.one_le_prod fun _ _ => wt_ge he z _
  apply (Green.wt_triangle he (x i) z (x j)).trans; rw [Green.wt_symm v (x i) z]
  let b k := wt v z (x k)
  have hh : ∏ k∈({i,j}:Finset ι),b k=b i*b j := by simp [h]
  rw [← show ∏ k ∈ ({i,j}:Finset ι), b k = _ from hh]; exact Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) (fun i _ => (Green.wt_pos ..).le) fun k _ _ => wt_ge he ..

def account (l : Side) (w : Option ι) (x : ι→Site n) (u : ι→ℝ) (C : ι→ℝ) (h : ∀ i,0 ≤ C i) : Purse ι (Site n) :=
    ⟨w,(l.val:ℝ)^2,sq_nonneg _,C,h,fun i a => wt (u i/l.val) a (x i),fun _ _ => Green.wt_pos ..⟩
omit [Fintype ι] [DecidableEq ι] in
lemma travels (w : Option ι) (x : ι→Site n) (u : ι→ℝ) (C : ι→ℝ) (h : ∀ i,0 ≤ C i) (l : Side)
    {η : ℝ} (ht : ∀ i,|u i| ≤ η) : tollRate (account l w x u C h) l η := fun i _ _ => scaled l (ht i) _ _ _

lemma journey (hp : 0 < u) (P : Purse (Fin k) (Site f)) (i : Fin k) (x : Fin k→Site f) (l : Side) (hk : k ≤ 4)
    (he : ∀ i y, P.toll i y=wt (boom u/l.val) y (x i)) :
    Stamp P Finset.univ l u (span (rate u/l.val) (x i) x) (x i) := by
  intro y
  let b := rate u/l.val; let h := boom u/l.val; let r := u/l.val
  have hb : 0 ≤ b := div_nonneg (after hp).le (by positivity)
  have hr : 0 < r := div_pos hp (by positivity)
  let V j := wt b y (x j); let Y j := wt b (x i) (x j)
  have hu j : Y j ≤ V i * V j := (Green.wt_triangle hb _ y _).trans_eq (by rw [Green.wt_symm b (x i) y])
  have hx : span b (x i) x ≤ (V i)^k*∏ j,V j := by
    refine (Finset.prod_le_prod (fun _ _ => (Green.wt_pos ..).le) (fun j _ => hu j)).trans_eq ?_; simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  let Z j := wt h y (x j)
  have hK : (V i)^k*wt r y (x i)*V i ≤ Z i := by
    unfold V Z wt; rw [← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
    rw [show r=b+b from by unfold b r rate; ring,show h=b*8 by unfold h b boom rate; ring]
    have hp := mul_le_mul_of_nonneg_right (show (k:ℝ) ≤ 4 by exact_mod_cast hk) (show 0 ≤ b*(separation y (x i):ℝ) by positivity)
    linarith [show 0 ≤ b*(separation y (x i):ℝ) by positivity]
  unfold price; simp_rw [he];
  change span b (x i) x * wt r y (x i) ≤ ∏ j,Z j
  apply (mul_le_mul_of_nonneg_right hx (Green.wt_pos ..).le).trans
  rw [← Finset.mul_prod_erase Finset.univ V (Finset.mem_univ i), ← Finset.mul_prod_erase Finset.univ Z (Finset.mem_univ i)]
  rw [show (V i)^k*(V i*_)*_=(V i)^k*wt r y (x i)*V i*(∏ j∈Finset.univ.erase i, V j) from by ring]
  have HH : b ≤ h := by unfold h b rate boom; gcongr; linarith
  exact mul_le_mul hK (Finset.prod_le_prod (fun _ _ => (Green.wt_pos ..).le) (fun j _ => wt_le HH ..))
    (Finset.prod_nonneg fun _ _ => (Green.wt_pos ..).le) (Green.wt_pos ..).le

lemma embedded (l : Side) (hp : 0<u) (x y z : Site n) :
    wt (rate u/l.val) x y * wt (u/l.val) z x ≤ wt (boom u/l.val) z x * wt (boom u/l.val) z y * wt (-u/l.val) z x := by
  let r := u / l.val; have hr : 0 < r := div_pos hp (by positivity)
  rw [show rate u/l.val=r/2 from by unfold r rate; ring,show boom u/l.val=4*r from by unfold r boom; ring,neg_div];
  change wt (r/2) x y * wt r z x ≤ wt (4*r) z x* _ * wt (-r) z x
  unfold wt; rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
  have hh : (separation x y:ℝ) ≤ (separation z x:ℝ)+(separation z y:ℝ) := by rw [separation_comm z x]; exact_mod_cast separation_triangle x z y
  have hx := mul_le_mul_of_nonneg_left hh hr.le
  nlinarith only [hx, mul_nonneg hr.le (by positivity : 0 ≤ (separation z x:ℝ)), mul_nonneg hr.le (by positivity : 0 ≤ (separation z y:ℝ))]

lemma severs (l : Side) (hp : 0<u) (x y t z : Site n) : wt (rate u/l.val) x y * wt (rate u/l.val) x t * wt (u/l.val) z y ≤
    wt (boom u/l.val) z y * wt (boom u/l.val) z t * wt (u/l.val) z x := by
  let r := u/l.val; have hr : 0<r := div_pos hp (by positivity)
  unfold wt; rw [← Real.exp_add,← Real.exp_add,← Real.exp_add,← Real.exp_add]
  rw [show rate u/l.val=r/2 from by unfold r rate; ring,show boom u/l.val=4*r from by unfold r boom; ring]
  apply Real.exp_monotone
  have hh (y : Site n) : (separation x y:ℝ) ≤ (separation z x:ℝ)+(separation z y:ℝ) := by rw [separation_comm z x]; exact_mod_cast separation_triangle x z y
  have hx := mul_le_mul_of_nonneg_left (hh y) hr.le; have hy := mul_le_mul_of_nonneg_left (hh t) hr.le
  change _ + r*(separation z y:ℝ) ≤ _ + r*(separation z x:ℝ)
  linarith only [hx,hy, mul_nonneg hr.le (by positivity : 0 ≤ (separation z y:ℝ)), mul_nonneg hr.le (by positivity : 0 ≤ (separation z t:ℝ))]

omit [DecidableEq ι] in
lemma span_coarse (u : ℝ) (x : Site c) (y : ι→Site c) :
    span (u/S.ratio.count.val) (S.ratio.embed x) (S.ratio.embed ∘ y)=span u x y :=
    Finset.prod_congr rfl fun _i _ => accrual S _ _ _
end Wages
end YM.AnalyticNext.QuarticMatch.Local
