import YM.RG08.Wallet.Stays
import YM.RG08.Ballast.Jets

/-! # Local Taylor jets in aggregates

Record per-translation bundle as any analytic germ on all seats,
including unused slots. Cost is post-block, any pre-chosen width. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths
open scoped Topology ContDiff Classical
variable {α β ι : Type} {w A : ℝ} {r : ℕ} {m : Side}
variable [Fintype ι] [DecidableEq ι] [Fintype α]

-- I=seats finite. unused reads coefficient=0.
def seats (s : ι → Option (Cover × α)) (x : Site m) : PAC α m →L[ℝ] Corn ι := ContinuousLinearMap.pi fun i=>
    (s i).elim 0 (fun v=> ContinuousLinearMap.proj (x+wrap m v.1,v.2))

def quavers (y : Cover × α) (s : ι→Option (Cover × α)) (b : Fin r → ι) : Beads α r := fun j=> (s (b j)).getD y
private def icicle (s : ι→Option (Cover × α)) (F : Corn ι→ℝ) (b : Fin r→ι) :=
    (∏ i, ((s (b i)).elim (0:ℝ) (fun _=>1))) * Tensor.coeff F r 0 (fun i=> Pi.single (b i) 1)
def breath (y : Cover × α) (s : ι→Option (Cover × α)) (F : Corn ι→ℝ) (r : ℕ) :=
    score (pool (icicle (r:=r) s F) (quavers y s))
omit [Fintype α] in
theorem breath_quote (F : Corn ι→ℝ) (s : ι→ Option (Cover × α)) (a : Cover × α) (w : ℝ) (hp : 0≤w) :
    ∃ A : ℝ,0≤A ∧ Glow (breath a s F r) w A := by
  let p := quavers (r:=r) a s; let f := icicle (r:=r) s F; let v := ((↑(r+1:ℕ)):ℝ)*w
  let C := ∑ i,ling v (p i)*‖f i‖
  have h : Charge (fun i=>ling v (p i)) f C := budget_finite (fun i=> mul_nonneg (ling_pos _ _).le (norm_nonneg _)) le_rfl
  exact ⟨_,h.nonneg,score_price (Charge.poolage p (ling_one (by positivity)) h) hp⟩
omit [Fintype α] in
private lemma pool_summable (a : Cover × α) (s : ι→Option (Cover × α)) (F : Corn ι→ℝ) : Summable (pool (icicle (r:=r) s F) (quavers a s)) :=
    ((Summable.of_finite (f:=icicle (r:=r) s F)).hasSum.tsum_fiberwise _).summable
lemma breath_tune (F : Corn ι→ℝ) (s : ι→ Option (Cover × α)) a : Tunable (breath a s F r) := score_tunable (pool_summable _ _ _)
omit [DecidableEq ι] in
def atmosphere (s : ι→Option (Cover × α)) (F : Corn ι→ℝ) (m : Side) :=
    fun x : PAC α m=> ∑ z,(F ∘ seats s z) x
private lemma seat_norm (T : Tensor.T (Corn ι) ℝ r) (v : Fin r→Corn ι) : T v =
    ∑ i : Fin r→ι,(∏ k,v k (i k))*T (fun k=> Pi.single (i k) 1) := by
  have hx := expand_coord T.toMultilinearMap v; rw [recording_apply] at hx; exact hx.symm

theorem breath_proofs (F : Corn ι→ℝ) (e : AnalyticAt ℝ F 0) (s : ι→ Option (Cover × α)) (a) (m r) :
    AnalyticAt ℝ (atmosphere s F m) 0 ∧ recital (breath a s F r) m=Tensor.coeff (atmosphere s F m) r 0 := by
  have he i : ContDiffAt ℝ ω (F ∘ seats s (m:=m) i) 0 := (show ContDiffAt ℝ ω F (seats s (m:=m) i 0) from by rw [map_zero]; exact e.contDiffAt).comp _ (seats s _).contDiff.contDiffAt
  have hp : AnalyticAt ℝ (atmosphere s F m) 0 := (show ContDiffAt ℝ ω _ _ from ContDiffAt.sum (s:=univ) (fun i _=> he i)).analyticAt
  constructor; exact hp
  apply Tensor.ext_diag _ _ ((breath_tune ..).2.2 m) (Tensor.coeff_symm hp.contDiffAt)
  funext v
  rw [← stanza,breath, stanza_score (pool_summable ..)] -- unfolding score ok rank/s
  unfold stanza Tensor.diagonal; rw [recital_pool _ Summable.of_finite]
  rw [show atmosphere s F m=(∑ i,F ∘ seats s i) from funext fun x=> Eq.symm (Finset.sum_apply x ..), Tensor.coeff_sum _ _ _ _ (fun i _=> (he i).of_le le_top),_root_.sum_apply]
  refine sum_congr rfl fun i hi=>?_
  rw [tsum_fintype,show Tensor.coeff (F ∘ seats s i) r 0 (fun _=>v)=Tensor.coeff F r 0 (fun _=> seats s i v) from ?_,seat_norm (Tensor.coeff F r 0)]; swap
  · simp only [Tensor.coeff,_root_.smul_apply]; rw [wired _ (by rw [map_zero]; exact e),map_zero]; rfl
  apply sum_congr rfl; intro b hb
  rw [icicle,mul_right_comm _ (Tensor.coeff _ _ _ _),rosary, ← Finset.prod_mul_distrib]; congr 1; apply prod_congr rfl; intro k _
  unfold seats quavers silks; simp only [ContinuousLinearMap.pi_apply];
  cases h : s (b k) <;> simp
end YM.RG08
