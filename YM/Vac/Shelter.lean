import YM.Gauge.Size
import YM.Shoot.Criteria
import YM.Vac.Caps


/-!
# No flags on integration test shelter

No assertion of global logs; all original positive orientations including
period selectors in pull. Estimated per SITE and all periods. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG
open Lattice Wilson MeasureTheory Filter Set Function
open scoped Topology Matrix.Norms.Frobenius ENNReal BigOperators
variable {n : Side} {G : Gauge}

/-- Small link ball at level m; choose r=hatCoupling/4 -/
def calm (G : Gauge) (n : Side) (r : ℝ) := Set.pi (univ : Set (Edge (Site n))) fun _ => G.shell (r/4)
lemma calm_meas (r : ℝ) : MeasurableSet (calm G n r) := MeasurableSet.univ_pi fun _ => G.shell_meas _
lemma holds (s : Signed) (t : Site n) {r : ℝ} {U : Config G n} (h : U ∈ calm G n r) : pull s t U∈calm G n r := by
  intro i _; change G.chord (pull s t U i) ≤ _; unfold pull Step.read; split
  · rw [G.chord_inv]; exact h _ (mem_univ _)
  exact h _ (mem_univ _)

lemma pathBound {r : ℝ} {U : Config G n} (h : U ∈ calm G n r) (x : Site n) (p : Walk) : G.chord (travel U x p) ≤ p.length*(r/4) := by
  induction p generalizing x with
  | nil => simp [travel]
  | cons d w ih =>
    have he : G.chord (d.read U x) ≤ r/4 := by unfold Step.read; split; rw [G.chord_inv]; exact h _ (mem_univ _); exact h _ (mem_univ _)
    rw [travel]; apply (G.chord_triangle _ _).trans ((add_le_add he (ih (x+d.vec))).trans ?_); simp [add_mul,add_comm]
lemma faceBound {r : ℝ} {U : Config G n} (h : U∈calm G n r) (p : Face (Per n)) : G.chord (faceValue U p) ≤ r := by
  refine (pathBound h p.1 (square p.2.val.1 p.2.val.2)).trans_eq ?_; simp [square]; ring
lemma voids {r t : ℝ} {U : Config G n} (h : U∈calm G n r) (ht : r≤t) : flags t U=∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]; intro i hi
  obtain ⟨p,-,hp⟩ := (flags_spec ..).mp hi
  exact hp.not_ge ((faceBound h _).trans ht)

lemma space (G : Gauge) (n : Side) (r : ℝ) (hr : 0 < r) (hh : r≤1) :
    ((r/16)^Module.finrank ℝ G.Mat)^Fintype.card (Edge (Site n)) ≤ (prior G n).real (calm G n r) := by
  have hb : (r/16)^Module.finrank ℝ G.Mat ≤ G.probHaar.real (G.shell (r/4)) := by
    rw [show r/16=(r/4)/4 by ring]; exact G.shell_ge _ (by positivity) (by linarith)
  unfold prior calm
  rw [measureReal_def,Measure.pi_pi,Finset.prod_const,Finset.card_univ,ENNReal.toReal_pow]
  exact pow_le_pow_left₀ (by positivity) hb _

variable {β σ A Λ δ w : ℝ}
def baseBudget (C : Clip) (A : ℝ) (s : ℝ) : ℝ := Fintype.card PlaqAxes*(C.direct*s^2/2 +(A*s)^2/2)

namespace PathData
lemma ellShell {R : PathData G} {C : Clip} (h : R.Bounds C σ A Λ) (s : ℝ) (hs : 0<s) (p : Face (Per n)) {U : Config G n}
    (hi : U∈calm G n s) : ‖R.ell U p‖ ≤ A*s := by
  obtain ⟨-,hg,hg'⟩ := h.rows p.2
  let f i := |(R.row p.2 i).1| * Real.exp (σ*(R.row p.2 i).2.length)
  have he (i) : ‖R.ellTerms p i U‖ ≤ f i * s := by
    let k := (R.row p.2 i).2
    let c : Face (Per n) := (wrap n k.offset+p.1,k.plaq)
    have hc : faceValue (expandAt p.1 U) (k.offset,k.plaq)=faceValue U c := travel_at ..
    have hl : ‖k.atSite U p.1‖ ≤ s := by
      rw [Slot.atSite, Slot.eval,G.norm_adjoint,hc]; exact (G.curvature_norm _).trans (faceBound hi c)
    rw [ellTerms,norm_smul,Real.norm_eq_abs]
    refine mul_le_mul ?_ hl (norm_nonneg _) (by unfold f; positivity)
    exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg h.width.le (by positivity)))
  have hv := (PathData.ell_dominated R h p).absolute U
  unfold ell; refine le_trans (norm_tsum_le_tsum_norm hv) (le_trans (hv.tsum_le_tsum he (hg.mul_right _)) ?_)
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right hg' hs.le

lemma under {R : PathData G} {C : Clip} {p : BudgetPoint} (h : R.Bounds C σ A Λ) (v : ℝ) (hv : 0<v)
    (ht : v≤p.threshold) (hb : 0≤β) {U : Config G n} (hi : U∈calm G n v) : R.inChannels C p β U ≤
    (Fintype.card (Site n):ℝ)*(PathData.loopsPrice p β A Λ+β*baseBudget C A v) := by
  change Branch.avg _ ≤ _
  apply le_trans (c := (Fintype.card (Site n):ℝ)*_) (b := Branch.avg (fun _ : Signed => _)) ?_ (Branch.avg_const (n:=Signed) _).le
  apply Branch.avg_mono; intro t
  let V := pull t 0 U
  have he : V ∈ calm G n v := holds t 0 hi
  have hs (f : Face (Per n)) : R.baseTerm C p V f ≤ C.direct*v^2/2+(A*v)^2/2 := by
    have hh := faceBound he f
    have ht' := R.ellShell h v hv f he
    unfold baseTerm clipped
    rw [if_pos (hh.trans ht)]; apply add_le_add
    · gcongr
      · exact C.quadratic_pos.le
      exact G.chord_nonneg _
    split
    · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ht' 2) (by positivity)
    positivity
  have hh : ∑ f,R.baseTerm C p V f ≤ (Fintype.card (Site n):ℝ)*baseBudget C A v := by
    apply le_trans (Finset.sum_le_sum fun f (_:f ∈ Finset.univ) ↦ hs f)
    simp [Face,mul_add,Site,mul_assoc, baseBudget]
  have he' := (abs_le.mp (R.volume_price C p β hb V h)).2
  change R.principal C p β V ≤ _
  dsimp only
  linarith [mul_le_mul_of_nonneg_left hh hb]
end PathData

namespace Rep
def scalar (R : Rep G n) := R.v*Fintype.card (Site n)
def exCost (R : Rep G n) (A Λ δ : ℝ) := δ+PathData.loopsPrice R.p R.beta A Λ

theorem exponent_lo (R : Rep G n) (h : R.Lawful σ A Λ δ w) (hs : 0≤R.beta) (s : ℝ) (hp : 0<s) (he : s≤R.p.threshold)
    {U : Config G n} (hh : U∈calm G n s) : R.scalar - (Fintype.card (Site n):ℝ)*(R.exCost A Λ δ+R.beta*baseBudget R.clip A s) ≤
      R.exponent U := by
  have H := PathData.under h.paths s hp he hs hh
  have he := (abs_le.mp (volumeE _ h.labels U)).2
  unfold scalar exponent exCost; linarith

theorem exponent_hi (R : Rep G n) (h : R.Lawful σ A Λ δ w) (hs : 0≤R.beta) (U : Config G n) :
    R.exponent U ≤ R.scalar+(Fintype.card (Site n):ℝ)*R.exCost A Λ δ := by
  have H := (abs_le.mp (volumeE _ h.labels U)).1
  have he := R.path.whole _ R.p _ hs U h.paths
  unfold scalar exponent exCost; linarith

theorem denominator (R : Rep G n) (h : R.Lawful σ A Λ δ w) (hs : 0≤R.beta) (s : ℝ) (hp : 0<s) (he : s≤R.p.threshold)
    (hpos : ∀ U,0≤R.eval U) :
    Real.exp (R.scalar - (Fintype.card (Site n):ℝ)*(R.exCost A Λ δ+R.beta*baseBudget R.clip A s)-
      (Fintype.card (Edge (Site n)):ℝ)*Module.finrank ℝ G.Mat* Real.log (16/s)) ≤ ∫ U,R.eval U∂prior G n := by
  let D := calm G n s
  let X := R.scalar - (Fintype.card (Site n):ℝ)*(R.exCost A Λ δ+R.beta*baseBudget R.clip A s)
  have hf (U : Config G n) (hU : U∈D) : Real.exp X ≤ R.eval U := by
    unfold Rep.eval; rw [Activities.gas_one _ _ (voids hU he),mul_one]
    exact Real.exp_monotone (R.exponent_lo h hs _ hp he hU)
  have hD : (prior G n).real D * Real.exp X ≤ ∫ U : Config G n,R.eval U ∂prior G n := calc
    _ = ∫ U : Config G n,D.indicator (fun _ => Real.exp X) U∂prior G n := by
      rw [integral_indicator (show MeasurableSet D from calm_meas _),setIntegral_const]; simp only [smul_eq_mul]
    _ ≤ _ := integral_mono (integrable_const _ |>.indicator (show MeasurableSet D from calm_meas _)) ((R.envelope h).integrable _) fun i => by
      by_cases he : i ∈ D
      · rw [indicator_of_mem he]; exact hf i he
      rw [indicator_of_notMem he]; exact hpos _
  let d := Module.finrank ℝ G.Mat
  let a := Fintype.card (Edge (Site n))
  apply le_trans ?_ hD
  apply le_trans ?_ (mul_le_mul_of_nonneg_right (space G n s hp (he.trans R.p.threshold_le)) (Real.exp_pos X).le)
  change Real.exp (X - (a:ℝ)*d*Real.log (16/s)) ≤ ((s/16)^d)^a*Real.exp X
  refine le_of_eq ?_
  have hy : Real.log (16/s) = -Real.log (s/16) := by rw [← Real.log_inv]; congr 1; field_simp
  rw [mul_comm _ (Real.exp X), hy, mul_neg, sub_neg_eq_add,Real.exp_add, mul_assoc (a:ℝ), Real.exp_nat_mul,Real.exp_nat_mul,
    Real.exp_log (by positivity)]
end Rep

lemma History.nonnegative (A : History G) (h : A.Selected) (N p m) (hm : m ≤ N) : ∀ U, 0 ≤ (A.rep N p m).eval U := by
  induction hm using Nat.decreasingInduction with
  | self => intro U; rw [(h.starts N p).2]; exact (bare_pos ..).le
  | of_succ i hI ih => intro U; rw [(h.steps N p i hI).1]; exact integral_nonneg fun V => mul_nonneg (StepData.density_positive ..) (ih _)
end YM.RG
