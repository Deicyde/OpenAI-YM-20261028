import YM.Push.LOCAL_SPLITTING.Calculus


set_option warningAsError false

/-!
# Dominated differentiation of a series by ordered LEFT jets

We work on an actual open field window, on the representatives before
masking. Finite-dimensional probe argument: need only a summable bound
on each fixed list of left derivatives through order k. The bound must
hold at *all* points of the window, not just the given center. We prove
both C^k in the base-point charts and exchange with the successive
ordered left derivations. The finite frame used below is for legitimating
differentiation, not for estimates (its size may depend on the period).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.LogJets
open Lattice RG Wilson Next.Foundations Filter Function
open Push.Local
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff

variable {G : Gauge} {n : Side} {ι : Type*} {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "Θ" => Directions G n
local notation "Ω" => Config G n

lemma increment_cont (u : Ω) : Continuous (increment u) := by
  unfold increment
  fun_prop

/-- Left coordinate of the change from x to y near the diagonal. -/
private def turn (x y : Θ) : Θ := fun e => G.plog (G.mat (G.lieExp (y e) * (G.lieExp (x e))⁻¹))

private lemma turn_self (x : Θ) : turn x x = 0 := funext fun e => by simp [turn]

private lemma turn_diff (x : Θ) : ContDiffAt ℝ ω (uncurry (turn (G:=G) (n:=n))) (x,x) := by
  apply contDiffAt_pi.mpr; intro e
  let f (p : Θ × Θ) := G.lieExp (p.2 e) * (G.lieExp (p.1 e))⁻¹
  have h : ContDiff ℝ ω (G.mat ∘ f) := by
    change ContDiff ℝ ω (fun p : Θ × Θ => G.mat (f p))
    simp only [f, G.mat_mul, G.mat_inv]
    exact (G.exp_jet.comp ((contDiff_apply ℝ G.Color e).comp contDiff_snd)).mul
      ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp
        (G.exp_jet.comp ((contDiff_apply ℝ G.Color e).comp contDiff_fst)))
  have he : (G.mat ∘ f) (x,x)=1 := by simp [f]
  exact (he.symm ▸ G.plog_diff).comp (x,x) h.contDiffAt

private def shift (x : Θ) := fderiv ℝ (turn x) x

private lemma shift_has (x : Θ) : HasFDerivAt (turn x) (shift x) x := by
  have h := (turn_diff x).comp x (f:=fun u : Θ => (x,u)) (contDiffAt_const.prodMk contDiffAt_id)
  exact (h.differentiableAt (by simp)).hasFDerivAt

private lemma shift_diff (x : Θ) : ContDiffAt ℝ ω (shift (G:=G) (n:=n)) x :=
  (turn_diff x).fderiv (g:=id) contDiffAt_id le_top

private lemma recenter (U : Ω) (x : Θ) : increment U =ᶠ[𝓝 x]
    increment (increment U x) ∘ turn x := by
  let f (i : Edge (Site n)) (y : Θ) := G.lieExp (y i) * (G.lieExp (x i))⁻¹
  have he (i) : Tendsto (f i) (𝓝 x) (𝓝 1) := by
    rw [← show f i x=1 by simp [f]]
    exact (show Continuous (f i) by unfold f; fun_prop).tendsto _
  filter_upwards [eventually_all.mpr (fun i => (he i).eventually G.plog_right)] with y hy
  ext1 i
  unfold increment turn; simp only [comp_apply]
  rw [show G.lieExp (G.plog _) = _ from hy i]
  unfold f; simp [mul_assoc]

private def first (f : Ω → E) (U : Ω) := fderiv ℝ (f ∘ increment U) 0

private lemma chart_has {U : Ω} {x : Θ} {f : Ω → E} (h : Chart 1 f (increment U x)) :
    HasFDerivAt (f ∘ increment U) ((first f (increment U x)).comp (shift x)) x := by
  have hg : HasFDerivAt (f ∘ increment (increment U x)) (first f (increment U x)) (turn x x) := by
    rw [turn_self]; exact (h.differentiableAt (by simp)).hasFDerivAt
  exact (hg.comp x (shift_has x)).congr_of_eventuallyEq ((recenter U x).fun_comp f)

private abbrev Axes (G : Gauge) (n : Side) := Fin (Module.finrank ℝ (Directions G n))
private def basis (b : Axes G n) : Θ := Module.finBasis ℝ Θ b
private def cell (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Axes G n) : E →L[ℝ] Θ →L[ℝ] E :=
  ContinuousLinearMap.smulRightL ℝ Θ E (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ Θ).coord b))

private lemma first_eq {f : Ω → E} {U : Ω} (h : Chart 1 f U) : first f U =
    ∑ b : Axes G n,cell E b (leftDerivs f [basis b] U) := by
  apply ContinuousLinearMap.ext; intro x
  have he (b : Axes G n) : leftDerivs f [basis b] U = first f U (basis b) := left_cons _ [] h (Nat.zero_lt_one)
  simp_rw [he, sum_apply]
  change first f U x = ∑ b : Axes G n, ((Module.finBasis ℝ Θ).repr x) b • first f U (basis b)
  simp_rw [← map_smul, ← map_sum,basis,Module.Basis.sum_repr]


/-- A summable bound, possibly different for each list (but *common*
for all fields in W). This condition exchanges even noncommuting
derivatives; no analogous condition on the masks is intended. -/
structure Termwise (k : ℕ) (W : Set Ω) (f : ι → Ω → E) : Prop where
  smooth (i U) : U ∈ W → Chart k (f i) U
  earns (l : List Θ) : l.length ≤ k →
    ∃ d : ι → ℝ, Summable d ∧ ∀ i U, U ∈ W → ‖leftDerivs (f i) l U‖ ≤ d i

namespace Termwise

variable {W : Set (Config G n)} {k : ℕ} {f : ι → Config G n → E}

/-- Reserve the LAST derivation in the ordered list. -/
lemma remove_last (h : Termwise (k+1) W f) (A : Θ) :
    Termwise k W (fun i => leftDerivs (f i) [A]) := by
  constructor
  · exact fun i U hu => leftDerivs_chart _ _ (by simpa [Chart, add_comm] using h.smooth i U hu)
  intro l hl
  have he := h.earns (l ++ [A]) (by simpa using hl)
  simp_rw [Work.G07.left_append] at he
  exact he

variable [CompleteSpace E]

lemma sums (h : Termwise k W f) (l : List Θ) (hl : l.length ≤ k) (U : Ω) (hu : U ∈ W) :
    Summable (fun i => leftDerivs (f i) l U) := by
  obtain ⟨d,hd,hb⟩ := h.earns l hl
  exact Summable.of_norm_bounded hd fun i => hb i U hu

private lemma base (hW : IsOpen W) (h : Termwise 0 W f) (U : Ω) (hu : U ∈ W) :
    Chart 0 (fun V => ∑' i, f i V) U := by
  let s := increment U ⁻¹' W
  have hs : IsOpen s := hW.preimage (increment_cont _)
  change ContDiffAt ℝ 0 _ 0
  refine contDiffAt_zero.mpr ⟨s, hs.mem_nhds (show increment U 0 ∈ W by rwa [Work.G07.at_zero_increment]), ?_⟩
  obtain ⟨g,hg,hl⟩ := h.earns [] (le_refl _)
  apply continuousOn_tsum (f:=fun i => f i ∘ increment U) _ hg
    (fun i x hx => hl i _ hx)
  intro i x hx
  have he : Chart 0 (f i) (increment U x) := h.smooth i _ hx
  refine (chart_comp he fun l => ?_).continuousAt.continuousWithinAt
  simp only [increment, G.mat_mul]
  exact ((G.exp_jet.comp (contDiff_apply ℝ _ _)).mul contDiff_const).contDiffAt

/-- The derivative in one fixed field chart. Its domain of
validity is an actual neighborhood of zero, the same for all summands.
We temporarily pay an arbitrary finite-volume factor for the basis. -/
private def slope (U : Ω) (i : ι) (x : Θ) := ((first (f i) (increment U x)).comp (shift x))

omit [CompleteSpace E] in
private lemma first_budget (h : Termwise (k+1) W f) : ∃ g : ι → ℝ, Summable g ∧
    ∀ i U, U ∈ W → ‖first (f i) U‖ ≤ g i := by
  choose d hd hs using fun b : Axes G n => h.earns [basis b] (by simp)
  let C (b : Axes G n) (i : ι) := ‖cell E b‖ * d b i
  refine ⟨fun i => ∑ b, C b i, summable_sum (fun b _ => (hd b).mul_left _), fun i U hu => ?_⟩
  rw [first_eq ((h.smooth i U hu).of_le (Nat.cast_le.mpr (by omega : 1 ≤ k+1)))]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum fun b _ => ?_)
  exact ((cell E b).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hs b i U hu) (norm_nonneg _))

private lemma neighborhood (hW : IsOpen W) (h : Termwise (k+1) W f) (U : Ω) (hu : U ∈ W) :
    ∃ r > 0, ∀ x ∈ Metric.ball (0:Θ) r, increment U x ∈ W ∧
      Summable (fun i => slope (f:=f) U i x) ∧
      HasFDerivAt (fun y => ∑' i, f i (increment U y)) (∑' i, slope (f:=f) U i x) x := by
  obtain ⟨g,hg,hb⟩ := first_budget h
  let K := ‖shift (0:Θ)‖ + 1
  have hK : ∀ᶠ x : Θ in 𝓝 0, ‖shift x‖ < K :=
    ((shift_diff _).continuousAt.norm).eventually_lt (g:=fun _ => K) continuousAt_const
      (by dsimp only [K]; linarith)
  have h₀ : increment U 0 ∈ W := by rwa [Work.G07.at_zero_increment]
  have hW' : ∀ᶠ x : Θ in 𝓝 0, increment U x ∈ W :=
    ((increment_cont U).continuousAt (x:=0)).preimage_mem_nhds (hW.mem_nhds h₀)
  obtain ⟨r,hr,hS⟩ := Metric.nhds_basis_ball.eventually_iff.mp (hW'.and hK)
  let s := Metric.ball (0:Θ) r
  have hs i x (hx : x ∈ s) : Chart 1 (f i) (increment U x) := (h.smooth i _ (hS hx).1).of_le (Nat.cast_le.mpr (by omega : 1 ≤ k+1))
  have he i x (hx : x ∈ s) : ‖slope (f:=f) U i x‖ ≤ g i * K :=
    (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_mul (hb i _ (hS hx).1) (hS hx).2.le
        (norm_nonneg _) ((norm_nonneg _).trans (hb i _ (hS hx).1)))
  refine ⟨r,hr,fun x hx => ⟨(hS hx).1, Summable.of_norm_bounded (hg.mul_right K) (fun i => he i _ hx),?_⟩⟩
  exact hasFDerivAt_tsum_of_isPreconnected (hg.mul_right K) Metric.isOpen_ball
    (convex_ball (0:Θ) r).isPreconnected (fun i y hy => chart_has (hs i y hy)) he
    (Metric.mem_ball_self hr) (h.sums [] (by simp) _ h₀) hx

private def frameSum (f : ι → Ω → E) (V : Ω) :=
    ∑ b : Axes G n,cell E b (∑' i,leftDerivs (f i) [basis b] V)

private lemma slope_sum (h : Termwise (k+1) W f) (U : Ω) (x : Θ) (hx : increment U x ∈ W) :
    (∑' i, slope (f:=f) U i x) = (frameSum f (increment U x)).comp (shift x) := by
  let V := increment U x
  have hg (i : ι) : Chart 1 (f i) V := (h.smooth i _ hx).of_le (Nat.cast_le.mpr (by omega : 1 ≤ k+1))
  have he : Summable (fun i => first (f i) V) := by
    obtain ⟨g,hg,hl⟩ := first_budget h
    exact Summable.of_norm_bounded hg (fun i => hl i V hx)
  let Q : (Θ →L[ℝ] E) →L[ℝ] (Θ →L[ℝ] E) := ContinuousLinearMap.precomp E (shift x)
  change (∑' i, Q (first (f i) V)) = Q (frameSum f V)
  rw [← Q.map_tsum he]
  apply congr_arg Q
  have hb b : Summable (fun i => leftDerivs (f i) [basis b] V) := h.sums _ (by simp) _ hx
  simp_rw [show ∀ i, first (f i) V = _ from fun i => first_eq (hg i)]
  unfold frameSum
  simp_rw [(cell E _).map_tsum (hb _)]
  exact Summable.tsum_finsetSum (fun i _ => (cell E i).summable (hb i))

private lemma assembled (hW : IsOpen W) (h : Termwise (k+1) W f) (U : Ω) (hu : U ∈ W)
    (hh : ∀ b : Axes G n, Chart k (fun V : Ω => ∑' i, leftDerivs (f i) [basis b] V) U) :
    Chart (k+1) (fun V => ∑' i,f i V) U := by
  let Q (x : Θ) := (frameSum f (increment U x)).comp (shift x)
  unfold Chart; push_cast
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  obtain ⟨r,hr,hv⟩ := h.neighborhood hW U hu
  refine ⟨Q, ⟨Metric.ball _ r, Metric.ball_mem_nhds _ hr, fun x hx => ?_⟩,?_⟩
  · obtain ⟨h1,-,h3⟩ := hv x hx
    rw [slope_sum h U x h1] at h3
    exact h3
  apply ContDiffAt.clm_comp _ ((shift_diff _).of_le le_top)
  exact ContDiffAt.sum fun b _ => (cell E b).contDiff.contDiffAt.comp _ (hh b)

private lemma exchange_first (hW : IsOpen W) (h : Termwise (k+1) W f) (U : Ω) (hu : U ∈ W)
    (hg : Chart (k+1) (fun V => ∑' i,f i V) U) (b : Θ) :
    leftDerivs (fun V => ∑' i,f i V) [b] U = ∑' i, leftDerivs (f i) [b] U := by
  obtain ⟨r,hr,hv⟩ := h.neighborhood hW U hu
  obtain ⟨h1,h2,h3⟩ := hv 0 (Metric.mem_ball_self hr)
  let T := fun V => ∑' i,f i V
  have he : first T U = ∑' i,slope (f:=f) U i 0 := h3.fderiv
  have ha i := h.smooth i U hu
  have ho : increment U 0 ∈ W := by rwa [Work.G07.at_zero_increment]
  have hf (i : ι) : first (f i) U = slope (f:=f) U i 0 :=
    (chart_has ((h.smooth i _ ho).of_le (Nat.cast_le.mpr (by omega : 1 ≤ k+1)))).fderiv
  change leftDerivs T [b] U = _
  rw [show leftDerivs T [b] U = first T U b from left_cons b [] hg (by simp),he]
  rw [show (∑' i,slope (f:=f) U i 0) b = ∑' i,slope (f:=f) U i 0 b from
    (ContinuousLinearMap.apply ℝ E b).map_tsum h2]
  apply tsum_congr; intro i; rw [← hf i]; exact (left_cons b [] (ha i) (by simp)).symm

/-- Absolute receipts license C^k and ordered termwise left
differentiation in the common window. Valid also if the centers here
are flag boundary points (provided W really contains them and the
summands are the unmasked functions with the indicated jets on W). -/
theorem smooth_exchange (hW : IsOpen W) (h : Termwise k W f) (U : Ω) (hu : U ∈ W) :
    Chart k (fun V => ∑' i,f i V) U ∧ ∀ l : List Θ, l.length ≤ k →
      leftDerivs (fun V => ∑' i,f i V) l U = ∑' i, leftDerivs (f i) l U := by
  induction k generalizing f U with
  | zero =>
    refine ⟨base hW h U hu,fun l hl => ?_⟩
    have hl' : l=[] := by simpa using hl
    subst l; rfl
  | succ k ih =>
    have ht (V) (hv : V ∈ W) := assembled hW h V hv fun b => (ih (h.remove_last (basis b)) _ hv).1
    refine ⟨ht _ hu,fun l hl => ?_⟩
    induction l using List.reverseRecOn with
    | nil => rfl
    | append_singleton l b _ =>
      have he : increment U 0 ∈ W := by rwa [Work.G07.at_zero_increment]
      let T := fun V => ∑' i, f i V
      let Q := fun i V => leftDerivs (f i) [b] V
      have hg : leftDerivs T [b] ∘ increment U =ᶠ[𝓝 0] (fun V => ∑' i,Q i V) ∘ increment U := by
        have hw : ∀ᶠ x : Θ in 𝓝 0, increment U x ∈ W :=
          ((increment_cont U).continuousAt (x:=0)).preimage_mem_nhds (hW.mem_nhds he)
        filter_upwards [hw] with t ht' using exchange_first hW h (increment U t) ht' (ht _ ht') b
      have hl : l.length ≤ k := by simpa using hl
      simp_rw [Work.G07.left_append]
      exact (left_congr l U hg).trans ((ih (h.remove_last b) U hu).2 l hl)

end Termwise
end YM.Further.LogJets
