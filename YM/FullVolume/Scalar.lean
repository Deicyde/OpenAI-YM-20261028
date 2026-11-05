import YM.Next.RANK.Axial
import YM.Push.RELAY_MARK.Cutoff
import YM.Vac.Shelter

/-!
# Field-independent cost

Yes, one *must* drop the scalar! No UV extraction can make all the
`Rep` parameters converge. At each level m and period p the physical Wilson
partition against **probability** Haar, with the scalar removed, is bounded
below, uniformly in depth. Put it back and the partition tends to zero.

This statement uses actual history parameters, so is independent of details
of shooting, strengthening of receipts, choice of sources, and doesn't depend
on uniqueness or a different ('continuum') calibration.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function RG Lattice Wilson MeasureTheory Filter Set
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {A : History G}

private theorem can_cost (h : G.Simple) : ∃ u : G.El, 0 < G.price u := by
  obtain ⟨X,hX,Y,_,hp⟩ := h.1
  have hh : ∃ u : G.El, u ≠ 1 := by
    by_contra! hv
    have he : (fun t : ℝ => NormedSpace.exp (t • X)) = fun _ => (1 : G.Mat) := by
      funext t
      obtain ⟨u,hu⟩ := (show G.Generates X from hX) t
      exact hu.symm.trans (by rw [hv u, G.mat_one])
    have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) X 0 := by
      simpa using! hasDerivAt_exp_smul_const X (0 : ℝ)
    rw [he] at hd
    exact hp (by rw [hd.unique (hasDerivAt_const ..), mul_zero, zero_mul, sub_zero])
  obtain ⟨u,hu⟩ := hh
  have hk : 0<G.chord u := by
    apply div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr ?_)) (Real.sqrt_pos.mpr (by exact_mod_cast G.dimPos))
    exact fun hh => hu (G.mat_injective (hh.trans G.mat_one.symm))
  exact ⟨u, by linarith [G.chord_price u, pow_pos hk 2]⟩

/-- Strict upper cost at ANY one fixed positive beta. -/
theorem ceiling (h : G.Simple) {b : ℝ} (hb : 0<b) :
    ∃ q : ℝ, 0≤q ∧ q<1 ∧ ∀ n : Side, 1<n.val → ∀ β : ℝ, b ≤ β →
      partition G n β ≤ q^(3*Fintype.card (Site n)-3) := by
  let F (u : G.El) := Real.exp (-b*G.price u)
  have hf : Continuous F := by unfold F; fun_prop
  have hg : ∀ u, 0 ≤ F u := fun _ => (Real.exp_pos _).le
  have he : ∀ u, F u ≤ 1 := fun u => Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) (G.price_range _).1)
  refine ⟨∫ u,F u ∂G.probHaar,integral_nonneg hg,?_,?_⟩
  · obtain ⟨u,hu⟩ := can_cost h
    have hI : Integrable F G.probHaar := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    let f (u : G.El) : ℝ := 1-F u
    have hx : f u ≠ 0 := (sub_pos.mpr (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hb) hu))).ne'
    have hs := integral_pos_iff_support_of_nonneg (μ:=G.probHaar) (f:=f) (fun u => sub_nonneg.mpr (he u)) ((integrable_const _).sub hI)
    have hw := hs.mpr (IsOpen.measure_pos _ (isOpen_ne_fun (f:=f) (continuous_const.sub hf) continuous_const) ⟨u,hx⟩)
    unfold f at hw; rw [integral_sub (integrable_const _) hI] at hw; simpa using hw
  · intro n hn β hβ
    calc
      _ ≤ partition G n b := integral_mono (bare_integrable _) (bare_integrable _) fun x =>
        Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg hβ) (energy_nonneg x))
      _ = ∫ U : Config G n, ∏ p : Face (Per n), F (faceValue U p) ∂prior G n := by
        unfold partition F bare energy; simp_rw [Finset.mul_sum, ← Real.exp_sum]
      _ ≤ _ := Next.Rank.Axial.elimination hn F hf hg he

theorem raw_lost (h : A.Selected) (hp : G.Simple) (P : ℕ → ℕ) :
    Tendsto (fun N => partition G (A.S.side N (P N)) (A.β N (P N) N)) atTop (𝓝 0) := by
  obtain ⟨q,hq,hr,H⟩ := ceiling hp (b:=1/2) (by norm_num)
  let d (N : ℕ) := A.S.side N (P N)
  have hx : Tendsto (fun N => (d N).val) atTop atTop := by
    refine tendsto_atTop.mpr (fun k=>?_)
    filter_upwards [Push.Mark.lengths A.S k] with N hn using hn _
  have he : Tendsto (fun N : ℕ => 3*Fintype.card (Site (d N))-3) atTop atTop := by
    have hh := (tendsto_pow_atTop (α:=ℕ) (n:=4) (by norm_num)).comp hx
    refine tendsto_atTop.mpr (fun k => ?_)
    filter_upwards [hh.eventually_ge_atTop (k+3)] with N hn
    change k + 3 ≤ (d N).val^4 at hn; rw [site_card]; omega
  apply squeeze_zero' (Eventually.of_forall fun _ => (partition_pos _).le) _
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hr).comp he)
  filter_upwards [hx.eventually_ge_atTop 2] with N hn
  apply H (d N) hn; refine le_trans ?_ (h.represents N (P N) N le_rfl).band.1
  gcongr; exact (A.levels.fits.delayed _).le

/-- Expense with the field-independent scalar removed. -/
def stripped (A : History G) (N p m : ℕ) :=
  Real.exp (-(A.rep N p m).scalar) * partition G (A.S.side N p) (A.β N p N)

/-- Identity at THIS fixed level (not a new Wilson law). -/
theorem strips (h : A.Selected) {N p m} (he : m≤N) :
    stripped A N p m = ∫ U, Real.exp (-(A.rep N p m).scalar) *
        (A.rep N p m).eval U ∂prior G (A.S.side m p) := by
  rw [integral_const_mul,A.partition_eq h _ _ _ he]; rfl

/-- A mesh-uniform lower bound, unweighted level scalar removed. -/
theorem saved (h : A.Selected) (m p : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ N≥m, c ≤ stripped A N p m := by
  let B := A.levels.budget m
  let P := A.levels.params m
  let F := A.levels.clock.allowance m
  let T := A.levels.clock.loopCap m
  let H := 2*A.levels.clock.hatBeta m
  let v := B.threshold
  have hV : 0<v := B.threshold_pos
  let E : ℝ := Fintype.card (Site (A.S.side m p))
  let k := E*((F + PathData.loopsPrice B H P.paths T)+ H*baseBudget P.clip P.paths v)
  refine ⟨Real.exp (-k-(Fintype.card (Edge (Site (A.S.side m p))):ℝ)*Module.finrank ℝ G.Mat*Real.log (16/v)), Real.exp_pos _,fun N hn=>?_⟩
  let R := A.rep N p m
  have hp := h.represents N p m hn
  have hs : R.p = B := hp.vac
  have hx : 0≤R.beta := (div_nonneg ((zero_lt_one.trans (A.levels.fits.delayed _)).le) (by norm_num)).trans hp.band.1
  have hh : R.beta ≤ H := hp.band.2
  have hK : E * (R.exCost P.paths T F + R.beta * baseBudget R.clip P.paths v) ≤ k := by
    have hE : 0 ≤ E := Nat.cast_nonneg _
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hE
    · unfold Rep.exCost; rw [hs]; unfold PathData.loopsPrice
      have hh' := P.paths_pos; dsimp only [v] at hV
      gcongr
    change R.beta * baseBudget R.clip P.paths v ≤ _
    rw [show R.clip=P.clip from hp.clip]; apply mul_le_mul_of_nonneg_right hh
    unfold baseBudget; have h:=P.clip.quadratic_pos; positivity
  rw [stripped, ← A.partition_eq h N p m hn]
  apply (le_trans ?_ (mul_le_mul_of_nonneg_left
    (R.denominator hp.good hx v hV (le_of_eq (congr_arg BudgetPoint.threshold hs.symm)) (A.nonnegative h N p m hn)) (Real.exp_pos (-R.scalar)).le))
  · rw [← Real.exp_add]; apply Real.exp_monotone
    change -k-_ ≤ _
    linarith only [hK]

theorem field_independent (h : A.Selected) (hp : G.Simple) (m p : ℕ) :
    Tendsto (fun N => (A.rep N p m).v) atTop atBot := by
  obtain ⟨c,hc,H⟩ := saved h m p
  let E : ℝ := Fintype.card (Site (A.S.side m p))
  have hE : 0<E := Nat.cast_pos.mpr Fintype.card_pos
  apply tendsto_atBot.mpr
  intro t
  filter_upwards [eventually_ge_atTop m, (raw_lost h hp (fun _=>p)).eventually (gt_mem_nhds (show 0 < c / Real.exp (-(t*E)) from by positivity))] with N hn hm
  change partition _ _ (A.β N p N)< _ at hm
  by_contra! hw
  have hi : stripped A N p m < c := calc
    _ ≤ Real.exp (-(t*E)) * _ := mul_le_mul_of_nonneg_right (Real.exp_monotone (neg_le_neg (mul_le_mul_of_nonneg_right hw.le hE.le))) (partition_pos _).le
    _ < _ := (lt_div_iff₀' (Real.exp_pos _)).mp hm
  exact hi.not_ge (H N hn)
end YM.FullVolume
