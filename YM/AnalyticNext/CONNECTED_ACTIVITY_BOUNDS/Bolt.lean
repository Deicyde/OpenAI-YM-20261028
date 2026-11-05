import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Bearer
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Walls

/-!
# Borel nature of the folia and family estimates, even off protectors

One conditional slice k. These are at all V. `K_α`s hard, cost
stipulations for actual Rep.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Canvas
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint Paths Chains Calls Mixed Cab
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}
  {P : Teller G} {α : Type} [MeasurableSpace α]

lemma gates_meas {U : α → Config G f} {V : α→Config G c} (q : Chi) (p : Stores S) (x W : ℝ) (k : S.Choices)
    (he : S.patch.Branches S.kernel G) (L : Finset ℕ) (R : Activities G f) (h : Measurable U) (hh : Measurable V) :
    (∀ i, Measurable fun a => fine p q x (U a) i) ∧ (∀ i, Measurable fun a => wireMask p q W x (U a) k (V a) i) ∧
    (∀ i, Measurable fun a => αSite (U a) i k) ∧ (∀ i,Measurable fun a => αBond (U a) i k) ∧
      ∀ t i, Measurable fun a => edgeBan R L (U a) t i := by
  have hm (b : ℝ) : Measurable (q.innerShare b) := q.smooth.continuous.measurable.comp
    ((measurable_id.div_const _).pow_const 2)
  refine ⟨fun i => ?_,fun i => ?_,fun i => ?_,fun i => ?_,fun t i => ?_⟩
  · unfold fine; dsimp only; split
    next => exact measurable_const.sub ((hm _).comp (toll_meas _ h))
    exact (hm _).comp (toll_meas _ h)
  · unfold wireMask; dsimp only; split
    next => exact measurable_const.sub ((hm _).comp (wire_meas k _ he h hh))
    exact (hm _).comp (wire_meas k _ he h hh)
  · unfold αSite; exact measurable_const.mul ((S.patch.frameMass_meas (k.1 _)).comp ((show Continuous
      (fun a : Config G f => expandAt (S.ratio.embed i) a) from by unfold expandAt; fun_prop).measurable.comp h))
  · unfold αBond; exact measurable_const.mul ((S.patch.predictorMass_meas (k.2 _)).comp
      ((S.connector_meas he k.1 i).comp h))
  unfold edgeBan; apply Measurable.ite _ measurable_const measurable_const
  by_cases he : noHolder R L i
  · simp only [he,true_and]; exact h (RG.flags_open ..).measurableSet
  simp [he]

-- bundle
namespace Bent
variable {v z : α→ ArrayR G f} {Y : α→Mint T F A x} {r : ℝ} {h : Chi} {k : S.Choices}
  {N : ChartRatio G} (b : Bent Y r h k) (hT : P.Funds S T) (hv : Choice N r) (he : Measurable v)
include b he
lemma cloth (T : Finset (Bond f)) : Measurable fun p => robe (Y p) T (v p) := by
  unfold robe; simp only [show ∀ i, _ from fun i => (b.q i).1]
  refine Finset.measurable_fun_prod _ fun i _ => ?_
  exact h.smooth.continuous.measurable.comp ((((measure_lds he i).norm).div_const _).pow_const 2)

include hv
lemma capes (W β : ℝ) (L : Finset ℕ) (R : Activities G f) (hP : P.Funds S T) :
    (∀ p : Stores S, Measurable fun x => pact p R L β W N (Y x) (v x)) ∧
    (∀ i : Bg S, Measurable fun x => chip (Y x) R L W (v x) i) ∧
      (∀ i : Flick S, Measurable fun x => slash (Y x) β N (v x) i) := by
  let U i := (Y i).build (v i)
  let V i := (Y i).V
  have hx p := gates_meas h p x W k (funds_branch hP) L R (b.buildField he) b.V
  have ht i : Measurable fun p => broad x S.patch (Y p).q (lie (v p) i) := by
    simp_rw [show ∀ i, _ from fun i => (b.q i).1]
    exact h.smooth.continuous.measurable.comp ((((measure_lds he i).norm).div_const _).pow_const _)
  refine ⟨fun p => ?_,fun i => ?_,fun i => ?_⟩
  · simp_rw [parses]; apply Measurable.mul
    · apply Measurable.mul
      · unfold noMore curb; dsimp only
        obtain ⟨h1,h2,h3,h4,h5⟩ := hx p
        simp_rw [show ∀ i, _ from fun i => (b.q i).1, show ∀ i, _ from fun i => (b.q i).2]
        exact (Finset.measurable_fun_prod _ fun i _ => h5 _ _).mul ((((Finset.measurable_fun_prod _ fun i _ => h1 _).mul
          (Finset.measurable_fun_prod _ fun i _ => h2 _)).mul (Finset.measurable_fun_prod _ fun i _ => h3 _)).mul
            (Finset.measurable_fun_prod _ fun i _ => h4 _))
      unfold chambers; refine Finset.measurable_fun_prod _ fun i _ => ?_
      unfold prorated; apply (ht i).mul (hv.h.borel.comp (measure_lds he i))
    apply Measurable.exp; unfold coverEnergy; exact (((Measurable.mul measurable_const
      (Finset.measurable_fun_sum _ fun i _ => (b.shells hP hv he i).1)).add (Finset.measurable_fun_sum _ fun i _ => b.pair_lab i)).sub measurable_const)
  · unfold chip; split
    swap; exact measurable_const
    apply Measurable.mul (g:=fun p => tooth (Y p) R L W (v p) i-1)
    · split
      next => exact measurable_const
      exact b.cloth he _
    refine Measurable.sub (f:=fun a => tooth (Y a) R L W (v a) i) ?_ measurable_const
    obtain ⟨h1,h2,h3,h4,h5⟩ := hx A
    rcases i with i|i|i|i|i|i
    · simp_rw [tooth,show ∀ i,_ from fun i => (b.q i).1]; exact h1 _ -- figure unused
    · simp_rw [tooth,show ∀ i,_ from fun i => (b.q i).1,show ∀ i,_ from fun i => (b.q i).2]; exact h2 _
    · simp_rw [tooth,show ∀ i,_ from fun i => (b.q i).2]; exact h3 _
    · simp_rw [tooth,show ∀ i,_ from fun i => (b.q i).2]; exact h4 _
    · exact h5 _ _
    exact ht i
  rcases i with i|i|i <;> dsimp only [slash] <;> split
  next => exact measurable_const
  next => exact ((((measurable_const.mul (b.cloth he _)).mul ((b.shells hP hv he i).2)).exp).sub measurable_const)
  next => exact measurable_const
  next => exact (b.pair_lab i).exp.sub measurable_const
  next =>
    unfold hat; simp_rw [show ∀ i, _ from fun i => (b.q i).1]; have hX := measure_lds he i
    exact (h.smooth.continuous.measurable.comp ((hX.norm.div_const _).pow_const 2)).mul
      ((hv.h.borel.comp hX).sub measurable_const)
  next => exact measurable_const

omit hv in
lemma buttons_meas (T' : PathData G) (s : ℝ) (H : Clip) (i : Buttons f) : Measurable fun p =>
    chiffon T' H i (till x) 1 s ((Y p).build (v p)) := by
  have hx := pulling_meas i.1 (b.buildField he)
  let a := (i.2.2.1,i.2.1)
  have hh j : Continuous fun p => T'.ellTerms a j (n:=f) p := by
    unfold PathData.ellTerms Slot.atSite expandAt; fun_prop
  unfold chiffon drain; apply Measurable.ite _ ((ip ((hh _).measurable.comp hx) ((hh _).measurable.comp hx)).div_const _) measurable_const
  by_cases hi : ¬(strip T' a.2 (till x) 1 i.2.2.2.1 ∧ strip T' a.2 (till x) 1 i.2.2.2.2)
  · unfold a at hi; dsimp only at hi; simp only [hi,not_false_eq_true,and_true]; exact hx (PathData.kept_closed ..).measurableSet
  unfold a at hi; dsimp only at hi; simp [hi]

omit hv he in
lemma buttout (T' : PathData G) (s : ℝ) (H : Clip) (i : Buttons c) : Measurable fun p =>
    chiffon T' H i (till x) S.patch.L.val s ((Y p).V) := by
  have hx := pulling_meas i.1 b.V
  let a := (i.2.2.1,i.2.1)
  have hh j : Continuous fun p => T'.ellTerms a j (n:=c) p := by
    unfold PathData.ellTerms Slot.atSite expandAt; fun_prop
  unfold chiffon drain; apply Measurable.ite _ ((ip ((hh _).measurable.comp hx) ((hh _).measurable.comp hx)).div_const _) measurable_const
  by_cases hi : ¬(strip T' a.2 (till x) S.patch.L.val i.2.2.2.1 ∧ strip T' a.2 (till x) S.patch.L.val i.2.2.2.2)
  · unfold a at hi; dsimp only at hi; simp only [hi,not_false_eq_true,and_true]; exact hx (PathData.kept_closed ..).measurableSet
  unfold a at hi; dsimp only at hi; simp [hi]

omit he in
lemma treeWalk (hp : P.Funds S T) {σ C Λ δ w : ℝ} (R : Rep G f) (hR : R.Lawful σ C Λ δ w)
    (W : ℝ) (L : Finset ℕ) (s : Tab S) (hz : Measurable z) :
    Measurable fun p => leaf T x W R N L (Y p) (z p) s := by
  let Z p := cashB (Y p) R.beta (z p); let U p := (Y p).build (Z p)
  have hZ := b.pledges hp hv R.beta hz
  obtain ⟨h1,h2,h3⟩ := b.capes hv hZ W R.beta L R.activities hp
  have hk := hR.labels; have hU : Measurable U := b.buildField hZ
  rcases s with s| k|(l| (i|i|i)|i|i)| (i|i)|i|i
  · exact h1 s
  · exact (b.cloth hZ _).mul ((hR.labels.forced.meas k).comp hU)
  · exact ((Measurable.mul (Measurable.neg (b.cloth hZ _))
      ((masked_measurable _ _ _ (hk.regular.smooth l).borel).comp hU)).exp).sub measurable_const
  · exact ((Measurable.mul (measurable_const.mul (b.cloth hZ _)) ((masked_measurable _ _ _
      ((R.path.loop i.2.2).unmasked_cont i.2.1).measurable).comp (pulling_meas i.1 hU))).exp).sub measurable_const
  · exact ((Measurable.mul (measurable_const.mul (b.cloth hZ _)) ((masked_measurable _ _ _
      ((R.path.cubic i.2.2).unmasked_cont i.2.1).measurable).comp (pulling_meas i.1 hU))).exp).sub measurable_const
  · exact ((Measurable.mul (measurable_const.mul (b.cloth hZ _)) ((masked_measurable _ _ _
      ((R.path.quartic i.2.2).unmasked_cont i.2.1).measurable).comp (pulling_meas i.1 hU))).exp).sub measurable_const
  · exact ((Measurable.mul (measurable_const.mul (b.cloth hZ _)) (b.buttons_meas hZ _ _ _ i)).exp).sub measurable_const
  · exact ((measurable_const.mul (b.buttout _ _ _ i)).exp).sub measurable_const
  · exact h2 _
  · exact h3 _
  · exact b.screen hz i
  have hf := b.rotational hp hv
  change Measurable fun p => snapSale (Y p) _ R.beta (z p); unfold snapSale snapCharge
  apply Measurable.sub _ measurable_const; apply Measurable.exp; apply Finset.measurable_fun_sum; intro j _
  exact ((measurable_const.mul ((measurable_pi_apply (i,j)).comp
    ((vector_mul b.sheets.2 hf.2.2).add hf.2.1))).mul ((measurable_pi_apply _).comp hz))
end Bent
end YM.AnalyticNext.ConnectedActivity.Canvas
