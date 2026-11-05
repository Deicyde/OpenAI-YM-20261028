import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Factor
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical

set_option warningAsError false

/-!
# Measurability and compact-bounds for the packet and arrears

``compact'' bounds here purely a finite-period L¹ justification in use
at restricted support. No small-sector prices being inferred from such
envelopes. Need the actual masks and tails for this, including at kinks.
V fixed Y,z both variable. The hypothesis `Continuous m` holds in the
prescribed application at such level, NOT asserting it on V changes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus
open Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree
    YM.Push.SectorMeasure Oriented Exterior Bloch Next.SectorChange Set MeasureTheory Metric Presented Matrix
    Next.Fluctuations
open YM.SectorNext.Remainder (onWindow)
open YM.SectorNext.Remainder.Affine
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}

section moderate
variable {X : Type} [TopologicalSpace X] [MeasurableSpace X]

structure Modest (g : X → ℝ) : Prop where
  reads : Measurable g
  localCost (s : Set X) (h : IsCompact s) : ∃ C : ℝ,∀ i ∈ s, ‖g i‖ ≤ C

lemma good [BorelSpace X] {g : X → ℝ} (h : Continuous g) : Modest g := by
  refine ⟨h.measurable,fun s hs => ?_⟩
  obtain ⟨c,hc⟩ := (hs.image h.norm).bddAbove
  exact ⟨c,fun i hi => hc (Set.mem_image_of_mem _ hi)⟩

namespace Modest
variable {a b : X → ℝ}

lemma flat (c : ℝ) : Modest (fun _ : X => c) := ⟨measurable_const,fun _ _ => ⟨‖c‖,fun _ _ => le_rfl⟩⟩
lemma coated (ha : Envelope a) : Modest a := ⟨ha.meas,fun _ _ => ⟨ha.cost.choose,fun i _ => ha.cost.choose_spec i⟩⟩
lemma add (ha : Modest a) (hb : Modest b) : Modest (fun x => a x+b x) := by
  refine ⟨ha.reads.add hb.reads,fun s h => ?_⟩
  obtain ⟨c,hc⟩ := ha.localCost s h; obtain ⟨b,hb⟩ := hb.localCost s h
  exact ⟨c+b,fun i hi => (norm_add_le ..).trans (add_le_add (hc _ hi) (hb _ hi))⟩
lemma neg (ha : Modest a) : Modest (fun x => -a x) := by
  refine ⟨ha.reads.neg,fun s h => ?_⟩; simpa only [norm_neg] using ha.localCost s h
lemma mul (ha : Modest a) (hb : Modest b) : Modest (fun x => a x*b x) := by
  refine ⟨ha.reads.mul hb.reads,fun s h => ?_⟩
  obtain ⟨c,hc⟩ := ha.localCost s h; obtain ⟨d,hd⟩ := hb.localCost s h
  exact ⟨c*d,fun i hi => (norm_mul ..).trans_le (mul_le_mul (hc _ hi) (hd _ hi) (norm_nonneg _) ((norm_nonneg _).trans (hc _ hi)))⟩
lemma exp (ha : Modest a) : Modest (fun x => Real.exp (a x)) := by
  refine ⟨ha.reads.exp,fun s h => ?_⟩
  obtain ⟨c,hc⟩ := ha.localCost s h; exact ⟨_,fun i hi => (Real.norm_of_nonneg (Real.exp_pos _).le).trans_le
    (Real.exp_monotone ((le_abs_self _).trans (hc i hi)))⟩
lemma sum {ι : Type} (s : Finset ι) (a : ι → X → ℝ) (h : ∀ i,Modest (a i)) : Modest (fun x => ∑ i ∈ s, a i x) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using flat 0
  | insert i s hi ih => simpa only [Finset.sum_insert hi] using (h i).add ih
lemma mean (a : Signed → X → ℝ) (h : ∀ i,Modest (a i)) : Modest (fun x => averaged fun i => a i x) :=
  (flat _).mul (sum _ a h)
end Modest
end moderate

abbrev PaintBox (G : Gauge) (A : Stores S) (x : ℝ) (F : Forest S.ratio) :=
  LinkArray G (Frozen A x F) × Prices G (Active A x F)

namespace Borel
variable (T : Tube G S) (x w : ℝ) (V : Config G c) (A O : Stores S) (k : S.Choices)
    (F : Forest S.ratio) (D : ℕ) (p q : Chi) (J : ChartRatio G) (d β : ℝ)
    (m : LinkArray G (Frozen A x F) → Prices G (Active A x F))
    (C : Gaussian.Table (Rows.In x A F (G:=G)))

lemma rated {X : Visits S} (hb : S.patch.Branches S.kernel G) : Envelope (fun U : Config G f => tagRate X k U) := by
  refine ⟨?_,_,fun i => (Real.norm_of_nonneg (rate_cost ..).1).trans_le (rate_cost ..).2⟩
  have hl (i : Site c) : Measurable (fun U : Config G f => expandAt (S.ratio.embed i) U) :=
    (show Continuous (fun U : Config G f => expandAt (S.ratio.embed i) U) by unfold expandAt; fun_prop).measurable
  unfold tagRate frameRate bondRate
  refine (Finset.measurable_fun_prod _ fun i _ => ?_).mul (Finset.measurable_fun_prod _ fun i _ => ?_)
  · exact measurable_const.mul ((S.patch.frameMass_meas _).comp (hl i))
  exact measurable_const.mul ((S.patch.predictorMass_meas _).comp (S.connector_meas hb k.1 i))

lemma posted_env (X : Visits S) (hb : S.patch.Branches S.kernel G) : Envelope (fun U => border X A q x w U V k) := by
  have he {ι : Type} [DecidableEq ι] (s : Finset ι) (d : ℝ) (r : (Config G f) → ℝ) (hr : Measurable r) (i : ι) :
      Measurable (fun x => Seed.piece q s d (r x) i) := by
    have hh : Measurable (fun x => q.innerShare d (r x)) := q.smooth.continuous.measurable.comp ((hr.div_const _).pow_const 2)
    unfold Seed.piece; split
    · exact measurable_const.sub hh
    exact hh
  refine ⟨?_,1,fun i => (Real.norm_of_nonneg (border_range ..).1).trans_le (border_range ..).2⟩
  unfold border
  exact measurable_const.mul ((Finset.measurable_fun_prod _ fun i _ => he _ _ _ (toll_meas i measurable_id) i).mul
    (Finset.measurable_fun_prod _ fun i _ => he _ _ _ (wire_meas k i hb measurable_id measurable_const) i))

set_option maxHeartbeats 700000 in
lemma work_env (X : Window S) {P : Teller G} (hp : P.Funds S T) : Envelope (fun U => X.work T x U k V) := by
  obtain ⟨a,b,ha,hb⟩ := hp.feeds
  rw [← hp.high] at ha
  let t := fiery G x S.patch.L; let R := till x
  let H := S.prediction (G:=G)
  have hF (i : Cell f) : Envelope (fun U : Config G f => T.workF R U V t (temp x) i) := by
    unfold workF
    exact (env_crown ha _ _ _ _).add (Envelope.sum _ _ (fun j => Env.compact
      (continuous_const.sub (continuous_const.inner (plotted_cont ha ..)))))
  have hI (i : Bond c) : Envelope (fun U : Config G f => T.workI R (H U k) V (temp x) i) := Env.along
    (Env.compact (show Continuous (fun Q : Config G c => T.workI R Q V (temp x) i) by unfold workI monetary wire Z; fun_prop))
    (S.prediction_meas (funds_branch hp) k)
  have hL (i : Cell c) : Envelope (fun U : Config G f => T.workL R U (H U k) V (temp x) i) := by
    let L (u : Config G f × Config G c) := T.workL R u.1 u.2 V (temp x) i
    have he : Continuous L := by
      unfold L workL unzip Z
      have h (a : Twin f) := plotted_cont ha R 1 a; unfold Xf; fun_prop
    have hh : Measurable (fun u : Config G f => (u,S.prediction u k)) := measurable_id.prodMk (S.prediction_meas (funds_branch hp) k)
    change Envelope (fun u : Config G f => L (u,S.prediction u k))
    exact Env.along (F:=L) (g:=fun u : Config G f => (u,S.prediction u k)) (Env.compact he) hh
  unfold Window.work onWindow
  exact (((Envelope.sum _ _ hF).add (Envelope.sum _ _ hI)).add
    (Envelope.sum X.coarse _ fun i => (Envelope.const _).add ((hL i).add (Envelope.const _)))).add (Envelope.const _)

variable (hm : Continuous m)

def colorize (i : PaintBox G A x F) := m i.1 + coupling β • i.2
include hm
lemma colorized : Continuous (colorize x A F β m) := (hm.comp continuous_fst).add (by fun_prop)

lemma entrances : Measurable (fun i : PaintBox G A x F => physical A F V i.1 (tape (colorize x A F β m i))) :=
 by
  let K (i : PaintBox G A x F) := (i.1,tape (colorize x A F β m i))
  have hK : Measurable K := measurable_fst.prodMk (tape.measurable.comp (colorized x A F β m hm).measurable)
  change Measurable ((Function.uncurry (physical (x:=x) A F V)) ∘ K)
  exact (physical_meas A F V).comp hK

variable {P : Teller G} (hP : P.Funds S T) (hd : 0<d)
include hP hd

lemma openings (h : LocalRatio J) (he : 4*d<J.radius) (X : Visits S) (N : Finset (Active A x F)) :
    Modest (fun i : PaintBox G A x F => releaseOn x w V A k F p q J d β m i.1 i.2 X N) := by
  have he1 : Continuous (fun i : PaintBox G A x F => tape (colorize x A F β m i)) := gaugeCount.continuous.comp (colorized x A F β m hm)
  let θ (i : PaintBox G A x F) := tape (colorize x A F β m i)
  have hl : Continuous (fun i => jacob J q d N (θ i)) := by
    refine continuous_finsetProd _ fun j _ => ?_
    have hm : Continuous (fun i => θ i j) := (continuous_apply j).comp he1
    exact ((extended_smooth q h hd he).continuous.comp hm).mul ((broad_smooth q _).continuous.comp hm)
  let H := (funds_branch hP)
  let U (i : PaintBox G A x F) := physical A F V i.1 (θ i)
  have hm : Envelope (fun i => border X A p x w (U i) V k * tagRate X k (U i)) := Env.along (g:=U)
    ((posted_env x w V A k p X H).mul (rated k H)) (entrances x V A F β m hm)
  change Modest (fun i => jacob J q d N (θ i) * (border X A p x w (U i) V k * tagRate X k (U i)))
  exact (good hl).mul (Modest.coated hm)

variable (hg : 2*d<firstRadius G)
include hg

omit hm in
lemma squares_cont (s : Signed) (X : Window S) :
    Continuous (fun i : PaintBox G A x F => squares T x V k A F q d i.1 i.2 s X) := by
  obtain ⟨l,e,h,-⟩ := hP.feeds
  let B := PaintBox G A x F
  let H (i : B) := Rows.lands T x V k (shots S x) A F q d i.1 i.2
  have hf : Continuous (H) := by
    unfold H Rows.lands
    apply Continuous.add continuous_const
    let M : Directions G f →ₗ[ℝ] LogArray G (Slots S) :=
      { toFun := Rows.bump T x V k, map_add' := Rows.bump_add T x V k h,
        map_smul' := fun w a => Rows.bump_smul T x V k h a w }
    have hm : Continuous (Rows.bump T x V k) := M.continuous_of_finiteDimensional
    refine hm.comp (Continuous.add ?_ ?_)
    · have hi : Continuous (Rows.input x A F (G:=G)) := by
        apply continuous_pi; intro i
        unfold Rows.input; split
        · split <;> fun_prop
        fun_prop
      exact hi.comp ((autoShell_continuous q hd hg).comp (continuous_const.prodMk continuous_fst))
    have hi : Continuous (Rows.fresh x (shots S x) A F (G:=G)) := by
      apply continuous_pi; intro i
      unfold Rows.fresh; split
      · split <;> fun_prop
      fun_prop
    exact hi.comp (gaugeCount.continuous.comp continuous_snd)
  have hr (i : Slots S) : Continuous (fun j : B => ‖H j i‖^2/2) := (((continuous_apply i).comp hf).norm.pow _).div_const _
  unfold squares; refine Continuous.add (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_)
    (continuous_finsetSum _ fun i _ => ?_)
  · unfold Rows.chargedUp; split
    · exact hr _
    fun_prop
  unfold Rows.chargedSide; split
  · exact hr _
  fun_prop

lemma debts (s : Signed → Window S) :
    Modest (fun i : PaintBox G A x F => labor T x V A k F q d β m i.1 i.2 s) := by
  let B := PaintBox G A x F
  let a := colorize x A F β m
  let U i := physical A F V i.1 (tape (a i))
  have hv t : Modest (fun i : B => debris T x V k A F q d i.1 (a i) (U i) t (s t)) := by
    have heU : Measurable (fun i => pull t 0 (U i)) := (continuous_pull ..).measurable.comp (show Measurable U from entrances x V A F β m hm)
    have he : Envelope (fun i : B => (s t).work T x (pull t 0 (U i)) (choice t k) (pull t 0 V)) :=
      Env.along (g:=fun i => pull t 0 (U i)) (work_env T x (pull t 0 V) (choice t k) (s t) hP) heU
    have hi : Continuous (fun i : B => squares T x V k A F q d i.1 (a i) t (s t)) :=
      (squares_cont T x V A k F q d hP hd hg t (s t)).comp (f:=fun i : B => (i.1,a i))
        (continuous_fst.prodMk (show Continuous a from colorized x A F β m hm))
    simp only [debris,sub_eq_add_neg]; exact Modest.add (Modest.coated he) (Modest.neg (good hi))
  let L (i : B) := averaged (fun t => squares T x V k A F q d i.1 (m i.1) t (s t))
  have hH t : Continuous (fun i : B => squares T x V k A F q d i.1 (m i.1) t (s t)) :=
    (squares_cont T x V A k F q d hP hd hg t (s t)).comp (f:=fun i : B => (i.1,m i.1))
      (continuous_fst.prodMk (hm.comp continuous_fst))
  have hC : Modest L := Modest.mean _ (fun t => good (hH t))
  unfold labor; dsimp only; simp only [sub_eq_add_neg,div_eq_mul_inv]
  exact (((Modest.flat _).mul (Modest.mean _ hv)).add (hC.mul (Modest.flat _)).neg)

lemma moves : Continuous (fun i : PaintBox G A x F => shiftRisk T x V A k F q d β m C i.1 i.2) := by
  obtain ⟨l,e,h,-⟩ := hP.feeds
  have ht := Rows.source_continuous T x V k (shots S x) A F q d h hd hg
  unfold shiftRisk Rows.eta Rows.blame dotProduct mulVec dotProduct; fun_prop

lemma packet_tested (h : LocalRatio J) (he : 4*d<J.radius) : Modest (Function.uncurry (packet T x w V A O k F D p q J d β m)) := by
  unfold packet Function.uncurry
  exact (openings T x w V A k F p q J d β m hm hP hd h he _ _).mul
    ((((debts T x V A k F q d β m hm hP hd hg _).add (Modest.flat _)).add (Modest.flat _)).exp)

lemma outside_tested (h : LocalRatio J) (he : 4*d<J.radius) : Modest (Function.uncurry (outsider T x w V A O k F D p q J d β m C)) := by
  unfold outsider Function.uncurry
  exact (openings T x w V A k F p q J d β m hm hP hd h he _ _).mul
    ((((((debts T x V A k F q d β m hm hP hd hg _).add (Modest.flat _)).add (Modest.flat _)).add (Modest.flat _)).add
      (good (moves T x V A k F q d β m C hm hP hd hg))).exp)
lemma arrears (h : LocalRatio J) (he : 4*d<J.radius) (R : Rep G f) {σ E Λ δ w'} (hR : R.Lawful σ E Λ δ w') :
    Modest (fun i : PaintBox G A x F => owing T x w V A O k F D p q J d m C i.1 i.2 R) := by
  unfold owing; exact (outside_tested T x w V A O k F D p q J d R.beta m C hm hP hd hg h he).mul
    (Modest.coated (Env.along (env_exposed R hR _) (entrances x V A F R.beta m hm)))
end Borel
end YM.AnalyticBridge.Annulus
