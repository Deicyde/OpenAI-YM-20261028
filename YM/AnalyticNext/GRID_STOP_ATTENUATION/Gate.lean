import YM.Next.MULTISOURCE.OneRate
import YM.Next.MULTISOURCE.Tome
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.RELAY_DIFFERENCE.TwoSided

set_option warningAsError false

/-!
# Local susceptibility requirements

Analogous to `Multi.Adjoining`, but at the signed-source step; its
singleton outputs must be the chosen signed comparison pulses.

No radius on the output in this estimate, no simultaneous sum or
Bills/Holds, no scaled signal of an ordered history interval.

We will
ask this only at individual steps, retaining the costs even if the output
probes cost more than the norm of the raw pushed function (no divided
physical densities used).

Test on the actual joint responses to proper
subsets; no inference from separate evolutions at different cutoffs or
agreement of singleton coordinates alone.

We can even ask a normalized version before engineering
scaling and costing outputs at marker radii.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Stepwise
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {V : Type} [DecidableEq V] [Fintype V] (R : Census V)
variable {G : Gauge}

abbrev Foci (R : Census V) (G : Gauge) (n : Side) := Hot R → Pulse G n

/-- `M` can be a prescribed comparison
singleton: in that case a producer must keep the same signed remainders for
its singleton operations even at fine Combo->Pulse re-expression, or account
for the change in prescription at all the other primitive responses.

Do not
require *all* possible M's when using this type as an input on an actual
problem!

The universal prescription, even with an exponent +4 on
output-singles and full geometric price gates, has not been shown feasible. -/
def UnitTest (C : Family G) (i N p : ℕ) (o : V→Site (C.side i p)) (D : Foci R G (C.side (i+1) p))
    (M : V → Pulse G (C.side i p)) (b : ℝ) :=
    ∃ Z : Hot (parts R) → Pulse G (C.side i p), (∀ x : V, Z (Multi.Step.polyse R x) = M x) ∧
      ∀ q, 2 ≤ (unionOfHot q).sites.card →
        Raw (C.path.levels.clock.op i p) (C.path.rep N p i) (C.path.rep N p (i+1)) Z D b (money C.path.levels i) (fun _ => 1) o q

def splitNorm (R : Census V) {G : Gauge} {n : Side} (D : Foci R G n) (k : Hot R→ℝ) (u : Hot R) :=
    Multi.Step.normalize (D u) (k u)

def outNorm (R : Census V) {G : Gauge} {n : Side} (M : V → Pulse G n) (L : ℝ) (k : Hot R→ℝ) (i : V) :=
    (L:ℂ)⁻¹ • Multi.Step.normalize (M i) (k (Hot.one R i))

variable {R} {C : Family G} {i N p : ℕ} {L a ℓ u b κ : ℝ} {o : V→Site (C.side i p)}
variable {D : Foci R G (C.side (i+1) p)} {M : V→Pulse G (C.side i p)} {k : Hot R → ℝ}

omit [Fintype V] in
lemma norm_self (hL : 0<L) (hk : ∀ i, 0<k (Hot.one R i)) (i : V) :
    (L:ℂ) • ((k (Hot.one R i):ℂ) • outNorm R M L k i) = M i := by
  have hL' : (L:ℂ)≠0 := by exact_mod_cast hL.ne'
  have hk' : ((k (Hot.one R i):ℝ):ℂ)≠0 := by exact_mod_cast (hk i).ne'
  unfold outNorm Multi.Step.normalize; rw [smul_comm (k (Hot.one R i):ℂ),smul_inv_smul₀ hL',smul_inv_smul₀ hk']

omit [Fintype V] in
lemma unscale (H : C.Makes) (he : i<N) (hL : 0<L) (_hk : ∀ i,0<k (Hot.one R i))
    (hD : ∀ x : Hot R, Multi.Credit (C.path.rep N p (i+1)).p 0 (money C.path.levels (i+1))
      (x.sites.image ((C.path.levels.clock.op i p).ratio.embed ∘ o)) (D x) (k x))
    (hM : ∀ x, tangent (C.path.rep N p i) (M x) =
      (L:ℂ) • (C.path.levels.clock.op i p).push (C.path.β N p (i+1)) (tangent (C.path.rep N p (i+1)) (D (Hot.one R x))))
    (x : V) : tangent (C.path.rep N p i) (outNorm R M L k x) =
      (C.path.levels.clock.op i p).push (C.path.β N p (i+1))
        (tangent (C.path.rep N p (i+1)) ((splitNorm R D k) (Hot.one R x))) := by
  let y := Hot.one R x
  have hC : (L:ℂ)≠0 := by exact_mod_cast hL.ne'
  have hf := hM x; unfold splitNorm outNorm Multi.Step.normalize
  rw [tangent_scale,tangent_scale,tangent_scale,hf,StepData.push_smul,smul_comm (L:ℂ)⁻¹ ((k (Hot.one R x):ℝ):ℂ)⁻¹,inv_smul_smul₀ hC]
  rw [← first_jet _ (H.wilson.represents _ _ _ he).good.labels D (parts R)]
  exact evaluate_int _ (H.wilson.represents _ _ _ he).good D hD _

omit [Fintype V] in
/-- Like the dilation calculation of Multi.Step.fixed, but for a paid
matched singleton prescription. -/
theorem scale (H : C.Makes) (he : i<N) (hL : 0<L) (hk : ∀ i,0<k (Hot.one R i))
    (hD : ∀ x : Hot R, Multi.Credit (C.path.rep N p (i+1)).p 0 (money C.path.levels (i+1))
      (x.sites.image ((C.path.levels.clock.op i p).ratio.embed ∘ o)) (D x) (k x))
    (h : UnitTest R C i N p o (splitNorm R D k) (outNorm R M L k) b) :
    ∃ Z : Hot (parts R) → Pulse G (C.side i p), (∀ x : V,(L:ℂ) • Z (Multi.Step.polyse R x) = M x) ∧
      ∀ q, 2 ≤ (unionOfHot q).sites.card →
        Raw (C.path.levels.clock.op i p) (C.path.rep N p i) (C.path.rep N p (i+1)) Z D b (money C.path.levels i) k o q := by
  obtain ⟨Z,hZ,hw⟩ := h
  let A := C.path.levels; let S := A.clock.op i p; let P := C.path.rep N p i; let Q := C.path.rep N p (i+1)
  let Y := splitNorm R D k
  let f (x : Hot R) := (k x:ℂ)
  let T := ampl f Z
  have hℓ := (H.wilson.represents N p (i+1) he).good
  have hP := (H.wilson.represents N p i he.le).good
  have hu x := Multi.Step.normalizeCredit (D x) (hD x)
  refine ⟨T,fun x => ?_,fun q hq => ?_⟩
  · unfold T ampl; rw [show (Multi.Step.polyse R x).sites = {Hot.one R x} from rfl,Finset.prod_singleton,hZ]; exact norm_self hL hk _
  obtain ⟨ht,hi⟩ := hw q hq
  change tangent P _ = _ ∧ _
  constructor
  · have hg : jet Q (parts R) D q.val=(∏ t∈q.sites,f t) • jet Q (parts R) Y q.val :=
      (congrArg (fun F => jet Q (parts R) F q.val) (show D=(fun x => f x • Y x) from funext fun x => (hu x).2)).trans (ampl_jet ..)
    have hr (U : Config G (C.side i p)) : (many P (parts R) Z U).part q.val=S.push Q.beta (jet Q (parts R) Y q.val) U := by
      rw [jet_account P Z hP.labels q]; rw [ht]; unfold defect; rw [sub_add_cancel]
    funext U
    unfold defect
    rw [hg, StepData.push_smul _ _ _ _ (evaluate_int Q hℓ Y (fun i => (hu i).1) q.val), Pi.smul_apply,smul_eq_mul,
      ← hr U, show (∏ t∈q.sites,f t)*(many P (parts R) Z U).part q.val=(many P (parts R) T U).part q.val from (dilation_part ..).symm.trans (by rw [amplify]),
      jet_account P T hP.labels q, add_sub_cancel_right]
  refine Multi.Credit.expand (hi.scale (∏ t∈q.sites,f t)) ?_
  have hReal (i) : ‖k i‖=k i := Real.norm_of_nonneg (hD i).2.2.2.1
  simp only [f,norm_prod,Complex.norm_real,hReal,Finset.prod_const_one,mul_one]
  exact (mul_comm ..).le


end YM.AnalyticNext.GridStop.Stepwise
