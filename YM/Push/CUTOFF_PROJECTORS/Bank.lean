import YM.Next.EXTRACTION.Detector
import YM.Push.CUTOFF_PROJECTORS.Spectral

/-!
# Up to actual finite top tests

Provide more local estimates leading to the optional separation gate.
With (i) the top equation `x_N` coordinates read on the actual local
holonomy probes at N and (ii) a fixed triangular stencil model accurate **on
a finite list of those probes themselves** with a prescribed positive
tolerance (as suggested by ), prove the top margin for using
our gate, uniformly. We don't imply the tolerance is achieved, even along
any subsequence; costs, jet accuracy and the construction of the top
receipts themselves are substantial separate projects.

Require it as additional exact input; not automatic just by finding
some ComesFrom packet (e.g., how are supports and their possible wrapping
handled?). This assertion is needed here only on an equation parameter
basis; so is numerical accuracy. Use the probe **of the very same
family**, at finite torus anchor and threshold t_N; assess (ii) on jets with
*t_N* slot scaling before testing. Upper inputs may buy much better
powers, or test huge lists, but the list here and tolerance and downstream
singular value do not vary with N or p.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.CutoffProjectors
open Function Filter Next.Extract Next.Foundations Extraction Labels Lattice Source Wilson
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {d p N : ℕ} (F : Labels.Frame G d)

abbrev Lens (G : Gauge) (d : ℕ) := Jet G × Fin (d+1)

/-- Test linear functional on reference coefficients. -/
def probe (v : Lens G d) : F.Coeff →L[ℂ] ℂ :=
  let L := (tier (v.2:ℕ)).comp ((localFields G d).subtype.comp F.coords.symm.toLinearMap)
  ((v.2.val.factorial : ℂ) • ((Labels.read v.1).toLinearMap.comp L)).toContinuousLinearMap

lemma probe_eq (v : Lens G d) (x : F.Coeff) :
    probe F v x = iteratedDeriv (v.2:ℕ)
      (fun t => Labels.read (scaleJet v.1 t) (F.coords.symm x).val) 0 := by
  rw [deriv_read]
  change (v.2.val.factorial : ℂ) • (Labels.read v.1 (tier _ (F.coords.symm x).val)) = _
  simp only [Complex.real_smul, Complex.ofReal_natCast, smul_eq_mul]

/-- Finite computing bank, at each fixed level. Uses no Maxwell detector. -/
lemma probes_bound : ∃ (I : Finset (Lens G d)) (c : ℝ), 0 < c ∧ ∀ x : F.Coeff,
    c * ‖x‖ ≤ ∑ i ∈ I, ‖probe F i x‖ := by
  have he (x : F.Coeff) (h : ∀ i, probe F i x = 0) : x = 0 := by
    apply F.coords.symm.injective
    apply jet_test_ext; intro J k hk
    let i : Lens G d := (J,⟨k,Nat.lt_succ_of_le hk⟩)
    exact ((probe_eq F i x).symm.trans (h i)).trans ((probe_eq F i 0).symm.trans (map_zero (probe F i))).symm
  obtain ⟨I,c,hc,hu⟩ := finite_detectors (ContinuousLinearMap.id ℂ F.Coeff) (probe F) (fun x _ h => he x h)
  exact ⟨I,c,hc,fun x => by simpa using hu x⟩

def parameters (F : Labels.Frame G d) := Module.finBasis ℂ (equationSpace F)

namespace Packet
variable (E : Packet C d N p)

/-- Exact read assertion at N. Use only where fitted (E.ComesFrom,
nonwrapping along Campaign). Includes order 0/flat test; also *true*
smoothness condition along the probes as in Foundations.
-/
def TopTest (w : equationSpace (C.labels.level d)) :=
  let F := C.labels.level d
  let t : ℝ := C.path.levels.clock.threshold N
  JetTest C.params (0 : Site (C.side N p)) (F.coords.symm (F.scaled t⁻¹ (E.topEquation w)))
    ((C.S.a N:ℂ)^d • E.Jorigin w)

/-- Direct test on J. -/
def amount (w : equationSpace (C.labels.level d)) (i : Lens G d) : ℂ :=
  let t : ℝ := C.path.levels.clock.threshold N
  iteratedDeriv (i.2:ℕ) (fun h => (C.S.a N:ℂ)^d * E.Jorigin w
    (C.params.testLinks d (0 : Site (C.side N p)) (t • i.1) h)) 0

lemma probed (w : equationSpace (C.labels.level d)) (h : E.TopTest w) (i : Lens G d) :
    probe (C.labels.level d) i (E.topEquation w) = E.amount w i := by
  let F := C.labels.level d
  let t : ℝ := C.path.levels.clock.threshold N
  have ht : 0 < t := (C.path.levels.budget N).threshold_pos
  let v := E.topEquation w
  let u := F.scaled t⁻¹ v
  have hh (s : ℝ) : Labels.read (scaleJet (t • i.1) s) (F.coords.symm u).val =
      Labels.read (scaleJet i.1 s) (F.coords.symm v).val := by
    have hx : scaleJet (t • i.1) s = t • scaleJet i.1 s := funext fun j => smul_comm (s^(j+2)) t (i.1 j)
    rw [hx, ← read_frame_scaled (scaleJet i.1 s) F u t, show F.scaled t u = v from F.scaled_inv ht.ne' v]
  rw [probe_eq]
  have hv : E.amount w i = iteratedDeriv (i.2:ℕ)
      (fun h => Labels.read (scaleJet (t • i.1) h) (F.coords.symm u).val) 0 :=
    (h (t • i.1)).2.2 _ (Nat.le_of_lt_succ i.2.2)
  rw [hv]; simp_rw [hh]; rfl

/-- Additional exact and quantitative inputs. `T` fixed across cutoffs
in the application. No estimates on projected coordinates themselves. -/
structure Bill (T : Model (C.labels.level d)) (I : Finset (Lens G d)) (ε : ℝ) : Prop where
  reads (j) : E.TopTest (parameters (C.labels.level d) j)
  near (j) : let F := C.labels.level d
             ∀ i ∈ I, ‖E.amount (parameters F j) i - probe F i (T (parameters F j))‖ ≤ ε
end Packet

-- Precalculate positive tolerances; includes constants for actual coefficient test
-- basis and exact domain norm.
def priorFee : ℝ := 1 + ∑ i, ‖((parameters F).coord i).toContinuousLinearMap‖

lemma priorFee_pos : 0 < priorFee F := by unfold priorFee; positivity

lemma budget {η : ℝ} (L : Model F) (he : 0 ≤ η) (h : ∀ i, ‖L (parameters F i)‖ ≤ η) :
    ‖L‖ ≤ priorFee F * η := by
  let b := parameters F
  let Q := fun i => (b.coord i).toContinuousLinearMap
  refine L.opNorm_le_bound (mul_nonneg (priorFee_pos _).le he) fun x => ?_
  have hh i : ‖b.repr x i‖ ≤ ‖Q i‖*‖x‖ := (Q i).le_opNorm x
  nth_rw 1 [← b.sum_repr x]
  rw [map_sum]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ i, (‖Q i‖*η*‖x‖) := Finset.sum_le_sum fun i _ => by
      rw [map_smul, norm_smul, mul_right_comm]
      exact mul_le_mul (hh i) (h i) (norm_nonneg _) (by positivity)
    _ = (∑ i, ‖Q i‖)*η*‖x‖ := by simp_rw [Finset.sum_mul]
    _ ≤ priorFee F * η * ‖x‖ := by
      have hs : ∑ i, ‖Q i‖ ≤ priorFee F := by dsimp only [Q, priorFee,b]; linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs he) (norm_nonneg _)

/-- Pick a finite accuracy gate once, before claiming any cylinder tests
pass it. Then work with estimates at whichever cutoffs/periods are actually
served. The predicate supplied to Bank concerns *actual* local functions and
holonomy/linear jets only. -/
lemma within_fee (d : ℕ) (T : Model (C.labels.level d)) (σ : ℝ) (ht : 0 < σ) :
    ∃ (I : Finset (Lens G d)) (ε : ℝ), 0 < ε ∧ ∀ (N p) (E : Packet C d N p),
      E.Bill T I ε → ‖E.topEquation - T‖ ≤ σ := by
  let F := C.labels.level d
  obtain ⟨I,c,hc,hu⟩ := probes_bound F
  let r := σ / priorFee F
  let n : ℝ := I.card
  let ε := (c*r)/(1+n)
  have hn : 0 < 1+n := by dsimp [n]; positivity
  have hr : 0 < r := div_pos ht (priorFee_pos F)
  have hε : 0 < ε := div_pos (mul_pos hc hr) hn
  refine ⟨I, ε, hε, fun N p E h => ?_⟩
  have hi (i) : ‖(E.topEquation-T) (parameters F i)‖ ≤ r := by
    let v := parameters F i
    let w := E.topEquation v - T v
    have ha (j) (hj : j ∈ I) : ‖probe F j w‖ ≤ ε := by
      have hk : probe F j w = probe F j (E.topEquation v) - probe F j (T v) := map_sub ..
      rw [hk, Packet.probed E v (h.reads i)]
      exact h.near i j hj
    have hs := (hu w).trans (Finset.sum_le_sum (fun j hj => ha j hj))
    rw [Finset.sum_const,nsmul_eq_mul] at hs
    have hv : n*ε ≤ c*r := calc
      _ ≤ (1+n)*ε := by linarith
      _ = _ := by dsimp [ε]; field_simp
    exact le_of_mul_le_mul_left (hs.trans hv) hc
  exact (budget F _ hr.le hi).trans (le_of_eq (by dsimp only [r]; field_simp [(priorFee_pos F).ne']))

/-- The full optional positive lower gate up to finite hypotheses. -/
theorem spectral_bank (d : ℕ) (T : Model (C.labels.level d)) (ht : triangular T) :
    ∃ (I : Finset (Lens G d)) (ε c : ℝ), 0 < ε ∧ 0 < c ∧ ∀ (N p) (E : Packet C d N p),
      E.Bill T I ε → C.Makes → ∀ W : Bid.Worth, Bid.Bank W C.path.levels →
        Bid.roomCost C.path.levels W → E.Compares W → E.Separation c := by
  let F := C.labels.level d
  obtain ⟨r,hr⟩ := has_floor T (triangular_injective _ ht)
  obtain ⟨I,ε,hε,hh⟩ := within_fee d T (r/2) (half_pos hr.1)
  exact ⟨I,ε,(r/2)/(Packet.loss F),hε,div_pos (half_pos hr.1) (Packet.loss_pos F),fun N p E h H _ he hw hx =>
    (hr.perturb (hh N p E h)).separation hx he hw H⟩


end YM.Push.CutoffProjectors
