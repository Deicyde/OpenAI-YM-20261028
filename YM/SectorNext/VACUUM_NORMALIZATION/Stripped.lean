import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.IntegralConvolution
import YM.Complex.Columns
import YM.SectorNext.VACUUM_NORMALIZATION.Noise
import YM.Source.Construction
import YM.Vac.Shelter



/-!
# Reading and stripping the actual vacuum scalar

The designated log here is real. The lower bound for the interacting
partition is EXPONENTIAL in the number of sites, with uniform per-site
cost on the actual trajectory. Likewise for the additional strict bounds
on log GAS itself (keep costs separate; at rare fields log magnitude may
also cost a beta, no proposal to pay source schedules with that).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open RG Shoot Wilson Lattice MeasureTheory Filter
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology
variable {G : Gauge} {c n : Side} {b : BudgetPoint}

/-- Number of physical sites in this *particular* density's torus. -/
def sites (n : Side) : ℝ := Fintype.card (Site n)
lemma site_pos (n : Side) : 0 < sites n := by
  unfold sites; exact_mod_cast (show 0 < Fintype.card (Site n) from Fintype.card_pos)
lemma wires_sites (n : Side) : wires n=sites n*4 := by simp [Edge,Axis,wires,sites]
lemma sites_ratio (S : StepData c n) : sites n = sites c * (S.patch.L.val : ℝ)^4 := by
  simp only [sites,site_card,S.sizes,Nat.cast_pow,Nat.cast_mul]; ring

private theorem blankCalm (n : Side) {r : ℝ} (h : 0≤r) : (1:Config G n)∈calm G n r := by
  intro i _; change G.chord 1 ≤ _; rw [G.chord_one]; linarith

private lemma chord_flat (p : Face (Per n)) : G.chord (faceValue (1:Config G n) p) = 0 :=
  le_antisymm (faceBound (blankCalm n le_rfl) _) (G.chord_nonneg _)
private lemma pull_flat (s : Signed) : pull s 0 (1:Config G n) = 1 := by
  funext i; unfold pull Step.read; split <;> simp
private lemma slot_flat (d : Slot) (x : Site n) : d.atSite (1:Config G n) x = 0 := by
  apply norm_le_zero_iff.mp
  unfold Slot.atSite Slot.eval; rw [G.norm_adjoint]; apply (G.curvature_norm _).trans
  let p := (d.offset,d.plaq)
  rw [show faceValue (expandAt x (1:Config G n)) p = faceValue (1:Config G n) (wrap n d.offset+x,d.plaq) from travel_at ..,chord_flat]
private lemma atom_flat {m : ℕ} [NeZero m] (A : Atom G m) (x : Site n) (p : BudgetPoint) :
    A.placed p (1:Config G n) x = 0 := by
  unfold Atom.placed
  by_cases he : Healthy p.threshold (A.footprint x) (1:Config G n)
  · rw [masked_eq _ _ _ _ he]
    unfold Atom.unmasked Atom.poly
    apply Finset.sum_eq_zero; intro i _
    rw [Finset.prod_eq_zero (Finset.mem_univ (0:Fin m)) (by dsimp only; rw [slot_flat]; rfl),mul_zero]
  rw [masked_ne _ _ _ _ he]
private lemma base_flat (R : PathData G) (C : Clip) (p : BudgetPoint) (x : Face (Per n)) :
    R.baseTerm C p (1:Config G n) x=0 := by
  simp only [PathData.baseTerm,PathData.clipped,chord_flat,PathData.ell,PathData.ellTerms,slot_flat,smul_zero,tsum_zero,norm_zero]
  split <;> split <;> ring
private theorem channels_flat (R : Rep G n) : R.path.inChannels R.clip R.p R.beta (1:Config G n) = 0 := by
  simp only [PathData.inChannels,pull_flat,PathData.principal,base_flat,PathData.atomSeries,atom_flat,tsum_zero,
    Finset.sum_const_zero,add_zero,mul_zero]

/-- The scalar really is fixed by the density, given the Rep receipt.
Countable coefficients and equality-case masks also here. -/
theorem flat_density {σ C Λ δ w : ℝ} (R : Rep G n) (h : R.Lawful σ C Λ δ w) :
    R.eval 1 = Real.exp R.scalar := by
  have ht : flags R.p.threshold (1:Config G n)=∅ := voids (blankCalm n R.p.threshold_pos.le) le_rfl
  have hm i : R.activities.regularOccurrence R.p i (1:Config G n)=0 := by
    rw [Activities.regularOccurrence, masked_eq _ _ _ _ (by simp [Healthy,ht]),h.labels.regular.at_flat]
  unfold Rep.eval Rep.exponent; rw [channels_flat, Activities.additive, Activities.gas_one _ _ ht]; simp [hm,Rep.scalar]



/-- Strip *only* the prescribed vacuum energy factor. -/
def stripped (R : Rep G n) (U : Config G n) := Real.exp (- R.scalar) * R.eval U

def strippedZ (R : Rep G n) := vacuumMass (stripped R)

theorem restore (R : Rep G n) (U : Config G n) : Real.exp R.scalar * stripped R U = R.eval U := by
  rw [stripped,←mul_assoc,←Real.exp_add]; simp



theorem stripped_int (R : Rep G n) {σ C Λ δ w : ℝ} (h : R.Lawful σ C Λ δ w) : Integrable (stripped R) (prior G n) := ((R.envelope h).integrable _).const_mul _













variable (A : History G) (h : A.Selected) (N p m : ℕ)
include h

lemma beta_positive (hm : m ≤ N) : 0 < A.β N p m :=
  (half_pos (zero_lt_one.trans (A.levels.fits.delayed m))).trans_le (h.represents N p m hm).band.1

theorem strictly (hm : m ≤ N) (U : Config G (A.S.side m p)) : 0 < (A.rep N p m).eval U := by
  rcases Nat.eq_or_lt_of_le hm with rfl|he
  · rw [(h.starts m p).2]; exact bare_pos ..
  rw [(h.steps N p m he).1]
  apply push_pos (A.levels.clock.op m p) (A.levels.blocks m p).branches
  · exact ((Rep.envelope _ (h.represents N p (m+1) he).good).integrable _)
  · exact History.nonnegative A h N p (m+1) he
  unfold vacuumMass; rw [A.partition_eq h N p (m+1) he]; exact partition_pos _














end YM.SectorNext.Vacuum
