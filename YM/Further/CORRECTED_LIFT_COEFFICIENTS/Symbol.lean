import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.LensBill
import YM.Push.CORRECTED_COLUMNS.Assembly
import YM.Push.CORRECTED_COLUMNS.Funding

/-!
# Symbol calibration, all tests on the same C

Several charts/path conventions may be used, to implement e.g. exact
signed symmetry by averaging. Weighted on *these same* primary tuples;
no credit for an equivariant scan bought after the placement/propagation
price. `Faith.signs` costs exact equivariance on the symbol polynomials.
See also symmetry sufficient-condition options. `tight` is explicit numerical
gate (paths, number of slots, schedule, calibration chart and covariance
costs), not a hypothesis about c.v/tune or tested arrays.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift
open Filter Function Lattice Wilson RG Source Source.Drops Labels Next.Extract Extraction
open Push.Corrected Push.Corrected.Issue Push.CutoffProjectors Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {C : Family G} {d m k N p t : ℕ}

/-- Ex ante probe budget (no dependency on cutoffs or charts). -/
def lenses (C : Family G) (d : ℕ) : Finset (Lens G d) := (probes_bound (C.labels.level d)).choose
def angle (C : Family G) (d : ℕ) : ℝ := (probes_bound (C.labels.level d)).choose_spec.choose



/-- One calibrated matrix construction: use average over Signed paths at
origin; single paths repeatable by taking `const ...`. The WHOLE matrix is
paid under the error bound. -/
structure Portfolio (C : Family G) (m p t : ℕ) where
  sheets : Signed → Screen C m p t
  stock : Copper G (C.side m p)



namespace Portfolio
variable (A : Portfolio C m p t)

def lump : ℝ := Fintype.card Signed
lemma lump_pos : 0 < lump := Nat.cast_pos.mpr Fintype.card_pos

def gather (N : ℕ) (v : C.label d) (r : ℝ) : Pol G := (lump:ℂ)⁻¹ • ∑ s, (A.sheets s).rows A.stock r v N

-- Attest on actual finite symbols, after any path/k-symmetrization.
-- θ,g are of the chosen history; even the `Paid` check uses its Σ.
structure Faith (d N : ℕ) : Prop where
  traced s : Resolution C d N (A.sheets s)
  hue (v : C.label d) : A.gather N v 1∈ invariantSpace G
  signs s (v : C.label d) : A.gather N (turn (C.labels.level d) s v) 1 = rotated (Signed.inclusionO s) (A.gather N v 1)
  real (v : C.label d) : A.gather N (star v) 1 = conjPol (A.gather N v 1)

-- cap engine map.
private lemma comparator (d : ℕ) (X Y : Jet G) {x y : Pol G}
    (h : ∀ r : ℝ, Labels.read (scaleJet X r) x = Labels.read (scaleJet Y r) y) :
    Labels.read X (capRead d x) = Labels.read Y (capRead d y) := by
  unfold capRead; rw [map_sum,map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  apply smul_right_injective ℂ (show (i.factorial:ℝ) ≠ 0 by positivity)
  simp only
  rw [← deriv_read,←deriv_read]; simp_rw [h]





def writer (e : A.Faith d N) (h : C.Makes) (r : ℝ) : C.label d →ₗ[ℂ] Pol G :=
    let V := (lump:ℂ)⁻¹ • ∑ s, (A.sheets s).mapper A.stock h (e.traced s) r
    (∑ i∈Finset.range (d+1), tier (G:=G) i).comp V

lemma writer_eq (e : A.Faith d N) (h : C.Makes) (r : ℝ) (v : C.label d) :
    A.writer e h r v = capRead d (A.gather N v r) := by simp_rw [writer,gather]; simp [Screen.scanned,capRead]





lemma eligible (e : A.Faith d N) (h : C.Makes) (v : C.label d) :
    A.writer e h 1 v ∈ localFields G d := by
  rw [writer_eq]; refine ⟨cap_limited ..,?_⟩
  intro J u; refine comparator d _ _ fun r => ?_
  rw [show scaleJet (colored u J) r=colored u (scaleJet J r) from funext fun i => (map_smul (Taylor.paint u) _ _).symm]; exact e.hue v _ _

def stamp (e : A.Faith d N) (h : C.Makes) :=
    (A.writer e h 1).codRestrict _ (fun v => A.eligible e h v)

/-- Actual scan matrix from finite k tensors. -/
def readout (e : A.Faith d N) (h : C.Makes) : Mat C d :=
    ((C.labels.level d).coords.toLinearMap.comp (A.stamp e h)).toContinuousLinearMap

lemma reads (a : Lens G d) (e : A.Faith d N) (h : C.Makes) (v : C.label d) :
    probe (C.labels.level d) a (A.readout e h v)=probeJet a (A.gather N v 1) := by
  let F := C.labels.level d; let s := A.stamp e h
  change probe F a (F.coords (s v))=_
  rw [probe_eq,F.coords.symm_apply_apply]; simp_rw [show (s v).val=capRead .. from A.writer_eq e h 1 v,probeJet_value,deriv_read]
  rw [tier_capRead _ _ _ (Nat.le_of_lt_succ a.2.isLt)]





lemma first (e : A.Faith d N) (h : C.Makes) : A.readout e h (C.refUnit d)=(C.labels.level d).e0 := by
  let F := C.labels.level d; let S := A.stamp e h
  have hz : S (C.refUnit d)=unit G d := by
    apply Subtype.ext; change A.writer e h _ _=1; rw [writer_eq]
    unfold gather; simp_rw [show ∀ s, (A.sheets s).rows A.stock 1 (C.refUnit d) N=1 from fun s => (A.sheets s).rows_unit A.stock h (e.traced s) 1,
      Finset.sum_const, Finset.card_univ]
    have he : (lump:ℂ) ≠ 0 := by exact_mod_cast lump_pos.ne'
    rw [← Nat.cast_smul_eq_nsmul ℂ,show (↑(Fintype.card Signed):ℂ)=(lump:ℂ) by simp [lump],smul_smul,inv_mul_cancel₀ he,one_smul]; exact limited_cap d _ (unit G d).property.1
  change F.coords _=_
  rw [show F.coords (S _)=_ from congr_arg F.coords hz]; exact F.coords_unit

def charge (a : Lens G d) := lump⁻¹ * ∑ s, (A.sheets s).bill A.stock a

theorem paid (a : Lens G d) (e : A.Faith d N) (h : C.Makes) (v : C.label d) :
    ‖probe (C.labels.level d) a (A.readout e h v) - probe (C.labels.level d) a (primary C v m N p)‖ ≤
      A.charge a * ‖primary C v m N p‖ := by
  let f (s : Signed) := probeJet a ((A.sheets s).rows A.stock 1 v N); let g := probe _ a (primary C v m N p)
  have ht : probe (C.labels.level d) a (A.readout e h v) = (lump:ℂ)⁻¹ • ∑ s,f s := by rw [reads,gather,map_smul,map_sum]
  have hh : g=(lump:ℂ)⁻¹ • ∑ _s : Signed, g := by
    have hq : (Fintype.card Signed:ℂ)≠0 := by exact_mod_cast Fintype.card_pos.ne_zero
    simp [lump,hq]
  change ‖_-g‖ ≤ _; rw [ht]; nth_rw 1 [hh]
  rw [←smul_sub,←Finset.sum_sub_distrib,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg lump_pos.le]
  unfold charge; rw [mul_assoc, Finset.sum_mul]; exact mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans
    (Finset.sum_le_sum fun i _ => (A.sheets i).each_price A.stock h v (e.traced i) a)) (inv_nonneg.mpr lump_pos.le)

/-- Needs the numerical affordability on THIS family / volume. May be per
volume, in cutoffs where `Analyzed` to be used. Handle tiny p with padding. -/
def tight (d : ℕ) (δ' : ℝ) := ∑ a∈lenses C d, A.charge a ≤ angle C d*δ'





/- A positive lower margin on actual primary x, not desired label lifts. -/

end Portfolio
end YM.Further.CorrectedLift
