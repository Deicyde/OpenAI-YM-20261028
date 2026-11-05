import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Next.FOUNDATIONS.SU2
import YM.Org.Theatre
import YM.Pressure.Seeds

set_option warningAsError false

/-!
# Source derivative convention

Realized here also as actual ordinary real-amplitude mixed derivatives. Use
the multiaffine representative of the **specified source density** (with all
λ_i² and forbidden monomials truncated, ). Not plugging numbers into
the factors before doing marker multiplication; that in general gives a
different function. Reusing a physical observable in a source word uses
different marker names; repeating the SAME amplitude derivative instead gives
zero in this lift. These are not derivatives in beta or V. Hard indicators
are not differentiated!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Marked.SourceJet
open Function Filter Lattice Wilson RG MeasureTheory Overlay Marker Finset
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {I : Type*} [DecidableEq I] {B : Census I}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Successive partial derivatives with the head outermost. -/
def mixed (f : (I → ℝ) → X) : List I → (I → ℝ) → X
  | [], t => f t
  | i::l, t => deriv (fun s : ℝ => mixed f l (t + Pi.single i s)) 0

def rest (l : List I) (p : B.Mode) (t : I → ℝ) : ℝ :=
    if l.Nodup ∧ l.toFinset ⊆ p.val then ∏ i∈ p.val \ l.toFinset,t i else 0

def read (g : B.Mode → X) (l : List I) (t : I → ℝ) := ∑ p, rest l p t • g p

def lift (g : B.Mode → X) : (I → ℝ) → X := read g []



private lemma held (l : List I) (i : I) (t : I → ℝ) (p : B.Mode) :
    HasDerivAt (fun s => rest l p (t+Pi.single i s)) (rest (i::l) p t) 0 := by
  have he : ((i::l).Nodup ∧ (i::l).toFinset⊆p.val) ↔
      (l.Nodup ∧ l.toFinset ⊆ p.val) ∧ i ∈ p.val \ l.toFinset := by simp [Finset.insert_subset_iff]; tauto
  by_cases h : l.Nodup ∧ l.toFinset ⊆ p.val
  · let q := p.val \ l.toFinset
    by_cases hi : i∈q
    · have hg : p.val \ (i::l).toFinset=q.erase i := by ext; simp [q]; tauto
      unfold rest; simp_rw [if_pos h,if_pos (he.mpr ⟨h,hi⟩),hg]
      have hh (s : ℝ) : ∏ j∈q,(t+Pi.single i s : I → ℝ) j=(t i+s)*(∏ j∈q.erase i,t j) := by
        rw [← mul_prod_erase q _ hi,Pi.add_apply,Pi.single_eq_same]; congr 1
        exact prod_congr rfl fun j hj => by simp [(mem_erase.mp hj).1]
      change HasDerivAt (fun s : ℝ => ∏ j∈q,(t+Pi.single i s : I → ℝ) j) _ 0
      simp_rw [hh]; simpa using ((hasDerivAt_id' (0 : ℝ)).const_add (t i)).mul_const (∏ j∈q.erase i,t j)
    have hx (s : ℝ) : rest l p (t+Pi.single i s) = rest l p t := by
      unfold rest; rw [if_pos h,if_pos h]
      exact prod_congr rfl fun j hj => by
        have : j ≠ i := fun e => hi (e ▸ hj)
        simp [this]
    simp_rw [hx]
    rw [show rest (i::l) p t=0 from if_neg (fun h => hi (he.mp h).2)]; exact hasDerivAt_const ..
  have hx (s : ℝ) : rest l p (t+Pi.single i s) = 0 := if_neg h
  simp_rw [hx]
  rw [rest, if_neg (fun hh => h (he.mp hh).1)]
  exact hasDerivAt_const ..

lemma increment (l : List I) (t : I → ℝ) (i : I) (g : B.Mode → X) :
    HasDerivAt (fun s : ℝ => read g l (t+Pi.single i s)) (read g (i::l) t) 0 :=
  HasDerivAt.fun_sum fun (p : B.Mode) _ => (held l i t p).smul_const (g p)

theorem mixed_lift (l : List I) (g : B.Mode → X) : mixed (lift g) l = read g l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext t; rw [mixed,ih]; exact (increment l t i g).deriv



lemma at_origin (l : List I) (p : B.Mode) :
    rest l p 0 = if l.Nodup ∧ l.toFinset=p.val then 1 else 0 := by
  unfold rest; split <;> rename_i hh
  · split
    next h => simp [h.2]
    next h =>
      have he : (p.val \ l.toFinset).Nonempty := nonempty_iff_ne_empty.mpr fun he =>
        h ⟨hh.1,Subset.antisymm hh.2 (sdiff_eq_empty_iff_subset.mp he)⟩
      exact prod_eq_zero he.choose_spec rfl
  rw [if_neg (fun he => hh ⟨he.1,he.2.le⟩)]

theorem names (l : List I) (p : B.Mode) (h : l.Nodup) (hp : l.toFinset=p.val) (g : B.Mode → X) :
    mixed (lift g) l 0 = g p := by
  rw [mixed_lift, read, sum_eq_single p, at_origin, if_pos ⟨h,hp⟩,one_smul]
  · intro b _ hb; rw [at_origin,if_neg (fun he => hb (Subtype.ext (he.2.symm.trans hp))), zero_smul]
  simp



variable {Y : Type*} [MeasurableSpace Y] (M : Measure Y)

/-- Coefficientwise interchange, finite sums already gathered (e.g. over
histories). -/
lemma integral_read (l : List I) (g : B.Mode → Y → X) (t : I → ℝ) (h : ∀ p, Integrable (g p) M) :
    Integrable (fun y => read (fun p => g p y) l t) M ∧
      (∫ y, read (fun p => g p y) l t ∂M) = read (fun p => ∫ y, g p y ∂M) l t := by
  unfold read
  constructor
  · exact integrable_finsetSum _ fun p _ => (h p).smul (rest l p t)
  rw [integral_finsetSum]
  · simp_rw [integral_smul]
  exact fun p _ => (h p).smul (rest l p t)

lemma smul_read (l : List I) (g : B.Mode → X) (t : I → ℝ) (r : ℝ) :
    r • read g l t = read (fun i => r • g i) l t := by
  unfold read; rw [smul_sum]; exact sum_congr rfl fun _ _ => smul_comm ..

end YM.Next.SectorChange.Marked.SourceJet
