import YM.Extra.ITERATION_NO_LOSS.ComplexDerivs
import YM.Next.SCHEDULE.Blocks
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Dual
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.JetProducts
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Push.STRESS_FLUX.Low
import YM.UVNext.COUPLING_RESET.Reset
import YM.UVNext.PRICED_KERNELS.Echo

/-! Per-anchor and per-hit support taxes and duality. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc
open RG Wilson Lattice Filter Function Set Push.AbsoluteSums Trees
open scoped Classical Matrix.Norms.Frobenius Topology BigOperators
variable {ι κ : Type*} {G : Gauge} {n : Side}

def roots (Y : ι → RegularAddress n) (B : ℕ) (a : ℝ) : Tax ι (Site n) where
  cost o i := if (Y i).site=o then currency B a (Y i).support else 0
  nonneg o i := by split; exact (Real.exp_pos _).le; exact le_rfl
  visible i := ⟨(Y i).site, (if_pos rfl).symm ▸ Real.exp_pos _⟩

def hits {Y : ι → Support n} (h : ∀ i, (Y i).Nonempty) (B : ℕ) (a : ℝ) : Tax ι (Site n) where
  cost o i := if o∈Y i then currency B a (Y i) else 0
  nonneg o i := by split; exact (Real.exp_pos _).le; exact le_rfl
  visible i := (h i).imp fun _ hx => (if_pos hx).symm ▸ Real.exp_pos _

variable {Y : ι → RegularAddress n} {Z : ι → Support n} {B : ℕ} {a b C D : ℝ} {c d : ι → ℝ}

abbrev Seated (Y : ι → RegularAddress n) (B : ℕ) (c : ι → ℝ) (a C : ℝ) := Footprint.Anchored
    (fun i => (Y i).site) c (fun i => coverNumber B (Y i).support) a C

lemma seated_iff : (roots Y B a).Credits c C ↔ (∀ i, 0 ≤ c i) ∧ Seated Y B c a C := by
  unfold Seated Footprint.Anchored
  simp only [roots,currency,mul_comm (c _)]
  constructor
  · rintro ⟨hc,h⟩; exact ⟨hc,by simpa [ite_mul,zero_mul] using h⟩
  rintro ⟨hc,h⟩; exact ⟨hc,by simpa [ite_mul,zero_mul] using h⟩







lemma seated_add (h : Seated Y B c a C) (h' : Seated Y B d a D) : Seated Y B (c+d) a (C+D) := by
  intro o; convert budget_plus (h o) (h' o) using 1; ext i; split <;> simp [*,add_mul]
lemma seated_scale (h : Seated Y B c a C) {r : ℝ} (hr : 0≤ r) : Seated Y B (fun i => r*c i) a (r*C) := by
  intro o; simpa [mul_ite,mul_assoc] using budget_scale hr (h o)

lemma sums_join {f : ι ⊕ κ → ℝ} (hc : SumBudget (f ∘ Sum.inl) C) (hd : SumBudget (f ∘ Sum.inr) D) : SumBudget f (C+D) := by
  have he i : 0 ≤ f i := by cases i; exact hc.1 _; exact hd.1 _
  refine budget_of_sum he fun s => ?_
  nth_rw 1 [← Finset.toLeft_disjSum_toRight (u:=s)]
  rw [Finset.sum_disjSum]; exact add_le_add (budget_sum hc _) (budget_sum hd _)
lemma seated_join {Y' : κ → RegularAddress n} {d : κ→ℝ} (hc : Seated Y B c a C) (hd : Seated Y' B d a D) :
    Seated (Sum.elim Y Y') B (Sum.elim c d) a (C+D) := fun o => sums_join (hc o) (hd o)

structure Reading (G : Gauge) (p : BudgetPoint) (r : RegularAddress n) where
  point : Config G n
  admitted : Healthy p.threshold r.support point
  dirs : List (Directions G n)
  order : dirs.length ≤ p.order
  bounds d : d∈dirs → p.dirBound r.site d

namespace Reading
variable {p : BudgetPoint} {r : RegularAddress n}
instance : Nonempty (Reading G p r) := ⟨⟨1,Next.Foundations.one_healthy _ _ p.threshold_pos.le, [],Nat.zero_le _, by simp⟩⟩

def jet (f : Field G n) (u : Reading G p r) := leftDerivs f u.dirs u.point

lemma cost (f : Field G n) (hc : 0 ≤ C) : p.supBounds r.site r.support f C ↔ ∀ v : Reading G p r, |jet f v| ≤ C :=
  ⟨fun H v => H.2 v.point v.admitted v.dirs v.order v.bounds,fun h => ⟨hc,fun U hu l hl hd => h ⟨U,hu,l,hl,hd⟩⟩⟩
end Reading

lemma rooted_box (f : ι → Field G n) (p : BudgetPoint) : (roots Y B a).Box (U:=fun i => Reading G p (Y i)) (fun i => Reading.jet (f i)) C ↔
    ∃ c, (∀ i,p.supBounds (Y i).site (Y i).support (f i) (c i)) ∧ Seated Y B c a C := by
  simp only [Tax.Box,seated_iff]
  constructor
  · rintro ⟨c,⟨hc,hc'⟩,h⟩; exact ⟨c,fun i => (Reading.cost _ (hc i)).mpr (h i),hc'⟩
  rintro ⟨c,hc,h⟩; exact ⟨c,⟨fun i => (hc i).1,h⟩, fun i => (Reading.cost _ (hc i).1).1 (hc i)⟩

end YM.PhysicalNext.InterpolatedSecantsFc
