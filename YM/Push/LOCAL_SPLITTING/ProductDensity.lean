import YM.Push.LOCAL_SPLITTING.Raw



/-!
# Product inserts as actual singleton sources

Insert a local function multiplying the vacuum, specified by a regular germ
on the measured domain and a bounded attaching complement. Then in particular
insert finite products of regular local factors as ONE source of requested
weight d. Costs include indicator corrections, and any required full-group
cost (for unmasked factors). Genuine function identity, not a statement
about the multi-marker *propagation* dynamics.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
namespace Insert
open Function Lattice Wilson RG Source Labels Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d} {X : Support n} {o : Site n}
variable {R : Rep G n} {S : Slots R.activities (fun _ : Unit => X)}

variable (F X R S) in
def atom (f g : Config G n → ℂ) : Raw F n where
  seed := 0
  bulk i := if i=0 then f else 0
  forced := S.pack R.p.threshold fun _ => g



private theorem tsum_single {Y : Type*} [AddCommMonoid Y] [TopologicalSpace Y] {z : ℕ → Y} (h : ∀ i : ℕ, i ≠ 0 → z i = 0) :
    (∑' i : ℕ, z i) = z 0 := tsum_eq_single 0 h



private theorem sumBudget_atom {x c : ℝ} {f : ℕ → ℝ} (h : 0 ≤ x) (hx : x ≤ c) (he : f 0 = x) (hq : ∀ i, i≠0 → f i = 0) : SumBudget f c :=
  ⟨fun i => by rcases eq_or_ne i 0 with hr|hr; rw [hr,he]; exact h; rw [hq i hr],summable_of_ne_finset_zero (s:={0}) (by simpa using hq), (tsum_single hq).trans_le (he.trans_le hx)⟩

/-- Explicit price for a raw local atom on X with optional complement.
A direct nonuniform mass bill (see Funding for exponent reserves that can pay
it). No dependence hidden on the number of sites/paths through a constant.
-/
def bill (A : Hol G) (T : SectionData F) (o : Site n) (X : Support n) (B : BudgetPoint) (w v κ a b : ℝ) :=
  Raw.rawMass A T o X B w a + (mergePrice B v X b / κ + Raw.rawMerge A T o X B w v a / κ)

theorem income {A : Hol G} (T : SectionData F) {w a b v κ : ℝ} (h : Readable A T R.p n w) {f g : Config G n → ℂ} (hr : R.activities.KBound R.p v)
    (hv : 0 ≤ v) (hκ : 0 < κ) (hf : R.p.supBounds o X f a) (hg : ∀ U, ‖g U‖ ≤ b) :
    Raw.Income (atom F X R S f g) o (fun _ => X) A T R w v κ (bill A T o X R.p w v κ a b) := by
  have hb := (norm_nonneg _).trans (hg 1)
  have hk : 0 ≤ atomPrice A F w*a := mul_nonneg (zero_le_one.trans (atomPrice_ge_one _ _ h.nonneg)) hf.1
  have hp : 0 ≤ mergePrice R.p v X b := mergePrice_nonneg R.p X hv hb
  have hy : 0 ≤ Raw.rawMerge A T o X R.p w v a := mergePrice_nonneg R.p _ hv hk
  refine ⟨_,_,_,hk.trans (R.p.loMass _ _ hk),div_nonneg hp hκ.le,div_nonneg hy hκ.le,le_rfl,
    ⟨fun i => if i=0 then a else 0, ?_,sumBudget_atom (hk.trans (R.p.loMass _ _ hk)) le_rfl ?_ ?_,sumBudget_atom hy (le_of_eq (by field_simp)) ?_ ?_⟩,?_⟩
  · intro i; by_cases hi : i=0; simpa only [atom,if_pos hi] using hf
    simp only [atom,if_neg hi]; simpa only [norm_zero,Pi.zero_def] using! bound_const (G:=G) (B:=R.p) (X:=X) (o:=o) (0:ℂ)
  · rfl
  · intro i hi; simp [hi,Raw.rawMass,BudgetPoint.mass]
  · rfl
  · intro i hi; simp [hi,Raw.rawMerge,mergePrice,BudgetPoint.mass]
  rw [mul_div_cancel₀ _ hκ.ne']; exact S.forceCost (a:=fun _ => b) hr ⟨fun _ => hp,.of_finite, by rw [tsum_fintype,Fintype.sum_unique]⟩ (fun _ => hb) (fun _ => hg)




end Insert
end YM.Push.Local
