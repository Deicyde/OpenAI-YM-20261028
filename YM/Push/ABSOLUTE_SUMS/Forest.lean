import YM.Push.ABSOLUTE_SUMS.Array
import YM.Push.ABSOLUTE_SUMS.Weigh


/-!
# Absolute tree sums, spatially rooted exponential tails

For countable alphabets (or any types), the whole occurrence grammar
of nonnegative label weights. Forest roots attach to an external `Y`;
when the internal root is designated instead it carries a possibly
different label weight array, convenient e.g. for one marker. Tail in
number of nonroot vertices, IN THE weighted estimates. Includes Y = ∅,
one or no vertices/edges etc and works at every period. Hypotheses are
on vertex weights, not a convergence assertion for forests.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Trees
open Lattice Finset RG Relation
open scoped Topology BigOperators Classical
variable {ι : Type*} {n : Side} (X : ι → Support n) (B : ℕ)

/-- Address system. `none` or the external root is NOT counted by `m`. -/
abbrev ForestAt (ι : Type*) (m : ℕ) := (Fin m → Option (Fin m)) × (Fin m → ι)
abbrev Forest (ι : Type*) := Σ m, ForestAt ι m
abbrev RootAt (ι : Type*) (m : ℕ) := ι × ForestAt ι m
abbrev Root (ι : Type*) := Σ m, RootAt ι m

/-- Sufficient smallness condition and convenient geometric rate `q`. -/
def Ready (w : ι → ℝ) (a γ δ q : ℝ) : Prop :=
    0 < γ ∧ 0 < δ ∧ degreePrice B γ δ ≤ q ∧ q < 1 ∧ (∀ i, 0 ≤ w i) ∧ Ac.Hit X B w (a+δ) γ

lemma ready_pos {w : ι → ℝ} {a γ δ q : ℝ} (h : Ready X B w a γ δ q) : 0 < q := by
  rcases h with ⟨hg,hd,hq,-⟩
  unfold degreePrice at hq; have ht := stretch_pos B hg hd; linarith

def forestW (Y : Support n) (w : ι → ℝ) (a : ℝ) (z : Forest ι) :=
    forestWeight X B w a Y z.2.1 z.2.2

def rootW (w u : ι → ℝ) (a : ℝ) (z : Root ι) :=
    let i := z.2.1
    -- u the (test-hit, marked or arbitrary paid) ROOT weight
    u i * currency B a (X i) * forestW X B (X i) w a ⟨z.1,z.2.2⟩

lemma forest_at (Y : Support n) {w : ι → ℝ} {a γ δ q : ℝ}
    (h : Ready X B w a γ δ q) (m : ℕ) : SumBudget
      (fun z : ForestAt ι m => forestW X B Y w a ⟨m,z⟩)
      (currency B δ Y * q^m) := by
  rcases h with ⟨hg,hd,hq,h1,hw,hh⟩
  apply budget_assignments (fun z : _ × (Fin m → ι) => forestWeight X B w a Y z.1 z.2)
    (fun i => forest_nonneg X B hw a Y i.1 i.2)
  intro D
  have hp : 0 ≤ degreePrice B γ δ := mul_nonneg (by norm_num) (stretch_pos B hg hd).le
  exact (trees_afford X B m D Y hg hd hw hh).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hp hq _) (Real.exp_pos _).le)



lemma root_at {w u : ι → ℝ} {a γ δ q b : ℝ} (hu : ∀ i, 0 ≤ u i)
    (h : Ready X B w a γ δ q) (he : SumBudget (fun i => u i * currency B (a+δ) (X i)) b)
    (m : ℕ) : SumBudget (fun z : RootAt ι m => rootW X B w u a ⟨m,z⟩) (b * q^m) := by
  rw [mul_comm b]
  refine budget_rows _ (fun i => q^m*(u i * currency B (a+δ) (X i))) (fun k => ?_)
    (budget_scale (pow_nonneg (ready_pos X B h).le m) he)
  have hx := budget_scale (show 0 ≤ u k * currency B a (X k) from
    mul_nonneg (hu k) (Real.exp_pos _).le) (forest_at X B (X k) h m)
  apply budget_loosen hx
  unfold currency; rw [add_mul,Real.exp_add]; apply le_of_eq; ring



section Cover
variable {α : Type*}

/-- Includes the root Y as well; in logs use with the footprint of the
designated root address. -/
def overall [Fintype α] (Y : Support n) (z : α → ι) := univ.biUnion (installed X Y z)

lemma rooted_paths [Fintype α] {Y : Support n} {p : α → Option α} {z : α → ι}
    (h : Sprouts X Y p z) (j : Option α) : Ac.chain (installed X Y z) univ none j := by
  obtain ⟨⟨f,hf⟩,hk⟩ := h
  let A := installed X Y z
  have he : ∀ m : ℕ, ∀ i, f i ≤ m → Ac.chain A univ none (some i) := by
    intro m; induction m with
    | zero =>
      intro i hi; have hz : p i = none := by
        cases hh : p i with
        | none => rfl
        | some j => have he := hf i j hh; omega
      have hs := hz ▸ hk i
      exact .single (show Ac.bonds A univ none (some i) from ⟨mem_univ _,mem_univ _,hs⟩)
    | succ m IH =>
      intro i hi; have ht : Ac.bonds A univ (p i) (some i) := ⟨mem_univ _,mem_univ _,hk i⟩
      cases hz : p i with
      | none => exact .single (hz ▸ ht)
      | some j =>
        have hl := hf i j hz
        exact .tail (IH j (by omega)) (hz ▸ ht)
  cases j with
  | none => exact .refl
  | some i => exact he (f i) i le_rfl

lemma overall_covered [Fintype α] {Y : Support n} {p : α → Option α} {z : α → ι}
    (h : Sprouts X Y p z) : coverNumber B (overall X Y z) ≤ coverNumber B Y +
      ∑ i, coverNumber B (X (z i)) := by
  let A := installed X Y z
  have he : Ac.Spark A univ :=
    ⟨⟨none,mem_univ _⟩, fun i _ j _ => ReflTransGen.trans (Ac.swaps A (rooted_paths X h i))
      (rooted_paths X h j)⟩
  have ht := Ac.cover A B he
  rwa [Fintype.sum_option] at ht

lemma currency_add (a a' : ℝ) (Y : Support n) : currency B (a+a') Y =
    currency B a Y * currency B a' Y := by rw [currency,add_mul,Real.exp_add]; rfl

lemma overall_paid [Fintype α] {Y : Support n} {p : α → Option α} {z : α → ι}
    {a : ℝ} (ha : 0 ≤ a) (h : Sprouts X Y p z) : currency B a (overall X Y z) ≤
      currency B a Y * ∏ i, currency B a (X (z i)) := by
  unfold currency; simp only [← Real.exp_sum,← Real.exp_add,← Finset.mul_sum,← mul_add]
  exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast overall_covered X B h) ha)



-- convenient whole covers for price/geometry users




lemma forestW_nonneg (Y : Support n) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (a : ℝ)
    (z : Forest ι) : 0 ≤ forestW X B Y w a z := forest_nonneg X B hw a _ _ _

lemma rootW_nonneg {u w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 ≤ u i) (a : ℝ)
    (z : Root ι) : 0 ≤ rootW X B w u a z := mul_nonneg (mul_nonneg (hu _) (Real.exp_pos _).le)
      (forestW_nonneg X B _ hw a _)







/-- Hit x by the designated root. Logs that may be hit at ANY
vertex use this estimate over arbitrary numberings with their proper
factorial (the normalization here already allows for the root choice).
Supports w/o hits need their separate treatment. -/
def hit (w : ι → ℝ) (x : Site n) (i : ι) := if x∈X i then w i else 0

lemma hit_pos {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (x : Site n) (i : ι) : 0 ≤ hit X w x i := by
  unfold hit; split <;> first | exact hw i | exact le_rfl

lemma test_hit {w : ι → ℝ} {a γ δ q : ℝ} (h : Ready X B w a γ δ q) (x : Site n) :
    SumBudget (fun i => hit X w x i * currency B (a+δ) (X i)) γ := by
  convert h.2.2.2.2.2 x using 1
  ext i; by_cases he : x∈X i <;> simp [hit,currency,he]


end Cover
end YM.Push.AbsoluteSums.Trees
