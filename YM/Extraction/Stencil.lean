import YM.Extraction.Tame
import YM.Analysis.Multilinear
import YM.Euclid.Table

/-!
# Single sequence for the multilinear limit, patch topology

Actual label mixtures commute with the limits by multilinearity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open Function Set Filter TopologicalSpace Metric
open scoped ContDiff Topology BigOperators

namespace Meets
variable {X : Type*} [MetricSpace X] {T S : ℕ → X → ℂ} {f g : X → ℂ} {U : Set X}

lemma plus (H : Meets U T f) (h : Meets U S g) : Meets U (fun i x => T i x + S i x) (f+g) := by
  refine ⟨H.continuousOn.add h.continuousOn,?_⟩
  intro K hx hk ε he
  filter_upwards [H.uniform K hx hk (ε/2) (by positivity), h.uniform K hx hk (ε/2) (by positivity)] with i hi hi' x hK
  exact lt_of_le_of_lt (dist_add_add_le ..) <| (add_lt_add (hi x hK) (hi' x hK)).trans_eq (by ring)

lemma times (H : Meets U T f) (c : ℂ) : Meets U (fun i x => c*T i x) (fun x => c*f x) := by
  refine ⟨continuousOn_const.mul H.continuousOn,?_⟩
  intro K hx hk ε he
  rcases eq_or_ne c 0 with e|e
  · subst c; simp [he]
  filter_upwards [H.uniform K hx hk (ε/‖c‖) (by positivity)] with i hi x hK
  rw [dist_eq_norm,← mul_sub,norm_mul, ← dist_eq_norm,mul_comm]
  exact (lt_div_iff₀ (by positivity : 0 < ‖c‖)).mp (hi x hK)

lemma sums {ι : Type*} (F : ι → ℕ → X → ℂ) (B : ι → X → ℂ) (s : Finset ι) (H : ∀ i ∈ s, Meets U (F i) (B i)) :
    Meets U (fun i x => ∑ k ∈ s, F k i x) (fun x => ∑ k ∈ s, B k x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]; exact ⟨continuousOn_const,fun _ _ _ _ h => by simp [h]⟩
  | @insert i s hv ih =>
    simp_rw [Finset.sum_insert hv]
    exact (H _ (Finset.mem_insert_self ..)).plus (ih (fun k hk => H _ (Finset.mem_insert_of_mem hk)))
end Meets

variable {G : Gauge} {L : Register G}

/-- One coordinate in a table. -/
abbrev Indices (L : Register G) := (n : ℕ) × (d : Caps n) × ((i : Fin n) → (L.grid.level (d i)).Index)

def dial {n : ℕ} (d : Caps n) (i : Fin n) : Module.Basis ((L.grid.level (d i)).Index) ℂ (L.Ref (d i)) :=
  Pi.basisFun ℂ _

def stack (p : Indices L) (i : Fin p.1) : L.Token := ⟨p.2.1 i,dial p.2.1 i (L := L) (p.2.2 i)⟩

theorem components (P : Table L) (F : ℕ → Table L) (U : (n : ℕ) → Set (Points n)) (H : ∀ p : Indices L,
    Meets (U p.1) (fun i x => (F i).read x (stack p)) (fun x => P.read x (stack p))) (n : ℕ) (v : Fin n → L.Token) :
    Meets (U n) (fun i x => (F i).read x v) (fun x => P.read x v) := by
  let d := fun i => (v i).1
  let w := fun i => (v i).2
  let E (i) := dial d i (L := L)
  let X := Fintype.piFinset fun i => ((E i).repr (w i)).support
  let c := fun y : ((i : Fin n) → (L.grid.level (d i)).Index) => ∏ i, (E i).repr (w i) (y i)
  have he (S : Table L) (x : Points n) : S.read x v = ∑ y ∈ X, c y * S.read x (stack (L := L) ⟨n,d,y⟩) :=
    Multilabel.expansion E (S.value d x) w
  simp_rw [he]
  apply Meets.sums
  exact fun i _ => (H ⟨n,d,i⟩).times _

def fitted (g : (p : Indices L) → Points p.1 → ℂ) : Table L where
  value d x := Multilabel.ofBasis (dial (L := L) d) (fun i => g ⟨_,d,i⟩ x)

@[simp] theorem knobs (g : (p : Indices L) → Points p.1 → ℂ) (d : Indices L) (x : Points d.1) :
    (fitted g).read x (stack d) = g d x := Multilabel.applyBasis (dial (L := L) d.2.1) _ _

end YM.Extraction
