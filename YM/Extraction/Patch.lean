import YM.Lattice.Scale
import YM.Euclid.Test

/-!
# Period comparison and compact room

Centered fundamental reps as in Lattice. Tests eventually supported in strict
interior. At fixed period, collisions exclude all periodic images. `Cyclic`
excludes coordinate projection ties (used in point-limit hypothesis but
not assumed smooth limits everywhere at fixed period).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open Function Set Filter Metric MeasureTheory Lattice
open scoped BigOperators Topology
variable (S : Schedule) {n : ℕ}

def Inside (p n : ℕ) : Set (Points n) := {x | ∀ i a, -(S.radius p) < x i a ∧ x i a < S.radius p}

abbrev length (p : ℕ) : ℝ := (S.period p).val

def periodic (p : ℕ) (x y : ℝ) := ∃ j : ℤ, x-y=j * length S p

def NoHit (p n : ℕ) : Set (Points n) :=
  {x | ∀ i j, i ≠ j → ∃ a : Axis, ¬ periodic S p (x i a) (x j a)}

def Cyclic (p n : ℕ) : Set (Points n) :=
  {x | ∀ i j, i ≠ j → ∀ a : Axis, ¬ periodic S p (x i a) (x j a)}

def suitable (p : ℕ) (f : Test n) := tsupport f ⊆ Inside S p n

theorem scalar_periodic (p : ℕ) (x y : ℝ) (H : -(S.radius p) < x) (G : -(S.radius p) < y)
    (h : x < S.radius p) (g : y < S.radius p) : periodic S p x y ↔ x=y := by
  constructor
  · rintro ⟨j,hj⟩
    have hx : 0 ≤ length S p := by unfold length; positivity
    have he : length S p = (S.radius p)*2 := by unfold length Schedule.radius; ring
    rcases lt_trichotomy j 0 with hp|hp|hp
    · have hi : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
      nlinarith
    · subst j; simp_all; linarith
    have hi : (1:ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    nlinarith
  rintro rfl; exact ⟨0,by simp⟩

theorem no_wrap_hit {p : ℕ} {x} (h : x ∈ Inside S p n) : x ∈ NoHit S p n ↔ x ∈ conf n := by
  constructor
  · intro H i j he
    by_contra hh
    obtain ⟨a,ha⟩ := H i j hh
    exact ha ((scalar_periodic S p _ _ (h i a).1 (h j a).1 (h i a).2 (h j a).2).2
      (congr_arg (fun w : E4 => w a) he))
  intro H i j hij
  by_contra! he
  exact hij ((show Injective x.ofLp from H) (PiLp.ext fun a =>
    (scalar_periodic S p _ _ (h i a).1 (h j a).1 (h i a).2 (h j a).2).1 (he a)))

theorem no_wrap_tie {p : ℕ} {x} (h : x ∈ Inside S p n) : x ∈ Cyclic S p n ↔ x ∈ generic n := by
  constructor
  · intro H i a b hab
    by_contra hh
    exact H a b hh i ((scalar_periodic S p _ _ (h a i).1 (h b i).1 (h a i).2 (h b i).2).2 hab)
  intro H i j hij a he
  exact hij (H a ((scalar_periodic S p _ _ (h i a).1 (h j a).1 (h i a).2 (h j a).2).1 he))

theorem room {K : Set (Points n)} (H : IsCompact K) : ∀ᶠ p : ℕ in atTop, K ⊆ Inside S p n := by
  have hi (i : Fin n) (a : Axis) : ∀ᶠ p : ℕ in atTop, ∀ x ∈ K,
      -(S.radius p) < x i a ∧ x i a < S.radius p := by
    obtain ⟨R,hR⟩ := (H.image (show Continuous fun x : Points n => |x i a| from by fun_prop)).bddAbove
    filter_upwards [S.radius_diverges.eventually (eventually_gt_atTop R)] with p hp
    intro x hx
    exact abs_lt.mp (lt_of_le_of_lt (hR ⟨x,hx,rfl⟩) hp)
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (hi i))] with p hp
  exact fun x h i a => hp i a x h

theorem reading (f : Test n) : ∀ᶠ p : ℕ in atTop, suitable S p f := room S f.hasCompactSupport

theorem readable (p : ℕ) (f : Test n) (h : suitable S p f) : tsupport f ⊆ NoHit S p n :=
  fun _ hx => (no_wrap_hit S (h hx)).mpr (f.tsupport_subset hx)

/-- Projection ties use *any* integer image. -/
lemma periodicClosed (p : ℕ) : IsClosed (Set.range fun j : ℤ => (j : ℝ) * length S p) := by
  -- scale closed discrete
  have hl : length S p ≠ 0 := by unfold length; positivity
  let H := Homeomorph.mulRight₀ (length S p) hl
  have he : (fun j : ℤ => (j : ℝ) * length S p) = H ∘ ((↑) : ℤ → ℝ) := rfl
  rw [he, range_comp]
  exact H.isClosedEmbedding.isClosedMap _ Int.isClosedEmbedding_coe_real.isClosed_range

lemma not_tie_open (p : ℕ) (i j : Fin n) (a : Axis) :
    IsOpen {x : Points n | ¬ periodic S p (x i a) (x j a)} := by
  rw [show {x : Points n | ¬ periodic S p (x i a) (x j a)} = (fun x => x i a - x j a) ⁻¹'
    (Set.range fun j : ℤ => (j : ℝ) * length S p)ᶜ from by ext; simp [periodic, eq_comm]]
  exact (periodicClosed S p).isOpen_compl.preimage (by fun_prop)

lemma cyclicOpen (p n : ℕ) : IsOpen (Cyclic S p n) := by
  rw [show Cyclic S p n = ⋂ i : Fin n, ⋂ j : Fin n, ⋂ _ : i ≠ j, ⋂ a : Axis,
    {x : Points n | ¬ periodic S p (x i a) (x j a)} by ext; simp [Cyclic]]
  exact isOpen_iInter_of_finite fun _ => isOpen_iInter_of_finite fun _ =>
    isOpen_iInter_of_finite fun _ => isOpen_iInter_of_finite fun _ => not_tie_open _ _ _ _ _
end YM.Extraction
