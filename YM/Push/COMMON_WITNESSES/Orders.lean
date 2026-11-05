import YM.Next.BOUNDARY.Synchronize
import YM.Next.EXTRACTION.Stages

/-!
# Ordered-station invoices for COMMON_WITNESSES

Use the NEXT diagonal lemmas. Some invoices can just be read off a tower
of actual stations. Sometimes they will require an `OnDemand` assumption,
i.e., producer able to run on an *arbitrary inherited* order under f. We'll
state when we need that sort of assumption (important if future refinements
must be made AFTER some numerical data or fields have been fixed). No
intersection assumption through otherwise independent extractions.

Compare . Never use a diagonal of (mesh,period) as the limiting
operation; even when using a `fuse` tail predicate it describes a
mesh-then-period estimate and not the existence of both limits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Filter Function Set Extraction Next.Extract
open scoped Topology

theorem refines_iff {f g : Order} : Next.BOUNDARY.Refines g f ↔ Tails g f := by
  constructor
  · intro h
    have he (s : Sequence) : range s ∈ Filter.map (fun n => s n) atTop := by
      change ∀ᶠ n : ℕ in atTop, s n ∈ range (fun i => s i)
      exact Eventually.of_forall fun n => mem_range_self (f:=fun i => s i) n
    exact ⟨h.mesh (he _), h.per (he _)⟩
  intro h
  exact ⟨fun P hp => h.mesh.holds _ hp, fun P hp => h.per.holds _ hp⟩

/-- Invoices can come true on *successive* orders under `f`. `r` gives
stations in order-axes relative to f. Not even assuming a final order
satisfying each! Need tail stability to diagonalize this receipt. -/
def Stationed {ι : Type*} (f : Order) (P : ι → Order → Prop) : Prop :=
  ∃ r : ℕ → Order,
    (∀ i : ℕ, ∃ g, r (i+1)=(r i).refine g) ∧
    ∀ j : ι, ∃ i, P j (f.refine (r i))

/-- A stronger port (may use before even a tower is known). -/
def OnDemand {ι : Type*} (f : Order) (P : ι → Order → Prop) : Prop :=
  ∀ i : ι, ∀ r : Order, ∃ g : Order, P i ((f.refine r).refine g)

variable {ι : Type*} {f : Order} {P : ι → Order → Prop}

/-- Tails suffices despite all the index-dependent cutoff estimates, *if*
we pay the displayed transport prerequisite. -/
theorem Stationed.collect (A : Stationed f P) (H : ∀ i u v, Tails u v → P i v → P i u) :
    ∃ g : Order, ∀ i, P i (f.refine g) := by
  obtain ⟨r, hr, hp⟩ := A
  let F (n : ℕ) := f.refine (r n)
  have he (i : ℕ) : ∃ g, F (i+1)=(F i).refine g := by
    obtain ⟨g,hg⟩ := hr i
    exact ⟨g,by dsimp only [F]; rw [hg]; rfl⟩
  obtain ⟨g,hg⟩ := diagonal F he
  refine ⟨(r 0).refine g, fun i => ?_⟩
  obtain ⟨k,hk⟩ := hp i
  exact H i _ _ (hg k) hk

lemma OnDemand.stations [Countable ι] (A : OnDemand f P) : Stationed f P := by
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨fun _ => Order.full, fun _ => ⟨Order.full,rfl⟩,fun i => isEmptyElim i⟩
  | inr h =>
    choose g hg using A
    obtain ⟨s, hs⟩ := exists_surjective_nat ι
    let r : ℕ → Order := Nat.rec Order.full fun n t => t.refine (g (s n) t)
    refine ⟨r, fun i => ⟨_, show r (i+1) = (r i).refine (g _ (r i)) from rfl⟩, fun i => ?_⟩
    obtain ⟨n, rfl⟩ := hs i
    exact ⟨n+1,hg _ (r n)⟩

/-- Convenience at a producer charged more than needed (no changes of
order required). -/
lemma already (h : ∀ i, P i f) : Stationed f P :=
  ⟨fun _ => Order.full, fun _ => ⟨Order.full,rfl⟩,fun i => ⟨0,h i⟩⟩

/-- Positive sequence of invoice tolerances. -/
def toll (j : ℕ) := (((j : ℝ)+1)⁻¹ : ℝ)
lemma toll_pos (j) : 0<toll j := by dsimp [toll]; positivity
lemma toll_go : Tendsto toll atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
lemma within (ε : ℝ) (hε : 0<ε) : ∃ j, toll j ≤ ε := by
  obtain ⟨j,hj⟩ := (toll_go.eventually (gt_mem_nhds hε)).exists
  exact ⟨j,hj.le⟩


end YM.Push.Common
