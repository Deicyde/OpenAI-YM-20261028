import YM.Push.COMMON_WITNESSES.Plot

/-!
# Merge Grill at the order in use at RSeed

`Menu` supports simultaneous transport and an on-demand sufficient port.
The h's in it must work for ALL finite arities, all needed configurations
specified below. Keep this in mind if building the hypothesis. No asserting
that shrinking cells around the fields or one-cell bounds have furnished the
actual approximation here. No relation to mass gap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Function Filter Set Extraction Cells OS Table Next.Extract
open scoped Topology BigOperators ContDiff

variable {G : Gauge}

/-- Countable placements: incl empty, axes tie hypotheses in `serves` (not
usable at ties). No cost request wrt labels outside listed grades in a slot. -/
abbrev Party := Σ (n : ℕ), Caps n × (Fin n → Lattice.Cover)

abbrev Slot := ℕ × ℕ  -- d and floor station m

def serves (C : Family G) (h d : ℕ) (v : Party) : Prop :=
    (∀ i, v.2.1 i≤d) ∧ Order.grid C h v.2.2 ∈ generic v.1

structure Menu where
  place : Slot → ℕ
  placed (i) : i.2 ≤ place i
  guide : Slot → Party → GrillCosts

abbrev GridBooks (C : Family G) := (i : Slot) → (v : Party) → Exhibit C v.2.1

/-- Quantitative covering supply at every relevant `place`, with actual
common plots and budgets. This IS enough for Grill. -/
def Sustained (C : Family G) (Y : Menu) (P : GridBooks C) (f : Order) :=
    ∀ i v, serves C (Y.place i) i.1 v → Exhibits C (Y.place i) v.2.2 v.2.1 (Y.guide i v) f (P i v)

variable (C : Family G)

lemma ready_grill (Y : Menu) (P : GridBooks C) {f : Order} (H : Sustained C Y P f) : Org.Grill C f := by
  intro d m
  let i : Slot := (d,m)
  let k := Y.place i
  refine ⟨k,Y.placed i, ?_⟩
  intro n v hv h x hx
  let w : Party := ⟨n,(fun i => (v i).1),x⟩
  let u : C.book.Vector w.2.1 := fun i => (v i).2
  refine ⟨onRails k x w.2.1 u (Y.guide i w) (P i w),?_⟩
  exact coherence k x w.2.1 u (show Grid.plain (C:=C) (tagged w.2.1 u) from h)
    (H i w ⟨hv,hx⟩)

lemma Sustained.upon {C : Family G} {Y : Menu} {P : GridBooks C} {f g : Order} (H : Sustained C Y P f) (h : Tails g f) :
    Sustained C Y P g := fun i v e => (H i v e).upon h

def GridInvoice (Y : Menu) (i : Slot × Party × (ℕ × ℕ × ℕ)) (f : Order) :=
    let h := Y.place i.1
    let v := i.2.1
    let (k,t,J) := i.2.2
    serves C h i.1.1 v → PrefixBill C h v.2.2 v.2.1 (Y.guide i.1 v) f k t J

/-- These estimates suffice (on successive stations). -/
def GrillInputs (f : Order) : Prop := ∃ Y : Menu, Stationed f (GridInvoice C Y)



/-- Sufficient way to port the bills from the producer, *if* they can handle
requests under arbitrary inherited Orders below f.

Choose h before arity or
any placement signature.

`PrefixBill` allows postponing to successive orders
under there, one at a time.

`past` and `cap` of trajectory chosen before
prefix demands but choice can depend on k (A only USED at k).

No summability
or all-k boundedness assumed.

Cf. . -/
def GrillDemand (f : Order) := OnDemand f (fun (i : Slot) (u : Order) =>
    ∃ h : ℕ, i.2≤h ∧ OnDemand u (fun (v : Party × ℕ) (t : Order) => ∃ A : GrillCosts,
      serves C h i.1 v.1 → Stationed t (fun (j : ℕ × ℕ) (g : Order) =>
        PrefixBill C h v.1.2.2 v.1.2.1 A g v.2 j.1 j.2)))

-- Auxiliary: safe to reassign the reserve/threshold OUTSIDE this k.
lemma rebudget {C : Family G} {n : ℕ} {d : Caps n} {x : Fin n → Lattice.Cover} {A B : GrillCosts}
    {k t J h : ℕ} {g : Order} (H : PrefixBill C h x d A g k t J)
    (he : A.cap k=B.cap k) (hp : A.past k=B.past k) : PrefixBill C h x d B g k t J := by
  refine H.mono fun i hi => hi.mono ?_
  rintro j ⟨u,hu⟩
  exact ⟨u,⟨fun i h => he ▸ hu.safe i h, fun i j p v => hp ▸ hu.joins i j p v⟩⟩

theorem GrillDemand.inputs {f : Order} (H : GrillDemand C f) : GrillInputs C f := by
  let P := fun (i : Slot) (t : Order) =>
    ∃ h : ℕ, i.2≤h ∧ ∃ A : Party → GrillCosts, ∀ v : Party, serves C h i.1 v →
      ∀ k y J, PrefixBill C h v.2.2 v.2.1 (A v) t k y J
  have he : OnDemand f P := by
    intro i t
    obtain ⟨r,h,hr,hx⟩ := H i t
    let V := (f.refine t).refine r
    let Q := fun (v : Party × ℕ) (g : Order) => ∃ A : GrillCosts, serves C h i.1 v.1 →
      ∀ y J, PrefixBill C h v.1.2.2 v.1.2.1 A g v.2 y J
    have hy : OnDemand V Q := by
      intro v p
      obtain ⟨g,A,hA⟩ := hx v p
      by_cases hp : serves C h i.1 v.1
      · obtain ⟨a,ha⟩ := (hA hp).collect (fun _ _ _ H h => h.upon H)
        exact ⟨g.refine a,A,fun _ y J => ha (y,J)⟩
      exact ⟨g,A,fun h => (hp h).elim⟩
    have hw v y j (he : Tails j y) (hq : Q v y) : Q v j := by
      obtain ⟨A,hA⟩ := hq
      exact ⟨A,fun hp u J => (hA hp u J).upon he⟩
    letI : Countable (Party × ℕ) := by unfold Party; infer_instance
    obtain ⟨p,hp⟩ := hy.stations.collect (fun v u t h => hw v t u h)
    choose A hA using hp
    let B (v : Party) : GrillCosts := ⟨fun k => (A (v,k)).cap k,fun k => (A (v,k)).nonneg k,
      fun k => (A (v,k)).past k⟩
    refine ⟨r.refine p,h,hr,B,?_⟩ -- use unchanged k
    intro v hv k j J
    exact rebudget (B := B v) (hA (v,k) hv j J) rfl rfl
  obtain ⟨r, hr, ht⟩ := he.stations
  choose u hu using ht
  choose m hm A hA using hu
  let Y := Menu.mk m hm A
  refine ⟨Y,r,hr,?_⟩
  rintro ⟨i,v,k,t,J⟩
  exact ⟨u i,fun hx => hA i v hx k t J⟩
end YM.Push.Common
