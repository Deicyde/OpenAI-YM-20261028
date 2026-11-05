import YM.Extra.MULTISOURCE_TRAJECTORIES.Stubs
/-!
# Reserving actual hangers before joint-source operations

One option at *construction* time, not an assertion about the arbitrary
retain predicates or blank labels of any already chosen representation.
Never enlarge or change a nonzero old K; the map of the old alphabet with all
its predicates is simultaneous for all consumers. Does not suffice alone for
price reserves `After` or `InitialRoom`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories.Hangers
open RG Wilson Lattice Function Finset MeasureTheory Filter Source
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {n : Side}

private instance : Finite (Room n) := Finite.of_injective (β:=Support n × Support n) (fun r => (r.wall,r.bill)) (fun ⟨_,_,_,_⟩ ⟨_,_,_,_⟩ h => Room.mk.injEq .. |>.mpr (Prod.mk.inj h))

def numbers (n : Side) : ℕ ⊕ Room n ≃ ℕ :=
  letI := Encodable.ofCountable (ℕ ⊕ Room n)
  letI := Denumerable.ofEncodableOfInfinite (ℕ ⊕ Room n)
  Denumerable.eqv _

def named (n : Side) : ℕ ↪ ℕ := Embedding.inl.trans (numbers n).toEmbedding

def shift {X} [Zero X] (f : ℕ → X) (n : Side) (i : ℕ) : X := ((numbers n).symm i).elim f 0

def entries (P : Activities G n) : Activities G n :=
    { P with forced := fun i => ((numbers n).symm i).elim P.forced (fun a => ⟨a.wall,a.bill,a.needs,a.inside,fun _ => True⟩)
             K := shift P.K n }

lemma shift_in {X} [Zero X] (f : ℕ → X) (i : ℕ) : shift f n (named n i) = f i := by simp [named, shift]
lemma shift_zero {X} [Zero X] (f : ℕ → X) {i} (h : i ∉ Set.range (named n)) : shift f n i=0 := by
  unfold shift; cases he : (numbers n).symm i
  next j => exact (h ⟨j,(congrArg (numbers n) he.symm).trans ((numbers n).apply_symm_apply i)⟩).elim
  rfl
lemma forced (P : Activities G n) (i : ℕ) : (entries P).forced (named n i) = P.forced i := by simp [entries,named]

lemma admissible (P : Activities G n) (p : BudgetPoint) (U : Config G n) (b : Finset ℕ) :
    (entries P).admissible p U (b.map (named n)) ↔ P.admissible p U b := by
  unfold Activities.admissible
  have he : (b.map (named n)).biUnion (fun i => ((entries P).forced i).inventory) = b.biUnion fun i => (P.forced i).inventory := by
    rw [map_eq_image,image_biUnion]; simp [forced]
  rw [he]; congr! 1; unfold Set.Pairwise; simp [forced]

lemma zero_outside {b : Finset ℕ} (h : b ∉ Set.range (Finset.map (named n))) : ∃ i∈b,i∉Set.range (named n) := by
  by_contra! hn
  apply h; exact ⟨b.preimage (named n) (named n).injective.injOn, Finset.ext (fun i => by
    simp only [Finset.mem_map,mem_preimage]
    constructor
    · rintro ⟨j,hj,rfl⟩; exact hj
    intro h; obtain ⟨j,rfl⟩ := hn i h; exact ⟨j,h,rfl⟩)⟩

lemma gas_term (P : Activities G n) (p : BudgetPoint) (U : Config G n) (b : Finset ℕ) :
    (entries P).gasOccurrence p (b.map (named n)) U = P.gasOccurrence p b U := by
  simp only [Activities.gasOccurrence,admissible,prod_map]; split
  · exact prod_congr rfl fun i _ => congrFun (shift_in P.K i) U
  rfl
lemma gas_vanish (P : Activities G n) (p : BudgetPoint) (U : Config G n) {b : Finset ℕ} (h : b ∉ Set.range (Finset.map (named n))) :
    (entries P).gasOccurrence p b U = 0 := by
  unfold Activities.gasOccurrence; split
  · obtain ⟨i,hi,hj⟩ := zero_outside h; exact prod_eq_zero hi (congrFun (shift_zero P.K hj) U)
  rfl
lemma gas (P : Activities G n) (p : BudgetPoint) (U : Config G n) : (entries P).gas p U=P.gas p U := by
  unfold Activities.gas
  rw [← (map_injective (named n)).tsum_eq (fun b hb => by by_contra hn; exact hb (gas_vanish P p U hn))]
  exact tsum_congr (gas_term P p U)

lemma forcedFamily {P : Activities G n} {p : BudgetPoint} (h : P.ForcedFamily p) : (entries P).ForcedFamily p := by
  constructor
  · intro i; dsimp only [entries,shift]; cases (numbers n).symm i
    next i => exact h.sym i
    exact fun _ _ => rfl
  · intro i; dsimp only [entries]; cases (numbers n).symm i
    next i => exact h.symtest i
    exact fun _ _ => Iff.rfl
  · intro i; dsimp only [entries,shift]; cases (numbers n).symm i
    next i => exact h.meas i
    exact measurable_const
  · intro i; dsimp only [entries]; cases (numbers n).symm i
    next i => exact h.meas_test i
    simp
  · intro i; dsimp only [entries,shift]; cases (numbers n).symm i
    next i => exact h.reads i
    exact fun _ _ _ _ => rfl
  · intro i; dsimp only [entries]; cases (numbers n).symm i
    next i => exact h.reads_test i
    exact fun _ _ _ _ => rfl
  intro i U; dsimp only [entries,shift]; cases (numbers n).symm i
  next i => exact h.permit i U
  simp

def turn (e : Equiv.Perm (Site n)) (a : Room n) : Room n :=
  ⟨a.wall.image e, a.bill.image e, a.needs.image _, image_subset_image a.inside⟩
lemma turn_back (e : Equiv.Perm (Site n)) : LeftInverse (turn e.symm) (turn e) := fun i => by simp [turn, image_image]

def spin (e : Equiv.Perm (Site n)) : Equiv.Perm (Room n) := ⟨turn e,turn e.symm, turn_back e, turn_back e.symm⟩

lemma moves {P : Activities G n} {s : Signed} {b : Site n} (h : P.Moves s b) : Nonempty ((entries P).Moves s b) := by
  let g := s.actEquiv.toEquiv.trans (Equiv.addRight b)
  let e := Equiv.sumCongr h.kp (spin (n:=n) g)
  let kp := (numbers n).symm.trans (e.trans (numbers n))
  have he i : (numbers n).symm (kp i) = e ((numbers n).symm i) := by simp [kp]
  refine ⟨⟨h.ep,kp,h.reg_site,h.reg_support,?_,?_,?_,h.valuesE,?_⟩⟩
  · intro i; dsimp only [entries]; rw [he]; cases (numbers n).symm i
    next i => exact h.forced_support i
    rfl
  · intro i; dsimp only [entries]; rw [he]; cases (numbers n).symm i
    next i => exact h.forced_inventory i
    rfl
  · intro i U; dsimp only [entries]; rw [he]; cases (numbers n).symm i
    next i => exact h.forced_tests i U
    rfl
  intro i U; dsimp only [entries, shift]; rw [he]; cases (numbers n).symm i
  next i => exact h.valuesK i U
  rfl

lemma kbound {P : Activities G n} {p : BudgetPoint} {u : ℝ} (h : P.KBound p u) : (entries P).KBound p u := by
  obtain ⟨b,hb,h⟩ := h
  have he i : 0 ≤ shift b n i ∧ ∀ U,‖shift P.K n i U‖ ≤ shift b n i := by unfold shift; cases (numbers n).symm i; exact hb _; simp
  refine ⟨shift b n,he,fun i => budget_image (named n).injective injective_id (fun j => ?_) (fun j hj => ?_) (h i) (fun j => ?_)⟩
  · split; exact mul_nonneg (Real.exp_pos _).le (he j).1; rfl
  · rw [shift_zero b hj]; simp [BudgetPoint.mass]
  exact le_of_eq (by dsimp only [id_eq]; by_cases ht : i ∈ (P.forced j).support <;> simp [ht,forced,shift_in])

lemma valid {P : Activities G n} {p : BudgetPoint} {δ κ : ℝ} (h : P.Valid p δ κ) : (entries P).Valid p δ κ :=
  ⟨⟨h.regular.smooth,h.regular.at_flat,h.regular.vanish⟩,forcedFamily h.forced, fun s b => (h.moves s b).elim moves,h.boundE,kbound h.boundK⟩

def rep (P : Rep G n) : Rep G n := {P with activities := entries P.activities}

lemma density (P : Rep G n) : (rep P).eval = P.eval := by funext U; unfold Rep.eval; congr 1; exact gas ..
lemma lawful {P : Rep G n} {σ C Λ δ w} (h : P.Lawful σ C Λ δ w) : (rep P).Lawful σ C Λ δ w := ⟨h.paths,valid h.labels⟩

def history (H : History G) : History G := {H with rep := fun N p j => rep (H.rep N p j)}
theorem selected {H : History G} (h : H.Selected) : (history H).Selected where
  path_shared := h.path_shared
  represents N p m hm := let h := h.represents N p m hm; ⟨h.vac,h.clip,lawful h.good,h.band⟩
  starts N p := ⟨(h.starts ..).1,(density ..).trans (h.starts ..).2⟩
  steps N p m hm := ⟨by rw [history,density,density]; exact (h.steps N p m hm).1,(h.steps N p m hm).2⟩
  reaches := h.reaches
  running := h.running
end YM.Extra.Trajectories.Hangers
