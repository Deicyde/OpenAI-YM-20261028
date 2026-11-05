import YM.Bid.Craft
import YM.Extra.SOURCE_HISTORIES.Clusters
import YM.Extra.SOURCE_HISTORIES.Motion

/-!
# Supplying the top-level address shelf (keeping public label/name data)

An enrichment procedure for the planner: always preallocate *all* finite
support shapes with nonempty flags and countable duplicates. Doesn't assert
that one can assume this in an *arbitrary already supplied Bolt*. Shows
extension by literally zero labels in chosen history/action, to use in
constructing a Bolt with that property. Exact paths & all old unmarked
addresses remain (old K through one fixed renaming). Extra test is True
but eligible still uses exact flags; richer predicates on this shape
checked in the payload as in `Attach`. All vacuum costs unchanged incl
exponential and the strong extra cap in `Directed.Move`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Pads
open Lattice Wilson RG Source Function Filter Set MeasureTheory Bid Labels Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge}

abbrev Ghost (n : Side) := StockTag n × ℕ

def sidekick (n : Side) : ℕ ⊕ Ghost n ≃ ℕ := by
  letI : Encodable (ℕ ⊕ Ghost n) := Encodable.ofCountable _
  letI := Denumerable.ofEncodableOfInfinite (ℕ ⊕ Ghost n)
  exact Denumerable.eqv _

def old (n : Side) : ℕ ↪ ℕ := ⟨(sidekick n) ∘ Sum.inl,(sidekick n).injective.comp Sum.inl_injective⟩
def reserve (n : Side) : Ghost n ↪ ℕ := ⟨(sidekick n) ∘ Sum.inr,(sidekick n).injective.comp Sum.inr_injective⟩

variable {n : Side} (p : Ghost n) (A : Activities G n)

def joins {α : Type*} (n : Side) (f : ℕ → α) (g : Ghost n → α) : ℕ → α := (Sum.elim f g) ∘ (sidekick n).symm
lemma joins_old {α : Type*} (f : ℕ → α) (g : Ghost n → α) (j) : joins n f g (old n j)=f j := by simp [joins,old]
lemma joins_stock {α : Type*} (f : ℕ → α) (g : Ghost n → α) (j) : joins n f g (reserve n j)=g j := by simp [joins,reserve]

lemma cases_cell (n : Side) (i : ℕ) : (∃ j,old n j=i) ∨ ∃ j, reserve n j=i := by
  obtain ⟨j|j,rfl⟩ := (sidekick n).surjective i ; exacts [Or.inl ⟨j,rfl⟩,Or.inr ⟨j,rfl⟩]

lemma budget_joins {f : ℕ → ℝ} {w : ℝ} (h : SumBudget f w) (n : Side) :
    SumBudget (joins n f (fun _ => 0)) w := by
  let z := joins n f (fun _ => 0)
  have he : z ∘ old n = f := funext fun _ => joins_old ..
  have hv (i : ℕ) (hi : i∉range (old n)) : z i=0 := by
    obtain h|⟨j,rfl⟩ := cases_cell n i; exact (hi h).elim; exact joins_stock ..
  have hg : Function.support z ⊆ range (old n) := by intro i hi; by_contra hu; exact hi (hv i hu)
  refine ⟨fun i => ?_, ((old n).injective.summable_iff hv).mp (he.symm ▸ h.2.1),?_⟩
  · obtain ⟨j,rfl⟩|⟨j,rfl⟩ := cases_cell n i
    · rw [joins_old]; exact h.1 _
    rw [joins_stock]
  change tsum z ≤ _
  rw [← (old n).injective.tsum_eq hg,show (fun j => z (old n j))=f from he]; exact h.2.2

/-- The ghost is identified by full supports and inventory. -/
def apparition : ForcedAddress G n := ⟨p.1.val.1,p.1.val.2,p.1.property.1,p.1.property.2,fun _ => True⟩

def enhanced : Activities G n := { A with
  forced := joins n A.forced apparition
  K := joins n A.K (fun _ => 0) }

lemma old_eq (j : ℕ) : (enhanced A).forced (old n j)=A.forced j := joins_old ..
lemma ghost_eq (j : Ghost n) : (enhanced A).forced (reserve n j)=apparition j := joins_stock ..
lemma old_k (j : ℕ) : (enhanced A).K (old n j)=A.K j := joins_old ..
lemma ghost_k (j : Ghost n) : (enhanced A).K (reserve n j)=0 := joins_stock ..

def supplies : Shelf (enhanced A) := by
  refine ⟨reserve n,?_,?_,?_,ghost_k A⟩
  · intro t; rw [ghost_eq]; rfl
  · intro t; rw [ghost_eq]; rfl
  intro t U; rw [ghost_eq]; exact trivial

/-- preserves ALL label permutations, even through reflections -/
private def new_shape (f : Site n ≃ Site n) (v : StockTag n) : StockTag n := ⟨(v.val.1.image f,v.val.2.image f),
  v.property.1.image _, Finset.image_subset_image v.property.2⟩
private lemma prod_shape (f : Site n ≃ Site n) (v : StockTag n) : new_shape f.symm (new_shape f v)=v := by
  apply Subtype.ext; apply Prod.ext <;> simp only [new_shape,Finset.image_image,comp_def,Equiv.symm_apply_apply,Finset.image_id']
private def fitting (f : Equiv.Perm (Site n)) : Equiv.Perm (StockTag n) :=
    ⟨new_shape f,new_shape f.symm, prod_shape f, prod_shape f.symm⟩

lemma actions {s : Signed} {b : Site n} (H : A.Moves s b) : Nonempty ((enhanced A).Moves s b) := by
  let g := Equiv.ofBijective (affine s b) (by
    have hx : Injective (affine s b) := fun i j h => s.act_injective (add_right_cancel h)
    exact ⟨hx,Finite.injective_iff_surjective.mp hx⟩)
  let u := (fitting g).prodCongr (Equiv.refl ℕ)
  let F := ((sidekick n).symm.trans (H.kp.sumCongr u)).trans (sidekick n)
  have he i : F (old n i)=old n (H.kp i) := by simp [F,old]
  have hl i : F (reserve n i)=reserve n (u i) := by simp [F,reserve]
  refine ⟨⟨H.ep,F,H.reg_site,H.reg_support,?_,?_,?_,H.valuesE,?_⟩⟩
  · intro i; obtain ⟨j,rfl⟩|⟨j,rfl⟩ := cases_cell n i
    · rw [he,old_eq,old_eq,H.forced_support]
    rw [hl,ghost_eq,ghost_eq]; rfl
  · intro i; obtain ⟨j,rfl⟩|⟨j,rfl⟩ := cases_cell n i
    · rw [he,old_eq,old_eq,H.forced_inventory]
    rw [hl,ghost_eq,ghost_eq]; rfl
  · intro i U; obtain ⟨j,rfl⟩|⟨j,rfl⟩ := cases_cell n i
    · rw [he,old_eq,old_eq,H.forced_tests]
    rw [hl,ghost_eq,ghost_eq]
    rfl
  intro i U; obtain ⟨j,rfl⟩|⟨j,rfl⟩ := cases_cell n i
  · rw [he,old_k,old_k,H.valuesK]
  rw [hl,ghost_k,ghost_k]; rfl

lemma zeros (P : BudgetPoint) (u : ℝ) (h : A.KBound P u) : (enhanced A).KBound P u := by
  obtain ⟨a,ha,hA⟩ := h
  let t := joins n a (fun _ => 0)
  refine ⟨t,fun i => ?_, fun x => ?_⟩
  · obtain ⟨j,rfl⟩|⟨j,rfl⟩ := cases_cell n i
    · unfold t; rw [joins_old,old_k]; exact ha _
    unfold t; simp [joins_stock,ghost_k]
  let r (i : ℕ) := if x∈(A.forced i).support then P.mass (A.forced i).support (a i) else 0
  have he : (fun i => if x∈((enhanced A).forced i).support then P.mass ((enhanced A).forced i).support (t i) else 0) =
        joins n r (fun _ => 0) := by
    funext i; obtain ⟨i,rfl⟩|⟨i,rfl⟩ := cases_cell n i
    · simp only [t,r,joins_old,old_eq]
    simp [t,joins_stock,BudgetPoint.mass]
  exact he.symm ▸ (budget_joins (hA x) n)

lemma family (P : BudgetPoint) (h : A.ForcedFamily P) : (enhanced A).ForcedFamily P := by
  constructor
  all_goals
    intro i; obtain ⟨j,rfl⟩|⟨j,rfl⟩ := cases_cell n i
    · simp only [old_eq,old_k]
      first | exact h.sym j | exact h.symtest j | exact h.meas j | exact h.meas_test j | exact h.reads j |
        exact h.reads_test j | exact h.permit j
  all_goals
    simp only [ghost_eq,ghost_k,apparition]
    first
    | exact fun _ _ => rfl
    | exact fun _ _ _ _ => rfl
    | exact measurable_const
    | simp

lemma legitimate (P : BudgetPoint) {u v : ℝ} (h : A.Valid P u v) : (enhanced A).Valid P u v := by
  have hh : (enhanced A).RegularFamily P := ⟨h.regular.smooth,h.regular.at_flat,h.regular.vanish⟩
  exact ⟨hh,family A P h.forced,fun s b => actions A (Classical.choice (h.moves s b)),h.boundE,zeros A P v h.boundK⟩

lemma fuels (P : BudgetPoint) (U : Config G n) : (enhanced A).gas P U=A.gas P U := by
  let f := old n
  let g := Finset.map f
  let h b := (enhanced A).gasOccurrence P b U
  have ht (b) : h (g b)= A.gasOccurrence P b U := by
    have hh : (enhanced A).admissible P U (g b) ↔ A.admissible P U b := by
      unfold Activities.admissible g
      rw [Finset.map_eq_image,Finset.image_biUnion]
      simp_rw [show ∀ i, (enhanced A).forced (f i)=_ from old_eq A]
      constructor
      · rintro ⟨h,a⟩
        refine ⟨?_,a⟩
        intro i hi j hj hx
        have hg := h (Finset.mem_image_of_mem f hi) (Finset.mem_image_of_mem f hj) (f.injective.ne hx)
        simpa only [f,old_eq] using hg
      rintro ⟨h,a⟩; refine ⟨?_,a⟩
      intro i hi j hj hx
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hj
      simpa only [f,old_eq] using h hk hl (f.injective.ne_iff.mp hx)
    unfold h Activities.gasOccurrence
    rw [hh]; simp only [g,Finset.prod_map,f,old_k]
  have hz : Function.support h ⊆ range g := by
    intro b hb
    have he (i) (hi : i∈b) : i∈range f := by
      obtain hh|⟨j,rfl⟩ := cases_cell n i; exact hh
      exfalso; apply hb
      unfold h Activities.gasOccurrence
      split; exact Finset.prod_eq_zero hi (by rw [ghost_k]; rfl); exact rfl
    let t (i : ℕ) := ((sidekick n).symm i).elim id (fun _ => 0)
    have ht (i : ℕ) : t (f i)=i := by simp [t,f,old]
    refine ⟨b.image t,?_⟩
    ext a; constructor
    · intro ha
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨c,rfl⟩ := he c hc
      rwa [ht]
    intro ha; obtain ⟨a,rfl⟩ := he a ha
    refine Finset.mem_map.mpr ⟨a,Finset.mem_image.mpr ⟨f a,ha,ht a⟩,rfl⟩
  change tsum h = _
  rw [← (Finset.map_injective f).tsum_eq hz]; exact tsum_congr ht

variable (R : Rep G n)

def bulk := { R with activities := enhanced R.activities }
lemma bulky {σ C Λ δ w : ℝ} (h : R.Lawful σ C Λ δ w) : (bulk R).Lawful σ C Λ δ w :=
  ⟨h.paths, legitimate R.activities _ h.labels⟩
lemma charged : (bulk R).eval=R.eval := by
  funext U
  unfold Rep.eval
  change _ * (enhanced R.activities).gas R.p U = _
  rw [fuels]; rfl
end YM.Extra.Histories.Pads
