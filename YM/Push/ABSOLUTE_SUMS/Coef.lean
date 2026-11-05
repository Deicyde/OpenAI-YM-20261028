import YM.Push.ABSOLUTE_SUMS.Partition

/-! # Coefficient recurrence with *actual* factorials -/

set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Coef
open Relation Graph Ursell Partition Finset
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] (R : ι → ι → Prop) (w : ι → ℝ)

section Numbers
variable (α : Type*) [DecidableEq α] [Fintype α]

def all : ℝ := ∑ z : α → ι, allMass (pot R z) * ∏ i, w (z i)
def linked : ℝ := ∑ z : α → ι, coefficient R z * ∏ i, w (z i)
end Numbers

def gasRow (n : ℕ) := all R w (Fin n) / n.factorial
def logRow (n : ℕ) := linked R w (Option (Fin n)) / (n+1).factorial

section Reindex

variable {α β : Type*} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (e : α ≃ β)

include e in
lemma linked_equiv : linked R w α = linked R w β := by
  symm; apply Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl _))
  intro z
  change coefficient R z * _ = coefficient R (z ∘ e) * ∏ i,w (z (e i))
  rw [relabel R e]; congr 1; exact (Fintype.prod_equiv e _ _ fun i => rfl).symm

include e in
lemma all_equiv : all R w α = all R w β := by
  symm; apply Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl _))
  intro z
  change allMass _ * _ = allMass (pot R (z ∘ e)) * ∏ i,w (z (e i))
  congr 1
  · simp only [Partition.allMass_eq]; rw [relabel_pot R e z]
    simp only [Equiv.finsetCongr,Equiv.coe_fn_mk,Finset.map_eq_empty]
  exact (Fintype.prod_equiv e _ _ fun i => rfl).symm
end Reindex

section SlotSums
variable {α : Type*} [DecidableEq α] [Fintype α]
private def parts (s : Finset α) : (α → ι) ≃ ((↥s → ι) × (↥(sᶜ) → ι)) where
  toFun z := (Partition.restrict s z,Partition.restrict sᶜ z)
  invFun p i := if h : i∈s then p.1 ⟨i,h⟩ else p.2 ⟨i,mem_compl.mpr h⟩
  left_inv z := by funext i; dsimp only; split <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext i; simp [Partition.restrict]
    funext i; have hi : i.val∉s := mem_compl.mp i.property; simp [Partition.restrict,hi]

private lemma subset_cost (s : Finset α) :
    ∑ z : α → ι, (coefficient R (Partition.restrict s z)*allMass (pot R (Partition.restrict sᶜ z)) * ∏ i,w (z i)) =
      linked R w ↥s * all R w ↥(sᶜ) := by
  let x z := coefficient R z * ∏ i : ↥s,w (z i)
  let y z := allMass (pot R z) * ∏ i : ↥(sᶜ), w (z i)
  calc
    _ = ∑ p : (↥s → ι) × (↥(sᶜ)→ι), x p.1 * y p.2 := by
      apply Fintype.sum_equiv (parts s); intro z
      unfold parts x y; dsimp only [Equiv.coe_fn_mk]
      rw [← prod_mul_prod_compl s (f:=fun i => w (z i)), prod_subtype s (p:=(·∈s)) (fun _ => Iff.rfl),
        prod_subtype sᶜ (p:=(·∈sᶜ)) (fun _ => Iff.rfl)]
      unfold Partition.restrict; ring
    _ = _ := by
      change _ = (∑ i,x i)*∑ i,y i
      rw [Fintype.sum_prod_type,sum_mul]; simp only [mul_sum]

lemma unbased (x : α) : all R w α = ∑ s ∈ (univ : Finset (Finset α)) with x∈s,
    linked R w ↥s * all R w ↥(sᶜ) := by
  unfold all
  rw [Finset.sum_congr rfl (fun (i : α → ι) (_:i∈univ) => congr_arg (· * (∏ j,w (i j)))
    (Partition.partition R i x))]
  simp_rw [sum_mul]; rw [sum_comm]; exact sum_congr rfl fun s _ => subset_cost R w s
end SlotSums

lemma discrete (m : ℕ) : all R w (Option (Fin m)) = ∑ k∈range (m+1), (Nat.choose m k:ℝ) *
    (linked R w (Option (Fin k))*all R w (Fin (m-k))) := by
  let V := Option (Fin m)
  rw [unbased R w (none : Option (Fin m))]
  let U := (univ : Finset (Finset V)).filter (none∈·)
  let f := fun s : Finset V => s.card-1
  have he (s : Finset V) (h : none∈s) : s.card = f s+1 := by
    have he := card_pos.mpr (show s.Nonempty from ⟨_,h⟩); unfold f; omega
  have hN (s : Finset V) : s.card ≤ m+1 := by simpa [V] using s.card_le_univ
  have hU (s) (hs : s∈U) : f s∈range (m+1) := by
    have hb := he s (mem_filter.mp hs).2; have hv := hN s
    rw [mem_range]; omega
  rw [← sum_fiberwise_of_maps_to hU (fun s : Finset V => linked R w ↥s * all R w ↥(sᶜ))]
  apply sum_congr rfl; intro k hk
  let Q := U.filter (fun s => f s=k)
  have hQ s (h : s∈Q) : none∈s ∧ s.card=k+1 := by
    obtain ⟨hg,hf⟩ := mem_filter.mp h; have hh := (mem_filter.mp hg).2
    exact ⟨hh,hf ▸ (he s hh)⟩
  have hq : Q.card=Nat.choose m k := by
    let D := (univ : Finset V).erase none
    let e := fun (s : Finset V) => insert none s
    have hd : Q=(D.powersetCard k).image e := by
      ext s; constructor
      · intro h; obtain ⟨h1,h2⟩ := hQ s h
        refine mem_image.mpr ⟨s.erase none,Finset.mem_powersetCard.mpr ⟨?_,?_⟩,insert_erase h1⟩
        · exact Finset.erase_subset_erase _ (subset_univ _)
        rw [Finset.card_erase_of_mem h1,h2]; omega
      intro h; obtain ⟨s,h2,rfl⟩ := mem_image.mp h
      obtain ⟨h1,h2⟩ := Finset.mem_powersetCard.mp h2
      have he : none∉s := fun hi => notMem_erase none _ (h1 hi)
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,mem_insert_self ..⟩,?_⟩
      unfold f e; rw [Finset.card_insert_of_notMem he,h2]; omega
    have hi : Set.InjOn e (↑(D.powersetCard k)) := by
      have hi s (h : s∈D.powersetCard k) : (e s).erase none = s := by
        have hx : none∉s := fun hi => notMem_erase none _ ((Finset.mem_powersetCard.mp h).1 hi)
        simp [e,hx]
      intro i hi' j hj he; rw [← hi i hi',← hi j hj,he]
    rw [hd,Finset.card_image_iff.mpr hi,Finset.card_powersetCard]
    unfold D; simp [card_erase_of_mem,V]
  let C := linked R w (Option (Fin k))*all R w (Fin (m-k))
  calc
    _ = ∑ _i∈Q,C := sum_congr rfl fun s hs => by
      obtain ⟨h1,h2⟩ := hQ s hs
      let e := Fintype.equivOfCardEq (show Fintype.card ↥s=Fintype.card (Option (Fin k)) by simp [h2])
      let d := Fintype.equivOfCardEq (show Fintype.card ↥(sᶜ) = Fintype.card (Fin (m-k)) by simp [V,h2])
      unfold C; rw [linked_equiv R w e, all_equiv R w d]
    _ = _ := by rw [sum_const,hq,nsmul_eq_mul]

/-- Goes into the proof of the differential equation for the
polynomial (evaluate below with the actual absolute series). -/
lemma recurrence (m : ℕ) : (m+1:ℝ)*gasRow R w (m+1) =
    ∑ k∈range (m+1),(k+1:ℝ)*logRow R w k*gasRow R w (m-k) := by
  let e := Fintype.equivOfCardEq (show Fintype.card (Fin (m+1)) = Fintype.card (Option (Fin m)) by simp)
  unfold gasRow logRow
  rw [all_equiv R w e,discrete,sum_div,mul_sum]; apply sum_congr rfl; intro k hk
  have he := Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ (mem_range.mp hk))
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hv : (Nat.choose m k:ℝ)*k.factorial*(m-k).factorial=m.factorial := by exact_mod_cast he
  field_simp
  rw [← hv]; ring
end YM.Push.AbsoluteSums.Coef
