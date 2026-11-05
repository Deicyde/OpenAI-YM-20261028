import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Vault

/-!
# Sheet population invoices

Every expenditure through the packet priced after L, times number of
seeds even when a diameter could be much larger. No factorial component
budget. Useful also for other row/window vertices (absolute addresses).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Rates Mint
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
  {A : Stores S} {x : ℝ}

def densityF (L : Side) := ((L.val:ℝ)^4*16)*(Fintype.card PlaqAxes : ℝ)
def densityC (v : Type) [Fintype v] := 16*(Fintype.card v:ℝ)
def densityRack (L : Side) := (Fintype.card Signed:ℝ) *
    (densityF L+(densityC Axis+(densityC PlaqAxes+densityC Gain)))

lemma governs_fst (c : Side) (α : Type) [Fintype α] : governs (Prod.fst : (Site c×α) → Site c) (densityC α) :=
    population_copy (κ:=α) (id:Site c→Site c) (population_physical _)
lemma governs_booth (S : StepData c f) : governs (crib S) (densityRack S.patch.L) := by
  let K := fun i : Cell f => S.ratio.parent i.1
  have ht : governs K (densityF S.patch.L) := population_copy (κ:=PlaqAxes) S.ratio.parent (population_parent _)
  have he := population_add _ _ ht (population_add _ _ (governs_fst c Axis)
    (population_add _ _ (governs_fst c PlaqAxes) (governs_fst c Gain)))
  exact population_signed _ he

lemma governs_closer {n : Side} {v : Type} [Fintype v] (p : v→Site n) {C Y : ℝ} (hp : governs p C) (hc : C ≤ Y) :
    governs p Y := fun x d => le_trans (hp x d) (by gcongr)

lemma count_dome {v : Type} [Fintype v] (q : v→Site c) (T : Finset v) {A : Stores S} {C : ℝ} {d : ℕ}
    (hc : 0≤C) (he : governs q C) (ht : ∀ i∈T,q i∈A.dome d) :
    (T.card:ℝ) ≤ 4*A.shares * (C*(1+(d:ℝ))^4) := by
  let t x := univ.filter fun i => separation x (q i) ≤ d
  apply le_trans _ (mul_le_mul_of_nonneg_right (b:=((A.place.card:ℕ):ℝ)) ?_ (show 0 ≤ C*(1+(d:ℝ))^4 by positivity))
  · calc
      _ ≤ ((A.place.biUnion t).card:ℝ) := by
        apply Nat.cast_le.mpr (Finset.card_le_card (fun i hi => ?_))
        obtain ⟨o,h,hv⟩ := halo_spec.mp (ht i hi); exact mem_biUnion.mpr ⟨o,h,mem_filter.mpr ⟨mem_univ _,hv⟩⟩
      _ ≤ ((∑ i∈A.place, (t i).card : ℕ):ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ _ := by
        rw [Nat.cast_sum]
        apply le_trans (Finset.sum_le_sum (g:=fun _ => C*(1+(d:ℝ))^4) (fun i _ => he _ _))
        simp
  exact_mod_cast Work.E01.place_card _

-- bundle by *fixed* support factors. Lift receives no volume factor. X flagged selects only paid subsets.


-- Engine for aggregate within p, *actual* prereq U independent.

end YM.AnalyticNext.ConnectedActivity.Aff
