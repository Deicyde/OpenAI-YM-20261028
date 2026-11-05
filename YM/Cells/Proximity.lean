import YM.Cells.Margins

/-! 
One common tiling with margins M for all. Avoid coincidence points by separation
& shrinking physical cube width. Native coordinates only. -/
set_option autoImplicit false
noncomputable section
namespace YM.Cells.Tiling
open Lattice Function Set Filter Finset
open scoped Topology
variable {n : Side} (T : Tiling n)

def newly (o : Site n) : Tiling n := { T with base := o }

def hom : Per n →+* Per T.side := ZMod.castHom (show T.side.val ∣ n.val from by rw [T.units.exact_size]; simp) _

lemma succeeds {m : ℕ} (i : Axis) (x : Fin m → Site n) (K : ℕ) (h : m*(2*K)<T.side.val) :
    ∃ v : Per n, ∀ s, let r := (x s i-v).val % T.side.val
                      K ≤ r ∧ r+K < T.side.val := by
  classical
  let A (s : Fin m) := T.hom (x s i)
  let B : Per T.side → Prop := fun v => K ≤ v.val ∧ v.val+K < T.side.val
  suffices he : ∃ y : Per T.side, ∀ s, B (A s-y) by
    obtain ⟨y,h⟩ := he
    refine ⟨↑y.val,fun s => ?_⟩
    have hx := h s
    unfold B at hx
    have hz (t : Per n) : T.hom t = ↑t.val := calc
      _ = T.hom (↑t.val) := by rw [ZMod.natCast_zmod_val]
      _ = _ := map_natCast ..
    have hv : A s-y = T.hom ((x s i)-(y.val:Per n)) := by rw [map_sub,map_natCast, ZMod.natCast_zmod_val]
    rw [hv,hz (x s i-_), ZMod.val_natCast] at hx; exact hx
  let bad := ((range K).image ((↑) : ℕ→Per T.side)) ∪ ((range K).image fun i : ℕ => (↑(T.side.val-(i+1)):Per T.side))
  have he {y} (ht : y∉bad) : B y := by
    rcases lt_or_ge y.val K with g|g
    · exact (ht (mem_union_left _ (mem_image.mpr ⟨y.val,mem_range.mpr g,ZMod.natCast_zmod_val _⟩))).elim
    refine ⟨g,?_⟩; by_contra! hq
    have hm := y.val_lt
    exact ht (mem_union_right _ (mem_image.mpr ⟨T.side.val - (y.val+1), mem_range.mpr (by omega),by simp [show T.side.val-(T.side.val-(y.val+1)+1) = y.val by omega,Per]⟩))
  let W := Finset.univ.biUnion fun i : Fin m => bad.image fun b => A i-b
  have hx : W.card < Finset.univ.card := calc
    _ ≤ ∑ i : Fin m,(bad.image fun b => A i-b).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin m, 2*K := Finset.sum_le_sum fun i _ => Finset.card_image_le.trans (show bad.card ≤ 2*K by
      unfold bad; apply (Finset.card_union_le ..).trans
      rw [two_mul]
      apply add_le_add _ _ <;> exact Finset.card_image_le.trans (card_range K |>.le))
    _ = m*(2*K) := by simp
    _ < (Finset.univ (α := Per T.side)).card := by simpa [Per] using h
  obtain ⟨y,-,hy⟩ := Finset.exists_mem_notMem_of_card_lt_card hx
  refine ⟨y,fun i => he fun H => hy ?_⟩
  exact mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨_,H,sub_sub_cancel ..⟩⟩

lemma fits_together {m : ℕ} (x : Fin m → Site n) (K : ℕ) (hk : 0 < K) (h : m*(2*K)<T.side.val) :
    ∃ o : Site n, ∀ s, x s∈(T.newly o).margin ((T.newly o).which (x s)) K := by
  choose o ho using fun (i : Axis) => T.succeeds i x K h
  refine ⟨o,fun v => ?_⟩
  let B := T.newly o
  change x v∈B.margin (B.which (x v)) K
  have he (i : Axis) : K ≤ B.coordinated (B.which (x v)) (x v) i ∧ B.coordinated (B.which (x v)) (x v) i+K < B.side.val := by rw [Tiling.residual]; exact ho i v
  refine ⟨fun i => ?_,fun i => ⟨(he i).1,?_⟩⟩
  · have hh := he i
    change B.kind.Strict B.side.val (B.coordinated _ _ _)
    cases B.kind <;> unfold Kind.Strict <;> omega
  have hh := he i
  have ht : B.kind.shift ≤ 1 := by cases B.kind <;> unfold Kind.shift <;> decide
  omega

/-- Periodic site separation on this common cube. -/
lemma extent {v : T.Cell} {x y : Site n} (hx : x∈T.chamber v) (hy : y∈T.chamber v) :
    separation x y ≤ T.side.val := by
  unfold separation pdist; apply Finset.sup_le
  intro i _
  have he {x y} (hx : x∈T.chamber v) (hy : y∈T.chamber v) (hv : T.coordinated v y i ≤ T.coordinated v x i) :
      (ZMod.valMinAbs (x i-y i)).natAbs ≤ T.side.val := by
    rw [ZMod.valMinAbs_natAbs_eq_min]
    apply (min_le_left ..).trans
    rw [show x i-y i=(x i-T.starts v i)-(y i-T.starts v i) by abel, ZMod.val_sub hv]
    exact (Nat.sub_le ..).trans (small T hx _).le
  change (ZMod.valMinAbs (x i-y i)).natAbs ≤ _
  rcases le_total (T.coordinated v y i) (T.coordinated v x i) with h|h
  · exact he hx hy h
  rw [show x i-y i = -(y i-x i) by abel, ZMod.natAbs_valMinAbs_neg]
  exact he hy hx h

/-- Moving by less than k from any margin-k site still fits. Require k positive; no winding comparison. -/
lemma fits_stencil {x : Site n} {v : T.Cell} {k} (hx : x∈T.margin v k) {z : Cover}
    (hz : ∀ a, (z a).natAbs < k) : wrap n z+x ∈ T.chamber v := by
  intro i
  have he := hz i
  obtain ⟨hr,h⟩ := (show _∧_ from hx.2 i)
  let a := T.coordinated v x i
  let b : ℤ := ↑a + z i
  change k ≤ a at hr; change a+k+_ ≤ _ at h
  have hp : 0 < b := by dsimp [b];omega
  have ht : b.toNat < T.side.val := by dsimp [b]; omega
  have hs : T.coordinated v (wrap n z+x) i = b.toNat := by
    unfold coordinated
    rw [show (wrap n z+x) i-T.starts v i = ((b.toNat:ℕ):Per n) from ?_, ZMod.val_natCast_of_lt (ht.trans T.narrow)]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hp.le]; unfold b a; push_cast
    change (z i:Per n)+x i-T.starts v i=_
    simp [coordinated, Per]; abel
  change Kind.Strict _ _ (T.coordinated v _ _); rw [hs]
  cases T.kind <;> unfold Kind.Strict <;> omega
end YM.Cells.Tiling
