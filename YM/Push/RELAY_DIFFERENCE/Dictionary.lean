import YM.Push.RELAY_DIFFERENCE.SingleMajorant

/-!
# Supplying the Range call from a literal dictionary

Can use when speaker presents L on the EXACT old labels for each call
(same principle ). Not an assertion these arrays at these
prices exist. Useful especially if using always the same moves and
addresses for the comparison columns even at all finer steps. Does ALL
copies and directions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference.Single
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson RG Labels Lattice Cells Marker Overlay Stock Bid Source Mix
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {C : Family G} {N p m i d r : ℕ} {f : Extraction.Order} {F : Trial C} {P : Prices}

local notation "Centrants" => Site (C.side m p)

open scoped Classical in
/-- Indexed identification of all singleton terms INSIDE the same L,
at this level. Same orientation as its arbitrary-later futures in
ArrayStep. `Active` will additionally demand all its rooted labels; in
particular must have secured the kernel alphabet to carry these. Can use
`Activities.Moves` when constructing if appropriate. Don't ask the new L
to infer Frame dynamics. Extra addresses allowed (require their one-body
components vanish on that stencil, not simply cancel with other terms).
-/
structure Dictionary (S : Solo C F d) (L : GridLane C m N p) (hi : m ≤ i) where
  token : Centrants × ℕ ↪ ℕ
  idF : Centrants × ℕ ↪ (ℕ × ℕ)
  pins (j : Centrants) : (L.sites i).origins j = camp C p m i j
  measure j : (L.sites i).units j = hand (decide ((center C.S p hi 0).hand j)) ((germ S N p i).x 0)
  localH j k : let x := camp C p m i j
               let T := center C.S p hi 0
               let s := T.omega j; let B := L.sites i; let l := token (j,k)
               B.rays l=(census _).fire j ∧ B.support l=(roots S N p i k).image (affine s x) ∧
               B.H l = oriented (body S N p i k) (decide (T.hand j)) s x
  tagged j k : let x := camp C p m i j
               let T := center C.S p hi 0
               let s := T.omega j; let B := L.sites i; let l := idF (j,k)
               B.marks l.1 l.2 = (census _).fire j ∧ bareSet C N p i l.1=(bareSet C N p i k).image (affine s x) ∧
               B.entries l.1 l.2 = oriented ((germ S N p i).forced k) (decide (T.hand j)) s x
  blank (j) : ranked ((L.sites i).rays j)=false → j ∉ Set.range token → (L.sites i).H j=0
  lean (j : ℕ × ℕ) : ranked ((L.sites i).marks j.1 j.2)=false → j ∉ Set.range idF → (L.sites i).entries j.1 j.2=0



open scoped Classical in
private def file {ι ι' V : Type*} (f : ι → ι') (a : ι → V) (b : ι' → V) (i : ι') :=
    if h : i∈ Set.range f then a (Classical.choose h) else b i



variable {S : Solo C F d} {L : GridLane C m N p} {hi : m ≤ i}



/-- Replace singly priced Stubs costs and keep the mixed charts. -/
theorem replace {B T : Stubs (L.sites i)}
    (hh : ∀ j,ranked ((L.sites i).rays j)=true → T.a j=B.a j)
    (he : ∀ j : ℕ × ℕ,ranked ((L.sites i).marks j.1 j.2)=true → T.k j=B.k j)
    (u δ c d : ℝ) : Mixed T u δ c d ↔ Mixed B u δ c d := by
  let A := L.sites i
  have ht (i : Site (C.side m p)) (j : ℕ) :
      (if ranked (A.rays j)=true ∧ i∈(A.rays j).val then T.crown (fun _ => u) δ j else 0)=
       (if ranked (A.rays j)=true ∧ i∈(A.rays j).val then B.crown (fun _ => u) δ j else 0) := by
    split_ifs with hv; unfold Stubs.crown; rw [hh _ hv.1]
    rfl
  have hz (i : Site (C.side m p)) (j : ℕ × ℕ) :
      (if ranked (A.marks j.1 j.2)=true ∧ i∈(A.marks j.1 j.2).val then T.cord (fun _ => u) δ j else 0)=
       (if ranked (A.marks j.1 j.2)=true ∧ i∈(A.marks j.1 j.2).val then B.cord (fun _ => u) δ j else 0) := by
    split_ifs with hv; unfold Stubs.cord; rw [he _ hv.1]
    rfl
  unfold Mixed
  dsimp only [A] at ht hz; simp_rw [ht,hz]


end YM.Push.RelayDifference.Single
