import YM.Push.GRID_APPROXIMATION.Iterate

/-!
# Simultaneous evaluation under the same kernels

Full cell read sets, not bounding just the lengths of main probes: can
change laws if allowing two query cones to share a site tag. Here use the
proved cone widths from the **actual** paths. Number of different copies is
arbitrary. The radius prerequisite in these uses is independent of that
number.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson Cells Set Filter MeasureTheory Function
open scoped Topology BigOperators

variable {G : Gauge} {c f : Side}

lemma back_cells (S : StepData c f) (h : S.patch.Branches S.kernel G) (β : ℝ) (T : Tiling c)
    (l : Finset T.Cell) (F : T.Cell → Config G c → ℂ) (he : ∀ i∈l, Interior (T.chamber i) (F i)) :
    back S β (fun V => ∏ i∈l, F i V) = fun U => ∏ i∈l, back S β (F i) U := by
  classical
  induction l using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]; exact back_const (S.isKernel h β) 1
  | insert i l hi ih =>
    let X : Set (Site c) := {x | T.which x ∈ l}
    let V (x : Config G c) := ∏ i∈l, F i x
    have ht := he i (Finset.mem_insert_self ..)
    have hs j (hj : j∈l) := he j (Finset.mem_insert_of_mem hj)
    have hx : Interior X V := Interior.combines F l fun j hj => (hs j hj).enlarges
      (fun u hu => show T.which u ∈ l from (T.which_chamber hu).symm ▸ hj)
    have hd : Disjoint (T.chamber i) X := Set.disjoint_left.mpr fun x he hh =>
      hi ((T.which_chamber he) ▸ hh)
    have hb := back_factors h (cylinder_env ht) (cylinder_env hx) ht.localSites hx.localSites hd β
    simp_rw [Finset.prod_insert hi]
    change back S β (F i * V) = fun U => _
    rw [hb,show back S β V = _ from ih hs]; rfl

/-- Geometry ensures disjoint cones at *every* intervening call. -/
lemma backTo_cells (A : History G) (N p : ℕ) {h k m : ℕ} (hk : h ≤ k) (q : k ≤ m)
    (l : Finset (Site (A.S.side h p))) (F : Site (A.S.side h p) → Config G (A.S.side k p) → ℂ) (r : ℕ)
    (he : ∀ i∈l, Interior (window (anchor A.S p hk i) r) (F i)) (hh : room A.levels h k r) :
    backTo A N p q (fun V => ∏ i∈l, F i V) = fun U => ∏ i∈l, backTo A N p q (F i) U := by
  induction m, q using Nat.le_induction with
  | base => simp
  | succ m q ih =>
    simp_rw [backTo_next A N p q, ih]; apply back_cells _ (A.levels.blocks ..).branches _ (tilesAt A.S p (hk.trans q))
    intro i hi; exact (backTo_local A N p hk q i r (he i hi)).enlarges (room_fits p A.levels r hk q hh i)

variable (A : History G) (N p : ℕ) {h k m : ℕ}

-- Need the transformed observable too, with possible conjugation. Pass
-- its actual radius, generally much smaller than the final assigned cell.
lemma copy_window (hk : h ≤ k) (i : Site (A.S.side h p)) (r : ℕ) (F : Config G (A.S.side k p) → ℂ)
    (he : Interior (window 0 r) F) :
    Interior (window (anchor A.S p hk i) r) ((tilesAt A.S p hk).copy i F) := by
  have hx := window_affine (r:=r) 0 (anchor A.S p hk i) ((tilesAt A.S p hk).omega i)
  rw [show affine _ _ 0 = anchor A.S p hk i from by simp [affine]] at hx
  have hb := he.unchanged _ _ hx
  classical
  unfold Tiling.copy
  rw [tile_translate A.S p hk i]
  by_cases hh : (tilesAt A.S p hk).hand i <;> simp only [hh,↓reduceIte]; exacts [hb.real,hb]

lemma backTo_copies (hk : h ≤ k) (q : k ≤ m)
    (l : Finset (Site (A.S.side h p))) (F : Config G (A.S.side k p) → ℂ) (r : ℕ)
    (he : Interior (window 0 r) F) (hh : room A.levels h k r) :
    backTo A N p q (fun V => ∏ i∈l, (tilesAt A.S p hk).copy i F V) =
      fun U => ∏ i∈l, (tilesAt A.S p (hk.trans q)).copy i (backTo A N p q F) U := by
  let X := fun i : Site (A.S.side h p) => (tilesAt A.S p hk).copy i F
  have hx := backTo_cells A N p hk q l X r (fun i _ => copy_window A p hk i r F he) hh
  unfold X at hx
  refine hx.trans ?_; simp_rw [backTo_copy A N p hk q _ (cylinder_env he)]
end YM.Push.GridApprox
