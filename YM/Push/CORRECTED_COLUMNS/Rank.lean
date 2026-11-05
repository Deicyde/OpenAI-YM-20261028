import YM.Next.EXTRACTION.Base
import YM.Push.CORRECTED_COLUMNS.Count
/-!
# Issue RankWidths on the actual smooth hierarchy

`Offer` still an unmet producer requirement as is the finite count
from the equation-comparison physics; see Entry. Uses the same extraction
as all these finite matrices (source and projection). Includes
conjugate partner and exact unit, through all subsets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected
open MeasureTheory Set Function Lattice Cells Wilson Extraction Filter Dash Table Next.Extract
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {S R T : Table C.book} {d : ℕ}
variable {f : Extraction.Order} {b : Presentation C} {B : Bin R} {M : ℕ → Table C.book} {W : DiffPlan T}
variable {h : G.Simple}

section Retarget
-- The S parameter of Columns is *phantom*. Candidate proto data may
-- well be obtained before we get T. Exact transfer.
def retarget (X : Columns C S d) (T : Table C.book) : Columns C T d :=
    ⟨X.dim,X.H,X.basis,X.realBasis,X.initial,X.amount,X.row,X.full⟩
variable {X : Columns C S d}

def Tests.take (Y : Tests X) (T : Table C.book) : Tests (retarget X T) :=
    ⟨Y.B,Y.room,Y.tune,Y.real,Y.unit⟩
lemma Tests.revoke (Y : Tests X) (T : Table C.book) (P : Prices) (h : Tests.Offer Y P f) : Tests.Offer (Y.take T) P f := ⟨h.known,h.solves⟩
lemma Tests.carry (Y : Tests X) (T : Table C.book) (z t) (h : Settled f Y z t) : Settled f (Y.take T) z t := ⟨h.rows,h.outer⟩
end Retarget

section
variable {X : Columns C T d} {Y : Tests X} {P : Prices} {z : ℕ → AxisX X → ℕ → C.label d} {t : ℕ → AxisX X → C.label d}

-- The one actual Trial. lift is the literal path, not only agreeing later.
def offered (h : G.Simple) (Y : Tests X) (P : Prices) (t : ℕ → AxisX X → C.label d) : Columns.Trials X where
  depth := Y.B.depth
  width := Y.B.side
  window := Y.B.side_le
  scale := Y.B.scale
  positive := Y.B.scale_pos
  zoom := (Zone.goesZero _ _ h).comp Y.B.depth.cofinal
  mark k i := Y.B.address k (X.row i).expected
  lift := Y.tune
  later := t
  gap k := Real.exp (P.Q k)/ P.W k
  allowed k := div_nonneg (Real.exp_pos _).le (zero_le_one.trans (P.weight k))
  small := P.runs

-- Y.target already T smooth. Rank not from Gram convergence alone --
-- here using finite COUNT + base bin consequence to prove eventual span.
lemma surject (h : G.Simple) (p : Base C f R M B T W) (H : Y.Offer P f)
    (he : Settled f Y z t) (hc : Persist.Count b f d) (q) (hv : Projected b f B q) :
    ∀ᶠ k in atTop, Surjective (T.project d ∘ₗ Persist.emit X t k) := by
  have hi := Persist.concur hc hv
  rw [← p.null] at hi
  have hp : Module.finrank ℂ (T.Field d)+Module.finrank ℂ (T.null d)=Module.finrank ℂ (C.label d) :=
    Submodule.finrank_quotient_add_finrank _
  filter_upwards [Persist.remains p.family p.clean.mesh H he h] with k hk
  let U := T.project d ∘ₗ Persist.emit X t k
  have ht (x : C.label d) (hx : x ∈ T.null d) (i : Row X) : Persist.pixels T Y t k x i=0 :=
    (T.criterion _ _).mp hx _ _ _ (generic_conf _ ((Y.room k i).1))
  have hu : Injective U := by
    intro a b hab; apply hk
    let L := (T.null d).liftQ (Persist.pixels T Y t k) (fun x hx => LinearMap.mem_ker.mpr (funext fun i => ht x hx i))
    exact congr_arg L hab
  apply LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq _)
  rw [LinearMap.finrank_range_of_inj hu]
  change Module.finrank ℂ ((standard C).Field d) = Module.finrank ℂ (T.Field d)
  have hT : Module.finrank ℂ ((standard C).Field d) ≤ Module.finrank ℂ (T.Field d) := LinearMap.finrank_le_finrank_of_injective hu
  omega

/-- Issue the actual correction. All costs remain on the same fixed
reference fit. No modification of chosen bases for limiting symmetries. -/
lemma valid (h : G.Simple) (p : Base C f R M B T W) (H : Y.Offer P f)
    (he : Settled f Y z t) (hc : Persist.Count b f d) (q) (hv : Projected b f B q) :
    (offered h Y P t).Valid f := by
  let Z := offered h Y P t
  refine
    { ratios := ⟨Y.B.b,Y.B.b0,fun k => rfl⟩
      same_stage k m hm ht := (Y.B.h k).plateau _ hm ht
      conjugate := Y.real
      scale_down := Y.B.decreasing
      unit := Y.unit
      responds := he.respond
      bounded k := by obtain ⟨D,hD,hp⟩ := H.known k; exact ⟨D,hp⟩
      span := ?_
      tuned i := Y.B.tuned h _
      seams := ?_
      generic k i := (Y.room k i).1
      cheap k ε hε := ?_ }
  · filter_upwards [surject h p H he hc q hv] with k hk
    apply top_unique
    intro x _
    let U := T.project d ∘ₗ Persist.emit X t k
    obtain ⟨v,hv⟩ := hk x
    change x ∈ Submodule.span ℂ (Set.range fun i => T.project d (t k i))
    rw [← hv, ← X.basis.sum_repr v,map_sum]
    apply Submodule.sum_mem; intro i _; rw [map_smul]
    apply Submodule.smul_mem; exact Submodule.subset_span ⟨i,by simp [Persist.emit]⟩
  · refine ⟨1/4,by positivity,fun k i j a => ?_⟩
    have hh := (Y.room k i).2 j a
    exact hh.trans_eq (show C.S.a (Y.B.side k)/4=C.S.a (Y.B.side k)*(2⁻¹-1/4) from by ring)
  have hp := H.stamp _ k ε hε
  unfold Order.late at *
  filter_upwards [hp] with i hi
  filter_upwards [hi,f.mesh.cofinal.eventually (Recover.sits p.family Y k)] with j hj ha
  obtain ⟨hm,hj⟩ := hj
  refine ⟨hm,fun v c s => ⟨ha.choose_spec _ v c s,?_,fun x hx => ?_⟩⟩
  · have hg := hj v c {s} (Finset.singleton_nonempty _)
    simp_rw [Tests.single] at hg; exact hg
  have hg := hj v c {s,x} (Finset.insert_nonempty ..)
  simp_rw [Tests.pairs _ _ _ _ _ _ _ _ _ hx] at hg; exact hg
end
end YM.Push.Corrected
