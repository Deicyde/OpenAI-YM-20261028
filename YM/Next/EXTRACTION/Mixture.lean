import YM.Next.EXTRACTION.Tails
import YM.Org.Theatre

/-!
# Read out varying finite label combinations on the common extraction

At each fixed weak scale, for example, one may be able to prove bounds for
an auxiliary matrix of comparison coefficients and include its row and outer
limits using `raw` or `Reserve.gather`. Show what such limits buy regarding
point correlations and tested convergence. Use exactly the same tables,
including the individual-period tables (there is no assumption of a smooth
limit or of a distributional estimate for coefficients). Include compact
smooth separated tests, hence axis ties in their supports are allowed,
although there's no point claim at these ties. Cf. . The bounds
needed in `Reserve` are not automatically available from bounds for physical
moments; there is no inference of that kind here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Extract
open Function Set Filter MeasureTheory Extraction Lattice
open scoped Topology BigOperators

section Expansions
variable {G : Gauge} {L : Register G} {n : ℕ} {d : Caps n}

/- One finite basis for each slot. -/
private abbrev Choice (L : Register G) (d : Caps n) := (i : Fin n) → (L.coord (d i)).Index

private def scaleBy (d : Caps n) (v : L.Vector d) (r : Choice L d) :=
  ∏ i, (dial (L:=L) d i).repr (v i) (r i)
private def inBasis (d : Caps n) (r : Choice L d) : L.Vector d := fun i => dial d i (r i)

private lemma basis_expansion (M : Moment L n d) (v : L.Vector d) :
    M v = ∑ r : Choice L d, scaleBy d v r * M (inBasis d r) := by
  classical
  let E (i) := dial (L := L) d i
  have ht (i) : ∑ k, (E i).repr (v i) k • E i k = v i := (E i).sum_repr _
  conv_lhs => rw [← funext ht]
  rw [MultilinearMap.map_sum]
  exact Finset.sum_congr rfl fun r _ => M.map_smul_univ (fun i => (E i).repr (v i) (r i)) _

private lemma scale_limit {v : ℕ → L.Vector d} {w : L.Vector d} (h : Tendsto v atTop (𝓝 w)) (r : Choice L d) :
    Tendsto (fun j => scaleBy d (v j) r) atTop (𝓝 (scaleBy d w r)) := by
  apply tendsto_finsetProd Finset.univ
  intro k _
  exact ((dial (L:=L) d k).coord (r k)).continuous_of_finiteDimensional.continuousAt.tendsto.comp (tendsto_pi_nhds.mp h k)

/-- Name the slots of these actual Wilson moments (different capped weight
in every slot allowed). -/
def names (L : Register G) (d : Caps n) (v : L.Vector d) (i : Fin n) : L.Token := ⟨d i,v i⟩




end Expansions

section Uniform
variable {α : Type*}

/-- Local argument, varying subsets of arbitrary location index. -/
private def patch (A : ℕ → α → Prop) (u v : ℕ → α → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∀ r : α, A j r → ‖u j r - v j r‖ < ε

private lemma patch_sum {ι : Type*} {A : ℕ → α → Prop} {u v : ι → ℕ → α → ℂ}
    (H : ∀ i, patch A (u i) (v i)) (I : Finset ι) :
    patch A (fun j r => ∑ i ∈ I, u i j r) (fun j r => ∑ i ∈ I, v i j r) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact fun _ h => Eventually.of_forall fun _ _ _ => (by simpa using h)
  | @insert i I hi ih =>
    intro ε hε
    filter_upwards [H i (ε/2) (by positivity), ih (ε/2) (by positivity)] with j hj hj' r hr
    rw [Finset.sum_insert hi,Finset.sum_insert hi,add_sub_add_comm]
    exact lt_of_le_of_lt (norm_add_le _ _) ((add_lt_add (hj r hr) (hj' r hr)).trans_eq (by ring))

private lemma patch_product {A : ℕ → α → Prop} {u v : ℕ → α → ℂ} (H : patch A u v)
    (hp : ∃ R : ℝ, ∀ᶠ j : ℕ in atTop, ∀ r, A j r → ‖v j r‖ ≤ R)
    {c : ℕ → ℂ} {w : ℂ} (h : Tendsto c atTop (𝓝 w)) : patch A (fun j r => c j * u j r) (fun j r => w * v j r) := by
  obtain ⟨R,hR⟩ := hp
  let M := max R 0 + 1
  have hm : 0 < M := by dsimp [M]; positivity
  let L := ‖w‖ + 1
  have hL : 0 < L := by dsimp [L]; positivity
  intro ε hε
  filter_upwards [hR,H (ε/(2*L)) (by positivity), h.norm.eventually (gt_mem_nhds (lt_add_one ‖w‖)),
    Metric.tendsto_nhds.mp h (ε/(2*M)) (by positivity)] with j hd hj hl hw r hr
  have hc : ‖c j-w‖ < ε/(2*M) := by simpa only [dist_eq_norm] using hw
  have ha : ‖v j r‖ ≤ M := (hd r hr).trans ((le_max_left _ _).trans <| le_add_of_nonneg_right zero_le_one)
  specialize hj r hr
  change ‖c j * u j r - w * v j r‖ < _
  calc
    ‖c j * u j r - w * v j r‖ = ‖c j*(u j r - v j r) + (c j - w)*v j r‖ := by ring_nf
    _ ≤ ‖c j‖*‖u j r-v j r‖ + ‖c j-w‖*‖v j r‖ := by simpa only [norm_mul] using norm_add_le (c j*(u j r - v j r)) ((c j - w)*v j r)
    _ ≤ L*‖u j r - v j r‖ + ‖c j - w‖*M := by gcongr
    _ < L*(ε/(2*L)) + ε/(2*M)*M := add_lt_add (by gcongr) (by gcongr)
    _ = ε := by field_simp; ring

private lemma patch_variation {A : ℕ → α → Prop} {G : Gauge} {L : Register G} {n : ℕ} {d : Caps n}
    (F P : ℕ → α → Moment L n d)
    (h : ∀ v : L.Vector d, patch A (fun j r => F j r v) (fun j r => P j r v))
    (hm : ∀ v : L.Vector d, ∃ C : ℝ, ∀ᶠ j : ℕ in atTop, ∀ r, A j r → ‖P j r v‖ ≤ C)
    {u : ℕ → L.Vector d} {v : L.Vector d} (hu : Tendsto u atTop (𝓝 v)) :
    patch A (fun j r => F j r (u j)) (fun j r => P j r v) := by
  classical
  have H (i : Choice L d) := patch_product (h (inBasis d i)) (hm (inBasis d i)) (scale_limit hu i)
  have he (j r) : F j r (u j) = _ := basis_expansion (F j r) (u j)
  have ht (j r) : P j r v = _ := basis_expansion (P j r) v
  simp_rw [he,ht]
  exact patch_sum H Finset.univ
end Uniform

section Passage
variable {G : Gauge} {C : Family G} {S : Table C.book} {M : ℕ → Table C.book} {f : Extraction.Order}
variable {n : ℕ} {d : Caps n} {v : ℕ → C.book.Vector d} {u : C.book.Vector d}

/-- Coordinate varying columns, local uniform version on the actual cutoff
grids. ALL p's separately. Cyclically generic, not all of Conf here. -/
theorem mixture_mesh (H : f.Meshes C M) (p : ℕ) {K : Set (Points n)} (hK : IsCompact K) (hk : K ⊆ Cyclic C.S p n)
    (he : Tendsto v atTop (𝓝 u)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∀ r : Fin n → Cover, Order.grid C (f.mesh j) r ∈ K →
      ‖C.numeric (f.mesh j) p (names C.book d (v j)) (fun i => wrap _ (r i)) -
        (M p).value d (Order.grid C (f.mesh j) r) u‖ < ε := by
  let A (j : ℕ) (r : Fin n → Cover) := Order.grid C (f.mesh j) r ∈ K
  let F (j : ℕ) (r : Fin n → Cover) : Moment C.book n d := C.ensemble d (fun i => wrap (C.side (f.mesh j) p) (r i))
  let P (j : ℕ) (r : Fin n → Cover) := (M p).value d (Order.grid C (f.mesh j) r)
  have ht (w : C.book.Vector d) : patch A (fun j r => F j r w) (fun j r => P j r w) := H.onK p n K hK hk (names C.book d w)
  refine patch_variation F P ht (fun w => ?_) he ε hε
  obtain ⟨B,hb⟩ := hK.exists_bound_of_continuousOn ((H.continuous p (names C.book d w)).mono hk)
  exact ⟨B,Eventually.of_forall fun j r hr => hb _ hr⟩

/-- The same local uniform passage for the outer period limit. `H.regular`
for S suffices; can also use its later `Cleaner.mesh`. -/
theorem mixture_volume (H : RawLimits C f S M) {K : Set (Points n)} (hK : IsCompact K) (hk : K ⊆ generic n)
    (he : Tendsto v atTop (𝓝 u)) (ε : ℝ) (hε : 0 < ε) : ∀ᶠ j : ℕ in atTop, ∀ x ∈ K,
      ‖(M (f.per j)).value d x (v j) - S.value d x u‖ < ε := by
  let F (j : ℕ) (x : Points n) := (M (f.per j)).value d x
  let P (_ : ℕ) (x : Points n) := S.value d x
  have ht (w : C.book.Vector d) : patch (fun _ x => x ∈ K) (fun j x => F j x w) (fun j x => P j x w) :=
    H.volume n K hK hk (names C.book d w)
  refine patch_variation F P ht (fun w => ?_) he ε hε
  obtain ⟨B,hb⟩ := hK.exists_bound_of_continuousOn ((H.regular _ (names C.book d w)).mono hk)
  exact ⟨B,Eventually.of_forall fun j x hx => hb _ hx⟩


end Passage
end YM.Next.Extract
