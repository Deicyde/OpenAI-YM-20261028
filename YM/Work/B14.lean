import YM.Bid.Phase

/-!
# B14 -- one countable list of Future words

At fixed arity and caps the raw parameters for a Future word are separable.
Use `Table.Pairing.displacement` on these parameters: inner
products of plants vary continuously, *including* in the coefficients by
finite-dimensional multilinearity. So the plant map for each Schwinger
space is continuous here, even if we know nothing separately about that
space's separability. This works with the same parameter spaces and dense
sets for every character. Conclude density of the **span**, as needed to
use countably many plant tests in ground selection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.B14
open Function Set Filter TopologicalSpace Word Table Table.Pairing OS
open scoped Topology BigOperators InnerProductSpace

variable {G : Gauge} {L : Register G} {S : Table L} {a : Axis} {n m : ℕ}

/-- Continuous dependence on positions *and* on label coefficients at given caps.
As when passing to limits for varying coefficient fields, take a fixed finite
sum over all coordinate choices (not varying supports). -/
lemma value_cont {Y : Type*} [TopologicalSpace Y] (h : S.Smooth) (d : Caps n)
    (x : Y → Points n) (hx : Continuous x) (hc : ∀ y, x y ∈ conf n)
    (v : Y → L.Vector d) (hv : ∀ i, Continuous (fun y => v y i)) :
    Continuous (fun y => S.value d (x y) (v y)) := by
  let E (i) := Extraction.dial (L := L) d i
  let J := (i : Fin n) → (L.coord (d i)).Index
  letI : Fintype J := Pi.instFintype
  let B (j : J) (i) := E i (j i)
  let W (t : L.Vector d) (j : J) := ∏ i, (E i).repr (t i) (j i)
  -- The finite-dimensional expansion here uses the same formula
  -- as in Cells.when_varying.
  have he (X : Moment L n d) (t : L.Vector d) :
      X t = ∑ j : J, W t j * X (B j) := by
    have ht : t = fun i => ∑ k, (E i).repr (t i) k • E i k :=
      funext fun i => ((E i).sum_repr _).symm
    conv_lhs => rw [ht]
    rw [MultilinearMap.map_sum]
    exact Finset.sum_congr rfl fun i _ => X.map_smul_univ (fun k => (E k).repr (t k) (i k)) _
  rw [show (fun y => S.value d (x y) (v y)) =
    fun y => ∑ j : J, W (v y) j * S.value d (x y) (B j) from funext (fun _ => he _ _)]
  apply continuous_finsetSum
  intro j _
  have hW : Continuous fun y => W (v y) j := by
    unfold W
    refine continuous_finsetProd _ fun k _ => ?_
    exact ((E k).coord (j k)).continuous_of_finiteDimensional.comp (hv k)
  exact hW.mul ((h.on_conf d (B j)).continuousOn.comp_continuous hx hc)

/-- Positions above the given plane, separated (off diagonals), and raw
reference coefficients, all independent of a character or of S. -/
abbrev Address (L : Register G) (a : Axis) {n : ℕ} (d : Caps n) :=
  {x : Points n // Pairing.single x a} × L.Vector d

def mkFuture (d : Caps n) (x : Address L a d) : Future L a :=
  ⟨realize (fun i => ⟨d i, x.2 i⟩) x.1.val, living _ x.1.property⟩

lemma inner_plant_cont (X : Schwinger S a) (h : S.Symmetric) (hs : S.Smooth) (d : Caps n) (e : Caps m) :
    Continuous (fun y : Address L a d × Address L a e =>
      inner ℂ (X.plant (mkFuture d y.1)) (X.plant (mkFuture e y.2))) := by
  let Y := Address L a d × Address L a e
  let z₁ (y : Y) : Points n := y.1.1.val
  let z₂ (y : Y) : Points m := y.2.1.val
  let z (y : Y) := closedUp a (z₁ y) (z₂ y)
  have hz : Continuous z := by
    have h₁ : Continuous z₁ := continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
    have h₂ : Continuous z₂ := continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
    exact (pairIso a).symm.continuous.comp (h₁.prodMk h₂)
  have hh (y : Y) : z y ∈ conf (n+m) := spans y.1.1.property y.2.1.property
  let v (y : Y) : Fin (n+m) → L.Token := tied (fun i => ⟨d i,y.1.2 i⟩) (fun i => ⟨e i,y.2.2 i⟩) a
  -- S-gram reads the reflected word (including conjugate/H action).
  have he (y : Y) : inner ℂ (X.plant (mkFuture d y.1)) (X.plant (mkFuture e y.2)) = S.read (z y) (v y) := by
    rw [X.measure]
    exact displacement S h _ _ y.1.1.property y.2.1.property
  have hu (i : Fin (n+m)) : ∃ (k : ℕ) (f : Y → L.Ref k), Continuous f ∧ ∀ y, v y i=⟨k,f y⟩ := by
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine ⟨d i, fun y => L.adj (d i) a (y.1.2 i), ?_, ?_⟩
      · have h₁ : Continuous (fun y : Y => y.1.2 i) :=
          (continuous_apply i).comp (continuous_snd.comp continuous_fst)
        change Continuous (fun y : Y => L.mirrorGroup (d i) (Signed.mirror a) (star (y.1.2 i)))
        exact (L.mirrorGroup _ _).continuous_of_finiteDimensional.comp h₁.star
      intro y
      simp only [v,tied,Fin.append_left,Function.comp_apply]; rfl
    · intro i
      refine ⟨e i, fun y => y.2.2 i, (continuous_apply i).comp (continuous_snd.comp continuous_snd), ?_⟩
      intro y
      simp only [v,tied,Fin.append_right]
  choose p q hq hp using hu
  have hp' (y : Y) : v y = fun i => ⟨p i,q i y⟩ := funext (fun i => hp i y)
  rw [funext he]
  simp_rw [hp']
  exact value_cont hs p z hz hh (fun y i => q i y) hq

lemma plant_cont (X : Schwinger S a) (h : S.Symmetric) (hs : S.Smooth) (d : Caps n) :
    Continuous (fun x : Address L a d => X.plant (mkFuture d x)) := by
  let J := Address L a d
  have he := inner_plant_cont X h hs d d
  apply continuous_iff_continuousAt.mpr
  intro x
  apply ketC (D := X.H)
  · exact (he.comp (show Continuous (fun y : J => (y,y)) from continuous_id.prodMk continuous_id)).continuousAt
  exact (he.comp (show Continuous (fun y : J => (x,y)) from continuous_const.prodMk continuous_id)).continuousAt

/-- All positive words are covered, including `[]`. -/
lemma addresses (w : Future L a) : ∃ (n : ℕ) (d : Caps n) (x : Address L a d), mkFuture d x = w := by
  let q := w.val
  let d (i : Fin q.length) : ℕ := (tokens q i).1
  let u : L.Vector d := fun i => (tokens q i).2
  have hx : Pairing.single (positions q) a := ⟨w.property.1,fun i => w.property.2 _ (List.get_mem ..)⟩
  refine ⟨q.length,d,(⟨positions q,hx⟩,u),Subtype.ext ?_⟩
  exact rebuilt q

/-- Choose the addresses once, even before being given the Schwinger spaces. -/
theorem universal (L : Register G) (a : Axis) :
    ∃ R : ℕ → Future L a, ∀ S : Table L, S.Symmetric → S.Smooth → ∀ X : Schwinger S a,
      DenseRange (Finsupp.linearCombination ℂ (fun k => X.plant (R k))) := by
  choose B hB hD using fun (n : ℕ) (d : Caps n) => exists_countable_dense (Address L a d)
  let C : Set (Future L a) := ⋃ n : ℕ, ⋃ d : Caps n, mkFuture d '' B n d
  have hc : C.Countable := countable_iUnion fun n => countable_iUnion fun d => (hB n d).image _
  obtain ⟨R,hR⟩ := (hc.insert (air a)).exists_eq_range (by exact ⟨_, mem_insert _ _⟩)
  refine ⟨R,?_⟩
  intro S h hs X
  let M := LinearMap.range (Finsupp.linearCombination ℂ (fun k => X.plant (R k)))
  have he (n : ℕ) (d : Caps n) : MapsTo (fun x : Address L a d => X.plant (mkFuture d x)) (B n d) M := by
    intro x hx
    have hW : mkFuture d x ∈ Set.range R := by
      rw [← hR]
      exact subset_insert _ _ (mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨d,mem_image_of_mem _ hx⟩⟩)
    obtain ⟨j,hj⟩ := hW
    exact (show X.plant (mkFuture d x) ∈ M from ⟨Finsupp.single j 1,by simp [hj]⟩)
  have ht : Submodule.span ℂ (Set.range X.plant) ≤ M.topologicalClosure := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    obtain ⟨n,d,x,rfl⟩ := addresses w
    exact (he n d).closure (plant_cont X h hs d) (hD n d x)
  change Dense (M : Set X.H)
  intro x
  exact closure_minimal ht M.isClosed_topologicalClosure (X.dense x)

theorem answer : YM.Bid.B14 := by
  intro G C S V A P X p h hs hV hP t W
  obtain ⟨R,hR⟩ := universal C.book timeAxis
  exact ⟨R,fun i => hR (p i) (t.loci i).laws.toSymmetric (t.loci i).smooth (W i).GNS⟩
end YM.Work.B14
