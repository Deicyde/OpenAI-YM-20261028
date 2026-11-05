import YM.Cells.Packing

/-!
# Point estimates on actual cluster grids: automatic limit for varying combinations

Use point port *only at generic configurations* (including distant trains when
generic). No strengthening to R×N filter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Cells
open Function Set Filter MeasureTheory
open Lattice Wilson Extraction
open scoped Topology BigOperators
variable {G : Gauge} {L : Register G} {n : ℕ} (C : Family G) (f : Extraction.Order) (S : Table C.book)

lemma eventual_grid {n k} (H : f.PointLimits C S) (u : Fin n → Cover) (h : Extraction.Order.grid C k u ∈ generic n) (v : Fin n → C.book.Token) :
    f.limits (fun p => Extraction.Order.grid C k u ∈ Cyclic C.S p n) (fun N p => C.numeric N p v (fun i => location C.S k N p (u i)))
      (S.read (Extraction.Order.grid C k u) v) := by
  classical
  let x := Extraction.Order.grid C k u
  obtain ⟨P,hP,hV⟩ := H
  have he : ∀ᶠ i : ℕ in atTop, x∈ Cyclic C.S (f.per i) n := by
    filter_upwards [f.per.cofinal.eventually (room C.S (isCompact_singleton (x := x)))] with i hi
    exact (no_wrap_tie C.S (hi (mem_singleton x))).2 h
  refine ⟨he, fun p => (P p).read x v,?_,?_⟩
  · intro p hp
    let d (N : ℕ) : Fin n → Cover := fun i => if h : k ≤ N then (C.S.toDepth h p).count.val • u i else 0
    have hu : ∀ᶠ j : ℕ in atTop, k ≤ f.mesh j := f.mesh.cofinal.eventually (eventually_ge_atTop _)
    have hx (j : ℕ) (hj : k ≤ f.mesh j) : Extraction.Order.grid C (f.mesh j) (d (f.mesh j)) = x := by
      apply PiLp.ext; intro i
      apply PiLp.ext; intro a
      simp only [x,Extraction.Order.grid,d,dif_pos hj,points_apply]
      simp only [Schedule.gridPoint, WithLp.ofLp_toLp]
      rw [show ((((C.S.toDepth hj p).count.val • u i) : Cover) a : ℤ) =
        ((C.S.toDepth hj p).count.val : ℤ) * u i a by simp]
      rw [Int.cast_mul,Int.cast_natCast, ← mul_assoc,C.S.embeds_scale]
    have ht := f.evaluated C hP p n v x hp (fun j => d (f.mesh j))
      (tendsto_const_nhds.congr' (hu.mono fun i hi => (hx i hi).symm))
    refine ht.congr' (hu.mono ?_)
    intro i hi
    apply congr_arg (C.numeric _ _ _)
    simp_rw [location,d, dif_pos hi, Ratio.embed_wrap]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := hV n {x} isCompact_singleton (singleton_subset_iff.mpr h) v ε hε
  filter_upwards [he] with i hi
  rw [dist_eq_norm]
  exact hi x (mem_singleton _)

lemma when_varying {d : Caps n} (p : C.book.Vector d) (B : ℕ → ℕ → C.book.Vector d) {T : ℕ → ℕ → Moment C.book n d}
    (M : Moment C.book n d) {A : ℕ → Prop} (H : ∀ v, f.limits A (fun N P => T N P v) (M v))
    (H' : ∀ i : Fin n, f.limits A (fun N P => B N P i) (p i)) :
    f.limits A (fun N P => T N P (B N P)) (M p) := by
  have hp := (H p).1
  choose v hv hs using fun x => (H x).2
  choose g hg hh using fun i => (H' i).2
  let E (i) := dial (L := C.book) d i
  let J := (i : Fin n) → (C.book.coord (d i)).Index
  letI : Fintype J := Pi.instFintype
  let Y (r : J) i := E i (r i)
  let W (F : C.book.Vector d) (r : J) := ∏ i, (E i).repr (F i) (r i)
  have he (X : Moment C.book n d) (t : C.book.Vector d) :
      X t = ∑ j : J, W t j * X (Y j) := by
    have hx : t = fun i => ∑ k, (E i).repr (t i) k • E i k :=
      funext fun i => ((E i).sum_repr _).symm
    conv_lhs => rw [hx]
    rw [MultilinearMap.map_sum]; apply Finset.sum_congr rfl
    exact fun i _ => X.map_smul_univ (fun k => (E k).repr (t k) (i k)) _
  refine ⟨hp,fun p => ∑ j : J, W (fun i => g i p) j * v (Y j) p,?_,?_⟩
  · intro P hP
    have HH (j : J) : Tendsto (fun N => W (B (f.mesh N) P) j) atTop (𝓝 (W (fun i => g i P) j)) := by
      apply tendsto_finsetProd _; intro k _
      exact (((E k).coord (j k)).continuous_of_finiteDimensional.continuousAt.tendsto.comp (hg k P hP))
    exact (tendsto_finsetSum Finset.univ (fun j _ => (HH j).mul (hv (Y j) P hP))).congr'
      (Eventually.of_forall fun i => (he (T (f.mesh i) P) (B _ _)).symm)
  rw [he M p]
  refine tendsto_finsetSum _ fun j _ => Tendsto.mul (f := fun s : ℕ => W (fun i => g i (f.per s)) j) ?_ (hs (Y j))
  apply tendsto_finsetProd _; intro k _
  exact ((E k).coord (j k)).continuous_of_finiteDimensional.continuousAt.tendsto.comp (hh k)

lemma keeps_moments {k d} (u : Fin n → Cover) (hx : Extraction.Order.grid C k u∈ generic n) (H : f.PointLimits C S)
    (p : C.book.Vector (n := n) d) (B : ℕ → ℕ → C.book.Vector d)
    (hB : ∀ i : Fin n, f.limits (fun _ => True) (fun N P => B N P i) (p i)) :
    f.limits (fun p => Extraction.Order.grid C k u ∈ Cyclic C.S p n) (fun N P => C.ensemble d (fun i => location C.S k N P (u i)) (B N P))
    (S.value d (Extraction.Order.grid C k u) p) := by
  let A p := Extraction.Order.grid C k u ∈ Cyclic C.S p n
  have he (v : C.book.Vector d) : f.limits A (fun N P => C.ensemble d (fun i => location C.S k N P (u i)) v)
      (S.value d (Extraction.Order.grid C k u) v) := eventual_grid C f S H u hx (fun i => ⟨d i,v i⟩)
  apply when_varying C f p B _ he
  intro i
  obtain ⟨-,v,hV,ht⟩ := hB i
  exact ⟨(he p).1,v,fun p _ => hV p trivial,ht⟩
end YM.Cells
