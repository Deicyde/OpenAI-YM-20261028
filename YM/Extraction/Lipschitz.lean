import YM.Extraction.Integrate
import YM.Extraction.Stencil
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Use *lattice* equicontinuity. Supply from finite-cutoff transfer, not assumed

Proves one common ordered extraction, all fixed ordinary families, with
point limits on generic patches and integral limits on separated ones.
Does not supply the lattice oscillation/modulus itself, nor bootstrap through
coordinate ties. Each stage requirement explicit. B does NOT need to be uniform
as Volumes grow for the *each*-p demand; analogous distinction for modulus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open Function Set Filter Metric MeasureTheory Lattice TopologicalSpace
open scoped Topology ContDiff BigOperators

variable {G : Gauge} (C : Family G) (f : Order)

def LocalLattice {n : ℕ} (K : Set (Points n)) (v : Fin n → C.book.Token) (ε t : ℝ) (N p : ℕ) :=
  ∀ (b u : Fin n → Cover), tag (C.S.a N) b ∈ K → tag (C.S.a N) u ∈ K →
    dist (tag (C.S.a N) b) (tag (C.S.a N) u) < t → dist (lifted C N p v b) (lifted C N p v u) < ε

structure TransferLip : Prop where
  grid (p n : ℕ) (K : Set (Points n)) (h : IsCompact K) (hu : K ⊆ Cyclic C.S p n) (v : Fin n → C.book.Token)
      (ε : ℝ) (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i : ℕ in atTop, LocalLattice C K v ε δ (f.mesh i) p
  expanding (n) (K : Set (Points n)) (h : IsCompact K) (hu : K ⊆ generic n) (v : Fin n → C.book.Token)
      (ε : ℝ) (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ f.late (LocalLattice C K v ε δ)

theorem further (H : TransferLip C f) (g : Order) : TransferLip C (f.refine g) := by
  constructor
  · intro p n K h hu v ε hε
    obtain ⟨b,hb,H⟩ := H.grid p n K h hu v ε hε
    exact ⟨b,hb,g.mesh.cofinal.eventually H⟩
  intro n K h hu v ε hε
  obtain ⟨b,hb,H⟩ := H.expanding n K h hu v ε hε
  exact ⟨b,hb, Order.late_refine _ _ H⟩

def extendCut (N p : ℕ) : Table C.book where
  value d x := C.ensemble d (bucket N p x)

private lemma delta (n : ℕ) {ε : ℝ} (h : 0 < ε) : ∀ᶠ i : ℕ in atTop,
    ∀ x : Points n, dist (tag (C.S.a (f.mesh i)) (address (C.S.a (f.mesh i)) x)) x < ε := by
  have he : Tendsto (fun i => (4*n : ℝ)*C.S.a (f.mesh i)) atTop (𝓝 0) := by
    convert ((C.S.shrinks.comp f.mesh.cofinal).const_mul (4*n : ℝ)) using 1 <;> simp
  filter_upwards [he.eventually (gt_mem_nhds h)] with i hi x
  exact lt_of_le_of_lt (approximate (C.S.a_pos _) _) hi

lemma each_oscillates (H : TransferLip C f) (p n : ℕ) (v : Fin n → C.book.Token) :
    oscillation (Cyclic C.S p n) (fun i x => (extendCut C (f.mesh i) p).read x v) := by
  intro K hu hk ε hε
  obtain ⟨t,ht,hT⟩ := hk.exists_cthickening_subset_open (cyclicOpen C.S p n) hu
  obtain ⟨d,hd,H⟩ := H.grid p _ (cthickening t K) hk.cthickening hT v ε hε
  refine ⟨d/4,by positivity,?_⟩
  filter_upwards [H,delta C f n ht,delta C f n (show 0 < d/4 by positivity)] with i hi hf he x hx y hy hw
  let a := C.S.a (f.mesh i)
  let o (x : Points n) := tag a (address a x)
  refine hi (address a x) (address a y) ?_ ?_ ?_
  · exact mem_cthickening_of_dist_le _ x _ K hx (hf x).le
  · exact mem_cthickening_of_dist_le _ y _ K hy (hf y).le
  change dist (o x) (o y) < _
  have hr : dist (o x) x < d/4 := he x
  have hh : dist (o y) y < d/4 := he y
  have H := dist_triangle (o x) x y
  have hz := dist_triangle (o x) y (o y)
  rw [dist_comm] at hh; linarith

lemma address_matched {t : ℝ} (h : 0 < t) {n} (b : Fin n → Cover) : address t (tag t b) = b := by
  funext i j
  unfold address
  change ⌈t * (b i j : ℤ) / t⌉ = _
  rw [mul_comm t,mul_div_cancel_right₀ _ (ne_of_gt h)]; simp

def meshMore (t : Sequence) : Order := ⟨t,.full⟩

theorem setMeshes (H : TransferLip C f) (hB : Bound C f) : ∃ t : Sequence, ∃ P,
    (f.refine (meshMore t)).Meshes C P := by
  classical
  let I := ℕ × Indices C.book
  let U (i : I) := Cyclic C.S i.1 i.2.1
  let W (z : I) (j : ℕ) (x : Points z.2.1) := (extendCut C (f.mesh j) z.1).read x (stack z.2)
  have he (z : I) (x : Points z.2.1) (hx : x ∈ U z) : ∃ D : ℝ, ∀ᶠ i in atTop, ‖W z i x‖ ≤ D := by
    obtain ⟨K,hk,hv,h⟩ := exists_compact_subset (cyclicOpen C.S ..) hx
    obtain ⟨D,hD,H⟩ := hB.cyclic _ (stack z.2) z.1 K hk (fun _ hy i j hij => ⟨timeAxis,h hy i j hij _⟩)
    refine ⟨D,?_⟩
    filter_upwards [H, ((chosen (S := C.S) x).comp f.mesh.cofinal).eventually (mem_interior_iff_mem_nhds.mp hv)] with i hi hi'
    exact hi _ hi'
  obtain ⟨t,B,hBc⟩ := localAscoli (fun p : I => Points p.2.1) U (fun i => cyclicOpen C.S _ _) W
    (fun z : I => each_oscillates _ _ H z.1 _ (stack z.2)) he
  let P (p : ℕ) := fitted fun i : Indices C.book => B (p,i)
  have ht (p n) (v : Fin n → C.book.Token) : Meets (Cyclic C.S p n)
      (fun j x => (extendCut C (f.mesh (t j)) p).read x v) (fun x => (P p).read x v) := by
    apply components (P p) (fun i => extendCut C (f.mesh (t i)) p) (Cyclic C.S p) _ n v
    intro i; simpa only [P, knobs] using! (hBc (p,i))
  refine ⟨t,P, ⟨fun {i} p v => (ht p i v).continuousOn,?_⟩⟩
  intro p n K h hk v ε hε
  filter_upwards [(ht p n v).uniform K hk h ε hε] with i hi r hr
  let a := C.S.a (f.mesh (t i))
  have he := hi (tag a r) hr
  rw [dist_eq_norm] at he
  change ‖lifted C (f.mesh (t i)) p v (address a (tag a r)) - (P p).read (tag a r) v‖ < ε at he
  rw [address_matched (show 0 < a from C.S.a_pos _)] at he
  exact he

lemma genericOpen (n : ℕ) : IsOpen (generic n) := by
  have he : generic n = ⋂ i : Fin n, ⋂ j : Fin n, ⋂ _ : i ≠ j, ⋂ a : Axis,
      {x : Points n | x i a ≠ x j a} := by
    ext x
    simp only [generic,mem_setOf_eq, mem_iInter]
    exact ⟨fun h i j hij a => (h a).ne hij, fun h a i j hij => by_contra fun w => h i j w a hij⟩
  rw [he]; exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite
    fun _ => isOpen_iInter_of_finite fun a => isOpen_ne_fun (by fun_prop) (by fun_prop)

lemma volume_oscillates (H : TransferLip C f) (n : ℕ) {P} (Hp : f.Meshes C P) (v : Fin n → C.book.Token) :
    oscillation (generic n) (fun i x => (P (f.per i)).read x v) := by
  intro K hU hk ε hε
  obtain ⟨T,hT,hKT,hTg⟩ := exists_compact_between hk (genericOpen n) hU
  obtain ⟨d,hd,H⟩ := H.expanding n _ hT hTg v (ε/2) (by positivity)
  refine ⟨d,hd,?_⟩
  unfold Order.late at H
  filter_upwards [H, f.per.cofinal.eventually (room C.S hT)] with i hi hr x hx y hy hD
  let p := f.per i
  have he (x : Points n) (hx : x ∈ K) : x ∈ Cyclic C.S p n :=
    (no_wrap_tie C.S (hr (interior_subset (hKT hx)))).mpr (hU hx)
  let a (j : ℕ) := C.S.a (f.mesh j)
  let r (x : Points n) (j : ℕ) := address (a j) x
  let w j := tag (a j) (n := n)
  have hu (x) : Tendsto (fun i => w i (r x i)) atTop (𝓝 x) := (chosen (S := C.S) x).comp f.mesh.cofinal
  have hh (x hx) := f.evaluated C Hp p n v x (he x hx) (r x) (hu x)
  have ht : dist ((P (f.per i)).read x v) ((P (f.per i)).read y v) ≤ ε/2 := by
    apply le_of_tendsto ((hh x hx).dist (hh y hy))
    have hp := ((hu x).dist (hu y)).eventually (gt_mem_nhds hD)
    filter_upwards [hi, hp,(hu x).eventually (mem_interior_iff_mem_nhds.mp (hKT hx)),
      (hu y).eventually (mem_interior_iff_mem_nhds.mp (hKT hy))] with j ht hu hv hw
    exact (ht (r x j) (r y j) hv hw hu).le
  linarith

private lemma extendsBound (H : Bound C f) {n : ℕ} {P} (Hp : f.Meshes C P) (v : Fin n → C.book.Token) {x}
    (hx : x ∈ generic n) : ∃ D : ℝ, ∀ᶠ i in atTop, ‖(P (f.per i)).read x v‖ ≤ D := by
  obtain ⟨K,hk,hI,hU⟩ := exists_compact_subset (genericOpen n) hx
  obtain ⟨R,hR,H⟩ := H.volume n v K hk (Subset.trans hU (generic_conf _))
  refine ⟨R,?_⟩
  unfold Order.late at H
  have ht := (chosen (S := C.S) x).comp f.mesh.cofinal
  filter_upwards [H, f.per.cofinal.eventually (room C.S hk)] with i hi hr
  let p := f.per i
  have he : x ∈ Cyclic C.S p n := (no_wrap_tie C.S (hr (interior_subset hI))).2 hx
  have hh := f.evaluated C Hp p n v x he (fun i => address (C.S.a (f.mesh i)) x) ht
  refine le_of_tendsto hh.norm ?_
  filter_upwards [hi,ht.eventually (mem_interior_iff_mem_nhds.mp hI)] with j h hk
  exact h _ hk

/-- Generic smoothness through ties will require bootstrap; retain both S and all P. -/
structure RawLimits (S : Table C.book) (P : ℕ → Table C.book) : Prop where
  regular (n : ℕ) (v : Fin n → C.book.Token) : ContinuousOn (fun x => S.read x v) (generic n)
  mesh : f.Meshes C P
  volume : f.VolumePoints C S P
  integral : f.Ordered C S

theorem copy_down {P} {S} (h : RawLimits C f S P) (g) : RawLimits C (f.refine g) S P :=
  ⟨h.regular, ⟨h.mesh.continuous, fun p n K hh he v ε hε => g.mesh.cofinal.eventually (h.mesh.onK p n K hh he v ε hε)⟩,
    fun n K hk he v ε hε => g.per.cofinal.eventually (h.volume n K hk he v ε hε), Order.upon h.integral g⟩

theorem first_surface (H : TransferLip C f) (h : Bound C f) :
    ∃ g : Order, ∃ S P, RawLimits C (f.refine g) S P := by
  obtain ⟨t,P,hP⟩ := setMeshes C f H h
  let w := f.refine (meshMore t)
  let F (p : Indices C.book) (j) (x) := (P (w.per j)).read x (stack p)
  obtain ⟨u,v,hu⟩ := localAscoli (fun i : Indices C.book => Points i.1) (fun i => generic i.1) (fun i => genericOpen _)
    F (fun p => volume_oscillates _ _ (further _ _ H _) p.1 hP (stack p))
    (fun p x hx => extendsBound _ _ (h.further _) hP _ hx)
  let g := Order.mk t u
  let S := fitted v
  have Hs (n) (p : Fin n → C.book.Token) : Meets (generic n)
      (fun i x => (P ((f.refine g).per i)).read x p) (fun x => S.read x p) := by
    apply components S (fun i => P _) generic _ n p
    intro i; simpa only [S,knobs] using! hu i
  have hm : (f.refine g).Meshes C P := ⟨hP.continuous,hP.onK⟩
  have hV : (f.refine g).VolumePoints C S P := by
    intro n K hk he v ε hε
    simpa only [dist_eq_norm] using (Hs n v).uniform K he hk ε hε
  exact ⟨g,S,P,⟨fun n p => (Hs n p).continuousOn,hm,hV, Order.poses _ _ (h.further g) ⟨P,hm,hV⟩⟩⟩
end YM.Extraction

namespace YM.Extraction
open Function Set Filter Metric MeasureTheory
open scoped Topology ContDiff
variable {G : Gauge} {C : Family G} {f : Order} {S T : Table C.book} {P : ℕ → Table C.book}

/-- Promote after proving equality only on generic points. Thus no constraints
on coincident, aligned, or cross-tie limits accidentally baked in. -/
theorem RawLimits.ready (Hp : Bound C f) (h : RawLimits C f S P) (hs : T.Smooth)
    (H : ∀ n (w : Fin n → C.book.Token) (x : Points n), x ∈ generic n → S.read x w = T.read x w) :
    RawLimits C f T P := by
  have he : f.VolumePoints C T P := by
    intro n K hK hk v ε hε
    filter_upwards [h.volume n K hK hk v ε hε] with i hi x hx
    rw [← H n v x (hk hx)]; exact hi _ hx
  exact ⟨fun n v => ((T.smooth_read hs v).continuousOn).mono (generic_conf _), h.mesh, he,
    f.poses C Hp ⟨P,h.mesh,he⟩⟩
end YM.Extraction
