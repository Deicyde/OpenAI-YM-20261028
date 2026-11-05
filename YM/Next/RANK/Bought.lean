import YM.Extraction.Inherited
import YM.Next.RANK.Finite


/-!
# Read the purchases in one representation and extraction

Here an *intermediate* interface which will be an OUTPUT of our marker
arguments. Exposes the chosen basis/Trials for use even in RShort before
assembling `Columns.Trials.Valid` (which must also get span!). These particular
preparations supply every p, and an eventual N for given k (not after f).
Carry a mesh limit of lifts additionally for every p.

`to_rank` goes back to the exact fixed-arity consumer format.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Market
open Function Set Filter RG Lattice Wilson Cells Marker Glyph Exponential MeasureTheory Read Extraction
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff ENNReal

variable {G : Gauge} {C : Family G} {S S' : Table C.book} {f : Extraction.Order} {d k N p n : ℕ} {X : Columns C S d}
variable (Z : X.Trials)

lemma vision (a : ℝ) (ha : 0<a) (x : Points n) (hx : x∈YM.generic _) : a • x ∈ YM.generic _ := by
  intro b i j hh; apply hx b
  apply mul_left_cancel₀ ha.ne'; exact hh

lemma freed {Z : X.Trials} {i} (h : Z.realPlace k i∈YM.generic _) : Z.tested k i∈conf _ := generic_conf _ (vision (Z.scale k)⁻¹ (inv_pos.mpr (Z.positive _)) _ h)

def roles (X : Columns C S d) (i : Fin X.amount) (c : Fin (X.dim+1)) (s : Fin ((X.row i).extra+1)) : (standard C).Tag :=
  ⟨d,X.basis (Columns.Trials.names (X:=X) i c s)⟩

def gauges (k i c) := Read.maxProfile C (Z.tested k i) (roles X i c)

def pulse (k N p : ℕ) (i) (c : Fin (X.dim+1)) (s : Fin ((X.row i).extra+1)) : C.book.Token :=
  ⟨d, Z.lift k N p (Columns.Trials.names (X:=X) i c s)⟩

def echoes (k : ℕ) (i) (c : Fin (X.dim+1)) (s : Fin ((X.row i).extra+1)) : C.book.Token :=
  ⟨d, Z.later k (Columns.Trials.names (X:=X) i c s)⟩

def dialed (k N p) (i) (c : Fin (X.dim+1)) (h : Z.realPlace k i∈YM.generic _) : Config G (C.side N p) → veil (Fin ((X.row i).extra+1)) :=
  Read.cylinder (cumulants C (Z.tested k i) (roles X i c) (freed h)) (Z.weigh k N p i c)



lemma wake_one (k N p i c j) (h : Z.realPlace k i∈YM.generic _) (U) :
    (dialed Z k N p i c h U).part (scene {j}) = Z.subtract1 k N p i c j U := by
  unfold dialed
  rw [scene_single, Read.cylinder_single (cumulative C (Z.tested k i) (roles X i c) (freed h))]
  unfold maxProfile; rw [← scene_single,profile_single _ (Maxwell.table_sym C.labels) _ (freed h)]
  rfl

lemma wake_pair (k N p i c j t) (hj : j≠t) (h : Z.realPlace k i∈YM.generic _) (U) :
    (dialed Z k N p i c h U).part (scene {j,t})=Z.subtract2 k N p i c j t U := by
  unfold dialed; let e := Z.tested k i; let w := roles X i c
  rw [Read.cylinder_pair (cumulative C (Z.tested k i) w (freed h)) _ _ _ hj]; unfold maxProfile
  rw [← scene_single j,← scene_single t, profile_pair _ (Maxwell.table_sym C.labels) _ (freed h) _ _ _ hj]
  simp only [profile_single _ (Maxwell.table_sym C.labels) (Z.tested k i) (freed h) w];rfl

lemma roles_score (x : Columns C S d) (i : Fin x.amount) (c : Fin (x.dim+1)) :
    (standard C).useAt (standard C) (x.row i).expected (roles x i c)=(x.row i).tests (standard C) x.basis (x.basis c) := by
  unfold SampleRow.tests; congr 1
  funext a; refine Fin.cases ?_ (fun j => ?_) a <;> rfl

/-- Intermediate outputs. Purchases (don't mention `later`) survive replacing
that limit vector. -/
structure Purchases : Prop where
  proportion : ∃ b : ℝ, 0 < b ∧ ∀ k, Z.scale k = C.S.a (Z.depth k) * ((C.path.levels.clock.monitor (Z.depth k))^b)
  flat k m (hm : Z.width k≤m) (hx : m≤Z.depth k) : C.path.levels.clock.J m = C.path.levels.clock.J (Z.depth k)
  shrinks : StrictAnti Z.scale
  real k N p i : star (Z.lift k N p i)= Z.lift k N p i
  literal k N p : Z.lift k N p 0 = C.refUnit d
  bounded k : ∃ A : ℝ, ∀ N p i, ‖Z.lift k N p i‖ ≤ A
  tuned i : Tendsto (fun k => Z.tested k i) atTop (𝓝 (X.row i).expected)
  fit : ∃ η : ℝ, 0 < η ∧ ∀ k i j a,
    |Z.realPlace k i j a| ≤ C.S.a (Z.width k)*((2:ℝ)⁻¹-η)
  axis (k i) : Z.realPlace k i∈YM.generic _
  arrays (k : ℕ) : ∀ᶠ N in atTop, ∃ h : Z.depth k ≤ N, ∀ p,
    let T := center C.S p ((Z.window k).trans h) 0
    ∀ i c,
      (∀ u, Interior (T.chamber 0) (Z.weigh k N p i c u)) ∧
      (∀ s : modes (Fin ((X.row i).extra+1)), s.val.Nonempty →
        T.rootTest (C.beta N p) (fun U => (dialed Z k N p i c (axis k i) U).part s) ≤ Z.gap k)

def lands (f : Extraction.Order) := ∀ k i, f.limits (fun _ => True) (fun N p => Z.lift k N p i) (Z.later k i)

namespace Purchases
-- retain h explicitly
variable {Z} (h : Purchases Z)
include h







-- exact iterated limit (for each applicable p, not eventuality for integrated numbers).




lemma monitor_tends i c : Tendsto (fun k => Poly.price (fun _ => 1) (gauges Z k i c)*Z.gap k) atTop (𝓝 0) := by
  have hp := Poly.price_cont (fun _ => (1:ℝ))|>.continuousAt.tendsto.comp
    (profile_tends (standard C) (roles X i c) (Maxwell.table_smooth _) (generic_conf _ (X.row i).probes) (h.tuned i))
  simpa only [mul_zero] using! (hp.mul Z.small)



-- Also pass without reordering even the full list; not using symmetry of S yet!
lemma samples (hp : C.Makes) (H : lands Z f) (he : f.PointLimits C S) (k i c) : ‖S.read (Z.realPlace k i) (echoes Z k i c)-
    (standard C).useAt (standard C) (Z.tested k i) (roles X i c)‖ ≤ Poly.price (fun _ => 1) (gauges Z k i c)*Z.gap k := by
  let z := Columns.Trials.names (X:=X) i c
  have ht := Cells.keeps_moments C f S (k:=Z.depth k) (d:=fun _ => d) (Z.mark k i) (h.axis k i) he
    (fun s => Z.later k (z s)) (fun N p s => Z.lift k N p (z s)) (fun j => H k (z j))
  apply le_of_tendsto (((Order.along ht).sub (tendsto_const_nhds (x:=(standard C).useAt (standard C) (Z.tested k i) (roles X i c)))).norm)
  rw [Order.fused,Order.late]; refine Eventually.of_forall fun o => (f.mesh.cofinal.eventually (h.arrays k)).mono ?_
  intro j hj
  obtain ⟨a,b⟩ := hj
  let p := f.per o
  let T := center C.S p ((Z.window k).trans a) 0
  exact Read.full_cost (u := Z.mark k i) (t:=pulse Z k (f.mesh j) p i c) hp (freed (h.axis k i)) (Z.allowed k) T ((b p i c).1) ((b p i c).2)

lemma converge (hp : C.Makes) (H : lands Z f) (he : f.PointLimits C S) (i c) :
    Tendsto (fun k => S.read (Z.realPlace k i) (echoes Z k i c)) atTop
      (𝓝 ((X.row i).tests (standard C) X.basis (X.basis c))) := by
  rw [← roles_score]; refine tendsto_of_tendsto_of_dist
    (f₁:=fun k => (standard C).useAt (standard C) (Z.tested k i) (roles X i c)) ?_ (squeeze_zero (fun k => dist_nonneg) (fun k => ?_) (h.monitor_tends i c))
  · have hh := generic_conf _ (X.row i).probes
    have hi := ((standard C).class_smooth _ (Maxwell.table_smooth C.labels) (roles X i c)).continuousOn
    exact ((hi _ hh).continuousAt ((conf_open _).mem_nhds hh)).tendsto.comp (h.tuned i)
  rw [dist_comm,dist_eq_norm]; exact h.samples hp H he k i c

lemma to_rank (H : lands Z f) (hv : ∀ᶠ k in atTop, Submodule.span ℂ (Set.range fun i => S.project d (Z.later k i))=⊤) : Z.Valid f where
  ratios := h.proportion
  same_stage := h.flat
  scale_down := h.shrinks
  conjugate := h.real
  unit := h.literal
  responds := H
  bounded k := by
    obtain ⟨A,hx⟩ := h.bounded k
    exact ⟨A,fun p => Eventually.of_forall fun i => hx _ _⟩
  span := hv
  tuned := h.tuned
  seams := h.fit
  generic := h.axis
  cheap k ε he := by
    unfold Order.late
    refine Eventually.of_forall fun m => (f.mesh.cofinal.eventually (h.arrays k)).mono ?_
    rintro i ⟨a,b⟩
    let p := f.per m
    let T := center C.S p ((Z.window k).trans a) 0
    refine ⟨a,fun j c s => ⟨((b p j c).1 s), ?_, fun t ht => ?_⟩⟩
    · rw [show Z.subtract1 k (f.mesh i) p j c s=_ from funext fun U => (wake_one Z k (f.mesh i) p j c s (h.axis k j) U).symm]; exact
        (((b p j c).2 (scene {s}) (Finset.singleton_nonempty _))).trans (le_add_of_nonneg_right he.le)
    rw [show Z.subtract2 k (f.mesh i) p j c s t=_ from funext fun U => (wake_pair Z k (f.mesh i) p j c s t ht.ne (h.axis k j) U).symm]; exact
      (((b p j c).2 (scene {s,t}) (Finset.insert_nonempty ..))).trans (le_add_of_nonneg_right he.le)
end Purchases
end YM.Next.Rank.Market
