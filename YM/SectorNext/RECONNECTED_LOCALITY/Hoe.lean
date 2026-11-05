import YM.SectorNext.RECONNECTED_LOCALITY.Imprint
import YM.SectorNext.RECONNECTED_LOCALITY.Swell


set_option warningAsError false

/-! # Numerical range versus tested read, including seed answers

Helper to *earn* the Imprint locality ports from E stencil sizes.
`Wired` operates on variable raw context and full fields/table (same flags,
Σ, θ, columns, including charts not realizing any fine configurations).
Selection changes allowed past B-sized halo at footprint stage. Use every
queried V-link's BOTH endpoints, incl $U$ guards via coarse conditions and also
V flag queries: `UsesFinal` at Wilson activities doesn't authorize even a single
flag paid as site only here! No continuity assertions. Address stipulations
costed in output; Θ coordinates (incl Y frozen & all choices, even tag zeros)
priced in distance, not covariance range. Test/look reserves to process
incoming D may be larger and ALSO attached to that compulsory Form foot.
Sparse or zero costs need whole permits if determined by geometry. -/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect.Ice
open Finset Matrix Function Lattice RG Wilson Bind
open scoped BigOperators

variable {I J K ι η : Type*} {Y : η → Type*} {G: Gauge} {c : Side}

def around (r : ℕ) (x : Site c) : Support c := halo r {x}

@[simp] lemma visible {x z : Site c} {r : ℕ} : z∈around r x ↔ separation x z≤r := by simp only [around,halo_spec,mem_singleton]; simp

@[simp] lemma house {x : Site c} {r : ℕ} : x∈around r x := visible.mpr (by simp)

lemma bases {i j : Site c} {a b r : ℕ} (h : a+b≤r) (he : separation i j≤a) : around b j ⊆ around r i := by
  intro z hz
  exact visible.mpr ((separation_triangle ..).trans ((Nat.add_le_add he (visible.mp hz)).trans h))

/-- Packed query inputs (`Y` arbitrary, not assuming k split or averaging).
Each slot's hypotheses concern all drawers; numerical read can be pieced
from implementations on those drawers. -/
structure Slip (G:Gauge) (c:Side) (ι : Type*) {η : Type*} (Y : η→Type*) where
  live : Finset ι
  beam : Config G c
  pages : Tables Y

variable {X : ι → Support c} {p : I→Site c} {q : J→Site c} {l : K→Site c} {tag : η→Site c} {r d t u a b : ℕ}

structure Fresco (X : ι → Support c) (tag : η → Site c) (r : ℕ) (x : Site c) (s h : Slip G c ι Y) : Prop where
  seed : ∀ i,¬Disjoint (X i) (around r x) → (i∈s.live ↔ i∈h.live)
  paper : Agrees (around r x) s.beam h.beam
  book : ∀ i,separation x (tag i)≤r → s.pages i=h.pages i

variable {s e : Slip G c ι Y}

lemma Fresco.shift {x y : Site c} (h : Fresco X tag r x s e) (he : separation x y≤a) (ha : a+b≤r) :
    Fresco X tag b y s e := by
  have hh := bases ha he
  refine ⟨fun i hx => h.seed i (fun hd => hx (Finset.disjoint_of_subset_right hh hd)),agrees_mono h.paper (Finset.coe_subset.mpr hh),?_⟩
  intro i hi
  exact h.book i ((separation_triangle ..).trans ((Nat.add_le_add he hi).trans ha))

lemma Fresco.close {x : Site c} (h : Fresco X tag r x s e) (he : d≤r) : Fresco X tag d x s e :=
  h.shift (by simp : separation x x≤0) (by linarith)

/-- Test price at first endpoint, range can be much less (e.g. 15B vs B/100 in ).
Reserve $r$ & $d$ charged separately, must still show both fit committed B.
Measured in the ACTUAL `land p` integer pseudometric, not length or midpoint. -/
structure Wired (X : ι → Support c) (tag : η→Site c) (p : I→Site c) (q : J→Site c) (r d : ℕ)
    (F : Slip G c ι Y → Matrix I J ℝ) : Prop where
  wide : ∀ i j,r<separation (p i) (q j) → ∀ s,F s i j=0
  tests : ∀ i j s e,Fresco X tag d (p i) s e → F s i j=F e i j

namespace Wired
variable {F H : Slip G c ι Y → Matrix I J ℝ} {E : Slip G c ι Y → Matrix J K ℝ}

lemma more (h : Wired X tag p q r d F) (hr : r≤t) (hd : d≤u) : Wired X tag p q t u F := by
  refine ⟨fun _ _ he _ => h.wide _ _ (by omega) _, fun _ _ _ _ hx => h.tests _ _ _ _ (hx.close hd)⟩

lemma sum (h : Wired X tag p q r d F) (hh : Wired X tag p q r d H) : Wired X tag p q r d fun s=>F s+H s := by
  constructor <;> intro i j he hs
  · rw [Matrix.add_apply,h.wide _ _ he,hh.wide _ _ he,zero_add]
  intro hr; exact congrArg₂ (·+·) (h.tests i j _ _ hr) (hh.tests _ j _ _ hr)

lemma scale (h : Wired X tag p q r d F) (a : ℝ) : Wired X tag p q r d fun s=>a • F s := by
  constructor <;> intro i j he hs
  · rw [Matrix.smul_apply,h.wide _ _ he,smul_zero]
  intro hr; exact congrArg (a • ·) (h.tests i j _ _ hr)



lemma flip (h : Wired X tag p q r d F) : Wired X tag q p r (r+d) fun s=>(F s).transpose := by
  constructor
  · intro i j he v; rw [transpose_apply]; apply h.wide; rwa [separation_comm]
  intro i j v w hr
  simp only [transpose_apply]
  by_cases hi : separation (q i) (p j)≤r
  · exact h.tests _ _ _ _ (hr.shift hi le_rfl)
  have hi' : r<separation (p j) (q i) := by rw [separation_comm]; omega
  rw [h.wide _ _ hi',h.wide _ _ hi']





variable [Fintype I] [DecidableEq I] {W : I→Finset I} {A : Slip G c ι Y→Matrix I I ℝ}

omit [Fintype I] in
lemma from_source (h : Wired X tag p p r d A) (hW : ∀ i,∀ j∈W i,separation (p i) (p j)≤t) (z : ℝ) :
    Wired X tag p p t (t+d) (fun s=>(floe W (A s) z).transpose) := by
  constructor
  · intro i j he s; rw [transpose_apply,floe_else]; exact fun hy => by have:=hW i j hy; omega
  intro i j s e he; simp only [transpose_apply,floe,of_apply]
  suffices hotel (W i) (A s)=hotel (W i) (A e) by rw [this]
  ext v w; exact h.tests v.val w.val _ _ (he.shift (hW i v.val v.property) le_rfl)

omit [Fintype I] in
lemma twin (h : Wired X tag p p r d A) (hW : ∀ i,∀ j∈W i,separation (p i) (p j)≤t) :
    Wired X tag p p t (t+(t+d)) (fun s=>front W (A s)) := by
  have hh := h.from_source hW 0
  simpa only [front, transpose_transpose] using ((hh.flip.sum (hh.more le_rfl (by omega))).scale (1/2))



end Wired

/-! A Z in X.lines always prices an entire B-sized halo of seed centers,
used V links and possible withheld table choices for its column (even if on
unused flags), IN ADDITION to all support the address needs to be evaluated
(e.g. coarse loop) or held default. Compute positions of Y & tags through
`slots`; include all reserved keys too. -/
structure Board (X : Form G c ι I Y) (p : I → Site c) (q : η→Site c) (r : ℕ) : Prop where
  maps : ∀ l i,i∈X.lines l → around r (p i) ⊆ X.foot l
  slots : ∀ l i,i∈X.lines l → ∀ j,separation (p i) (q j)≤r → j∈X.stages l

namespace Board
variable {X : Form G c ι I Y} {p : I→Site c} {tag : η → Site c}






end Board
end YM.SectorNext.Reconnect.Ice
