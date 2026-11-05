import YM.SectorNext.RECONNECTED_LOCALITY.Carry
import YM.SectorNext.RECONNECTED_LOCALITY.Imprint
import YM.Work.H03

set_option warningAsError false

/-! # First gas weight transport

Can use pointwise gauge motion and signed affine motion even with a V-dependent
orthogonal orientation change on each Lie color block, at the very same θ lookup. Don't cook
up new choices where the standalone completion uses a different tree or determinant; supply
the entries and probabilities pointwise. This strong version asks for all V and Z (even
on a zero) and no dropping likelihood factors when checking the rules. Thus sufficient
but not asserting E extensions on all V for schemes that do not purchase this.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect

open Function Lattice MeasureTheory RG Wilson Words Bind Window
open scoped Classical

variable {G : Gauge} {c : Side} {ι κ η : Type*} {Y : η → Type*}

/-- A motion of address and parameter. Health computed with the *same* threshold P on
both sides (e.g. translations and signed flips, or gauge). The field motion goes from
evaluation on destination V to evaluation at source U.
-/
structure Drift (G : Gauge) (c : Side) (ι : Type*) where
  place : Equiv.Perm (Site c)
  letter : Equiv.Perm ι
  field : Config G c → Config G c

variable (x : Drift G c ι) (X : Form G c ι κ Y)

structure Drift.Authentic (P : BudgetPoint) : Prop where
  health V : (flags P.threshold (x.field V)).map x.place.toEmbedding = flags P.threshold V
  patch : carrying x.letter x.place X.foot X.foot
  required : carrying x.letter x.place X.flag X.flag
  eligible i s : X.gate (x.letter i) (x.letter.finsetCongr s) = X.gate i s

/-! Transport of reference θ and Z in integral, from source to destination law.
The covariance and *all* values must work at the pushed θ; it is enough e.g. if $C$ transforms
from $A$'s local window prescription. We allow using only when a component is actually
used. `R` coloring may vary by field, context and bindings, nonabelian frame/gauge included.
-/
variable [∀ i, MeasurableSpace (Y i)] [Fintype η] [Fintype κ]
variable (N : StageLaw G c ι κ Y) (m : ∀ i,Measure (Y i))

structure Drift.Transit (P : BudgetPoint) : Prop where
  trueMove : x.Authentic X P
  routed : ∀ (p : Finset ι) (V : Config G c), X.Ok p → Ac.Spark X.foot p → X.Reads P p (x.field V) →
    ∃ (θ : Tables Y → Tables Y) (R : Tables Y → κ → κ → ℝ),
      MeasurePreserving θ (Measure.pi m) (Measure.pi m) ∧
      (∀ t,N.cov (x.letter.finsetCongr p) V (θ t) = pushed (R t) (N.cov p (x.field V) t)) ∧
        ∀ i∈p,∀ t z,X.value (x.letter i) (x.letter.finsetCongr p) V (θ t) (run (R t) z) = X.value i p (x.field V) t z

namespace Drift
variable {x X N m} {P : BudgetPoint} {p : Finset ι}

omit [Fintype η] [Fintype κ] [∀ i,MeasurableSpace (Y i)] in
theorem screening (h : x.Authentic X P) {V : Config G c} :
    X.Reads P (x.letter.finsetCongr p) V ↔ X.Reads P p (x.field V) := by
  unfold Form.Reads
  simp only [Form.land,Form.vote,h.patch.region,h.required.region]
  rw [← h.health V]; simp only [Equiv.finsetCongr_apply,Finset.map_eq_image,Equiv.coe_toEmbedding]
  rw [← Finset.image_inter _ _ x.place.injective]; exact (Finset.image_injective x.place.injective).eq_iff

omit [Fintype η] [Fintype κ] [∀ i,MeasurableSpace (Y i)] in
theorem trials (h : x.Authentic X P) : X.Ok (x.letter.finsetCongr p) ↔ X.Ok p := by
  unfold Form.Ok permits; nth_rw 1 [Equiv.finsetCongr_apply]; simp only [Finset.forall_mem_map,Equiv.coe_toEmbedding,h.eligible]



/-- Use for the final ForcedFamily gauge. -/
def gauges (u : Site c → G.El) : Drift G c ι := ⟨Equiv.refl _, Equiv.refl _, Lattice.gauge u⟩

omit [Fintype η] [Fintype κ] [∀ i,MeasurableSpace (Y i)] in
theorem gauge_authentic (u : Site c → G.El) : (gauges u).Authentic X P := by
  constructor <;> simp [gauges,carrying]



def rotations (s : Signed) (b : Site c) (v : Equiv.Perm ι) : Drift G c ι :=
  ⟨sitePerm s b,v,pull s b⟩

omit [Fintype η] [Fintype κ] [∀ i,MeasurableSpace (Y i)] in
theorem rotation_authentic (s : Signed) (b : Site c) (v : Equiv.Perm ι)
    (hp : carrying v (sitePerm s b) X.foot X.foot) (hf : carrying v (sitePerm s b) X.flag X.flag)
    (he : ∀ i p,X.gate (v i) (v.finsetCongr p)=X.gate i p) : (rotations s b v).Authentic X P := by
  refine ⟨fun V => ?_,hp,hf,he⟩
  rw [Finset.map_eq_image, Equiv.coe_toEmbedding]
  change Finset.image (affine s b) _ = _
  exact Work.H03.flags_send s b P.threshold V

end Drift
end YM.SectorNext.Reconnect
