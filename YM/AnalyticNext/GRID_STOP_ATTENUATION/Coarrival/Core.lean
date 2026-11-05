import YM.AnalyticNext.GRID_STOP_ATTENUATION.Coarrival.Oper
import YM.Laurent.Turn
import YM.Push.GRID_APPROXIMATION.Palette
import YM.Work.B18

set_option warningAsError false

/-!
# Upstream gates applied to pairing

Common dictionary at all steps, no coefficient estimates on precomputed
signed differences. Core choices & unmarked path fully frozen even between
birth station and cutoff. The program/combinator and its compatibility
with the calibrated family are actual red gates. We pay this for the
primary part. Pinned mixed response still needs its own buys: even propagating
primary successfully one need NOT get required mixed responses with same
primary output choice from a separate existential statement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Coarrival
open Function Filter MeasureTheory RG Marker Wilson Lattice Source Bid Labels Multi Stock Multi.Couples Finset Stepwise
open Push.GridApprox
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {C : Family G} {m d p N k : ℕ} {W : Worth}

/-- Transformations of entries (a rotation typically reindexes several
addresses as well as acting on their arguments). Needn't choose a topology
or rep on all directions. Require the first projection even if using a
Book-limited address dictionary. These only concern this station's paper.
`axial` only addresses the effective ancestor at origin. -/
structure Atlas (C : Family G) (W : Worth) (N p d k : ℕ) (r : ℝ) where
  exponent : 0≤r
  slot : (i : ℕ)→ ℕ→ Support (C.side i p)
  seat (i : ℕ) : ∀ j,0∈slot i j
  launch : Room (C.path.rep N p k)
  axial (i : ℕ) (he : C.ref d ≤ i) (hk : i < k) : Adjacent C W N p d slot r i
  mirror (i : ℕ) : Wire (C.labels.level d) (C.side i p) → Wire (C.labels.level d) (C.side i p)
  turn (i : ℕ) : Signed → Wire (C.labels.level d) (C.side i p) → Wire (C.labels.level d) (C.side i p)
  soundm i u : (mirror i u).1=star u.1
  sounds i s u : (turn i s u).1=(C.labels.level d).act s.ortho u.1
  beginm v : mirror k (beginAt (C.localSection d) 0 launch v)=beginAt (C.localSection d) 0 launch (star v)
  begins v s : turn k s (beginAt (C.localSection d) 0 launch v)=beginAt (C.localSection d) 0 launch ((C.labels.level d).act s.ortho v)
  commutesm (i : ℕ) (he : C.ref d ≤ i) (hk : i < k) z : enroll C (N:=N) (i:=i+1) (slot (i+1)) z →
    (∃ v, tariff C (N:=N) (i:=i+1) (slot (i+1)) z v) →
    (axial i he hk).travel (mirror (i+1) z) = mirror i ((axial i he hk).travel z)
  commutess (i : ℕ) (he : C.ref d ≤ i) (hk : i < k) z s : enroll C (N:=N) (i:=i+1) (slot (i+1)) z →
    (∃ v, tariff C (N:=N) (i:=i+1) (slot (i+1)) z v) →
    (axial i he hk).travel (turn (i+1) s z) = turn i s ((axial i he hk).travel z)
  /-- Compatibility stronger than one needs for C factory & J; only
require origin and that Master eventually arrives, even if allocated different
indices outside our k region. Very important; otherwise no subtraction
with these stencils. -/
  belongs (i) (he : C.ref d ≤ i) (hk : i≤k) : (Match.old C i N p (0:C.label d)).support=slot i
  identical (i) (he : C.ref d ≤ i) (hk : i < k) (v : C.label d) :
    wire (Match.old C i N p v) = (axial i he hk).travel (wire (Match.old C (i+1) N p v))

variable {r : ℝ}
namespace Atlas
variable (A : Atlas C W N p d k r)

def pulses (i : ℕ) : C.label d →ₗ[ℂ] Wire (C.labels.level d) (C.side i p) :=
    if h:i = k then h ▸ (begin_linear (C.localSection d) 0 A.launch).mk' _
    else if he : C.ref d ≤ i ∧ i < k then LinearMap.comp (A.axial i he.1 he.2).travel (pulses (i+1))
    else 0
termination_by k-i

def salaries (v : C.label d) (i : ℕ) := if i = k then (C.labels.level d).coeffSize ((C.labels.level d).core v)
    else if he : C.ref d ≤ i ∧ i < k then Adjacent.cost (C:=C) (W:=W) (i:=i) (A.pulses (i+1) v) (salaries v (i+1)) else 0
termination_by k-i

def resume : Paper (Match.view C.path N) k p (C.labels.level d) := ⟨fun i v => address (A.slot i) (A.pulses i v), fun i v => A.salaries v i⟩

lemma first (v : C.label d) : A.resume.inits k v = address (A.slot k) (beginAt (C.localSection d) 0 A.launch v) ∧
    A.resume.paid k v = (C.labels.level d).coeffSize ((C.labels.level d).core v) := by
  unfold resume; simp only; rw [pulses,dif_pos rfl,
      salaries,if_pos rfl]; exact ⟨rfl,rfl⟩

lemma step (i) (h : C.ref d ≤ i) (hh : i < k) : A.pulses i = LinearMap.comp (A.axial i h hh).travel (A.pulses (i+1)) := by
  rw [pulses,dif_neg hh.ne,dif_pos ⟨h,hh⟩]

lemma salary_st (v : C.label d) (i) (h : C.ref d ≤ i) (hh : i < k) : A.salaries v i=Adjacent.cost (C:=C) (i:=i) (W:=W) (A.pulses (i+1) v) (A.salaries v (i+1)) := by
  rw [salaries,if_neg hh.ne,dif_pos ⟨h,hh⟩]

variable (H : C.Makes) (hr : C.ref d ≤ k) (hk : k≤N)
    (hY : Maquette.room (C.localSection d) ≤ C.path.levels.clock.coverSize k)
    (hF : money C.path.levels k*openingFee C d k ≤ 1)
include H hk hY hF

lemma logged (v : C.label d) (i) (h : C.ref d ≤ i) (hi : i≤k) :
    enroll C (N:=N) (i:=i) (A.slot i) (A.pulses i v) ∧ tariff C (N:=N) (i:=i) (A.slot i) (A.pulses i v) (A.salaries v i) := by
  by_cases he:i = k
  · subst i; unfold pulses salaries; rw [dif_pos rfl,if_pos rfl]
    obtain ⟨hu,hv,-⟩ := arrival H (0:Site (C.side k p)) (A.slot k) (A.seat k) A.launch hk hY hF v; exact ⟨hu,hv⟩
  obtain ⟨hl,hj⟩:= logged v (i+1) (h.trans (Nat.le_succ _)) (show i < k by omega)
  let J := A.axial i h (by omega)
  have ht := J.levied _ hl hj
  rw [A.step i h (show i < k by omega), A.salary_st v i h (show i < k by omega)]
  exact ⟨(J.conveys _ hl ⟨_,hj⟩).1,Pair.funds_erases J.hr ht.1⟩
termination_by k-i

lemma locks (v : C.label d) (i) (h : C.ref d ≤ i) (he : i≤k) :
    A.pulses i (star v)=A.mirror i (A.pulses i v) ∧ ∀ s, A.pulses i ((C.labels.level d).act s.ortho v)= A.turn i s (A.pulses i v) := by
  have hl i h he := A.logged H hk hY hF v i h he
  by_cases ht : i = k
  · subst i; rw [pulses,dif_pos rfl]; exact ⟨(A.beginm v).symm,fun s => (A.begins v s).symm⟩
  have hf:i < k := lt_of_le_of_ne he ht
  obtain ⟨hx,hy⟩ := locks v (i+1) (h.trans (Nat.le_succ _)) hf
  rw [A.step i h hf]; simp only [LinearMap.comp_apply,hx,hy]
  have hz := hl (i+1) (h.trans (Nat.le_succ _)) hf
  exact ⟨A.commutesm _ h hf _ hz.1 ⟨_,hz.2⟩, fun s => A.commutess _ h hf _ _ hz.1 ⟨_,hz.2⟩⟩
termination_by k-i

omit H hk hY hF in
lemma unity (i) (h : C.ref d ≤ i) (he : i≤k) : A.pulses i (unitVec (C.labels.level d) C.path k)=lead (unitVec _ C.path i) := by
  by_cases ht : i = k
  · subst i; rw [pulses,dif_pos rfl]; let F := C.labels.level d; let P := (C.path.rep N p k).p; let S := C.localSection d
    have he : F.core F.e0=0 := by ext1 i; by_cases e:i=0 <;> simp [Frame.core,Frame.e0,e]
    refine Prod.ext rfl (Prod.ext rfl ?_); let Z := kit S (0:Site (C.side k p)) P.threshold (unitVec F C.path k)
    have hu U : Z.tail (C.path.rep N p k) U=0 := by
      unfold Z; rw [tail_is,Pi.sub_apply]; unfold unitVec; rw [map_smul,he,smul_zero,map_zero]; unfold SectionData.places
      rw [show S.evaluate 0=0 from map_zero (S.eval_linear.mk' _)]; simp [masked]
    funext j U
    change Primary.allocate A.launch (ballast (S.footprint 0) _ (Z.tail (C.path.rep N p k))) j U=0
    unfold Primary.allocate; split
    · unfold ballast; split; rw [hu,zero_mul]; rfl
    rfl
  have hf:i < k := lt_of_le_of_ne he ht
  rw [A.step i h hf,LinearMap.comp_apply,unity (i+1) (h.trans (Nat.le_succ _)) hf]
  exact (A.axial i h hf).constant
termination_by k-i

include hr

end Atlas
end YM.AnalyticNext.GridStop.Coarrival
