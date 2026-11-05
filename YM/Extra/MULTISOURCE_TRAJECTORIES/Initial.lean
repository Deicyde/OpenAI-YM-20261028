import YM.Extra.MULTISOURCE_TRAJECTORIES.Geometry
/-!
# Exact singleton birth and its actual unmasked presentation bounds

At cutoff even overlapping translated/rotated/starred stencils have a log
linear in the markers. All additional window coefficients vanish in this
dictionary (on every physical configuration). Estimates use the purchased
`Family.Makes.priced`, transfer `.back` through all preceding levels and
unitary group compactness also *outside* the good set.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Wilson RG Lattice Source Labels Overlay Marker Mix Function Filter MeasureTheory Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {R : Census V} {C : Family G} {H : History G} {N p : ℕ}

lemma pass_fire (f : V → ℂ) (s : R.Mode) : (Poly.pass (∑ i,Poly.send (R.fire i) (f i))).part s = ∏ i∈s.val,f i := by
  have h (u : Finset V) : Fits R.fire u ↔ u∈R.choices := by simp [Fits,Census.fire, Set.PairwiseDisjoint,Set.Pairwise, onFun]
  rw [pass_sum _ _ (by simp [Census.fire]),prod_one_add,Poly.part_sum,sum_eq_single s.val]
  · rw [tagged_prod R.fire s.val ((h s.val).mpr s.property),show unionTag R.fire s.val ((h s.val).mpr s.property) = s from
      Subtype.ext (by simp [unionTag,Census.fire]),Poly.part_send,if_pos rfl]
  · intro b _ hb
    by_cases he : Fits R.fire b
    · rw [tagged_prod R.fire b he,Poly.part_send,if_neg]; intro hg
      exact hb (by simpa [unionTag,Census.fire] using congrArg Subtype.val hg.symm)
    exact (by rw [of_not_not (mt (fits_of_tagged_prod R.fire) he),Poly.part_nil])
  simp

lemma connected_birth (A : Insertions H V N p) (x) : connected (A.ratios R N x) =
    ∑ i,Poly.send (R.fire i) (((H.S.a N:ℂ)^A.load i) * A.field i x) := by
  have hr : (∑ i, Poly.send (R.fire i) (((H.S.a N:ℂ)^A.load i) * A.field i x)).part R.quiet = 0 := by
    rw [Poly.part_sum]; exact sum_eq_zero fun i _ => by simp [(R.fire_hot _).symm]
  refine pass_inj (connected_quiet (A.ratios_quiet le_rfl x)) hr ?_
  rw [pass_connected (A.ratios_quiet le_rfl x)]; ext s
  rw [pass_fire,A.part_ratios,Insertions.total_top,Insertions.source,Insertions.vac_top,prod_mul_distrib,Ride.bump,Complex.ofReal_inv]
  have hz := (thermal (H.β N p N) x)
  have h0 : (thermal (H.β N p N) x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  field_simp

namespace Probes
variable (Q : Probes C V N p) (W : Windows (C.side N p))

def fraction (i : V) (U : Config G (C.side N p)) := ((C.S.a N : ℂ)^Q.d i) * Q.eval i U

lemma birth (s : R.Mode) (U : Config G (C.side N p)) : Q.toInsertions.cumulant N s (matrixField U) =
    ∑ i : V, if s=R.fire i then Q.fraction i U else 0 := by
  rw [Insertions.cumulant,connected_birth,Poly.part_sum]; simp only [Poly.part_send]
  exact sum_congr rfl fun i _ => congrArg (fun z : ℂ => if s=R.fire i then ((C.S.a N : ℂ)^Q.d i)*z else 0) (congrFun (Q.physical i) U)

lemma region_empty (i : V) (a : Hot R × W.Piece) (he : a.1.val = R.fire i) (h : a.2.val=∅) :
    (Q.layers R W).region a = Q.footprint i := by
  simp [layers,Insertions.fragments,he,Census.fire,h,Windows.patch,cores]

lemma top_birth (a : Hot R × W.Piece) (U : Config G (C.side N p)) :
    (Q.layers R W).H a U = if a.2.val=∅ then Q.toInsertions.cumulant N a.1.val (matrixField U) else 0 := by
  let f := Q.toInsertions.cumulant N a.1.val
  let X := a.1.val.val.biUnion (Q.cores N)
  have he (t : Finset (Support (C.side N p))) (Y : Config G (C.side N p)) :
      f (hybrid (Windows.patch X t) (matrixField U) (matrixField Y)) = f (matrixField U) := by
    rw [field_hybrid]; unfold f; rw [birth, birth]; refine sum_congr rfl fun i _ => ?_
    split
    next he =>
      unfold fraction; rw [Q.visible i _ U ?_]
      intro b hb hb'; apply if_pos
      simpa [Windows.patch,X,cores,he,Census.fire] using ⟨Or.inl (a:=_ ) hb,Or.inl (a:=_) hb'⟩
    rfl
  have hp (t) : project (Windows.patch X t) f (matrixField U) = f (matrixField U) := by simp [project,he]
  change delta (fun t => project (Windows.patch X t) f _) a.2.val = _
  simp_rw [hp]
  split
  next h => rw [h]; simp [delta,f]
  next h =>
    obtain ⟨i,hi⟩ := nonempty_iff_ne_empty.mpr h
    nth_rw 1 [← insert_erase hi]
    rw [delta_insert (notMem_erase _ _),sub_self]

lemma masked_top (a : Hot R × W.Piece) (U : Config G (C.side N p)) :
    (Q.layers R W).H a U = if a.2.val=∅ then ∑ i : V, (if a.1.val=R.fire i then Q.fraction i U else 0) else 0 := by
  rw [Q.top_birth W a U,birth]

/-- Keep the actual automorphism and adjoint even in the sup tests. -/
def oriented (i : V) := (C.labels.level (Q.d i)).act (Q.signed i).ortho (Q.z i)
def effective (i : V) := if Q.reflect i then star (Q.oriented i) else Q.oriented i

def costs (i : V) := (C.factory (Q.d i) N p).terminal.symm (Q.effective i)

omit [Fintype V] [DecidableEq V] in
lemma eval_relocated (h : C.Makes) (i : V) (hi : C.ref (Q.d i) ≤ N) (U) : Q.eval i U = C.O N p (Q.effective i) (Q.place i) U := by
  simp only [eval, effective,place,oriented,← C.rotated h hi (Q.z i)]
  split
  · exact (C.reality h hi ..).symm
  rfl

omit [Fintype V] [DecidableEq V] in
lemma fraction_places (h : C.Makes) (i : V) (hi : C.ref (Q.d i) ≤ N) :
    Q.fraction i = (C.localSection (Q.d i)).places
      ((C.labels.level (Q.d i)).scaled ((C.path.rep N p N).p.threshold)⁻¹ (Q.costs i)) (Q.place i) := by
  funext U
  rw [fraction,eval_relocated Q h i hi U,(h.wilson.represents N p N le_rfl).vac]
  simp only [Family.O,TransferData.cylinder,initial,Pi.smul_apply, smul_eq_mul]; rw [← mul_assoc,show C.S=C.path.S from rfl,mul_inv_cancel₀ (by
    have := (C.S.a_pos N).ne'; exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr this)),one_mul]; rfl

omit [Fintype V] [DecidableEq V] in
lemma footprint_eq (h : C.Makes) (i : V) : Q.footprint i = (C.localSection (Q.d i)).footprint (Q.place i) := by
  let D := C.localSection (Q.d i)
  unfold footprint place SectionData.footprint
  rw [image_image]
  trans (D.stencil.image (Q.signed i).act).image (fun x : Cover => wrap (C.side N p) x + affine (Q.signed i) (Q.offset i) (Q.point i))
  · simp only [image_image,comp_def,affine,Signed.act_add,wrap_signed,add_assoc]; rfl
  rw [(h.sections (Q.d i)).stable]
end Probes
end YM.Extra.Trajectories
