import YM.Push.ABSOLUTE_SUMS.Breadth
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.Push.SECTOR_MEASURE.Oriented

/-!
# One tree slice, all channels

Output-scale locations with both endpoints, counting on actual torus.
When assigning whole rows in a turned channel we use the *turned anchor*,
not the minimum canonical base of the physical object. `near`-type tests
for seeds and shells must allow this convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums  
open SectorMeasure  Oriented Precision
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n c f : Side} {S : StepData c f}

namespace Channel
section turns
variable (s : Signed) (i : Bond n)

def edge (s : Signed) (i : Bond n) : Bond n := sendEdge s 0 i

@[simp] lemma affine0 (v : Site n) : affine s 0 v = s.act v := add_zero _

lemma positive (h : s.flip i.2=false) : edge s i=(s.act i.1,s.perm i.2) := by
  simp [edge,sendEdge,posDir,Step.rotate,Step.used,h]

lemma negative (h : s.flip i.2=true) : edge s i=(s.act (i.1+step i.2),s.perm i.2) := by
  have he := StepData.negsite s (0:Site n) i.1 i.2 h
  simp_rw [affine0] at he
  rw [he]; simp [edge,sendEdge,posDir,Step.rotate,Step.used,h]

lemma charge (U : Config G n) : pull s 0 U i = if s.flip i.2 then (U (edge s i))⁻¹ else U (edge s i) := by
  unfold pull Step.read; simp only [edge,sendEdge,posDir,Step.rotate,Bool.false_xor]

lemma endpoints (v : Site n) : v∈pinPos i ↔ s.act v∈pinPos (edge s i) := by
  cases ht : s.flip i.2
  · rw [positive s i ht]
    have he := StepData.possite s (0:Site n) i.1 i.2 ht
    simp_rw [affine0] at he
    simp only [pinPos,mem_insert,mem_singleton, ← he]; simp only [s.act_injective.eq_iff]
  rw [negative s i ht]
  have he := StepData.negsite s (0:Site n) i.1 i.2 ht
  simp_rw [affine0] at he
  simp only [pinPos,mem_insert,mem_singleton]
  rw [show s.act (i.1+step i.2)+step (s.perm i.2)=s.act i.1 by rw [he,sub_add_cancel]]
  rw [or_comm]; exact or_congr s.act_injective.eq_iff.symm s.act_injective.eq_iff.symm

lemma start (p : Cell f) : startPos S (Oriented.faces s f p) = (startPos S p).image s.act := by
  change (startPos _ (Face.send s 0 p))= _
  unfold startPos; rw [Work.H03.touched_send,image_image,image_image ]
  apply Finset.image_congr; intro i hi
  simp only [comp_apply,affine0,
    S.ratio.parent_signed S.patch.odd_side]

lemma site_face (v : Site c) (p : Cell f) : v∈startPos S p ↔ s.act v∈startPos S (Oriented.faces s f p) := by
  rw [start]; simp [s.act_injective.eq_iff]

lemma rotates_place (X : Stores S) (v : Site c) : v ∈ (turnStore s X).place ↔ s.act v ∈ X.place := by
  unfold Stores.place turnStore
  simp only [mem_union,mem_biUnion]; constructor
  · rintro ((⟨p,hp,h⟩|⟨p,hp,h⟩)|h)
    · exact Or.inl (Or.inl ⟨Oriented.faces s f p,by simpa using hp,(site_face s v p).mp h⟩)
    · exact Or.inl (Or.inr ⟨edge s p,(by
        have hh : StepData.sendBonds s 0 p∈X.aisles := by simpa only [Equiv.toEmbedding_apply,
          Equiv.symm_symm,Finset.mem_map_equiv] using! hp
        exact hh), (endpoints s p v).mp h⟩)
    · refine Or.inr ?_
      have hh : StepData.sendSites s 0 v ∈ X.flags := by simpa only [Equiv.toEmbedding_apply,Equiv.symm_symm,
        Finset.mem_map_equiv] using! h
      change affine s 0 v ∈ _ at hh; rwa [affine0] at hh
  · rintro ((⟨p,hp,h⟩|⟨p,hp,h⟩)|h)
    · obtain ⟨p,rfl⟩ := (Oriented.faces s f).surjective p
      exact Or.inl (Or.inl ⟨p,by simpa using hp,(site_face s v p).mpr h⟩)
    · obtain ⟨p,rfl⟩ := (StepData.sendBonds s 0).surjective p
      exact Or.inl (Or.inr ⟨p,by simpa only [mem_map_equiv,Equiv.toEmbedding_apply,Equiv.symm_symm]
        using! hp,(endpoints s p v).mpr h⟩)
    refine Or.inr ?_
    have ht : StepData.sendSites s 0 v=s.act v := affine0 s v
    simpa only [mem_map_equiv,Equiv.toEmbedding_apply,Equiv.symm_symm,ht] using! h

lemma rotates_dome (X : Stores S) (M : ℕ) (v : Site c) : v ∈ (turnStore s X).dome M ↔ s.act v∈X.dome M := by
  unfold dome; rw [halo_spec,halo_spec]; constructor
  · rintro ⟨x,hx,h⟩; exact ⟨s.act x,(rotates_place s X x).mp hx,(separation_signed ..).trans_le h⟩
  rintro ⟨x,hx,h⟩; obtain ⟨x,rfl⟩ := s.actEquiv.surjective x
  change s.act x ∈ _ at hx; exact ⟨x,(rotates_place s X x).mpr hx,(separation_signed x v s).symm.trans_le h⟩

lemma pulls_replica (V : Config G c) :
    pull s 0 (replica S.ratio V) = replica S.ratio (pull s 0 V) := by
  let g := S.ratio
  funext i; rcases i with ⟨x,a⟩; rw [charge]; dsimp only
  have hp := g.parent_signed S.patch.odd_side
  have hz := g.parents_hop S.patch.odd_side x a
  have he (hh : g.parent (x+step a) ≠ g.parent x) :
      g.parent (x+step a)=g.parent x+step a := by
    split at hz
    · exact hz
    exact (hh hz).elim
  cases hf : s.flip a
  · rw [if_neg (by simp),positive s (x,a) hf]
    have h := StepData.possite s (0:Site f) x a hf; rw [affine0,affine0] at h
    change (if g.parent (s.act x+step (s.perm a))=g.parent (s.act x) then 1 else V (g.parent (s.act x),s.perm a)) =
      if g.parent (x+step a)=g.parent x then 1 else pull s 0 V (g.parent x,a)
    rw [← h,hp,hp]
    by_cases H : g.parent (x+step a)=g.parent x
    · rw [if_pos H,if_pos (s.act_injective.eq_iff.mpr H)]
    rw [if_neg H,if_neg (s.act_injective.ne H),charge,positive s (g.parent x,a) hf]; simp only [hf, Bool.false_eq_true, ↓reduceIte]
  rw [if_pos (by simp),negative s (x,a) hf]
  have ht := StepData.negsite s (0:Site f) x a hf; rw [affine0,affine0] at ht
  let y := x+step a
  change (if g.parent (s.act y+step (s.perm a))=g.parent (s.act y) then (1:G.El) else V (g.parent (s.act y),s.perm a))⁻¹ =
      if g.parent y=g.parent x then 1 else pull s 0 V (g.parent x,a)
  rw [show s.act y+step (s.perm a)=s.act x by rw [show y=x+step a from rfl,ht]; abel,hp,hp]
  by_cases H : g.parent y=g.parent x
  · rw [if_pos (s.act_injective.eq_iff.mpr H.symm),if_pos H,inv_one]
  rw [if_neg (s.act_injective.ne (Ne.symm H)),if_neg H,charge,negative s (g.parent x,a) hf]; dsimp only; rw [hf, show g.parent y=_ from he H,if_pos rfl]
end turns

section tangent
-- Conjugation in the actual group/chart; no gauge-differentiability assumptions.
variable (u : G.El) (x : G.Color)
lemma exp_adjoint : G.lieExp (G.adjoint u x)=u*G.lieExp x*u⁻¹ := by
  apply G.mat_injective
  rw [G.mat_lieExp,G.mat_mul,G.mat_mul,G.mat_adjoint,G.exp_conjugate,G.mat_lieExp,G.mat_inv]; rfl

/-- Rotating increments at reference W. -/
def displacement (s : Signed) (a : Directions G n) (W : Config G n) (i : Bond n) : G.Color :=
  let j:=edge s i
  if s.flip i.2 then -(G.adjoint (W j)⁻¹ (a j)) else a j

variable (s : Signed) (a : Directions G n) (W : Config G n)
lemma size_displacement (i : Bond n) : ‖displacement s a W i‖ = ‖a (edge s i)‖ := by
  dsimp only [displacement]; split
  · rw [norm_neg,G.norm_adjoint]
  · rfl

lemma pull_increment : pull s 0 (increment W a) = increment (pull s 0 W) (displacement s a W) := by
  funext i
  rw [charge,increment,increment,charge]; dsimp only [displacement]
  split
  · rw [Work.F03.exp_neg_color,exp_adjoint]; group
  · rfl

lemma gauge_displacement (i : Bond n) (z : Site n → G.El) :
    displacement s (fun i => G.adjoint (z i.1) (a i)) (gauge z W) i =
      G.adjoint (z (s.act i.1)) (displacement s a W i) := by
  dsimp only [displacement]; split
  next ht =>
    rw [map_neg, ← G.adjoint_mul, ← G.adjoint_mul]
    let j := edge s i
    rw [show (gauge z W j)⁻¹ * z j.1=z (s.act i.1) * (W j)⁻¹ by
      unfold Lattice.gauge j
      rw [negative s i ht]; dsimp only
      have hp := StepData.negsite s (0:Site n) i.1 i.2 ht; simp_rw [affine0] at hp
      rw [hp, sub_add_cancel]; group]
  next ht =>
    have he : s.flip i.2=false := Bool.eq_false_iff.mpr ht
    rw [positive s i he]
end tangent
end Channel
end YM.ConnectedActivityE6
