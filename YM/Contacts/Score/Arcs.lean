import YM.Contacts.Score.Alive
import YM.Contacts.Normal.Rays
/-!
# Chosen alternatives and (when examining disjoint strata) shells

Absoluteness for several clusters, several alternatives simult. needs control over the punctured
pairings when one or more root arms are fixed, shell slice or not. The normal test localization
is optically AFTER the Taylor difference mask, never used on the test to compute the difference.
Germ equations still apply to the `action` of these scores.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory Submodule Ordered MultipleContact MultipleContact.Panel MultipleContact.Script
open scoped Topology Classical BigOperators ContDiff TensorProduct InnerProductSpace
variable {I A B E : Type*} [NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
 [CommRing A][Algebra ℂ A]
variable {k : ℕ} {p q : Optical E} {K L V T : Submodule ℝ E}
def Layered (K : Submodule ℝ E)(f : SmoothTests E) : Prop := ∀ x y,K.starProjection x= K.starProjection y → f.val x =f.val y
variable {f g : SmoothTests E}
lemma stillWindow (K : Submodule ℝ E) (r : ℝ) : Layered K (eclipse K r) := fun _ _ hx=> show (↑(cutoff _ _):ℂ)-(↑(cutoff _ _):ℂ)=(↑(cutoff _ _):ℂ)-(↑(cutoff _ _):ℂ) by rw [hx]
omit [FiniteDimensional ℝ E] in
lemma commute_direct (f g : SmoothTests E) : Commute (mask f) (mask g):= LinearMap.ext fun _=> Subtype.ext (funext fun x=>mul_left_comm (f.val x) (g.val x) _)
lemma free_slide (hf : Layered K f) (h : L ≤ Kᗮ)(t : ℝ)(x : E) : f.val (slide L t x)=f.val x:= hf _ _ (by change K.starProjection (x+(t-1) • L.starProjection x)=_; rw [map_add,map_smul,K.starProjection_apply_eq_zero_iff.mpr (h (L.starProjection_apply_mem x)),smul_zero,add_zero])
lemma free_scale (hf : Layered K f) (h : L ≤ Kᗮ) (g : SmoothTests E) (n : ℕ) (x:E) : (piece L n (mask f g)).val x= f.val x*(piece L n g).val x:= by
   have he:= atoms_equal L (mask f g) n 1 x; have he':=atoms_equal L g n 1 x; rw [slide_one] at he he'; rw [← he,← he',vat _ (onScale ..), vat _ (onScale ..)]
   rw [show (fun y:ℝ=>scaledField L (mask f g) (x,y))=(fun y:ℝ=> f.val x • scaledField L g (x,y)) from funext fun y=> by change f.val (slide L y x) * _= _; rw [free_slide hf h]; rfl]; unfold coeff
   have hk : ContDiff ℝ ∞ (fun y:ℝ=>scaledField L g (x,y)):= (onScale L g).comp (contDiff_const.prodMk contDiff_id)
   rw [show (fun y:ℝ=> f.val x • scaledField L g (x,y))= f.val x • (fun y:ℝ=>scaledField L g (x,y)) from rfl,iteratedFDeriv_const_smul_apply (lowerSmooth hk _|>.contDiffAt)]; exact smul_comm _ _ _
lemma free_taylor (hf : Layered K f)(h : L ≤ Kᗮ)(r : ℝ)(n : ℕ) : Commute (mask f) (taylor L r n) := by
    refine Eq.symm (LinearMap.ext fun g=> Subtype.ext (funext fun x=>?_)) -- coercions Commute?
    change (window _ _).val x * (jet L n (mask f g)).val x = f.val x*((window _ _).val x * (jet L n g).val x)
    rw [← mul_left_comm ((window L r).val x) (f.val x) ((jet L n g).val x)] -- names?
    apply congrArg ((window L r).val x*·); rw [jet_formula,jet_formula,Lens.atoms,Lens.atoms, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> free_scale hf h g _ x

inductive Attention (K : Submodule ℝ E) : Optical E → Prop
| thermal {p : Optical E} : Uses K p → Attention K p
| opt {L : Submodule ℝ E}{f : SmoothTests E} : L≤K → Layered L f → Attention K (mask f)
| times {p q : Optical E} : Attention K p→ Attention K q → Attention K (p*q)

lemma Layered.independent (hf : Layered K f)(he : Uses L p)(h : L ≤ Kᗮ) : Commute (mask f) p:= by
   induction he with
   | taylor M he v i=> exact free_taylor hf (he.trans h) ..
   | times _ _ hx hy=> exact hx.mul_right hy
   | id => exact Commute.one_right _

omit [FiniteDimensional ℝ E] in
lemma skip (h : K ≤ Lᗮ) : L ≤ Kᗮ := (le_orthogonal_orthogonal _).trans (orthogonal_le h)
lemma Attention.ready (hx : Attention K p)(hy : Attention L q)(h : K≤ Lᗮ) : Commute p q:= by
    induction hx with
    | thermal hx=>
      induction hy with
      | thermal hy=> exact hx.independent hy h
      | opt hy hm=> exact (hm.independent hx (h.trans (orthogonal_le hy))).symm
      | times _ _ hx hy=> exact hx.mul_right hy
    | opt hx hk=>
      induction hy with
      | thermal hy=> exact hk.independent hy (skip (hx.trans h))
      | opt hy hm=> exact commute_direct ..
      | times _ _ hx hy=> exact hx.mul_right hy
    | times _ _ hx hy=> exact hx.mul_left hy
lemma Attention.adhesive (h : Attention K p) {D : E→ₗ[ℝ] E4}(he : K≤D.ker) : Adhesive D p := by
   induction h with
   | thermal h=> exact Adhesive.from_use h he
   | @opt L f h'=> exact ⟨id, fun x a b he=> he.mono fun x hx=> congr_arg (f.val x *·) hx, fun _=>rfl⟩
   | times _ _ ha hb=> exact ha.multiply hb

variable {S U : Group k} (P : E →ₗᵢ[ℝ] Points k)
/-- none vote means keep all weights and residue. some vote an extended choice
(including residue). Horizon still determined by assigned grades. Slice for annular estimate. -/
structure Ballot where
   vote : Option (Option ℕ)
   slice : Option ℕ
namespace Ballot
variable (x : Ballot)
def tally {n : ℕ}(a : Option (Fin n)) := x.vote=none ∨ x.vote= some (Option.map Fin.val a)
def whole : Ballot:= ⟨none,none⟩
def adjust (v : Option (Option ℕ))(n : Option ℕ): Ballot:= ⟨v,n⟩
def flip (n : ℕ) : Ballot:= ⟨x.vote,some n⟩
end Ballot
abbrev Menu (k : ℕ) := Group k → Ballot
def widenMenu (q : Splittings S) (f : Menu k) : Menu k:= fun i=> if i∈ q.val.parts then Ballot.whole else f i
lemma menu_small (q : Splittings S)(f : Menu k)(h : U∈ q.val.parts): widenMenu q f U = Ballot.whole:= if_pos h
lemma menu_unchanged (q : Splittings S)(f : Menu k)(h : U ∉ q.val.parts): widenMenu q f U=f U := if_neg h
namespace System
variable (Y:System E A k) (s : ℝ) {g : Group k} (i : Group k)

-- test only
abbrev sliceAt (v : Option ℕ) : Optical E := v.elim 1 (fun n=>mask (eclipse (normalOn P i) (dyad n))) -- `1` lens id
abbrev maskScore (X : Score E A)(b : Ballot)(v : Y.Arm i) := X * instructionScore E A (sliceAt P i b.slice)*instructionScore E A (Y.maskAt P s i v) -- `After` rightmost first

def candidate (v : Y.Arm i)(b : Ballot) := Y.maskScore P s i (reshape (Y.treatment i v) (Y.punctured P s i)) b v
abbrev slate (b : Ballot) : Finset (Y.Arm i) := Finset.univ.filter b.tally
def vote (b : Ballot) := if 1 < i.card then ∑ v∈Y.slate i b, Y.candidate P s i v b else Y.full P s i
lemma pays (b : Ballot)(h : 1 < i.card) : Y.vote P s i b=∑ v∈Y.slate i b, Y.candidate P s i v b:= if_pos h
lemma alone (b : Ballot)(h : i.card ≤ 1): Y.vote P s i b= Y.full P s i := if_neg (not_lt.mpr h)
omit [FiniteDimensional ℝ E] in
lemma all_members (b : Ballot)(h : b.vote=none) : Y.slate i b= Finset.univ:= Finset.filter_true_of_mem fun _ _=> Or.inl h -- name?
omit [FiniteDimensional ℝ E] in
lemma one_member (b : Ballot)(v : Y.Arm i)(h : b.vote=some (Option.map Fin.val v)) : Y.slate i b={v}:= by
   ext a; simp only [slate, Finset.mem_filter, Ballot.tally,h, reduceCtorEq,Option.some.injEq,false_or, Finset.mem_singleton,Finset.mem_univ,true_and]; cases a <;> cases v <;> simp [eq_comm,Fin.ext_iff] -- iff
lemma from_unit (X : Score E A) : X * instructionScore E A (sliceAt P i none)=X:=mul_one X
lemma unsliced (v : Y.Arm i) (b : Ballot)(h : b.slice=none) : Y.candidate P s i v b= reshape (Y.treatment i v) (Y.punctured P s i) * instructionScore E A (Y.maskAt P s i v):= by rw [candidate,maskScore,h,from_unit]
lemma all_votes : Y.vote P s i Ballot.whole= Y.full P s i:= by
  by_cases h:1 < i.card; swap; · exact Y.alone P s _ _ (not_lt.mp h)
  rw [pays _ _ _ _ _ h, all_members _ _ _ rfl]; simp_rw [Y.unsliced P s i _ Ballot.whole rfl]; exact (Y.full_split P s i h).symm
lemma focused_candidate (v : Y.Arm i)(b : Ballot) : Mark (Attention (normalOn P i)) (Y.candidate P s i v b):= by
   let L := Attention (normalOn P i); apply Mark.prod (R:=L) (S:=L) ?_ ?_ (fun _ _ hx hy=>hx.times hy)
   · apply Mark.prod (R:=L) (S:=L) (Mark.transformed ((Y.uses_punctured P s i).switch fun _=> .thermal) _) ?_ (fun _ _ hx hy=> hx.times hy)
     cases b; next v w=> cases w with
     | none=> exact Mark.inst (.thermal Uses.id)
     | some n=> exact Mark.inst (.opt le_rfl (stillWindow _ _))
   cases v with
   | none=> exact Mark.inst (.thermal Uses.id)
   | some w=> rw [maskAt, instructionScore,deviation, show (1:E→A) ⊗ₜ[ℂ] (LinearMap.id - taylor (normalOn P i) s (Y.needle i w))=(1 ⊗ₜ[ℂ] (1:Optical E))-(1 ⊗ₜ[ℂ] taylor (normalOn P i) s (Y.needle i w)) from TensorProduct.tmul_sub (1:E→A) (1:Optical E) (taylor (normalOn P i) s (Y.needle i w)),sub_eq_add_neg]; exact Mark.plus (.atom _ (Attention.thermal Uses.id)) (Mark.minus (.atom _ (.thermal (.taylor _ le_rfl _ _))))
lemma focused (b : Ballot) : Mark (Attention (normalOn P i)) (Y.vote P s i b):= by
   unfold vote; split; exact Mark.sum (fun _ _=>focused_candidate ..); exact Mark.switch (Y.uses_full P s i) (fun _=> Attention.thermal)
end System
end YM.Contacts.Normal
