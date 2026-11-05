import YM.Next.RANK.Flux.Radius

/-!
# Actual NIL log as unforced marker entries

Use entry even when computed coefficient zero. Drop only by cert. Each
H.value in Value.SourceAt still globally local, mask at measure applies separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory
open scoped BigOperators Classical

variable {V W ι : Type*} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [DecidableEq ι] [Fintype ι]
variable {G : Gauge} {n : Side} {ζ : V→ Site n} (X : ι→ SourceAt G ζ) (b : V→ℝ) (M : ℕ) (a t : ℝ)

def feet := fun i=> (X i).extent

def strict (s : Finset ι) := (s:Set ι).PairwiseDisjoint (fun i=>(X i).fires.val)
abbrev MergeLog := { p : Finset ι // majesty (feet X) p≠0∧ strict X p }
def country (s : Finset ι) : modes V := scene (s.biUnion (fun i=> (X i).fires.val))

def Bond (p : MergeLog X) : SourceAt G ζ where
  extent := p.val.biUnion (feet X)
  fires := country X p.val
  chosen := by obtain ⟨i,hi⟩:= (majesty_spark _ p.property.1).1; obtain ⟨j,hj⟩:= (X i).chosen; exact ⟨j,mem_biUnion.mpr ⟨_,hi,hj⟩⟩
  remembers i h:= by obtain ⟨u,hu,hv⟩:=mem_biUnion.mp h; exact mem_biUnion.mpr ⟨u,hu,(X u).remembers i hv⟩
  value U:= majesty (feet X) p.val * ∏ j∈p.val,(X j).value U
  meas:= Measurable.mul measurable_const (Finset.measurable_fun_prod _ (fun i _=>(X i).meas))
  loc := by
    intro U V h; apply congr_arg;exact prod_congr rfl fun j hj=> (X j).loc U V (agrees_mono h (fun i hi=> mem_biUnion.mpr ⟨_,hj,hi⟩))
  inv := by intro k U; apply congr_arg;exact prod_congr rfl (fun j _=>(X j).inv k U)
lemma plays (p : MergeLog X) (U : Config G n) : (Bond X p).amount t U= majesty (feet X) p.val • (∏ i∈p.val,(X i).amount t U):= by
  let E:= p.val.biUnion (feet X); let v:=majesty (feet X) p.val; let H:= (Bond X p).fires
  unfold SourceAt.amount; rw [plasma,if_pos (show (p.val:Set ι).PairwiseDisjoint (fun j=>(X j).fires.val) from p.property.2)]; rw [show (Bond X p).extent=E from rfl]
  by_cases hp:Healthy t E U
  · have hf (j) (hj : j∈p.val) : Healthy t (X j).extent U:= Disjoint.mono_left (fun i hi=> mem_biUnion.mpr ⟨_,hj,hi⟩) hp
    rw [masked_eq _ _ _ _ hp,prod_congr (g:=fun i=>(X i).value U) rfl (fun i hi=> masked_eq _ _ _ _ (hf i hi))]
    change Poly.send H (v*_) = _ • Poly.send H _; ext i; simp only [Poly.part_smul,Poly.part_send]; split<;>simp [v]
  obtain ⟨x,hx,hh⟩:=not_disjoint_iff.mp (show ¬Disjoint _ _ from hp)
  obtain ⟨i,hi,hg⟩:=mem_biUnion.mp hx; have he: ¬Healthy t (X i).extent U:=not_disjoint_iff.mpr ⟨x,hg,hh⟩
  rw [masked_ne _ _ _ _ hp, Poly.send_zero,prod_eq_zero hi (masked_ne _ _ _ _ he),Poly.send_zero,smul_zero]



omit [DecidableEq ι] [Fintype ι] in
lemma pawn (i : ι) (U : Config G n) : ((X i).amount t U)*(X i).amount t U = 0:= by
  unfold SourceAt.amount;rw [plate_pair,if_neg]; simp [(X i).chosen.ne_empty]
lemma monarch (U : Config G n) (s : Finset ι) : Poly.pass (∑ p ∈ univ.filter (fun p:MergeLog X=> p.val⊆s),(Bond X p).amount t U) = chair (feet X) (fun i=>(X i).amount t U) s:= by
  let Q (i) := (X i).amount t U; let Z:=tiebreak Q (fun i=> pawn X t i U);let P:= feet X;let T:=univ.filter (fun p:MergeLog X=> p.val⊆s);let f(p: MergeLog X):veil V:=(Bond X p).amount t U
  have hh : Z (herald P s)=∑ p∈T,f p:= by
    rw [throne_up,map_sum]
    let v:=T.image Subtype.val
    have he : v⊆s.powerset:= fun i hi=> by obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; exact mem_powerset.mpr (mem_filter.mp hj).2
    rw [← sum_subset he, Finset.sum_image Subtype.val_injective.injOn]; apply sum_congr rfl; intro i _; exact (tiebreak_at ..).trans (plays ..).symm
    intro i hi h
    by_cases hh : majesty P i=0
    · rw [hh,Poly.send_zero,map_zero]
    have hg : ¬ strict X i:= by
      intro H; exact h (mem_image.mpr ⟨(⟨i,hh,H⟩:MergeLog X), mem_filter.mpr ⟨mem_univ _,mem_powerset.mp hi⟩, rfl⟩)
    unfold Z;rw [tiebreak_at]; change _ • (∏ j∈i,Q j)= _; unfold Q SourceAt.amount;rw [plasma,if_neg (show ¬ (i:Set ι).PairwiseDisjoint (fun j=> (X j).fires.val) from hg),smul_zero]
  have he : (Z (herald P s)).part (quiet V)=0:= by rw [hh,Poly.part_sum]; exact Finset.sum_eq_zero fun i _=> asleep _ (Bond X i|>.chosen) _
  change Poly.pass (∑ p∈T,f p)=_; rw [← hh,← star_up _ Z (herald_spec ..|>.1) he,(herald_spec ..).2,aura,chair,map_sum]
  unfold chair;apply sum_congr rfl;intro i _; split_ifs;rw [cluster_form];exact (tiebreak_at ..).trans (one_smul ..); exact map_zero _
end YM.Next.Rank.Flux
