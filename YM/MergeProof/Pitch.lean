import YM.MergeProof.Accent
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil 
variable (B : Census V)
-- tangent product rule
lemma comet (x y: B.Mode) (i:V) : Poly.merges x y (B.fire i) ↔ (x=B.quiet ∧ y=B.fire i) ∨ (y=B.quiet ∧ x=B.fire i) := by
   constructor
   · intro h; by_cases ht : x=B.quiet
     · exact Or.inl ⟨ht,(Poly.vacuum ..).1 (ht ▸ h)⟩
     have hr:x.val⊆ (B.fire i).val:=h.2 ▸ Finset.subset_union_left
     have hh:y.val⊆ (B.fire i).val:=h.2 ▸ Finset.subset_union_right
     have hv : x=B.fire i:=Subtype.ext ((Finset.subset_singleton_iff.mp hr).resolve_left (fun hh=>ht (Subtype.ext hh)))
     have hp : y=B.quiet :=Subtype.ext ((Finset.subset_singleton_iff.mp hh).resolve_right (fun hh=> (show False from by have H:=h.1; rw [hv,hh] at H; simp [Census.fire] at H)))
     exact Or.inr ⟨hp,hv⟩
   rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩);exact (Poly.vacuum ..).2 rfl; rw [Poly.wind]; exact (Poly.vacuum ..).2 rfl
lemma shock (a b : Poly B) (i : V) : (a*b).part (B.fire i)=a.part B.quiet*b.part (B.fire i)+a.part (B.fire i)*b.part B.quiet:= by
   rw [Poly.part_mul,← Finset.sum_erase_add _ _ (a:=B.fire i) (by simp),Finset.sum_eq_single B.quiet]; simp [comet,B.fire_hot i,(B.fire_hot i).symm]
   · intro x hx hp; simp [comet,hp,(Finset.mem_erase.mp hx).1]
   simp [(B.fire_hot i).symm]
lemma shockProd₀ (f:I→Poly B) (s:Finset I) : (∏ i∈s,f i).part B.quiet=∏ i∈s,(f i).part B.quiet:=by
   induction s using Finset.induction with
   | empty=>simp
   | insert i s hi ih=>rw [Finset.prod_insert hi,Finset.prod_insert hi,Poly.quiet_mul,ih]
lemma shockProd (f:I→Poly B) (s:Finset I)(v:V) : (∏ i∈s,f i).part (B.fire v)=∑ i∈s,(f i).part (B.fire v)* ∏ j∈s.erase i,(f j).part B.quiet:=by
   induction s using Finset.induction with
   | empty=>simp [B.fire_hot v]
   | insert i s he ih=>
     rw [prod_insert he,sum_insert he,shock, ih,shockProd₀,Finset.erase_insert he,mul_sum,add_comm]; congr 1; refine sum_congr rfl fun j hj=> ?_; rw [erase_insert_of_ne (ne_of_mem_of_not_mem hj he).symm,prod_insert (fun h=> he ((erase_subset ..) h))]; ring
variable [Fintype V]
lemma whisper (F : Poly B) (h:F.part B.quiet=0) (i:V) : (Poly.pass F).part (B.fire i)=F.part (B.fire i):=by
   unfold Poly.pass; rw [Poly.part_sum,Finset.sum_eq_single 1]; simp
   · intro j _ hp; by_cases hm:j=0
     · rw [hm]; simp [B.fire_hot i]
     rw [Poly.part_smul,Poly.high F h j _ ?_,mul_zero]; change ({i}:Finset V).card < _; rw [Finset.card_singleton]; omega
   intro hp; exfalso; have : Nonempty V:=⟨i⟩; exact hp (mem_range.mpr (by simpa using Fintype.card_pos (α:=V)))
lemma mute (f:V→ℂ) : (Mach B f).part B.quiet=0:=by simp [Mach,Poly.part_sum,fun i=>(B.fire_hot i).symm]
lemma sing (f:V→ℂ) (i:V) : (Mach B f).part (B.fire i)=f i:=by simp [Mach,Poly.part_sum]
omit [Fintype V] in
lemma hop (F:Poly B) (h:rises F): F.part B.quiet=0:=by by_contra hn; have ht:= h _ hn; simp [Census.quiet] at ht
omit [Fintype V] in
lemma hop₁ (F:Poly B) (h:rises F) (i:V) : F.part (B.fire i)=0:=by by_contra hn; have ht:= h _ hn; simp [Census.fire] at ht
variable {B}
-- canonical projection

def octave (p:Poly B) : Poly B:=Poly.inject fun i=> if 2≤ i.val.card then p.part i else 0
omit [Fintype V] in
lemma octaves (p:Poly B) : rises (octave p):= by intro i h; by_contra hn; exact h (if_neg hn)
omit [Fintype V] in
lemma crest (p:Poly B) (i:B.Mode) (h:2≤ i.val.card): (octave p).part i=p.part i:= if_pos h
omit [Fintype V] in
lemma starlet (p:Poly B) (i:B.Mode) (h:i.val.card<2): (octave p).part i=0:= if_neg (Nat.not_le.mpr h)
lemma hush (f:V→ℂ)(i:B.Mode)(h:2≤ i.val.card) : (Mach B f).part i=0:=by simp [Mach,Poly.part_sum,show ∀ j,i≠B.fire j from (fun j hh=> (by rw [hh] at h; simp [Census.fire] at h))]
lemma ballots (p:Poly B):p= Poly.bead B (p.part B.quiet)+Mach B (fun i=>p.part (B.fire i))+octave p:=by
   ext i; simp only [Poly.part_plus]; rcases Nat.lt_trichotomy i.val.card 1 with h|h|h
   · have he:i=B.quiet:= Subtype.ext (card_eq_zero.mp (by omega)); rw [he,mute,hop B (octave p) (octaves p)]; simp [Poly.bead]
   · obtain ⟨j,hj⟩:=card_eq_one.mp h; have hz:i=B.fire j:=Subtype.ext hj; rw [hz,sing,hop₁ B (octave p) (octaves p)]; simp [Poly.bead,B.fire_hot]
   rw [crest _ _ (by omega),hush _ _ (by omega)]; simp [Poly.bead,show i ≠ B.quiet from fun ht=> (by subst i; simp [Census.quiet] at h)]
end YM.MergeProof.Accent
