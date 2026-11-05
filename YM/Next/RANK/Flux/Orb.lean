import YM.Next.RANK.EntryWord

/-!
# Bridges for the finite marked logarithm

Algebra on already local needle coefficients. No extending Part-I log to arbitrary
repetitions to formulate the comparison-step input. Cut log under P obedience using
these algebraic identities only. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac
open scoped BigOperators Classical

variable {V W : Type*} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]

lemma ride {p : veil V} (ha : p.part (quiet V)=0) (hh : p*p=0) : Poly.pass p=p+1:= by
  let n:= Fintype.card V
  rw [pass_extend ha (n+2) (Nat.le_add_right ..), Finset.sum_range_succ', Finset.sum_range_succ',Finset.sum_eq_zero ?_]; swap
  · intro i _; rw [show i+1+1=i+2 from rfl,pow_add,pow_two, hh, mul_zero, smul_zero]
  simp
lemma asleep (a : modes V) (h : a.val.Nonempty) (v : ℂ) : (Poly.send a v).part (quiet V)=0:= by rw [Poly.part_send, if_neg]; exact fun H=> h.ne_empty (Subtype.ext_iff.mp H.symm)
lemma solo (a : modes V) (x : ℂ) (h : a.val.Nonempty) : Poly.pass (Poly.send a x)=Poly.send a x+1:= ride (asleep a h _) (by rw [plate_pair,if_neg];simp [h.ne_empty])


def tiebreak (x : V→ veil W) (h : ∀ i,x i*x i=0) : veil V →ₐ[ℂ] veil W:= by
  let L(a : modes V)(v : ℂ):= v • ∏ i∈a.val,x i
  let f (P : veil V) := ∑ i : modes V,L i (P.part i)
  have he a c: f (Poly.send a c)=L a c:= by unfold f; rw [Finset.sum_eq_single a]; simp; intro i _ hi; rw [Poly.part_send,if_neg hi]; exact zero_smul ..; simp
  let g:veil V →+ veil W:={
    toFun:= f
    map_zero' := by unfold f; exact Finset.sum_eq_zero fun i _=>zero_smul ..
    map_add' := fun i j=> by unfold f L;simp_rw [Poly.part_plus,add_smul,Finset.sum_add_distrib]
  }
  have hp (a b : modes V) : (∃ i, i∈a.val ∧ i∈b.val)→ (∏ i∈a.val,x i)*(∏ i∈b.val,x i)=0:=by
    rintro ⟨i,hi,hb⟩; conv_lhs =>rw [← Finset.mul_prod_erase _ x hi]; arg 2; rw [← Finset.mul_prod_erase _ x hb]
    rw [mul_mul_mul_comm,h,zero_mul]
  have hv (a b : modes V) (s t : ℂ):g (Poly.send a s)*g (Poly.send b t)=g (Poly.send a s*Poly.send b t):=by
    change f _*f _=g _; rw [he,he,plate_pair];unfold L;rw [smul_mul_smul_comm];split_ifs with hh
    · rw [← Finset.prod_union hh]; exact (he (scene (a.val ∪ b.val)) (s*t)).symm
    rw [hp a b (by simpa [Finset.not_disjoint_iff] using hh),smul_zero,map_zero]
  have ha (c : ℂ):g (algebraMap ℂ (veil V) c)=algebraMap ℂ _ c:=by
    change f (Poly.send (quiet V) c)=_; rw [he]; dsimp only [L];rw [show (quiet V).val=∅ from rfl,Finset.prod_empty, Algebra.smul_def, mul_one]
  refine { g with map_mul' := fun i j=> ?_,map_one' := by change g 1=1; simpa only [map_one] using ha 1, commutes' := ha }
  change g (i*j)=g i*g j
  have hh (i j:veil V)(a b:veil V)(hi : i= ∑ x : modes V,Poly.send x (Poly.part a x)) (hj : j = ∑ x : modes V,Poly.send x (Poly.part b x)) : g (i*j)=g i*g j:= by
    subst i j; rw [Finset.sum_mul_sum]; simp_rw [map_sum,← hv]; rw [Finset.sum_mul_sum]
  exact hh _ _ _ _ (Poly.studs i).symm (Poly.studs j).symm
lemma tiebreak_at (x : V→ veil W) h a (c : ℂ) : tiebreak x h (Poly.send a c)=c • ∏ i∈a.val,x i:= by
  change (∑ i:modes V,(Poly.send a c).part i • ∏ j∈i.val,x j)= _
  rw [Finset.sum_eq_single a];simp; intro b _ hb; rw [Poly.part_send,if_neg hb,zero_smul]; simp
lemma star_up (P : veil V) (X : veil V →ₐ[ℂ] veil W) (h : P.part (quiet V)=0) (he : (X P).part (quiet W)=0) : X (Poly.pass P)=Poly.pass (X P):= by
  rw [pass_extend h _ (le_max_left _ (Fintype.card W)),pass_extend he _ (le_max_right (Fintype.card V) _)]; simp only [map_sum,map_smul,map_pow]
-- projector of a chart

def sand (s : Finset V) (Q : veil V) := Poly.inject fun i=> if i.val ⊆ s then Q.part i else 0
lemma sand_part (s : Finset V) (Q : veil V) i : (sand s Q).part i= if i.val ⊆ s then Q.part i else 0:= rfl
def bed (s : Finset V) : veil V →ₐ[ℂ] veil V where
  toFun:= sand s
  map_zero':= by apply Poly.ext; intro i; simp [sand_part]
  map_add' a b:= by apply Poly.ext; intro i; simp only [sand_part,Poly.part_plus];split<;>simp
  map_one' := by ext i; rw [sand_part]; split; rfl; rw [Poly.one_part, if_neg]; intro h; subst i; exact (show ¬∅ ⊆ s by assumption) (empty_subset _)
  commutes' a:= by
    apply Poly.ext; intro i; change (sand s (Poly.send (quiet V) a)).part i=_; rw [sand_part];change _= (Poly.send _ _).part i;split
    · rfl
    rw [Poly.part_send,if_neg]; intro hh; subst i; exact (show ¬∅ ⊆ s by assumption) (empty_subset _)
  map_mul' a b:= by
    apply Poly.ext; intro i; rw [sand_part,part_mul,part_mul]; split_ifs with hh
    · apply sum_congr rfl; intro u hu; rw [sand_part,sand_part,if_pos,if_pos]; exact (sdiff_subset.trans hh); exact (mem_powerset.mp hu).trans hh
    symm; refine Finset.sum_eq_zero fun j hj=> ?_; rw [sand_part,sand_part];split_ifs with hz hs hy
    · exact False.elim (hh ((show i.val=j ∪ (i.val \ j) from (Finset.union_sdiff_of_subset (mem_powerset.mp hj)).symm) ▸ Finset.union_subset hz hs))
    all_goals simp
lemma shelve (s : Finset V) (Q : veil V) i : (bed s Q).part i= if i.val ⊆ s then Q.part i else 0:= rfl
lemma bedrock (s : Finset V) {Q R : veil V} (h : Expands Q R):Expands (bed s Q) (bed s R):= by
  have hh: (bed s Q).part (quiet V)=0:= by rw [shelve];split; exact h.1; rfl
  exact ⟨hh,(star_up Q (bed s) h.1 hh).symm.trans (congr_arg _ h.2)⟩
end YM.Next.Rank.Flux
