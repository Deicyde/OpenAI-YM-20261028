import YM.MergeProof.Temper
import YM.Next.MULTISOURCE.Formal
/-!
# Root alternatives on the physical marker polynomial

Contravariant license for forgetting an ancestor: every nonzero image
of a potential word (including precisely its square-zero condition) had
BETTER be legal upstairs. In particular this won't reopen pair exclusions
between siblings without another argument. `feed` absorbs explicit per-mark
weights, such as engineering, signs on exceptions, or native test payments;
no hidden marker factorial. Tows carry support prices across such a license.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Finset Filter MeasureTheory Set
open Marker MergeProof Accent Extra Multi
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {V W I J : Type*}[DecidableEq V][DecidableEq W]
variable {B:Census V}{C:Census W}{δ:V→W}

def Lit (C:Census W)(δ:V→W)(i:Finset V) : Prop := i.image δ∈ C.choices∧ Set.InjOn δ (i:Set V)
def License (C:Census W)(B:Census V) (δ:V→W):Prop:= ∀ i:Finset V,Lit C δ i→i∈ B.choices
omit [DecidableEq V] in
lemma dark_empty : Lit C δ (∅: Finset V) :=by simp [Lit,C.blank]
omit [DecidableEq V] in
lemma dark_one (i : V) : Lit C δ {i}:=by simp [Lit,C.solo]
omit [DecidableEq V] in
lemma Lit.down {x z:Finset V} (h:Lit C δ x)(hy:z⊆ x) : Lit C δ z:=⟨C.down h.1 _ (Finset.image_mono _ hy),h.2.mono hy⟩
def Lit.climb {x:Finset V}(h:Lit C δ x) : C.Mode:= ⟨x.image δ,h.1⟩
lemma Lit.together {x y z:B.Mode} (hx:Lit C δ x.val)(hy:Lit C δ y.val)(hz:Lit C δ z.val)(hi:Poly.merges x y z):Poly.merges hx.climb hy.climb hz.climb:=by
    obtain ⟨ha,hb⟩:= hi
    refine ⟨Finset.disjoint_left.mpr ?_,by dsimp only [Lit.climb]; rw [← hb,Finset.image_union]⟩
    intro i hj hk; obtain ⟨j,hj,hJ⟩:= mem_image.mp hj; obtain ⟨k,hk,hK⟩:= mem_image.mp hk
    exact Finset.disjoint_left.mp ha (show k ∈ x.val from hz.2 (hb ▸ mem_union_left _ hj) (hb ▸ mem_union_right _ hk) (hJ.trans hK.symm) ▸ hj) hk
lemma Lit.pooled {x y:Finset V}{w:C.Mode} (hx:Lit C δ x)(hy:Lit C δ y)(hi:Poly.merges hx.climb hy.climb w): Lit C δ (x∪y) :=by
    obtain ⟨hd,hb⟩:= hi; refine ⟨?_,?_⟩
    · dsimp only[Lit.climb] at hb; rw [Finset.image_union,hb]; exact w.property
    have he(i j:V)(h1:i∈x)(h2:j∈y):δ i≠ δ j:=fun h=> Finset.disjoint_left.mp hd (show δ j∈hx.climb.val from h ▸ mem_image_of_mem δ h1) (mem_image_of_mem _ h2)
    intro i h j h' ha; rcases Finset.mem_union.mp h with h|h <;> rcases mem_union.mp h' with h'|h'
    · exact hx.2 h h' ha
    · exact False.elim (he i j h h' ha)
    · exact False.elim (he j i h' h ha.symm)
    exact hy.2 h h' ha
lemma License.retain (he:License C B δ) {x y:B.Mode}{w:C.Mode} (hx:Lit C δ x.val)(hy:Lit C δ y.val)(hi:Poly.merges hx.climb hy.climb w): ∃ z, Poly.merges x y z:=by
    refine ⟨⟨_,he _ (hx.pooled hy hi)⟩,Finset.disjoint_left.mpr ?_,rfl⟩
    intro i hj hk; exact Finset.disjoint_left.mp hi.1 (mem_image_of_mem δ hj) (mem_image_of_mem _ hk)
omit [DecidableEq V] in
lemma Lit.keep_count {x: Finset V}(h:Lit C δ x):h.climb.val.card=x.card:=Finset.card_image_of_injOn h.2

section
variable (B C δ)
def move (i:B.Mode)(c:ℂ) : Poly C:= if h:Lit C δ i.val then Poly.send h.climb c else 0
lemma move_add (i:B.Mode)(c t:ℂ):move B C δ i (c+t)=move B C δ i c + move B C δ i t:=by by_cases he:Lit C δ i.val <;> simp [move,he,YM.Multi.send_add]
lemma move_scale (i:B.Mode)(c t:ℂ):move B C δ i (c*t)=c • move B C δ i t:=by by_cases he:Lit C δ i.val <;> simp [move,he,YM.Multi.send_scale]
def moveL : Poly B →ₗ[ℂ] Poly C where
    toFun a:=∑ i, move B C δ i (a.part i)
    map_add' a b:=by simp only[Poly.part_plus,move_add,Finset.sum_add_distrib]
    map_smul' r a:=by simp only[Poly.part_smul,move_scale,Finset.smul_sum,RingHom.id_apply]
lemma moveL_one (i:B.Mode)(c:ℂ) : moveL B C δ (Poly.send i c)=move B C δ i c:=by
    unfold moveL; simp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [sum_eq_single i]; simp
    · intro j _ h; by_cases he:Lit C δ j.val <;> simp [move,he,h]
    simp
end

variable (a:V→ℂ)
def forget (h:License C B δ) : Poly B →ₐ[ℂ] Poly C:= by
    refine AlgHom.ofLinearMap (moveL B C δ) ?_ ?_
    · change moveL B C δ (Poly.send B.quiet 1)=Poly.send C.quiet 1
      rw [moveL_one,move,dif_pos (show Lit C δ B.quiet.val from dark_empty)]; congr 1
    have hp (x y : B.Mode)(s t:ℂ): moveL B C δ (Poly.send x s*Poly.send y t)=moveL B C δ (Poly.send x s)*moveL B C δ (Poly.send y t):=by
       rw [moveL_one,moveL_one]; by_cases ht:∃ z,Poly.merges x y z
       · obtain ⟨z,hz⟩:=ht; rw [YM.Multi.send_prod hz, moveL_one]; unfold move
         by_cases hh : Lit C δ z.val
         · have hv := hz.2; have hx:Lit C δ x.val:=hh.down (hv ▸ subset_union_left); have hy:Lit C δ y.val:=hh.down (hv ▸ subset_union_right); rw [dif_pos hh,dif_pos hx,dif_pos hy,YM.Multi.send_prod (hx.together hy hh hz)]
         rw [dif_neg hh]; by_cases hx:Lit C δ x.val; by_cases hy:Lit C δ y.val
         · rw [dif_pos hx,dif_pos hy,YM.Multi.send_noProd ?_]; exact fun ⟨u,h⟩=> hh (hz.2 ▸ (hx.pooled hy h))
         · rw [dif_neg hy,mul_zero]
         rw [dif_neg hx,zero_mul]
       rw [YM.Multi.send_noProd ht, map_zero]; unfold move
       split
       next h'=> split; next hy=> rw [YM.Multi.send_noProd ?_]; rintro ⟨z,hi⟩; exact ht (License.retain h h' hy hi)
                 next=> rw [mul_zero]
       next=> rw [zero_mul]
    intro x y; rw [← Poly.studs x, ← Poly.studs y]; simp_rw [Finset.sum_mul,Finset.mul_sum,map_sum,hp,Finset.sum_mul,Finset.mul_sum]

def feed (h:License C B δ) := (forget h).comp (YM.Multi.dilation B a)
lemma mouth (h:License C B δ)(x:B.Mode) (c:ℂ):feed a h (Poly.send x c)=move B C δ x ((∏ i∈x.val, a i)*c) :=by
    change moveL B C δ (YM.Multi.dilation B a (Poly.send x c))=_; rw [YM.Multi.dilation_send,moveL_one] -- check
lemma parts_of_feed (h:License C B δ)(p:Poly B)(x:C.Mode):
    (feed a h p).part x= ∑ i:B.Mode,(move B C δ i ((∏ j∈i.val, a j)*p.part i)).part x:=by
    conv_lhs=> rw [← Poly.studs p,map_sum,Poly.part_sum]
    simp_rw [mouth]
lemma feed_fire (h:License C B δ)(i:V)(x:ℂ) : feed a h (Poly.send (B.fire i) x)= Poly.send (C.fire (δ i)) (a i*x):=by
    rw [mouth,move,dif_pos (show Lit C δ (B.fire i).val from dark_one i)]; simp [Lit.climb,Census.fire]
lemma feed_quiet (h:License C B δ)(p:Poly B):(feed a h p).part C.quiet=p.part B.quiet:=by
    rw [parts_of_feed,Finset.sum_eq_single B.quiet,move,dif_pos (show Lit C δ B.quiet.val from dark_empty)]; simp [Census.quiet,Lit.climb]
    · intro i _ he; unfold move; split
      next ht => rw [Poly.part_send,if_neg ?_]; exact fun h' => he (Subtype.ext (by simpa only [Lit.climb,Census.quiet,Finset.image_eq_empty] using congr_arg Subtype.val h'.symm))
      next=>rfl
    simp
section
variable [Fintype V][Fintype W]
lemma feed_mach (h:License C B δ)(p:V→ℂ): feed a h (Mach B p)= Mach C (fun j=>∑ i:V,if δ i=j then a i*p i else 0):=by
    ext j; unfold Mach; rw [map_sum]; simp_rw [feed_fire]
    all_goals
     by_cases hf:∃ i:W,C.fire i=j
     · obtain ⟨i,rfl⟩:=hf
       simp [Poly.part_sum,eq_comm]
     simp [Poly.part_sum,Poly.part_send,show ∀ i, j ≠ C.fire i from fun i e=>hf ⟨i,e.symm⟩]
end
end YM.RG05Readout.Many
