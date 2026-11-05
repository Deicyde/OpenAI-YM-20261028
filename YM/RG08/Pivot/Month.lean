import YM.RG08.Pivot.Better

/-! # Positive-sign Wick symbol, applied at exactly the announced frame. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Analysis Reflect Finset Needle Source Source.Drops Labels Planned.PrimaryIntegral295
open scoped Topology BigOperators
variable {I E : Type} {L: Side} {G:Gauge} {R c:ℝ} {r d n D t j k : ℕ} {F:Frame G d} {S:SectionData F} {V:ReadsU F D R}
-- always uses common d bound on slots, allowing more zero-field channels.
variable {U:BoardU D R G} {M:Row (Loc G 1) (Loc G 1)}
lemma wick_zeros {U:Spine (Voice D R) (Loc G 1)} (h:∀ i, n < i →U i=0) (hp:Plaque M c)(i j:ℕ)(ht:n<j+2*i): fig M U i j=0:= by
    induction i generalizing j with
    | zero=> rw [fig,h j (by omega)]
    | succ i ih=> rw [fig,ih (j+2) (by omega),phil_nil hp,smul_zero]
lemma wick_wt {U : Spine (Voice D R) (Loc G 1)} (x:ℝ)(M:Row (Loc G 1) (Loc G 1))(i j:ℕ) : fig M (x•U) i j=x • fig M U i j := by
    induction i generalizing j with
    | zero=>rw [fig,fig]; rfl
    | succ i ih=>
      have he {V:EnvelopeU D R G (j+2)}: jib none M (x•V)=x • jib none M V:= by
        unfold jib; rw [show knot none (x•V) M=x • knot none V M from funext fun b=> smul_comm (tuneS M none b) x (V b),show tub (x•knot none V M) stems=x • tub (knot none V M) stems from ?_,smul_comm _ x,sew_weight]; funext i; unfold tub; simp only [Pi.smul_apply]; exact tsum_const_smul'' x -- implicit?
      rw [fig,ih,he,smul_comm,fig]
lemma wick_more {U V: Spine (Voice D R) (Loc G 1)}(h:∀ i,Tidy (U i))(g:∀ i,Tidy (V i))(hp:Plaque M c)(i j :ℕ): fig M (U-V) i j=fig M U i j-fig M V i j := by
    induction i generalizing j with
    | zero=>rw [fig,fig,fig]; rfl
    | succ i ih=>rw [fig,ih,phil_less hp (song_front hp h ..|>.pens) (song_front hp g ..|>.pens),smul_sub,fig,fig] -- check
lemma wick_sums (p:Plaque M c)(u:I→ Spine (Voice D R) (Loc G 1))(f:Finset I)(h:∀ i∈f,∀ j,Tidy (u i j))(n r: ℕ):
    frisk M (∑ i∈f,u i) n r=∑ i∈f,frisk M (u i) n r := by
    classical
    unfold frisk; rw [sum_comm (s:=f)]
    refine sum_congr rfl fun i hi=> ?_; induction f using Finset.induction_on with
    | empty=> rw [sum_empty,sum_empty]; simpa only [zero_smul] using (wick_wt (U:=(0:Spine (Voice D R) (Loc G 1))) 0 M i r)
    | insert a s ha ih=>
      have ht j (hj:j∈s) := h j (mem_insert_of_mem hj); have hx:=h a (mem_insert_self ..)
      let v:=∑ i∈s,u i
      have hu i : Tidy (v i):= by unfold v; rw [Finset.sum_apply]; exact Tidy.additions (fun i hi=> ht i hi _)
      rw [sum_insert ha,sum_insert ha,← ih ht]; change fig M (u a+v) i r= _
      rw [← sub_neg_eq_add,wick_more (V:= -v) hx (fun i=> (hu i).neg) p, ← neg_one_smul ℝ v,wick_wt, neg_one_smul ℝ (fig M v i r),sub_neg_eq_add]
lemma wick_carry {U : Spine (Voice D R) (Loc G 1)}(h : ∀ i,n < i → U i=0)(hp:Plaque M c)(he:n≤j):
    frisk M U n r=frisk M U j r:= sum_subset (range_mono (by omega)) fun i _ ht=> wick_zeros h hp i r (by have h:= mt mem_range.mpr ht; omega)
lemma audit_ordinal (H:Hol G) (b:Letter F)(U:BoardU D R G) : auditT H F U 0 b= invest H (U 0 (slot b)) b:= by
  unfold auditT; rw [Finset.sum_eq_single_of_mem (slot b) (by simp),if_pos (by omega),show 0+slot b-slot b=0 from by omega]; intro j hj hz; rw [if_neg (by have he:=mem_range.mp hj; omega)]
-- matrix at zero

def hearth (H:Hol G)(S:Row (Loc G 1) (Loc G 1))(V:ReadsU F D R) : Needle.Loft F := Matrix.of fun i b=> invest H (frisk S (V b 0) d (slot i)) i
lemma candles_front (H:Hol G)(h:Genuine H V)(hp:Plaque M c) (a b:Letter F) (he:slot b ≤ slot a):
    hearth H M V a b=(1: Loft F) a b:= by
  have hx i (hi:slot b < i): V b 0 i=0:= not_ne_iff.mp (mt ((h.rank b).cap 0 i) (by omega))
  have ht : frisk M (V b 0) d (slot a)=V b 0 (slot a):= by
    unfold frisk; rw [Finset.sum_eq_single 0]; swap
    · exact fun i _ hi=> wick_zeros hx hp i _ (by omega)
    · rw [fig]
    simp
  unfold hearth; rw [Matrix.of_apply,ht,← audit_ordinal,←atlas_fees,h.cost,hot_one,if_pos rfl]
lemma debt_kernel (H:Hol G)(h:Genuine H V)(hp:Plaque M c): HollowP ((1:Loft F)-hearth H M V) := by
  have hh i j : ((1:Loft F)-hearth H M V) i j≠ 0→ slot i<slot j := by
    intro hb; contrapose! hb; rw [Matrix.sub_apply,candles_front H h hp i j hb,sub_self]
  exact ⟨fun i j hi=> (hh i j hi).le,fun i j hi=> cascade (hh i j hi)⟩
lemma settled_hearth (H:Hol G)(h:Genuine H V)(hp: Plaque M c) :
    let P:= hearth H M V; IsUnit P.det ∧ P⁻¹ = shellP (1-P) := by
    intro P; have ht: shellP (1-P)*P=1:=by simpa only [sub_sub_cancel] using shellP_ok (debt_kernel H h hp)
    have hh:=isUnit_det_of_left_inverse ht; exact ⟨hh,left_inv_eq_right_inv (nonsing_inv_mul P hh) (mul_eq_one_comm.mpr ht)⟩

end YM.RG08.Pivot
