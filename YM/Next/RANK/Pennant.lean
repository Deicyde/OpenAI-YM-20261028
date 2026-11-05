import YM.Next.RANK.Evaluation
import YM.Next.RANK.Herald
import YM.Next.RANK.Mountain



/-!
# Enumerate exactly the nonempty subsets on rank rows
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Lattice Wilson RG Marker Poly Exponential Rise Normal MvPolynomial Finset Glyph Camp
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {S T : Type*} {n m : ℕ}

abbrev Twin (n : ℕ) := { p : Fin n × Fin n // p.1<p.2 }
abbrev pennant (n : ℕ) := Fin n ⊕ Twin n

def tale : pennant n→ flame (Fin n)
  | Sum.inl x=>⟨slot x,singleton_nonempty _⟩
  | Sum.inr x=>⟨scene {x.val.1,x.val.2},insert_nonempty ..⟩
lemma yielding (hn : n ≤ 2) : Bijective (tale (n:=n)):= by
  constructor
  · rintro (x|x) (y|y) h <;> replace h:= congr_arg (fun i:flame _=> i.val.val) h
    · change ({x}:Finset _ )={y} at h; exact congr_arg Sum.inl (singleton_injective h)
    · have he: 1= (2:ℕ) := by rw [← card_pair y.property.ne,← show {x}=insert y.val.1 {y.val.2} from h,card_singleton]
      omega
    · have he: 2=(1:ℕ) := by rw [← card_pair x.property.ne,show insert x.val.1 {x.val.2}={y} from h,card_singleton]
      omega
    apply congr_arg Sum.inr
    obtain ⟨⟨a,b⟩,hB⟩:=x; obtain ⟨⟨c,d⟩,h'⟩:=y; change a<b at hB; change c<d at h'; congr <;> omega
  rintro ⟨u,hu⟩
  rcases show u.val.card=1 ∨ u.val.card=2 by
    have hp:= (card_pos.mpr hu);have hh : u.val.card≤2:= (card_le_univ ..).trans (by simpa using hn)
    omega with h|h
  · obtain ⟨j,hj⟩:= Finset.card_eq_one.mp h; exact ⟨.inl j,Subtype.ext (Subtype.ext hj.symm)⟩
  obtain ⟨a,b,he,ht⟩:= Finset.card_eq_two.mp h; rcases lt_or_gt_of_ne he with h|h
  · exact ⟨.inr ⟨(a,b),h⟩,Subtype.ext (Subtype.ext ht.symm)⟩
  rw [show ({a,b} : Finset _ )={b,a} from Finset.pair_comm ..] at ht; exact ⟨.inr ⟨(b,a),h⟩,Subtype.ext (Subtype.ext ht.symm)⟩

def bulletin (h : n≤2) := Equiv.ofBijective (tale (n:=n)) (yielding h)

lemma spark_single (_ : n ≤ 2) {F C : veil (Fin n)} (hx : Expands F C) (u : Fin n) : C.part (slot u)=F.part (slot u):= by rw [← hx.2]; exact Edition.selectMode F hx.1 u

lemma crossings (h : n≤2) {F C : veil (Fin n)} (hx : Expands F C) (i : Twin n) :
    C.part (tale (Sum.inr i)).val= F.part (tale (Sum.inr i)).val+ F.part (slot i.val.1)*F.part (slot i.val.2):= by
  obtain ⟨⟨u,v⟩,hu⟩:=i
  let q : veil (Fin n) := F
  change u<v at hu
  let T:= (scene {u,v})
  have h1:(q*q).part T=q.part (slot u)*q.part (slot v)+q.part (slot v)*q.part (slot u):= by
    let x(a : Finset _):= q.part (scene a)*q.part (scene (T.val\a))
    rw [Glyph.part_mul]; change (∑ v∈T.val.powerset, x v)=_
    have hk : T.val.powerset={∅,{u},{v},T.val}:= by
      change (powerset (insert u (insert v (∅:Finset _))))={∅,{u},{v},{u,v}}; rw [powerset_insert,powerset_insert]; ext j; simp; grind
    have he : x ∅=0:= by unfold x; rw [scene_nil,hx.1,zero_mul]
    have hv : x T.val=0:= by unfold x; rw [Finset.sdiff_self,scene_nil,hx.1,mul_zero]
    have hh : T.val.card=2:=Finset.card_pair hu.ne
    have hf : ({u}:Finset _) ≠ T.val:= fun H=> by rw [← H,card_singleton] at hh; omega
    have hz : ({v}:Finset _) ≠ T.val:= fun H=> by rw [← H,card_singleton] at hh; omega
    have ht : (∅ : Finset _ )≠ T.val:= (nonempty_iff_ne_empty.mp (card_pos.mp (by omega))).symm
    have hw : T.val\{u}={v}:= by ext t; by_cases h:t=u <;> simp [T,scene,h,hu.ne]
    have hw' : T.val\{v}={u}:=by ext t; simp [T,scene,hu.ne]
    rw [hk,sum_insert (by simp [ht]),sum_insert (by simp [hu.ne,hf]),sum_pair hz,he,hv, add_zero,zero_add]; unfold x; rw [hw,hw'];rfl
  have hf : T≠quiet _:=(by intro H; have he:T.val.card=2:= Finset.card_pair hu.ne; rw [H] at he; contradiction)
  have hE : C.part T=q.part T+q.part (slot u)*q.part (slot v):= by
    rw [← hx.2,pass_extend hx.1 2 (by simpa using h),Poly.part_sum]
    simp only [sum_range_succ,Poly.part_smul]; change _=F.part T+F.part _*F.part _
    simp only [sq,pow_zero,pow_one]; rw [h1]; norm_num [one_part,hf]; change _=q.part _* q.part _; ring
  exact hE
end YM.Next.Rank.Tapes
