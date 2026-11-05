import YM.Next.RANK.Evaluation
import YM.Next.RANK.Mountain

/-!
# Coefficient projection from the complete replica polymer

For the initial components of each marker compute both entries directly.
A monomial-only K slice from possible countably many *choices* with the very
same support may be summed thanks to mutual exclusion established by that
support and the exact inventory retained in the slice. This uses only density
transport along quota, BEFORE new thresholds and any reorganization on them.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells  Finset Baler Source
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {A : Activities G n} {Q : Rep G n} {V : Type} [DecidableEq V] [Fintype V]
variable {F : PathData G}
variable {d : ℕ} {W : Labels.Frame G d} {ζ : V→ Site n} {σ α δ η Λ e z : ℝ}
variable {K B : Coefficient W n}

lemma mute (v : V) : slot v≠ quiet V:=fun h=> by have hp := Subtype.ext_iff.mp h; simp [slot,Census.fire,quiet,Census.quiet] at hp
lemma dues (v : V) (a b : ℂ) : (Poly.send (quiet V) a+Poly.send (slot v) b).part (quiet _)= a ∧ (Poly.send (quiet V) a+Poly.send (slot v) b).part (slot v)=b:= by simp [Poly.part_plus,Poly.part_send,mute,Ne.symm (mute v)]
lemma faint (a : ℂ) (i j : V) (h : i≠j) : (Poly.send (slot j) a : veil V).part (slot i)=0 := (Poly.part_send ..).trans (if_neg (fun hh=> h (by simpa only [slot,Census.fire,singleton_inj] using Subtype.ext_iff.mp hh)))

-- dual projection independent of all other markers
structure Dual (x : V) (S T : veil V) : Prop where
  base : T.part (quiet _)= S.part (quiet _)
  tag : T.part (slot x)= S.part (slot x)
lemma dual_add {a : V} {U V' W P : veil V} (h : Dual a U V') (hh : Dual a W P) : Dual a (U+W) (V'+P):= by constructor <;> simp only [Poly.part_plus,h.base,h.tag, hh.base,hh.tag]


lemma Dual.sum {ι : Type*} {a : V} (Q : Finset ι) {x y : ι→ veil V} (h : ∀ i∈Q,Dual a (x i) (y i)): Dual a (∑ i∈Q,x i) (∑ i∈Q,y i):= by
  classical
  induction Q using Finset.induction_on with
  | empty => simpa only [sum_empty] using (show Dual a 0 0 from ⟨rfl,rfl⟩)
  | insert i Q hi ih => rw [sum_insert hi,sum_insert hi]; exact dual_add (h i (mem_insert_self _ _)) (ih fun i hv=> h _ (mem_insert_of_mem hv))
lemma Dual.zero {a : V} (t : Glyph.modes V) (h : 2 ≤ t.val.card) (V : ℂ) : Dual a (Poly.send t V) 0:= by
  have hp : t.val.Nonempty := card_pos.mp (by omega)
  refine ⟨Eq.symm ?_,Eq.symm ?_⟩ <;> simp only [Poly.part_send,Poly.part_nil] <;> apply if_neg
  · intro he; exact hp.ne_empty (Subtype.ext_iff.mp he.symm)
  intro he
  have he : t.val={a}:=Subtype.ext_iff.mp he.symm; rw [he,card_singleton] at h; omega


lemma mark_one (i : V) (F g : ℂ) (U : veil V) :
    (((Poly.send (quiet V) F+Poly.send (slot i) g)*U).part (slot i))= F*U.part (slot i)+g* U.part (quiet V):= by simp only [mul_solo, (dues ..).2,(dues ..).1]

-- component of the old law in canonical orientation, with no auxiliary weighting.

def identifier (B : Rep G n) i:= Baler.locator (B.activities.forced i)

def followed (P : Rep G n) (i : V) (v : Coefficient W n) (U : Config G n) (x : ℕ): veil V:= Poly.send (quiet _) ((P.activities.K x U:ℝ):ℂ)+Poly.send (slot i) (v.forced x U)

lemma tags_prod (B : Coefficient W n) (c : V) (P : Rep G n) (U : Config G n) (i : Finset ℕ):
    ((∏ j∈i,followed P c B U j).part (quiet _) =( (∏ j∈i,P.activities.K j U):ℝ)) ∧
    (∏ j∈i,followed P c B U j).part (slot c)=(∑ k∈i, B.forced k U *∏ j∈i.erase k, (P.activities.K j U:ℂ)):= by
  induction i using Finset.induction_on with
  | empty=> simp [Poly.one_part,mute,quiet]
  | insert a b h ih =>
    rw [prod_insert h, Finset.prod_insert h,Finset.sum_insert h]; constructor
    · simp only [s_extra]; rw [show (followed _ _ _ _ _).part (quiet _)=_ from (show (followed P c B U a).part _=↑(P.activities.K a U) from (dues c _ _).1),ih.1,Complex.ofReal_mul]
    rw [show (followed P c B U a* _ |>.part (slot c))=_ from mark_one (U:=∏ i∈b,followed P c B U i) (i:=c) (F:=↑(P.activities.K a U)) (g:=B.forced a U), ih.1,ih.2, Finset.erase_insert h,Complex.ofReal_prod,mul_sum]
    rw [add_comm]; congr 1; refine sum_congr rfl fun j hj=> ?_
    rw [Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hj h).symm,Finset.prod_insert (notMem_mono (erase_subset ..) h)]; ring
lemma tag_rebate (B : Coefficient W n) (c : V) (P : Rep G n) (U : Config G n) (i : Finset ℕ):
    (peeled (identifier P) (followed P c B U) (flags P.p.threshold U) i).part (quiet _)= ((P.activities.gasOccurrence P.p i U:ℝ):ℂ) ∧
    (peeled (identifier P) (followed P c B U) (flags P.p.threshold U) i).part (slot c)=B.marked P i U:= by
  by_cases ht : P.activities.admissible P.p U i
  · rw [Activities.gasOccurrence,Coefficient.marked,peeled, if_pos ht, if_pos ht, if_pos (show ripe (identifier P) i _ from ht)]; exact tags_prod ..
  rw [Activities.gasOccurrence,Coefficient.marked,peeled, if_neg ht, if_neg ht, if_neg (show ¬ ripe (identifier P) i _ from ht)]; simp

lemma strong_packet (P : Rep G n) (h : P.activities.Valid P.p δ η) (K : Coefficient W n) (i : V) (U : Config G n)
    (ht : K.remBound 0 P e z) :
    Summable (fun j=>P.activities.K j U)∧ Summable (fun j=> K.forced j U)∧ Summable (followed P i K U) ∧ Summable (peeled (identifier P) (followed P i K U) (flags P.p.threshold U)):= by
  obtain ⟨p,hp,hB⟩:= Activities.K_total h.boundK
  obtain ⟨a,b,hA,-,-,hE,-,u,hQ,hU⟩:=ht
  have hv : Summable u:= hQ.2.1.of_nonneg_of_le (fun i=>(hU i).1) (fun j=> P.p.loMass _ _ (hU j|>.1))
  let F:=followed P i K U
  let C:= identifier P
  let m (_:V):ℝ:= 1
  have hp' (j): Poly.price m (F j) ≤ p j+u j:= by
    dsimp only [F,followed]; apply (Poly.addition (w:=m) (fun i=>zero_lt_one) ..).trans
    rw [Poly.solo,Poly.solo,Complex.norm_real]; simp only [m,Poly.toll, Finset.prod_const_one,one_mul];exact add_le_add (hB j|>.2 U) (hU j|>.2 U)
  have hs (t : Finset ℕ): Poly.price m (peeled C F (flags P.p.threshold U) t) ≤ ∏ i∈t,(p i+u i):= by
    unfold peeled; split
    · apply (Poly.multiple (fun i=>zero_lt_one) ..).trans; exact Finset.prod_le_prod (fun i _=>Poly.nonnegative (fun i=>zero_lt_one) _) (fun i _=>hp' _)
    rw [Poly.zero_price]; exact Finset.prod_nonneg fun i _=> add_nonneg (hB i|>.1) (hU i|>.1)
  have hH i:0≤p i+u i:= add_nonneg (hB i|>.1) (hU i|>.1)
  exact ⟨hp.of_norm_bounded (fun i=> hB i|>.2 U), hv.of_norm_bounded (fun i=> hU i|>.2 U),
    (Poly.budgeted (fun i=>zero_lt_one) (hp.add hv) hp').1,(Poly.budgeted (fun i=>zero_lt_one) (summable_finsetProd_of_summable_nonneg hH (hp.add hv)) hs).1⟩

lemma clipped_single (P : Rep G n) (h : P.activities.Valid P.p δ η) (K : Coefficient W n) (i : V) (U : Config G n) (R : Neat n→Baler.Burst G n P.p.threshold) (hv : IsoVac P R η)
    (ht : K.remBound 0 P e z) :
    let S:=flags P.p.threshold U
    let c (B : Neat n): veil V:= Poly.send (quiet _) ((R B).value U:ℂ)+Poly.send (slot i) (Baler.piece (identifier P) (fun j=> K.forced j U) B)
    let C:=∑ i : Finset (Neat n),peeled id c S i
    C.part (quiet _)=(P.activities.gas P.p U:ℂ)∧ C.part (slot i)= ∑' m,K.marked P m U:= by
  intro S c C
  let B:= followed P i K U
  let Y:=identifier P
  let Z:=fun j=>K.forced j U
  obtain ⟨hs,hZ,hp,hf⟩:= strong_packet P h K i U ht
  have hI {R : Type} [AddCommGroup R] [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R] (f : ℕ→R) (B : Neat n) (h : Summable f) : Summable fun i=> if Y i=B then f i else 0 := by refine (h.indicator (s:={x|Y x=B})).congr fun x=> ?_; by_cases h:Y x=B <;> simp [Set.indicator,h]
  have ha : c=piece Y B := by
    ext1 b
    have hg:= hI Z b hZ; let T m:= P.activities.K m U; have heT:= hI T b hs
    have hj : (R b).value U = piece Y T b:= hv.value b U
    unfold piece at hj; apply Poly.ext; intro v
    unfold c piece; rw [Poly.share (hI B b hp), Poly.part_plus,hj,Poly.part_send,Poly.part_send];by_cases h₁ : v=quiet V
    · rw [if_pos h₁,if_neg (fun H=>mute i (H.symm.trans h₁)),add_zero,Complex.ofReal_tsum]
      refine tsum_congr fun j=>?_ ;by_cases h:Y j=b
      · simp [B, followed,h,h₁,Poly.part_send,( mute i).symm,T]
      rw [if_neg h,if_neg h,Poly.part_nil]; simp
    rw [if_neg h₁,zero_add]; by_cases h₂:v=slot i
    · rw [if_pos h₂]; refine tsum_congr fun j=>?_;rw [h₂];by_cases he:identifier P j=b<;>simp [Y,he,B,followed,mute]
    rw [if_neg h₂]; symm; refine (tsum_congr (g:=fun _=>0) ?_).trans tsum_zero;intro j;by_cases hg:Y j=b<;>simp [B,followed,hg,Poly.part_send,h₁,h₂]
  change (∑ i : Finset (Neat n),peeled id c S i).part _=_ ∧ _
  rw [ha, ← Baler.all Y B S hf (hI _ · hp), Poly.share hf]; constructor
  · rw [Activities.gas, Complex.ofReal_tsum]; apply tsum_congr; intro i; exact (tag_rebate ..).1
  change (∑ i, peeled id c S i).part _= _
  rw [ha, ← Baler.all Y B S hf (hI _ · hp), Poly.share hf]; exact tsum_congr fun _=> (tag_rebate ..).2
end YM.Next.Rank.Edition
