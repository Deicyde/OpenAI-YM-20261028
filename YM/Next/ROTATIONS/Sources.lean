import YM.Next.ROTATIONS.Axis
import YM.Ward.Genuine

/-!
# Character projection with off-centre spectators. Includes complex-conjugate convention

Orbit projections in raw alphabet distinct words vs actual labels in quotient. Equations
use only guarded readout. -/
noncomputable section
namespace YM.Outer
open Set Filter Function MeasureTheory Measure Table OS Row Word Boundary Complex
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal ENNReal ComplexConjugate
variable {G : Gauge} {L : Register G} {S : Table L}

lemma ink_join (s t : Signed) (A : Weight L) : ink s (ink t A)=ink (s*t) A := by
  induction A using Finsupp.induction_linear with
  | zero => simp
  | add _ _ h k => simp [h,k]
  | single i z => rw [ink_single,ink_single,ink_single]; congr 1; exact Subtype.ext (act_comp s t _)
lemma ink_one (A : Weight L) : ink 1 A=A := by
  induction A using Finsupp.induction_linear with
  | zero => simp
  | add _ _ h k => simp [h,k]
  | single i z => rw [ink_single]; congr 1; exact Subtype.ext (act_id _)
lemma mirror_k (i j : Axis) (A : Weight L) : ink (Signed.mirror i) (ink (Signed.mirror j) A)=ink (Signed.mirror j) (ink (Signed.mirror i) A) := by
  rw [ink_join,ink_join, show Signed.mirror i*Signed.mirror j=Signed.mirror j*Signed.mirror i from ?_]
  refine Signed.ext rfl ?_
  ext1 k
  simp [Signed.mirror,Bool.xor_comm]; rfl
lemma mirror_square (i : Axis) (A : Weight L) : ink (Signed.mirror i) (ink (Signed.mirror i) A)= A := by
  rw [ink_join, show Signed.mirror i*Signed.mirror i=1 from by
    conv_lhs => lhs; rw [← Signed.mirror_inv i]
    exact inv_mul_cancel _, ink_one]

def chooseSign (i : Axis) (b : Bool) (A : Weight L) := (2:ℂ)⁻¹ • (A+signValue b • ink (Signed.mirror i) A)
lemma chosen (i : Axis) (b : Bool) (A : Weight L) : Own (chooseSign i b A) i b := by
  unfold Own chooseSign
  rw [map_smul,map_add,map_smul,mirror_square,smul_comm,smul_add (signValue b),smul_smul,sign_sq,one_smul,add_comm]
lemma stable {j : Axis} (i b c) (A : Weight L) (h : Own A j c) : Own (chooseSign i b A) j c := by
  unfold Own chooseSign
  rw [map_smul,map_add,h,map_smul,mirror_k,h,map_smul,smul_comm (signValue c),smul_add (signValue c),smul_comm (signValue b)]
lemma joins (i : Axis) (A : Weight L) : chooseSign i true A+chooseSign i false A=A := by
  rw [chooseSign,chooseSign, ← smul_add]
  simp only [signValue, Bool.false_eq_true, ↓reduceIte, one_smul,neg_smul]
  rw [show (A + -ink (Signed.mirror i) A) + (A + ink (Signed.mirror i) A)=A+A by abel,← two_smul ℂ]; exact inv_smul_smul₀ (by norm_num) _

lemma pressed_ink (i a : Axis) (A : Weight L) (H : Pressed i A) : Pressed i (ink (Signed.mirror a) A) := by
  intro j hj p hp
  obtain ⟨v,rfl⟩ := (rotate (Signed.mirror a)).surjective j
  have hv : v∈A.support := by
    simp only [Finsupp.mem_support_iff] at *
    unfold ink at hj; simpa using hj
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
  change Ortho.move (Signed.reflect a) w.1 i=0
  rw [Signed.mirrored, H v hv w hw]; split_ifs <;> simp
lemma pressed_choose (i a : Axis) (A : Weight L) (h : Pressed i A) (b) : Pressed i (chooseSign a b A) := by
  classical
  intro j hj
  rcases Finset.mem_union.mp (Finsupp.support_add (Finsupp.support_smul hj)) with g|g
  · exact h j g
  exact pressed_ink i a A h j (Finsupp.support_smul g)

abbrev nice (w : Core L) : Weight L := Finsupp.single w 1
lemma reads_nice (S : Table L) (v w : Core L) (y : E4) : readsCluster S (nice v) (nice w) y=bare S v w y := by simp [readsCluster,nice]

def piece {d : ℕ} (v : L.Ref d) : Core L := ⟨[(0,⟨d,v⟩)],locations.mpr (by simp)⟩
abbrev pick {d : ℕ} (b : S.Field d) := nice (piece (S.representative _ b))

lemma raw_read (H : S.Hierarchy) {d : ℕ} (p q : L.Ref d) (z : ℂ) (he : S.project _ p=z • S.project _ q)
    (x : E4) (v : L.Word) :
    let F (p : L.Ref d) := open scoped Classical in if distinct ((x,⟨d,p⟩)::v) then S.expect ((x,⟨d,p⟩)::v) else 0
    F p=z*F q := by
  classical
  intro F
  have hu : distinct ((x,⟨d,p⟩)::v) ↔ distinct ((x,⟨d,q⟩)::v) := by rw [locations,locations]; rfl
  unfold F
  by_cases h : distinct ((x,⟨d,q⟩)::v)
  swap; · rw [if_neg (mt hu.mp h),if_neg h,mul_zero]
  rw [if_pos (hu.2 h),if_pos h,Ward.exact_table (hu.2 h) H, Ward.exact_table h H]
  let k := fun i => S.classTokens (tokens v i)
  let Q := Fin.cons (α:=fun _ => S.Tag) (⟨d,S.project d q⟩) k
  let y := Points.cons x (positions v)
  let b (u : S.Field d) := Fin.cons (α:=fun _ => S.Tag) ⟨d,u⟩ k
  have heq u : update Q 0 (⟨d,u⟩:S.Tag)= b u := by
    ext1 i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [Q,b]
  change Ward.disc (b (S.project d p)) y=z*Ward.disc (b (S.project d q)) y
  rw [← heq,← heq,← Ward.takes,← Ward.takes,he,map_smul]; rfl

lemma swapped_cons (H : S.Hierarchy) (x : L.Plant) (w : L.Word) :
    let K (p : L.Word) := open scoped Classical in if distinct p then S.expect p else 0
    K (w++[x])=K (x::w) := by
  classical
  let h : (x::w).Perm (w++[x]) := @List.perm_append_comm _ [x] w
  intro K; unfold K
  by_cases hp : distinct (x::w)
  · rw [if_pos ((locations).mpr ((h.map Prod.fst).nodup (locations.mp hp))), if_pos hp]; exact Table.order S H.laws.toSymmetric hp h
  rw [if_neg (fun hz => hp (locations.mpr ((h.symm.map Prod.fst).nodup (locations.mp hz)))),if_neg hp]

def equalRead (S : Table L) (A B : Weight L) := (∀ C y, readsCluster S C A y=readsCluster S C B y) ∧ ∀ C y, readsCluster S A C y=readsCluster S B C y
lemma raw_value (H : S.Hierarchy) {d} (p q : L.Ref d) (z : ℂ) (he : S.project _ p=z • S.project _ q) :
    equalRead S (nice (piece p)) (z • nice (piece q)) := by
  classical
  have hv (u : L.Ref d) w y : bare S w (piece u) y= if distinct ((y,⟨d,u⟩)::conjugate w.val.reverse) then S.expect ((y,⟨d,u⟩)::conjugate w.val.reverse) else 0 := by
    unfold bare piece carry
    simp only [List.map_cons,List.map_nil,zero_add]; exact swapped_cons H _ _
  have hl (u : L.Ref d) w y : bare S (piece u) w y= if distinct ((0,⟨d,star u⟩)::carry w.val y) then S.expect ((0,⟨d,star u⟩)::carry w.val y) else 0 := by rfl
  constructor
  · intro C y; rw [reads_smul_r]
    have hr w : bare S w (piece p) y=z*bare S w (piece q) y := by
      rw [hv, hv]; exact raw_read H p q z he y _
    unfold nice readsCluster
    simp [hr, Finsupp.sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by ring
  intro C y; rw [reads_smul_l]
  have h : S.project _ (star p)=star z • S.project _ (star q) := by rw [← S.conj_project H.spin,he,map_smulₛₗ,S.conj_project];rfl
  have hr w : bare S (piece p) w y=star z*bare S (piece q) w y := by
    rw [hl,hl]; exact raw_read H _ _ _ h _ _
  unfold nice readsCluster
  simp [hr,Finsupp.sum,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => by ring
lemma equalRead.trans {A B C : Weight L} (h : equalRead S A B) (l : equalRead S B C) : equalRead S A C :=
    ⟨fun i j => (h.1 i j).trans (l.1 i j),fun i j => (h.2 i j).trans (l.2 i j)⟩
lemma equalRead.scale {A B : Weight L} (h : equalRead S A B) (z : ℂ) : equalRead S (z • A) (z • B) := by
  constructor
  · intro v i; rw [reads_smul_r,reads_smul_r,h.1]
  intro v i; rw [reads_smul_l,reads_smul_l,h.2]
lemma equalRead.add {A B C D : Weight L} (h : equalRead S A B) (l : equalRead S C D) : equalRead S (A+C) (B+D) := by
  constructor
  · intro v i; rw [reads_add_r,reads_add_r,h.1,l.1]
  intro v i; rw [reads_add_l,reads_add_l,h.2,l.2]
lemma equalRead.transport (H : S.Hierarchy) {A B : Weight L} (h : equalRead S A B) (s : Signed) :
    equalRead S (ink s A) (ink s B) := by
  constructor <;> intro v i <;> obtain ⟨y,rfl⟩ := (ink s).surjective v <;> obtain ⟨x,rfl⟩ := s.ortho.motion.surjective i
  · rw [Ortho.motion_at,reads_turn S H.spin,reads_turn S H.spin,h.1]
  rw [Ortho.motion_at,reads_turn S H.spin,reads_turn S H.spin,h.2]

lemma signed_value (H : S.Hierarchy) {d} (b : S.Field d) (s : Signed) (e : ℂ) (v : S.Field d)
    (h : S.mirror H.spin _ s b=e • v) : equalRead S (ink s (pick b)) (e • pick v) := by
  unfold pick nice; rw [ink_single]
  let u := S.representative d b
  rw [show rotate s (piece (S.representative d b))=piece (L.mirrorGroup d s u) by
    apply Subtype.ext
    change [(Ortho.move s.ortho 0,L.move s _)] = _
    rw [← Ortho.motion_at,map_zero];rfl]
  refine raw_value H _ _ _ ?_
  rw [← S.mirror_project,S.rep]; exact h.trans (by rw [S.rep])

/-- Upper singleton stress/fixed field probe, included in all axis matrices in a family. -/
def Enters (H : S.Hierarchy) (e : Axis → Bool) {d : ℕ} (v : S.Field d) := ∀ i,
    S.mirror H.spin d (Signed.mirror i) v=signValue (e i) • v
lemma enters_weights (H : S.Hierarchy) (e : Axis → Bool) {d} (v : S.Field d) (hp : Enters H e v) :
    ∃ A : Weight L, equalRead S A (pick v) ∧ (∀ i,Own A i (e i)) ∧ ∀ i,Pressed i A := by
  classical
  have he (s : Finset Axis) : ∃ A : Weight L,equalRead S A (pick v) ∧ (∀ i∈s,Own A i (e i)) ∧ ∀ i, Pressed i A := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨pick v,⟨fun _ _ => rfl,fun _ _ => rfl⟩,by simp,fun a i hi p hj => ?_⟩
      unfold pick nice at hi; simp only [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hi
      subst i; rw [List.mem_singleton.mp hj]; rfl
    | insert i s hi ih =>
      obtain ⟨A,h,hb,hA⟩ := ih
      refine ⟨chooseSign i (e i) A, ?_, fun j he => ?_, fun j => pressed_choose j i A (hA j) _⟩
      · have ht := (h.transport H (Signed.mirror i)).trans (signed_value H v (Signed.mirror i) _ _ (hp i))
        have hl := (h.add (ht.scale (signValue (e i)))).scale ((2:ℂ)⁻¹)
        rw [smul_smul (signValue (e i)),sign_sq,one_smul,← two_smul ℂ,inv_smul_smul₀ (by norm_num)] at hl
        exact hl
      rcases Finset.mem_insert.mp he with rfl|h
      · exact chosen ..
      exact stable i (e i) (e j) A (hb j h)
  obtain ⟨A,h,hb,hA⟩ := he Finset.univ
  exact ⟨A,h,fun i => hb i (Finset.mem_univ i),hA⟩

lemma pair_reply (H : S.Hierarchy) {d l} (A B : Weight L) (v : S.Field d) (w : S.Field l)
    (hp : equalRead S A (pick v)) (hr : equalRead S B (pick w)) (y : E4) (hy : y≠0) :
    readsCluster S B A y= Ward.pair ⟨d,v⟩ ⟨l,S.conj H.spin _ w⟩ y := by
  rw [hp.1,hr.2]; unfold pick; rw [reads_nice]
  let a : L.Plant := (0,⟨l,star (S.representative l w)⟩)
  let b : L.Plant := (y,⟨d,S.representative d v⟩)
  unfold bare; simp only [piece, carry,List.map_nil,List.map_cons,List.reverse_singleton,Word.conjugate,List.cons_append,List.nil_append,zero_add]; rw [if_pos]
  swap; · rw [locations]; simp [Ne.symm hy]
  change S.expect [a,b]=_
  rw [Table.order S H.laws.toSymmetric (w:=[a,b]) (v:=[b,a]) (locations.mpr (by simp [b,a,hy])) (List.Perm.swap ..),
    show S.expect [b,a]=_ from Ward.scan H b a (show _ from hy)]
  simp only [b,a,Table.classTokens,← S.conj_project H.spin,S.rep,sub_zero]

end YM.Outer
