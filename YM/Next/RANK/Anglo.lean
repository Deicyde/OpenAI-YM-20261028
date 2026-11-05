import YM.Next.RANK.Earth

/-!
# Translation of path/action data

Use every shift whose ancestor mask was used. Measures not involved.
Positions work by affine plus signed rotations in channel convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker PathData
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}
variable {R : PathData G} {j k : ℕ} {p q : BudgetPoint} {c : Clip}

lemma s_translation (x : Site n) (U : Config G n) : expandAt (0:Site n) (pull 1 x U) = expandAt x U := by rw [expandAt_pull,pull_id]; simp [affine]
lemma keeper_shift (t : ℝ) (x : Site n) (U : Config G n) : kept c t 0 (pull 1 x U) ↔ kept c t x U := by
  let f : Equiv.Perm (Face (Per n)):=Equiv.ofBijective (Face.send 1 x) ⟨Face.injective_send .., Finite.injective_iff_surjective.mp (Face.injective_send ..)⟩
  have he (p : Face (Per n)) : G.chord (faceValue (pull 1 x U) p)= G.chord (faceValue U (f p)):= Face.send_price U p 1 x G.chord G.chord_inv fun k g=> G.chord_conj g k
  have hp (p : Face (Per n)) : (f p).1=p.1+x:= by
    change Face.lower p 1 x=p.1+x; simp [Face.lower,atFace,posDir,affine]
  have ht (p : Face (Per n)) : separation x (f p).1=separation 0 p.1 := by rw [hp]; simpa [affine] using s_sep 1 x 0 p.1
  constructor
  · intro hh i; obtain ⟨p,hp⟩:= f.surjective i; rw [←hp,←he p,ht]; exact hh _
  intro hh i; rw [he,← ht]; exact hh _
lemma l_shift (w : Slot) (x : Site n) (U : Config G n) : w.atSite (pull 1 x U) 0=w.atSite U x:= by rw [Slot.atSite,s_translation];rfl
lemma ell_shift (c : PlaqAxes) (x : Site n) (U : Config G n) : R.ell (pull 1 x U) (0,c)= R.ell U (x,c) := tsum_congr fun i=> by
    simp only [ellTerms,l_shift]
lemma lattice (f : Atom G j) (x : Site n) : swath 1 x (f.footprint (0:Site n))=f.footprint x := by unfold Thirst.swath Atom.footprint; rw [image_image]; apply image_congr; intro i _; simp [affine]
lemma atoms (k : ℕ) (i : Atom G k) (x : Site n) (p : BudgetPoint) (U : Config G n) : i.placed p (pull 1 x U) 0=i.placed p U x:= by
  have H : Healthy p.threshold (i.footprint (0:Site n)) (pull 1 x U) ↔ Healthy p.threshold (i.footprint x) U:= by rw [s_healthy,lattice i x]
  unfold Atom.placed; by_cases hh : Healthy p.threshold (i.footprint x) U
  · simp only [masked_eq _ _ _ _ (H.2 hh),masked_eq _ _ _ _ hh,Atom.unmasked, Slot.atSite,s_translation]
  rw [masked_ne _ _ _ _ (mt H.1 hh),masked_ne _ _ _ _ hh]

-- algebraic base reorganizing. canonical zero row all later. E part separately.

def lock (c : Clip) (a b : ℝ) (U : Config G n) : Prop := kept c a 0 U ∧ ¬ kept c b 0 U

def dam (c : Clip) (a b : ℝ) (U : Config G n) : ℝ:= if lock c a b U then 1 else 0
lemma dam_shift (P : PathData G) (c) (U : Config G n) (p q : BudgetPoint) (h : q.threshold ≤ p.threshold) (f : Face (Per n)) :
    P.baseTerm c p U f - P.baseTerm c q U f = Delta c p.threshold q.threshold f U + dam c p.threshold q.threshold (pull 1 f.1 U) * ‖P.ell (pull 1 f.1 U) (0,f.2)‖^2/2 := by
  rcases f with ⟨f,x⟩
  unfold baseTerm Delta dam lock; simp only [ell_shift,keeper_shift]
  have hh (hx : kept c q.threshold f U) : kept c p.threshold f U:=fun p' => (hx p').trans (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le)
  by_cases ht : kept c q.threshold f U
  · simp [ht,hh ht]
  by_cases hf : kept c p.threshold f U
  · simp only [hf,ht,↓reduceIte,true_and,not_false_eq_true]; ring
  simp [ht,hf]

-- whole signed/translated average

def rag (f : Config G n→ℝ) (U : Config G n) : ℝ:= (Fintype.card Signed : ℝ)⁻¹ * ∑ s : Signed, ∑ i : Site n, f (pull s i U)
lemma rag_add (f g : Config G n→ℝ) (U) : rag (fun x=> f x+g x) U=rag f U+rag g U := by simp only [rag,sum_add_distrib,mul_add]

lemma spin_shift (X : Config G n → ℝ) (U) (s : Signed) :
     ∑ i : Site n,X (pull 1 i (pull s 0 U))= ∑ i : Site n, X (pull s i U) := by
  refine Fintype.sum_equiv (sends s 0) _ _ fun i=>?_ ; rw [pull_pull,mul_one];rfl

def baseGift (P : PathData G) (p q : BudgetPoint) (C : Clip) (U : Config G n) :=
    ∑ x : PlaqAxes, dam C p.threshold q.threshold U * ‖P.ell U (0,x)‖^2/2

def atomGift (F : ℕ → Atom G j) (p q : BudgetPoint) (U : Config G n) := atomSeries F p U 0-atomSeries F q U 0

lemma law_shift (P : PathData G) (p q : BudgetPoint) (C : Clip) (β : ℝ) (h : q.threshold ≤ p.threshold) (U : Config G n) :
    P.inChannels C p β U-P.inChannels C q β U=β*(Shift C p.threshold q.threshold U+ rag (baseGift P p q C) U +
        rag (atomGift P.cubic p q) U + rag (atomGift P.quartic p q) U) + rag (atomGift P.loop p q) U:= by
  let S (s : Signed) := pull s 0 U
  let X := Shift C p.threshold q.threshold U
  have he (j) (f : ℕ→Atom G j) (p : BudgetPoint) (x : Site n) (U : Config G n) : atomSeries f p U x=atomSeries f p (pull 1 x U) 0 := tsum_congr fun i=>(atoms ..).symm
  let v (j : ℕ) (f : ℕ → Atom G j) (s : Signed) := ∑ x : Site n, atomGift f p q (pull s x U)
  let D (s : Signed) :=∑ x : Site n, baseGift P p q C (pull s x U)
  have hh (j) (f : ℕ→Atom G j) (s) (V : Config G n) (hV : V=S s) :
      (∑ i : Site n, atomSeries f p V i)-(∑ i : Site n, atomSeries f q V i) = v j f s := by
    subst V; rw [← sum_sub_distrib]; refine Eq.trans ?_ (spin_shift _ _ s)
    -- specify
    apply sum_congr rfl; intro i _; exact congr_arg₂ _ (he j f p i (S s)) (he j f q i (S s))
  have hp (s) : P.principal C p β (S s) - P.principal C q β (S s) =
      β*(X + D s + v _ P.cubic s+v _ P.quartic s)+v _ P.loop s := by
    let R:= S s
    have ht : (∑ f, P.baseTerm C p R f) - (∑ f,P.baseTerm C q R f)= X+D s := by
      rw [← sum_sub_distrib]; simp_rw [dam_shift _ _ _ _ _ h,sum_add_distrib]
      unfold X D; rw [shift s 0 U]; apply congr_arg (Shift C _ _ (S s) + ·)
      rw [Fintype.sum_prod_type]; exact spin_shift (baseGift P p q C) U s
    unfold PathData.principal; simp_rw [sum_add_distrib, ← hh _ P.cubic _ (S s) rfl, ← hh _ P.quartic _ (S s) rfl, ← hh _ P.loop _ (S s) rfl, ← ht]; ring
  unfold inChannels; rw [← mul_sub, ← sum_sub_distrib]; change (↑(Fintype.card Signed):ℝ)⁻¹ * (∑ s,(P.principal _ _ _ (S s)-P.principal _ _ _ (S s)))=_
  simp_rw [hp,sum_add_distrib,← mul_sum]; rw [sum_add_distrib,sum_add_distrib,sum_add_distrib,sum_const,nsmul_eq_mul]; dsimp only [X,v,D,rag]; rw [Finset.card_univ]; field_simp
end YM.Next.Rank.Alarm
