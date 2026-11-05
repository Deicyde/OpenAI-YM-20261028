import YM.Next.RANK.River

/-!
# Uncorrected polymer with its restored low sectors

`higher` assumption later on this same stamp may specify only moments of higher
TAG degree of the unnormalized density. Here show actual equality on singles.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source Labels
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {Q : Rep G n} {V ι κ : Type} [DecidableEq V] [Fintype V]
variable {d : ℕ} {W : Frame G d} {ζ : V→Site n} {σ α δ η Λ e z : ℝ} {τ : ℝ}
variable {F : Coefficient W n} {P : BudgetPoint} {H : Hol G}

section
-- Projection along one signed sector
variable (b : Prop) (r : ℂ) (v : V)

-- pull operator applied with cardinal-one scale
structure Reps (A P : veil V) : Prop where
  vac : P.part (quiet _)=dot b (A.part (quiet _))
  single : P.part (slot v)=dot b (r*A.part (slot v))

lemma same_mul {A B P Q : veil V} (h : Reps b r v A B) (hp : Reps b r v P Q) : Reps b r v (A*P) (B*Q):= by
  refine ⟨by rw [s_extra,s_extra,h.vac,hp.vac,dot_mul],?_⟩
  rw [mul_solo,mul_solo,h.single,h.vac,hp.vac,hp.single,← dot_mul,← dot_mul,← dot_add]; exact congr_arg _ (by ring)
lemma same_add {A B P Q : veil V} (h : Reps b r v A B) (hp : Reps b r v P Q) : Reps b r v (A+P) (B+Q):= by
  constructor
  · rw [Poly.part_plus,Poly.part_plus,h.vac,hp.vac,dot_add]
  rw [Poly.part_plus,Poly.part_plus,h.single,hp.single,mul_add,dot_add]
lemma Reps.sum (X : Finset κ) {f g : κ→veil V} (h : ∀ i∈X,Reps b r v (f i) (g i)) : Reps b r v (∑ i∈X,f i) (∑ i∈X,g i) := by
  classical
  induction X using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; constructor <;> simp [dot_zero]
  | insert i X hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact same_add b r v (h i (mem_insert_self ..)) (ih fun i hu=>h i (mem_insert_of_mem hu))
lemma Reps.prod (X : Finset κ) {f g : κ→veil V} (h : ∀ i∈X,Reps b r v (f i) (g i)) : Reps b r v (∏ i∈X,f i) (∏ i∈X,g i):= by
  classical
  induction X using Finset.induction_on with
  | empty=> simp only [prod_empty]; constructor <;> simp only [Poly.one_part, show slot v ≠ quiet _ from mute v, if_pos]
            · simp [dot]
            exact (by simp [dot])
  | insert i X hi IH=> rw [prod_insert hi,prod_insert hi]; exact same_mul b r v (h i (mem_insert_self ..)) (IH fun i hu=> h i (mem_insert_of_mem hu))
lemma Reps.extends {A B P : veil V} (h : Reps b r v A B) (hp : Dual v B P) : Reps b r v A P:= ⟨hp.base.trans h.vac,hp.tag.trans h.single⟩

lemma perm_covered (x : Finset (Neat n)) (S : Support n) (s : Signed) (p : Site n) :
    ripe id (x.map (sent s p).toEmbedding) (swath s p S) ↔ ripe id x S := by
  have hx : (x.map (sent s p).toEmbedding).biUnion (fun i=>i.val.2)= swath s p (x.biUnion (fun i=> i.val.2)) := by
    induction x using Finset.induction_on with
    | empty => simp [swath]
    | @insert i x hi IH=> rw [map_insert, biUnion_insert,biUnion_insert,IH];simp only [Equiv.coe_toEmbedding,sent_one,swath,image_union]
  constructor
  · rintro ⟨h,hf⟩; refine ⟨fun i hi j hj hh=> ?_,?_⟩
    · have hz:= h (mem_map.mpr (show _ from ⟨_,hi,rfl⟩)) (mem_map.mpr ⟨_,hj,rfl⟩) (show sent s p i ≠ sent s p j from (sent s p).injective.ne hh)
      change Disjoint (sent s p i).val.1 (sent s p j).val.1 at hz; rw [sent_one,sent_one] at hz; exact Finset.disjoint_image (sends s p).injective |>.1 hz
    exact Finset.image_inj (sends s p).injective |>.1 (hx.symm.trans hf)
  rintro ⟨h,hp⟩; refine ⟨fun i hi j hj hh=> ?_,hx.trans (congr_arg (swath s p) hp)⟩
  obtain ⟨c,hc,rfl⟩:=mem_map.mp hi; obtain ⟨w,hw,rfl⟩:=mem_map.mp hj
  change Disjoint (sent s p c).val.1 (sent s p w).val.1; rw [sent_one,sent_one]; exact (Finset.disjoint_image (sends s p).injective).2 (h hc hw fun H=> hh (by rw [H]))

lemma transDu (f g : Neat n→veil V) (U : Config G n) (s : Signed) (p : Site n) (t : ℝ)
    (hh : ∀ i,Reps b r v (f i) (g (sent s p i))) : Reps b r v (∑ i : Finset (Neat n), peeled id f (flags t (pull s p U)) i)
      (∑ i : Finset (Neat n),peeled id g (flags t U) i) := by
  let T:= sent s p
  nth_rw 1 [← Fintype.sum_equiv T.finsetCongr (fun i=> peeled id g (flags t U) (T.finsetCongr i)) (fun i=> peeled id g (flags t U) i) (fun _=> rfl)]
  apply Reps.sum b r v; intro i _; unfold peeled; by_cases h:ripe id i (flags t (pull s p U))
  · rw [if_pos h,if_pos (show ripe id (T.finsetCongr i) (flags t U) from (s_flags s p t U) ▸ (perm_covered i _ s p).2 h)]
    have hy := Reps.prod b r v (κ:=Neat n) i (fun i _=> hh i)
    rw [show (∏ i∈ T.finsetCongr i,g i)=_ from prod_map i T.toEmbedding g]; exact hy
  have hz: ¬ ripe id (T.finsetCongr i) (flags t U):=fun hi=> h ((perm_covered i _ s p).1 (by rw [s_flags];exact hi))
  rw [if_neg h,if_neg hz]; constructor <;> simp [dot_zero]
end

-- bare footprints (in addition to possible later ingredients)

variable (ζ : V→Site n)
variable (B : Neat n→Burst G n Q.p.threshold)
variable (K : V→Coefficient W n) (β : ℂ) (hd : ∀ i,(K i).Format 0 H Q) (s : V→Signed) (x : V→Prop)

abbrev Elders (n : Side) (V : Type) := Neat n ⊕ (V × Rootage n)

def bits (j : V) := chip (s j) (hd j) (x j) β (ζ:=ζ) j

def elder (i : Elders n V) := Sum.elim (enroll ζ ∘ B) (fun p => bits ζ K β hd s x p.1 p.2) i

variable {ζ}

lemma simpleTurns (h : IsoVac Q B η) (a : Signed) (x : Site n) (y : Neat n) (U : Config G n) : (B (sent a x y)).value U=(B y).value (pull a x U):= by
  obtain ⟨P,ha,hp⟩:=h.symmetry a x
  have he : P=sent a x:= by ext1 i; simpa only [h.points] using (ha i)
  subst P; exact hp ..

variable [Fintype ι]
variable (A : ι→Lifted G ζ Q.p.threshold)


def gamut (U : Config G n) (i : Neat n):veil V := ∑ j : Elders n V⊕ι,
    let p:=Sum.elim (elder ζ B K β hd s x) A j
    if attached p=i then p.amount U else 0
lemma comptable (h : IsoVac Q B η) (he : ∀ i,2 ≤ (A i).fires.val.card) (v : V) (i : Neat n) (U : Config G n) :
    let y:= ζ v; let V':= pull (s v) y U; let F:=K v
    let h₁ : veil V:= Poly.send (quiet _) ((B i).value V':ℝ) + Poly.send (slot v) (foam F Q i V')
    Reps (x v) β v h₁ (gamut B K β hd s x A U (sent (s v) y i)):= by
  intro y V' F h₁
  let g:=sent (s v) y i; let w:=Sum.elim (elder ζ B K β hd s x) A
  let G' t:veil V:= if attached (w t)=g then (w t).amount U else 0
  let M : veil V:= Poly.send (slot v) (dot (x v) (β*foam F Q i V'))
  let Y' : Elders n V⊕ι → veil V:= Sum.elim (Sum.elim (fun j=> if j=g then Poly.send (quiet _) ((B j).value U:ℂ) else 0)
      (fun j=> if j.1=v∧j.2.val=i then M else 0)) (fun _=>0)
  have ht : ∀ j : Elders n V⊕ι,Dual v (Y' j) (G' j):= by
    intro j
    dsimp only [G']; rcases j with (j|j)|j
    · change Dual _ (if j=g then (enroll ζ (B j)).amount U else 0) (if attached (enroll ζ (B j))=g then _ else _)
      rw [show attached (enroll ζ (B j)) = j from h.points j]; exact ⟨rfl,rfl⟩
    · obtain ⟨a,l⟩:= j
      by_cases ha : a=v
      · subst a; change Dual _ (if _ then M else 0) (if attached (bits ζ K β hd s x v l)=g then (bits ζ K β hd s x v l).amount U else 0)
        rw [show attached (bits ζ K β hd s x v l)=sent (s v) y l.val from seal_chip ..]; by_cases hz:l.val=i
        · rw [if_pos (And.intro rfl hz), if_pos (show sent (s v) y l.val=g from congr_arg (sent (s v) y) hz)]
          rw [show M=(bits ζ K β hd s x v l).amount U by rw [bits, Lifted.amount,chip]; dsimp only; rw [hz]]; exact ⟨rfl,rfl⟩
        rw [if_neg (fun ⟨_,he⟩=> hz he),if_neg (fun hh=> hz ((sent ..).injective hh))]; exact ⟨rfl,rfl⟩
      rw [show Y' (Sum.inl (Sum.inr (a,l)))=0 from if_neg (fun p=>ha p.1)]
      split
      · constructor
        · exact (Poly.part_send ..).trans (if_neg (mute a).symm)
        exact faint _ _ _ (Ne.symm ha)
      exact ⟨rfl,rfl⟩
    change Dual _ (0 : veil _) (if _ then (A j).amount _ else _); split
    · exact ⟨(Dual.zero _ (he j) _ (a:=v)).base.symm,(Dual.zero _ (he j) _ (a:=v)).tag.symm⟩
    exact ⟨rfl,rfl⟩
  apply Reps.extends (x v) β v _ (Dual.sum univ (fun i _=> ht i))
  rw [Fintype.sum_sum_type,show (∑ j:ι,Y' (Sum.inr j))=∑ i:ι,(0:veil V) from rfl,sum_const_zero,add_zero]
  unfold Elders; rw [Fintype.sum_sum_type]
  dsimp only [Y',Sum.elim_inl,Sum.elim_inr]; simp only [sum_ite_eq',mem_univ,if_true]
  rw [simpleTurns B h]
  have hp : (∑ j:V × Rootage n, if j.1=v ∧ j.2.val=i then M else 0)=M:= by
    by_cases H : 0∈ i.val.1
    · rw [sum_eq_single (v,(⟨i,H⟩:Rootage n))];simp
      · rintro ⟨a,c⟩ _ hn; split
        · rename_i h; exact False.elim (hn (congr_arg₂ Prod.mk h.1 (Subtype.ext h.2)))
        rfl
      simp
    have hf : M=0:= by unfold M; rw [dusted (hd _) _ H,mul_zero,dot_zero,Poly.send_zero]
    simp [hf]
  rw [hp]; constructor
  · rw [(dues v ..).1,(dues v ..).1]; exact (dot_real (x v) _).symm
  rw [(dues v ..).2,(dues v ..).2]

lemma all_gas (U : Config G n) : ∑ i : Finset (Neat n), peeled id (gamut B K β hd s x A U) (flags Q.p.threshold U) i =
    ∑ i:Finset _,Lifted.pack (Sum.elim (elder ζ B K β hd s x) A) i U:= by
  simp_rw [gather_plate]; symm
  let F:=Sum.elim (elder ζ B K β hd s x) A; let V t:= (F t).amount U; let g t:=attached (F t)
  refine Eq.trans ?_ (Eq.trans (Baler.some g V (flags Q.p.threshold U) univ) ?_)
  · rw [Finset.powerset_univ]
  apply congr_arg (fun f=>∑ i : Finset (Neat n),peeled id f (flags Q.p.threshold U) i); ext1 i
  unfold gamut; rw [sum_filter]

lemma birth (h : IsoVac Q B η) (he : ∀ i,2≤(A i).fires.val.card) (v : V) (U : Config G n) (HQ : Q.activities.Valid Q.p δ η) (hN : (K v).remBound 0 Q e z) :
    let S:=ζ v; let V':= pull (s v) S U; let W:= K v; let D:= Sum.elim (elder ζ B K β hd s x) A
    let P:=∑ i: Finset _, Lifted.pack D i U
    P.part (quiet _)=(Q.activities.gas Q.p V':ℂ) ∧ P.part (slot v)=dot (x v) (β*∑' i,W.marked Q i V') := by
  intro S V' W D P
  let f b:veil _:= Poly.send (quiet _) ((B b).value V':ℂ)+Poly.send (slot v) (foam W Q b V')
  have hu := transDu (x v) β v f (gamut B K β hd s x A U) U (s v) (ζ v) Q.p.threshold (fun _=>comptable B K β hd s x A h he v _ U)
  rw [all_gas] at hu
  have hb := (clipped_single Q HQ W v V' B h hN).1
  have hv := (clipped_single Q HQ W v V' B h hN).2
  refine ⟨hu.vac.trans ((congr_arg _ ?_).trans (dot_real (x v) _)),hu.single.trans (congr_arg (dot _) (congr_arg (β*·) ?_))⟩
  · exact hb
  exact hv

variable [Fintype κ] (L : κ → SourceAt G ζ)

-- prepared unnormalized density. K(S) uses EXACT K0 carried values through P, canonical fields.

def creds (Y : SectionData W) (U : Config G n) := (Real.exp (Q.exponent U):ℂ) • (
    Poly.pass ((∑ i : V,Poly.send (slot i) (dot (x i) (β*(K i|>.exponentialEntry 0 Y Q (pull (s i) (ζ i) U)))))+
      (∑ i,(L i).amount Q.p.threshold U)) * ∑ j:Finset _, Lifted.pack (Sum.elim (elder ζ B K β hd s x) A) j U)

lemma why (h : IsoVac Q B η) (he : ∀ i,2≤(A i).fires.val.card) (hl : ∀ i,2 ≤ (L i).fires.val.card)
    (v : V) (U : Config G n) (HQ : Q.Lawful σ α Λ δ η) (hN : (K v).remBound 0 Q e z) (Y : SectionData W) :
    let D:= creds B K β hd s x A L Y U;let V':= pull (s v) (ζ v) U
    D.part (quiet _) = (Q.eval V':ℂ) ∧ D.part (slot v)=dot (x v) (β*(K v).density 0 Y Q V') := by
  intro D V'
  let G':=∑ j : Finset _, Lifted.pack (Sum.elim (elder ζ B K β hd s x) A) j U
  obtain ⟨h',hM⟩:= birth B K β hd s x A h he v U HQ.labels hN
  let Γ i:= Poly.send (slot i) (dot (x i) (β*(K i|>.exponentialEntry 0 Y Q (pull (s i) (ζ i) U))))
  let ψ:veil V:= (∑ i:V,Γ i)+ ∑ i,(L i).amount Q.p.threshold U; let T:=Poly.pass ψ *G'
  have he i: Dual v ((L i).amount Q.p.threshold U) 0:= Dual.zero _ (hl i) _
  have hf : ψ.part (quiet _) = 0:= by
    rw [show ψ=_ from rfl, Poly.part_plus,Poly.part_sum,Poly.part_sum]; unfold Γ
    rw [Finset.sum_eq_zero (fun i _=> (Poly.part_send ..).trans (if_neg (mute i).symm)),Finset.sum_eq_zero (fun i _=> (he i).base.symm),add_zero]
  have hy : ψ.part (slot v)=dot (x v) (β*((K v).exponentialEntry 0 Y Q V')) := by
    rw [show ψ=_ from rfl,Poly.part_plus,Poly.part_sum,Poly.part_sum]; unfold Γ
    rw [sum_eq_single v]
    · rw [Finset.sum_eq_zero (fun i _=> (he i).tag.symm), add_zero]; exact (Poly.part_send ..).trans (if_pos rfl)
    · intro j _ h; exact faint _ _ _ (Ne.symm h)
    simp
  have hX : Q.exponent V'=Q.exponent U:=congr_fun (expSym HQ (s v) (ζ v)) U
  let r:= Real.exp (Q.exponent U); let E:= (Q.activities.gas Q.p V':ℂ)
  change ((r:ℂ) • (Poly.pass ψ*G')).part _=_ ∧ ((r:ℂ) • (Poly.pass ψ*G')).part _=_
  rw [Poly.part_smul,s_extra (Poly.pass _) G',Poly.pass_part ψ hf,h',one_mul]; constructor
  · unfold Rep.eval; rw [Complex.ofReal_mul,hX]
  rw [Poly.part_smul,mul_solo, selectMode _ hf,hy, Poly.pass_part ψ hf,hM,h',one_mul];
  rw [Coefficient.density,Rep.eval, hX, Complex.ofReal_mul]
  change (r:ℂ) * (dot (x v) (β*_) + dot (x v) (β*_)*E)= dot (x v) (β*(( (r:ℂ)*E) * _ + _* _))
  dsimp only [r,V',E]; simp only [dot_mul,dot_add,dot_real]; ring
end YM.Next.Rank.Edition
