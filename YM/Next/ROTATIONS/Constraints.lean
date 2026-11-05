import YM.Next.ROTATIONS.Pier
/-! # Divergence identities at the Fourier tests; tensor moment relations.

All operations in the test tensor positions before evaluation. -/
noncomputable section
namespace YM.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff NNReal ENNReal BigOperators InnerProductSpace Matrix.Norms.Frobenius

def Pmul (k : ℕ) (i : Axis) : TestMap →ₗ[ℝ] TestMap where
  toFun A := A.compLinearMap (fun j : Axis => if j=i then (pump k).toLinearMap else LinearMap.id)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma Pmul_at (k : ℕ) (i f) (Z : TestMap) : Pmul k i Z f=Z (stepAt k f i) := by
  change Z _=_; congr 1; ext1 j; by_cases h:j=i
  · subst j; simp [stepAt]
  simp [stepAt,h]
lemma Pplus (p q : ℕ) (i : Axis) (Z : TestMap) : Pmul p i (Pmul q i Z)=Pmul (q+p) i Z := by
  ext1 f; rw [Pmul_at,Pmul_at,Pmul_at,stepAt,stepAt]; simp only [update_self,update_idem,pump_pump]
lemma Pcomm (p q : ℕ) (i j : Axis) (Z : TestMap) : Pmul p i (Pmul q j Z)=Pmul q j (Pmul p i Z) := by
  by_cases h:i=j
  · subst j; rw [Pplus,Pplus,add_comm]
  ext1 f; simp_rw [Pmul_at]; unfold stepAt; rw [update_of_ne (Ne.symm h), update_of_ne h,update_comm h]

abbrev liftP := Pmul 1


abbrev SelfB (R : Series) i := sent (R i i i i)
abbrev Mux (R : Series) i := ∑ a∈other i,liftP a (sent (R a i i i))
def BL (R : Series) (i : Axis) : TestMap := ∑ j∈other i, ∑ a∈other i,liftP j (liftP a (sent (R a i j i)))
def Cash1 (R : Series) i := ∑ j∈other i,liftP j (source R i j i)

abbrev Mex (R : Series) i := ∑ j∈other i,∑ a∈other i,∑ b∈other i,liftP j (liftP a (liftP b (sent (R b a j i))))
def CL (R : Series) (i : Axis) : TestMap := ∑ j∈other i, ∑ a∈other i,∑ b∈other i,∑ c∈other i,liftP j (liftP a (liftP b (liftP c (sent (R c j a b)))))
def Cash2 (R : Series) i := ∑ j∈other i,∑ a∈other i,liftP j (liftP a (source R a j i))
def Cash3 (R : Series) i := ∑ j∈other i,∑ a∈other i,∑ b∈other i,liftP j (liftP a (liftP b (source R j a b)))
def DB (R : Series) i := Cash1 R i - liftP i (source R i i i)
def DC (R : Series) i := Cash3 R i - liftP i (Cash2 R i)
lemma cash0 (R : Series) (i b c d : Axis) : source R b c d=liftP i (sent (R i b c d))+∑ j∈other i,liftP j (sent (R j b c d)) := by
  ext1 f; simp_rw [_root_.add_apply,_root_.sum_apply,liftP,Pmul_at]; exact (source_at ..).trans (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)).symm
variable {G : Gauge} {L : Register G} {S : Table L}
lemma BL_law {R J D} (H : Portrait (S:=S) J D R) (i : Axis) : BL R i=Pmul 2 i (SelfB R i)+DB R i := by
  have he : Cash1 R i = liftP i (Mux R i)+BL R i := by
    unfold Cash1 Mux BL
    simp_rw [cash0 R i i _ i,map_add,_root_.map_sum,Finset.sum_add_distrib]; congr 1
    apply Finset.sum_congr rfl; intro j _; rw [H.UD i i j i,Pcomm]
  rw [DB,he,cash0 R i i i i,map_add]
  rw [show liftP i (liftP i _) = Pmul 2 i (SelfB R i) from Pplus ..]
  unfold Mux; abel
lemma CL_law {R J D} (H : Portrait (S:=S) J D R) (i : Axis) : CL R i=Pmul 2 i (BL R i)+DC R i := by
  have he : Cash2 R i=liftP i (BL R i)+Mex R i := by
    unfold Cash2 BL Mex; simp_rw [cash0 R i _ _ i,map_add,_root_.map_sum,Finset.sum_add_distrib]; congr 1
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro a _
    rw [H.LR i a,Pcomm 1 1 a i,Pcomm 1 1 j i]
  have hh : Cash3 R i=liftP i (Mex R i)+CL R i := by
    unfold Cash3 CL Mex; simp_rw [cash0 R i,map_add,_root_.map_sum,Finset.sum_add_distrib]; congr 1
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
    rw [H.LR i j,H.UD j i a b,H.LR a b,Pcomm 1 1 b i,Pcomm 1 1 a i,Pcomm 1 1 j i]
  rw [DC,hh,he,map_add]
  rw [show liftP i (liftP i (BL R i))=Pmul 2 i (BL R i) from Pplus ..]; abel

def Ach (w : Axis→ℝ) (δ : ℝ) (T : TestMap) := ∀ f, Budget δ (fun n => T (mails w f n))
lemma kstep (Z : TestMap) (k : ℕ) (w f n) (j : Axis) :
    Pmul k j Z (mails w f n)=↑(fuel (w j) n ^ k : ℝ) * Z (mails w (stepAt k f j) n) := by
  rw [Pmul_at,stepAt,show mails w f n j=_ from rfl, mails,bill,pump_width]
  rw [Z.map_update_smul,Complex.real_smul]; congr 1
  apply congr_arg Z
  ext1 i; unfold stepAt; by_cases h : i=j <;> simp [h,mails,bill]
lemma Ach.one {w a δ T} (h : Ach w δ T) (j) (he : w j ≤ a) : Ach w (δ+a) (liftP j T) := by
  intro f
  have ht : Budget (w j) (fun n => ((fuel (w j) n):ℂ)) := (budget_fuel (w j)).reduce (Eventually.of_forall fun i => le_of_eq (norm_real _))
  simp_rw [liftP,kstep,pow_one]; rw [add_comm]
  exact (ht.rise he).prod (h _)
lemma Ach.sum {ι : Type*} (w a) (t : Finset ι) (f : ι → TestMap) (h : ∀ i∈t,Ach w a (f i)) : Ach w a (∑ i∈t,f i) := by
  intro g; simp_rw [_root_.sum_apply]; exact budget_sum t _ a (fun i hi => h i hi _)
lemma Ach.sub {w a T U} (h : Ach w a T) (l : Ach w a U) : Ach w a (T-U) := fun f => by simp_rw [_root_.sub_apply]; exact (h _).sub (l _)

lemma accounts_cost {R J D} (H : Portrait (S:=S) J D R) (hd : 0<D) (P : DiffPlan S) (hP : P.Derivatives S)
    (hr : S.Hierarchy) (hp : Conserved P hr.spin J) (he : Strong J P D) (a : ℝ) (ha : a≤0) (w) (hw : ∀ j,w j≤a) (i) :
    Ach w (a*4) (DB (joint R) i) ∧ Ach w (a*6) (DC (joint R) i) := by
  let F := joint R
  have ht b c d : Ach w (a*3) (source F b c d) := source_cost hr P hP hd H hp he a ha b c d w hw
  refine ⟨?_,?_⟩
  · rw [show a*4=a*3+a by ring]; exact (Ach.sum w _ _ _ fun j _ => (ht _ _ _).one _ (hw j)).sub ((ht _ _ _).one _ (hw i))
  rw [show a*6=a*3+a+a+a by ring]
  apply Ach.sub
  · exact Ach.sum w _ _ _ fun j _ => Ach.sum w _ _ _ fun k _ => Ach.sum w _ _ _ fun l _ => (((ht j k l).one _ (hw l)).one _ (hw k)).one _ (hw j)
  · apply Ach.one _ i (hw i)
    exact Ach.sum w _ _ _ fun j _ => Ach.sum w _ _ _ fun k _ => ((ht k j i).one _ (hw k)).one _ (hw j)

def Disappears (i : Axis) (D : ℕ) (A : TestMap) := ∀ f : Grouping, Centred D (f i) → A f=0
lemma disappear_add (i f k a) (h : Centred (a+k) (f i)) : Centred a (stepAt k f i i) := by
  rw [stepAt,update_self]; intro j hj
  have he : tally j (pump k (f i))=tally (j+k) (f i) := by unfold tally; rw [ContinuousLinearMap.comp_apply,pump_pump]; rfl
  rw [he]; apply h; omega
lemma Disappears.pmul {i D A} (h : Disappears i D A) (j k) : Disappears i (D+k) (Pmul k j A) := by
  intro f hf
  rw [Pmul_at]; apply h; by_cases he : j=i
  · subst j; exact disappear_add i f k D hf
  unfold stepAt; rw [update_of_ne (Ne.symm he)]; exact fun j hj => hf j (by omega)
lemma Disappears.sum {ι : Type*} (i D) (t : Finset ι) (f : ι → TestMap) (h : ∀ i'∈t,Disappears i D (f i')) : Disappears i D (∑ i∈t,f i) := by
  intro g hg; rw [_root_.sum_apply]; exact Finset.sum_eq_zero fun j hj => h _ hj _ hg
lemma Disappears.sub {i D A B} (h : Disappears i D A) (l : Disappears i D B) : Disappears i D (A-B) := by
  intro f hf; simp_rw [_root_.sub_apply,h f hf,l f hf,sub_self]
lemma accounts_sink {R J D} (H : Portrait (S:=S) J D R) (P : DiffPlan S) (hP : P.Derivatives S) (hr : S.Hierarchy)
    (hp : Conserved P hr.spin J) (he : Strong J P D) (i) : Disappears i (D+1+1) (DB R i) ∧ Disappears i (D+1+1+1+1) (DC R i) := by
  have ht b c d : Disappears i (D+1) (source R b c d) := by
    intro f hf; change I*delta _ _ _ _ (polar f)=_; rw [closed_shell hr P hP H hp he b c d (polar f) i (polar_flat f i _ hf),mul_zero]
  refine ⟨?_,?_⟩
  · unfold DB Cash1; exact (Disappears.sum _ _ _ _ fun j _ => (ht i j i).pmul j 1).sub ((ht _ _ _).pmul _ 1)
  apply Disappears.sub
  · exact Disappears.sum _ _ _ _ fun j _ => Disappears.sum _ _ _ _ fun k _ => Disappears.sum _ _ _ _ fun l _ => (((ht _ _ _).pmul l 1).pmul k 1).pmul j 1
  · apply Disappears.pmul _ _ 1
    exact Disappears.sum _ _ _ _ fun j _ => Disappears.sum _ _ _ _ fun k _ => ((ht _ _ _).pmul k 1).pmul j 1

def Quest (w : Axis→ℝ) (i : Axis) (e : Axis→Bool) (δ : ℝ) (T : TestMap) :=
    ∀ f : Grouping, (∀ j, Ends (f j)) → Far (f i) → (∀ j,j≠i → Reflects (e j) (f j)) → Budget δ (fun n => T (mails w f n))
def toggle (i : Axis) (e : Axis→Bool) (j : Axis) := Bool.xor (e j) (decide (j=i))
lemma Quest.inserts {w i e a δ T} (h : Quest w i e δ T) (j : Axis) (he : w j ≤ a) : Quest w i (toggle j e) (δ+a) (liftP j T) := by
  intro f hf hg hk
  simp_rw [liftP,kstep,pow_one,mul_comm (Complex.ofReal _)];
  have ht : Budget (w j) (fun n => ((fuel (w j) n):ℂ)) := (budget_fuel (w j)).reduce (Eventually.of_forall fun i => le_of_eq (norm_real _))
  refine (h (stepAt 1 f j) ?_ ?_ ?_).prod (ht.rise he)
  · intro k; unfold stepAt; by_cases h : k=j
    · subst k; rw [update_self]; exact (hf j).pumps 1
    rw [update_of_ne h ..]; exact hf k
  · unfold stepAt; by_cases h:i=j
    · subst i; rw [update_self]; exact hg.pumps _
    rw [update_of_ne h ..]; exact hg
  intro k hi; unfold stepAt; specialize hk k hi; by_cases hp : k=j
  · subst k; rw [update_self]; intro x; rw [pump_at,hk x]
    cases h : e j <;> simp [toggle, h,pump_at]
  rw [update_of_ne hp]; simpa [toggle,hp] using hk
lemma Quest.sum {ι : Type*} (w i e a) (t : Finset ι) (f : ι → TestMap) (h : ∀ k∈t,Quest w i e a (f k)) : Quest w i e a (∑ k∈t,f k) := by
  intro g hg he hz; simp_rw [_root_.sum_apply]; exact budget_sum _ _ _ fun k hk => h k hk g hg he hz
lemma Quest.alters {w i e p δ T} (h : Quest w i p δ T) (he : ∀ j,j≠i → e j=p j) : Quest w i e δ T := by
  intro f hf hg hk; exact h f hf hg fun j hj => he j hj ▸ hk j hj
lemma accounts_fixed (V : ∀ i, Chamber S i) (K : S.Hierarchy) (P : DiffPlan S) (hp : P.Derivatives S) (ho : P.Orientation K.spin)
    (J : Stress S) (C : Conserved P K.spin J) (Y : RawTensor K.spin J)
    {D : ℕ} {R : Series} (hR : Portrait J D R) (δ : ℝ) (hd : 0<δ) (i) (w) (he : w i=0) (a : ℝ) (ha : a≤0) (hw : ∀ j,j≠i → w j≤a) :
    Quest w i (fun _ => false) δ (SelfB R i) ∧ Quest w i (fun _ => false) (δ+a+a) (BL R i) ∧
      Quest w i (fun _ => false) (δ+a+a+a+a) (CL R i) := by
  have H j k l m : Quest w i (axes j k l m) δ (sent (R j k l m)) := fun f h g t =>
    fixed V K P hp ho J C Y hR j k l m i f g h t w he (fun i' => by
      by_cases H:i'=i
      · simp [H,he]
      exact (hw i' H).trans ha) _ hd
  have hq (k) (hk : k ∈ other i) : w k ≤ a := hw _ (Finset.mem_erase.mp hk).1
  refine ⟨(H i i i i).alters (fun j hj => ?_),?_,?_⟩
  · simp [axes,spar,hj]
  · refine Quest.sum w _ _ _ (other i) _ fun j hj => Quest.sum _ _ _ _ _ _ fun k hk => ?_
    apply (((H k i j i).inserts k (hq _ hk)).inserts j (hq _ hj)).alters
    intro x hx; unfold toggle axes spar; cases decide (x=j)<;>cases decide (x=k)<;> cases decide (x=i)<;>decide
  unfold CL
  refine Quest.sum w i _ _ _ _ fun j hj => Quest.sum w i _ _ _ _ fun k hk => Quest.sum w i _ _ _ _ fun l hl => Quest.sum w i _ _ _ _ fun m hm => ?_
  apply (((((H m j k l).inserts m (hq _ hm)).inserts l (hq _ hl)).inserts k (hq _ hk)).inserts j (hq _ hj)).alters
  intro x hx; unfold toggle axes spar
  cases decide (x=j)<;>cases decide (x=k)<;>cases decide (x=l)<;>cases decide (x=m)<;>decide
end YM.Outer
