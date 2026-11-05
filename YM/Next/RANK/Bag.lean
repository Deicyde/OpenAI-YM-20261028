import YM.Next.RANK.EventBale
import YM.Next.RANK.Scatter
import YM.Next.RANK.Swath

/-!
# Packing vents at the unmarked level

For vacuum proof carry sym permutations on actual (pre- and post- threshold)
bags. Compress old Nat family (allowing angular/band-dependent K terms) and
enlarge back onto joined output address set. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Baler
open Function Filter RG Lattice Wilson Finset MeasureTheory Relation Corona Thirst
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {p q : BudgetPoint} {ι : Type}

abbrev Neat (n : Side) := Crate (Site n)

def sent (s : Signed) (x : Site n) : Equiv.Perm (Neat n) := by
  let y:=sends s x
  refine Equiv.subtypeEquiv (Equiv.prodCongr y.finsetCongr y.finsetCongr) fun ⟨a,b⟩ => ?_
  change b.Nonempty ∧ b⊆a ↔ (y.finsetCongr b).Nonempty ∧ y.finsetCongr b ⊆ y.finsetCongr a
  simp only [Equiv.finsetCongr,Equiv.coe_fn_mk];constructor
  · exact fun h=> ⟨h.1.map,map_subset_map.mpr h.2⟩
  exact fun h=>⟨map_nonempty.mp h.1,map_subset_map.mp h.2⟩
lemma sent_one (s : Signed) (x : Site n) (b : Neat n) : (sent s x b).val = (swath s x b.val.1, swath s x b.val.2) := by
  unfold sent; ext i <;> first| rfl| exact iff_of_eq (congr_arg (fun x : Finset (Site n)=>i∈x) (map_eq_image ..))

structure Burst (G : Gauge) (n : Side) (t : ℝ) where
  city : Neat n
  value : Config G n→ℝ
  inv : GaugeInvariant value
  meas : Measurable value
  uses : UsesFinal t city.val.1 value
  flag U : value U≠0 → city.val.1∩ flags t U=city.val.2

variable {A : Activities G n} {t w δ : ℝ}

def placed (B : ι→ Burst G n t) (p : Finset ι) (U : Config G n) := peeled (fun i=> (B i).city) (fun i=> (B i).value U) (flags t U) p

def Rhythm (B : ι→ Burst G n t) := ∀ s : Signed,∀ b : Site n, ∃ F : Equiv.Perm ι,
    (∀ i,(B (F i)).city= sent s b (B i).city) ∧ ∀ U i,(B (F i)).value U=(B i).value (pull s b U)

def SumHit (B : ι → Burst G n p.threshold) (e m : ℝ) := ∃ (b : ι → ℝ), (∀ i,0≤b i ∧ ∀ U, ‖(B i).value U‖≤b i) ∧
    Incur (fun i=> (B i).city.val.1) p.B b e m

def locator (F : ForcedAddress G n) : Neat n:= ⟨(F.support,F.inventory),F.inventory_ne,F.inventory_sup⟩

def orig (A : Activities G n) (P : BudgetPoint) (h : A.ForcedFamily P) (i : ℕ) : Burst G n P.threshold where
  city:=locator (A.forced i)
  value:=A.K i
  inv:=h.sym i
  meas:=h.meas i
  uses:=h.reads i
  flag U ha:=(h.permit i U ha).1
lemma gas_at (A : Activities G n) (p : BudgetPoint) (h : A.ForcedFamily p) (x : Finset ℕ) (U : Config G n) :
    A.gasOccurrence p x U=placed (orig A p h) x U := by
  by_cases hi : A.admissible p U x
  · exact (if_pos hi).trans (if_pos (show ripe (fun i => (orig A p h i).city) x _ from hi)).symm
  rw [show A.gasOccurrence p x U=0 from if_neg hi]; exact (if_neg (show ¬ ripe (fun i => (orig A p h i).city) x _ from hi)).symm
lemma old_hymn (h : A.Valid p δ w) : Rhythm (orig A p h.forced) := by
  intro s b; obtain ⟨P⟩:= h.moves s b
  refine ⟨P.kp, fun i=> Subtype.ext ?_,fun U i=> P.valuesK i U⟩; rw [sent_one]; exact congr_arg₂ Prod.mk (P.forced_support i) (P.forced_inventory i)

-- pay in two signatures
lemma shift_cost (p : BudgetPoint) {ι : Type} (X : ι → Support n) (b : ι→ℝ) (t : Site n) :
    (pay (fun i => b i*debt p.B p.supportExponent (X i)) (fun i => t∈X i))=(fun i => if t∈ X i then p.mass (X i) (b i) else 0) := by
  ext i; unfold pay; split_ifs; exact mul_comm ..; rfl
lemma old_cost (h : A.Valid p δ w) : SumHit (p:=p) (orig A p h.forced) p.supportExponent w := by
  obtain ⟨m,hv,ht⟩:= h.boundK; refine ⟨m, hv, fun i=> ?_⟩
  unfold Point; rw [shift_cost]; exact ht i

-- some utility for pay/tsum variance
lemma pack_all {ι β : Type} [Fintype β] (f : ι→ℝ) (x : ι→β) (h : Summable f) :
    ∑ i:β, ∑' j,pay f (fun j=> x j=i) j=∑' j,f j := by
  rw [← Summable.tsum_finsetSum]; refine tsum_congr fun i=> ?_
  · simp [pay,eq_comm]
  exact fun i _=> h.indicator (s:={j|x j=i})

lemma prepare [Countable ι] (B : ι→ Burst G n t) (i : Neat n) :
    ∃ x : Burst G n t,x.city=i ∧ ∀ U,x.value U=∑' j,if (B j).city=i then (B j).value U else 0 := by
  let X:=fun U : Config G n=> ∑' j, if (B j).city=i then (B j).value U else 0
  refine ⟨{city:=i,value:=X,inv:=?_,meas:=?_,uses:=?_,flag:=?_},rfl,fun _=>rfl⟩
  · intro j U; refine tsum_congr fun v=> ?_; rw [(B v).inv]
  ·
    apply Measurable.tsum; intro j; split
    · exact (B j).meas
    exact measurable_const
  · intro U V ht hp; apply tsum_congr; intro j; by_cases hh : (B j).city=i
    · rw [if_pos hh,if_pos hh]; exact (B j).uses U V (hh.symm ▸ ht) (hh.symm ▸ hp)
    rw [if_neg hh,if_neg hh]
  intro U hU; apply Classical.byContradiction; intro he; apply hU
  unfold X; refine (tsum_congr (g:=fun _=> (0:ℝ)) ?_).trans (tsum_zero); intro j; split
  · rename_i h; apply Classical.byContradiction; intro ho; apply he; rw [← h]; exact (B j).flag U ho
  rfl

variable (B : ι→ Burst G n p.threshold) {c d : ℝ}

lemma summable_present (H : SumHit (p:=p) B c d) (hc : 0≤c) (U : Config G n) : Summable fun i=> (B i).value U := by
  obtain ⟨m,hm,ht⟩:=H
  let f x := pay (fun i => m i*debt p.B c (B i).city.val.1) (fun i=> x∈(B i).city.val.1)
  have h : Summable fun i => ∑ j,f j i:= summable_sum fun j _=> (ht j).2.1
  have he i : m i≤∑ j : Site n,f j i := by
    let X := (B i).city; obtain ⟨x,hx⟩:= X.property.1.mono X.property.2
    apply le_trans _ (single_le_sum (fun j _=> (ht j).1 i) (mem_univ x))
    change m i≤pay _ _ _; unfold pay; simp only
    split_ifs; exact le_mul_of_one_le_right (hm i).1 (Real.one_le_exp (by positivity)); contradiction
  apply h.of_norm_bounded; exact fun i=> ((hm i).2 U).trans (he i)

lemma maintain (H : SumHit (p:=p) B c d) (hc : 0 ≤ c) (R : Neat n → Burst G n p.threshold) (hr : ∀ i,(R i).city=i)
    (he : ∀ i U,(R i).value U=∑' j,if (B j).city=i then (B j).value U else 0) : SumHit (p:=p) R c d := by
  obtain ⟨m,hm,hH⟩:=H
  let f (x : Neat n) := pay m (fun i=> (B i).city=x)
  have hn j i : 0 ≤ f j i:=by unfold f pay; split; exact (hm _).1; exact le_rfl
  have h (x) : Summable (f x) := by
    obtain ⟨y,hy⟩:= x.property.1.mono x.property.2
    apply (hH y).2.1.of_nonneg_of_le (hn _)
    intro b; by_cases hh:(B b).city=x
    · have h := hh.symm ▸ hy
      unfold f pay; simp only [hh,hy,↓reduceIte]; exact le_mul_of_one_le_right (hm _).1 (Real.one_le_exp (by positivity))
    exact (le_of_eq (show f x b=0 from if_neg hh)).trans ((hH y).1 b)
  let M j:= ∑' i,f j i
  refine ⟨M,fun i=>⟨tsum_nonneg (hn _),fun U=>?_⟩,fun i =>?_⟩
  · let L:=fun j=>if (B j).city=i then (B j).value U else 0
    have hl j: ‖L j‖≤ f i j:= by unfold L f pay; split_ifs; exact (hm j).2 U; rw [norm_zero]
    have hh:=(h i).of_nonneg_of_le (fun i=> norm_nonneg (L i)) hl
    rw [he]; exact (norm_tsum_le_tsum_norm hh).trans (hh.tsum_le_tsum hl (h i))
  let P (j : Neat n) := pay (fun x=> M x*debt p.B c (R x).city.val.1) (fun x=> i∈ (R x).city.val.1) j
  have hp j : 0 ≤ P j:=by
    unfold P pay; split
    · exact mul_nonneg (tsum_nonneg (hn _)) (Real.exp_pos _).le
    exact le_rfl
  let a x := pay (fun x=> m x*debt p.B c (B x).city.val.1) (fun x=> i∈ (B x).city.val.1) x
  refine ⟨hp,(hasSum_fintype P).summable,?_⟩
  rw [tsum_fintype]; change (∑ j,P j)≤ d; refine le_trans (le_of_eq (b:=∑' i,a i) ?_) (hH i).2.2
  rw [← pack_all a (fun i=>(B i).city) (hH i).2.1]; apply sum_congr rfl; intro j _; unfold P pay M; simp only [hr]
  by_cases hh : i ∈ j.val.1
  · rw [if_pos hh,← tsum_mul_right]; apply tsum_congr; intro x; by_cases he : (B x).city=j<;>simp [pay,f,Thirst.pay,a,he,hh]
  rw [if_neg hh]; symm; refine (tsum_congr (g:=fun _=> (0:ℝ)) ?_).trans (tsum_zero); intro x; by_cases h:(B x).city=j<;>simp [pay,a,h,hh]

lemma hymn (M : Rhythm B) (R : Neat n → Burst G n p.threshold) (hr : ∀ i,(R i).city=i)
    (he : ∀ i U,(R i).value U=∑' j,if (B j).city=i then (B j).value U else 0) : Rhythm R := by
  intro s b; obtain ⟨m,H,hv⟩:= M s b; refine ⟨sent s b,fun q=> ?_,fun U i=>?_⟩
  · exact (hr (sent s b q)).trans (congr_arg (sent s b) (hr q).symm)
  refine (he _ _).trans (Eq.trans ?_ (he _ _).symm)
  rw [← Equiv.tsum_eq m]; apply tsum_congr; intro i; rw [H,hv]; simp


theorem accommodate [Countable ι] (M : Rhythm B) (H : SumHit (p:=p) B c d) (hc : 0 ≤ c) (hV : ∀ U,Summable (fun i=> placed B i U)) :
    ∃ R : Neat n → Burst G n p.threshold,(∀ i,(R i).city=i) ∧ Rhythm R ∧ SumHit (p:=p) R c d ∧ (∀ x U,(R x).value U=∑' j,if (B j).city=x then (B j).value U else 0) ∧ ∀ U,
      ∑ i, placed R i U=∑' i, placed B i U := by
  choose R hr he using prepare B
  refine ⟨R,hr,hymn B M _ hr he,maintain B H hc _ hr he,he,fun U=>?_⟩
  unfold placed
  let P:= fun i=> (B i).value U
  let A:= fun i=> (B i).city
  have hh : Summable P:= summable_present B H hc U
  rw [Baler.all (fun i=> (B i).city) _ _ (hV U) (fun i => ((hh.indicator (s:={a| A a=i})).congr fun b => by by_cases h:(B b).city=i <;> simp [Set.indicator,h,A,P]))]; apply sum_congr rfl; intro a _
  rw [show (fun i=> (R i).city)=id from funext hr, show (fun i=> (R i).value U)=piece A P from funext fun i => he i U]

-- infinite padding; consumes Bound, with full exponent (caller chooses realization)

def anchor (B : Neat n) : ForcedAddress G n:= ⟨B.val.1,B.val.2,B.property.1,B.property.2,fun _=>True⟩

def lengthen (A : Activities G n) (p : BudgetPoint) (R : Neat n → Burst G n p.threshold) (E : Equiv ℕ ((Neat n) × ℕ)) : Activities G n where
  reg:= A.reg
  E:=A.E
  forced:=fun i=>anchor (E i).1
  K:=fun i U=>if (E i).2 = 0 then (R (E i).1).value U else 0

lemma presented (p : BudgetPoint) {A : Activities G n} (hA : ∀ s x, Nonempty (A.Moves s x))
    (E : Equiv ℕ ((Neat n) × ℕ))
    {R : Neat n → Burst G n p.threshold} (hr : ∀ i,(R i).city=i) (M : Rhythm R) :
      ∀ s x, Nonempty ((lengthen A p R E).Moves s x) := by
  intro s x
  obtain ⟨P⟩:=hA s x; obtain ⟨Y,h,H⟩:=M s x
  have he : Y=sent s x := Equiv.ext fun i=> (hr (Y i)).symm.trans ((h i).trans (by rw [hr]))
  let K:= (E.trans (Equiv.prodCongr Y (Equiv.refl _))).trans E.symm
  let A':= lengthen A p R E
  have ht i : E (K i)=(Y (E i).1,(E i).2):= by simp [K]; rfl
  refine ⟨⟨P.ep,K,P.reg_site,P.reg_support,fun i=>?_,fun i=>?_,fun _ _=>Iff.rfl,P.valuesE,fun i U=>?_⟩⟩
  · unfold lengthen anchor; dsimp only; rw [ht]; change _=swath _ _ _; simp only [he,sent_one]
  · unfold lengthen anchor; dsimp only; rw [ht]; change _=swath _ _ _; simp only [he,sent_one]
  unfold lengthen; simp only [ht,H]

lemma plenty (p : BudgetPoint) (R : Neat n → Burst G n p.threshold) (hr : ∀ i,(R i).city=i) (E : Equiv ℕ ((Neat n) × ℕ))
    (A : Activities G n) : (lengthen A p R E).ForcedFamily p := by
  let X:=lengthen A p R E
  constructor
  · intro i k U; simp only [lengthen,(R (E i).1).inv k U]
  · exact fun _ _ _=>Iff.rfl
  · intro i; change Measurable fun U=> if (E i).2=0 then _ else (0:ℝ)
    split; exact (R _).meas; exact measurable_const
  · intro i; exact (show MeasurableSet {U:Config G n|True} by simp)
  · intro i x y h1 h2; dsimp only [lengthen]; rw [(R _).uses x y]
    · rw [hr]; exact h1
    rw [hr]; exact h2
  · exact fun _ _ _ _ _=> rfl
  · intro i U hh
    refine ⟨?_,trivial⟩
    change (if _ then (R (E i).1).value U else (0:ℝ)) ≠ 0 at hh
    split_ifs at hh; exacts [(by
      have he:= (R (E i).1).flag U hh; rw [hr] at he; exact he), (hh rfl).elim]
lemma lengthy (p : BudgetPoint) (R : Neat n → Burst G n p.threshold) (hr : ∀ i,(R i).city=i) (E : Equiv ℕ ((Neat n) × ℕ))
    (A : Activities G n) (H : SumHit (p:=p) R p.supportExponent d) : (lengthen A p R E).KBound p d := by
  obtain ⟨m,h,hv⟩:=H
  let x i:= if (E i).2=0 then m (E i).1 else 0
  have hx i: 0≤ x i:= by unfold x;split;exact (h _).1; exact le_rfl
  refine ⟨x,fun i=> ⟨hx i,fun U=>?_⟩,fun i=>?_⟩
  · dsimp only [lengthen,x]; split_ifs; exact (h _).2 _; rw [norm_zero]
  let h₁:=fun j=> pay (fun j=>m j*debt p.B p.supportExponent j.val.1) (fun j : Neat n=> i∈j.val.1) j
  have hp : SumBudget h₁ d:=by
    have h:= hv i; unfold Point at h; simp_rw [hr] at h; exact h
  let f j := if i∈ ((lengthen A p R E).forced j).support then p.mass ((lengthen A p R E).forced j).support (x j) else 0
  have he (j : ℕ) : f j = if (E j).2=0 then h₁ (E j).1 else 0 := by
    dsimp only [f,x,h₁,Thirst.pay,lengthen,anchor]
    split_ifs <;> first| rfl| exact mul_comm ..| exact mul_zero _
  have hn j : 0≤ f j:= by rw [he]; split;exact hp.1 _;exact le_rfl
  let D := (univ : Finset (Neat n)).image (fun v=> E.symm (v,0))
  have ht (j : ℕ) : j∉ D → f j=0 := by
    intro h; rw [he,if_neg]; intro hx; apply h
    exact mem_image.mpr ⟨(E j).1,mem_univ _, by rw [← hx,Prod.eta, Equiv.symm_apply_apply]⟩
  refine ⟨hn,summable_of_ne_finset_zero ht,?_⟩
  change (∑' i,f i) ≤ _; rw [tsum_eq_sum ht,sum_image]
  · simp only [he,Equiv.apply_symm_apply,↓reduceIte]
    exact (tsum_fintype ..).symm.trans_le hp.2.2
  intro a _ b _ H; exact congr_arg Prod.fst (E.symm.injective H)

lemma stretcher (p : BudgetPoint) (R : Neat n → Burst G n p.threshold) (hr : ∀ i,(R i).city=i) (E : Equiv ℕ ((Neat n) × ℕ))
    (A : Activities G n) (H : (lengthen A p R E).Valid p δ w) (U : Config G n) :
      (lengthen A p R E).gas p U=∑ i,placed R i U := by
  let Q:=lengthen A p R E; let f:=orig Q p H.forced
  let P i:=(f i).value U
  let Y i:=(f i).city
  let Z := flags p.threshold U
  have hz (i) : Q.gasOccurrence p i U=peeled Y P Z i:=gas_at Q p H.forced ..
  change (∑' i,Q.gasOccurrence p i U)= _; simp_rw [hz]
  have he i : Y i = (E i).1:=rfl
  have hp : Summable P := summable_present (orig Q p H.forced) (old_cost H) p.exponent_pos.le U
  rw [Baler.all _ _ _ (((Activities.gasSeries H).summable U).congr hz) (fun i=> ((hp.indicator (s:={x| Y x=i})).congr fun b => by by_cases h:Y b=i <;> simp [Set.indicator,h,Y]))]
  unfold placed
  have hh (i) : piece Y P i=(R i).value U := by
    unfold piece; rw [tsum_eq_single (E.symm (i,0))]
    · rw [he,Equiv.apply_symm_apply]; change (if _ then (if (E _).2= _ then _ else _) else _)=_; simp [Equiv.apply_symm_apply]
    intro j hj; rw [he]; split_ifs with hx
    · apply if_neg; intro hy; apply hj
      apply E.injective; rw [Equiv.apply_symm_apply]; exact Prod.ext hx hy
    rfl
  apply Finset.sum_congr rfl; intro a _; rw [funext hh, show (fun i=> (R i).city)= id from funext hr]

end YM.Next.Rank.Baler
