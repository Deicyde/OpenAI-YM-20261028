import YM.Bid.Station
import YM.Next.RANK.Advice

/-!
# Optional tap agenda

Take individual signed path terms as stated. When persisting to Wickless budget
compress **within same support** before contributing. At fixed stage finite torus
can take that supports projection. The next output still constrained to true
occurrence. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker PathData
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {p q : BudgetPoint} {r : ℕ} {ι χ : Type}
variable {C : Clip} {t τ μ σ Λ : ℝ}
variable (P : PathData G)

lemma summable_verse {W : ι→Wickless G n τ} {r W₀ : ℝ} (H : Verse W q r W₀) (hr : 0≤r) (U : Config G n) : Summable (fun i=> (W i).value U) := by
  obtain ⟨x,hx,hV⟩:= H
  let P y:= pay (fun i=> x i*debt q.B r (W i).extent) (fun i=> y∈(W i).extent)
  have ht: Summable (fun i=>∑ v,P v i):= summable_sum fun i _=> (hV i).2.1
  refine ht.of_norm_bounded fun i=> ?_
  obtain ⟨y,hy⟩:= (W i).active
  refine le_trans ?_ (single_le_sum (f:=fun v=>P v i) (fun j _=> (hV j).1 i) (mem_univ y))
  rw [Real.norm_eq_abs]; apply ((hx i).2 U).trans; unfold P pay; rw [if_pos hy]; exact le_mul_of_one_le_right (hx i).1 (Real.one_le_exp (by positivity))

private lemma sum_fit {A : ι→ℝ} {B : χ→ℝ} {F : ι⊕χ→ℝ} {a b : ℝ}
    (h : SumBudget A a) (hp : SumBudget B b) (hc : ∀ i,F (Sum.inl i)=A i) (ht : ∀ i,F (Sum.inr i)=B i) : SumBudget F (a+b) := by
  have hM : Summable (F ∘ Sum.inl):=(by rw [show F ∘ Sum.inl=A from funext hc];exact h.2.1)
  have hP : Summable (F ∘ Sum.inr):=(by rw [show F ∘ Sum.inr=B from funext ht];exact hp.2.1)
  refine ⟨fun i=> ?_,Summable.sum _ hM hP,?_⟩
  · cases i with | inl i=>rw [hc];exact h.1 _| inr i=>rw [ht];exact hp.1 _
  rw [hM.tsum_sum hP]; simp_rw [hc,ht]; exact add_le_add h.2.2 hp.2.2

lemma Verse.add {X : ι→Wickless G n τ} {Y : χ→Wickless G n τ} {a b e : ℝ}
    (h : Verse X q e a) (he : Verse Y q e b) : Verse (Sum.elim X Y) q e (a+b):= by
  obtain ⟨m,H,hm⟩:=h; obtain ⟨L,HH,hL⟩:=he
  refine ⟨Sum.elim m L, fun i=> ?_,fun i=> ?_⟩
  · cases i with | inl i=>exact H _| inr i=>exact HH _
  exact sum_fit (hm i) (hL i) (fun _=>rfl) (fun _=>rfl)
lemma Garden.plant {X : ι→Wickless G n τ} {Y : χ→Wickless G n τ} (h : Garden X) (he : Garden Y) : Garden (Sum.elim X Y):= by
  intro s y; obtain ⟨p,h⟩:=h s y; obtain ⟨q,he⟩:=he s y
  refine ⟨Equiv.sumCongr p q,fun i=>?_⟩; rcases i with i|i; exacts [h _,he _]

/-- Certificate for optional LOG tap(s). signed values relative to new exponent.
 Carry before regrouping across κ. -/
def Volunteer (V : Config G n→ℝ) (q : BudgetPoint) (e r : ℝ) := ∃ (ι : Type), ∃ (_ : Countable ι), ∃ W : ι→Wickless G n q.threshold,
    Garden W∧ Verse W q e r ∧ ∀ U,V U=∑' i,(W i).value U
lemma Volunteer.add {F G : Config G n→ℝ} {p e f : ℝ} (he : 0≤e) (h : Volunteer F q e f) (hg : Volunteer G q e p) : Volunteer (F+G) q e (f+p) := by
  obtain ⟨ι,hι,W,hM,hm,h⟩:=h; obtain ⟨χ,hχ,Q,hG,hq,hH⟩:=hg
  refine ⟨ι ⊕ χ,inferInstance, Sum.elim W Q,hM.plant hG,hm.add hq,fun U=> ?_⟩; rw [Pi.add_apply,h,hH]
  let A:=fun i=> (Sum.elim W Q i).value U
  have he : Summable (A ∘ Sum.inl):= summable_verse (q:=q) hm he U
  have hp : Summable (A ∘ Sum.inr):= summable_verse (q:=q) hq (by assumption) U
  simpa only [A,Sum.elim_inl,Sum.elim_inr] using! (Summable.tsum_sum he hp).symm

-- group logs by support. X degenerate torus has always active hits
abbrev ValidX (n : Side):={ A : Support n // A.Nonempty }

def city (X : Wickless G n t) : ValidX n:= ⟨X.extent,X.active⟩

def pores [Countable ι] (W : ι→ Wickless G n τ) (i : ValidX n) : Wickless G n τ where
  extent:=i.val
  active:=i.property
  value U:=∑' j, pay (fun j=> (W j).value U) (fun j=>city (W j)=i) j
  inv k U:= by apply tsum_congr; intro j; unfold pay; split;exact (W j).inv k U; rfl
  sees U V a b:= by
    refine tsum_congr fun j=> ?_; unfold pay; split
    · rename_i h; have h : (W j).extent=i.val:=congr_arg Subtype.val h; exact (W j).sees U V (h.symm ▸ a) (h.symm ▸ b)
    rfl
  meas:= by apply Measurable.tsum; intro j; unfold pay; split;exact (W j).meas;exact measurable_const
  untouched U H:=by
    refine (tsum_congr (g:=fun _=>0) ?_).trans tsum_zero; intro j; unfold pay; split
    · rename_i h; have h : (W j).extent=i.val:=congr_arg Subtype.val h; exact (W j).untouched _ (h.symm ▸ H)
    rfl

def vert (s : Signed) (x : Site n) : Equiv.Perm (ValidX n) := by
  let Y:=sends s x; refine Equiv.subtypeEquiv Y.finsetCongr fun i=> ?_
  exact map_nonempty.symm
lemma vent_at (s : Signed) (x : Site n) (i : ValidX n) : (vert s x i).val=swath s x i.val:=map_eq_image ..
lemma pore_hymn [Countable ι] {W : ι→ Wickless G n τ} (h : Garden W) : Garden (pores W):= by
  intro s x; obtain ⟨Y,hY⟩:=h s x; refine ⟨vert s x,fun i=> ⟨vent_at ..,fun U=>?_⟩⟩
  have hv j : city (W (Y j))=vert s x (city (W j)):= Subtype.ext ((hY j).1.trans (vent_at s x (city (W j))).symm)
  dsimp only [pores]; rw [←Y.tsum_eq]; refine tsum_congr fun j=>?_ ; unfold pay; simp [hv,(hY j).2]
lemma poem [Countable ι] {W : ι→ Wickless G n τ} {e u : ℝ} (H : Verse W p e u) (hq : 0≤e) : Verse (pores W) p e u := by
  obtain ⟨m,hM,hm⟩:=H
  let f (x : ValidX n) (i : ι) := pay m (fun j=> city (W j)=x) i
  let P x:=∑' i,f x i
  have hn x i:0≤ f x i:= by unfold f pay; split; exact (hM _).1; exact le_rfl
  have hv (x) : Summable (f x):= by
    obtain ⟨j,hj⟩:= x.property; apply (hm j).2.1.of_nonneg_of_le (hn _); intro i; by_cases hh : city (W i)=x
    · have h : j∈ (W i).extent:= (show j∈ (city (W i)).val from hh.symm ▸ hj)
      unfold f pay; simp only [hh,h,↓reduceIte]; exact le_mul_of_one_le_right (hM _).1 (Real.one_le_exp (by positivity))
    exact (le_of_eq (show f x i=0 from if_neg hh)).trans (hm j|>.1 i)
  have he x: 0≤P x:=tsum_nonneg (hn _)
  refine ⟨P,fun i=>⟨he _,fun U=> ?_⟩, fun x=> ?_⟩
  · let H:= pay (fun j=> (W j).value U) (fun j=>city (W j)=i)
    have hx j : ‖H j‖≤ f i j:= by
      unfold f H pay; split_ifs; exact (hM j).2 U;rw [norm_zero]
    have hu:=(hv i).of_nonneg_of_le (fun i=> norm_nonneg (H i)) hx
    exact (norm_tsum_le_tsum_norm hu).trans (hu.tsum_le_tsum hx (hv i))
  let g := pay (fun i=> m i*debt p.B e (W i).extent) (fun i=> x∈ (W i).extent)
  have hz:= hm x
  let h (i : ValidX n) := P i*debt p.B e i.val
  refine (sum_pay u (fun z : ValidX n=> x∈ z.val) h (fun i=> mul_nonneg (he _) (Real.exp_pos _).le)).2 ?_
  refine le_trans (le_of_eq (b:=∑' i,g i) ?_) hz.2.2
  rw [← pack_all g (fun j=>city (W j)) hz.2.1]; apply sum_congr rfl; intro i _; split_ifs with H
  · unfold h P; rw [← tsum_mul_right]; apply tsum_congr; intro j; by_cases hh:city (W j)=i
    · simp only [pay,g,f,hh, ↓reduceIte]; have h : (W j).extent=i.val:= congr_arg Subtype.val hh; simp [h,H]
    simp only [g,f,pay,hh,↓reduceIte,zero_mul]
  symm; refine (tsum_congr (g:=fun _=>0) ?_).trans tsum_zero; intro j; unfold pay; split
  · rename_i hh; have h : x∉ (W j).extent:= by rw [show (W j).extent=i.val from congr_arg Subtype.val hh];exact H
    exact if_neg h
  rfl

def sizzle (p : Wickless G n τ) : Wickless G n τ where
  extent:=p.extent
  active:=p.active
  value U:= Real.exp (p.value U)-1
  inv i U:= by dsimp only; rw [p.inv i U]
  meas:= (Real.continuous_exp.measurable.comp p.meas).sub measurable_const
  sees U V a b:= by dsimp only; rw [p.sees U V a b]
  untouched U h:= by rw [p.untouched U h,Real.exp_zero,sub_self]

lemma broth [Fintype ι] {W : ι→ Wickless G n τ} {e u : ℝ} (H : Verse W p e u) (he : 0≤e) (hu : u ≤ 1/4):
    Verse (fun i=>sizzle (W i)) p e (2*u) := by
  obtain ⟨m,h,hM⟩:=H
  have ht (i) : m i ≤ u:= by
    obtain ⟨x,hx⟩:= (W i).active; let P:=pay (fun i=> m i*debt p.B e (W i).extent) (fun i=>x∈(W i).extent); have hf:= hM x
    have hp : ∑ v,P v ≤u := (tsum_fintype ..).symm.trans_le hf.2.2
    apply le_trans _ ((single_le_sum (fun j _=> hf.1 j) (mem_univ i)).trans hp)
    · change m i ≤ P i; unfold P pay; rw [if_pos hx]; exact le_mul_of_one_le_right (h _).1 (Real.one_le_exp (by positivity))
  refine ⟨fun i=> 2*m i,fun i=>⟨mul_nonneg (by positivity) (h _).1, fun U=> ?_⟩,fun i=> ?_⟩
  · let z:= (W i).value U
    have hh : |z| ≤ m i:= (h i).2 U
    have hb : |z|≤1:= hh.trans ((ht i).trans (hu.trans (by norm_num)))
    change |Real.exp z-1|≤_
    calc
      _ ≤ 2*|z| := ?_
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)
    have he := Real.abs_exp_sub_one_le hb
    exact he
  let T x:=pay (fun i=>m i * debt p.B e (W i).extent) (fun i=> x∈(W i).extent)
  have hp i : 0 ≤ 2*m i *debt p.B e (sizzle (W i)).extent:=by have hu:=h i|>.1;unfold debt; positivity
  apply (sum_pay (2*u) _ _ hp).2
  have H : (∑ x,T i x)≤u:=(tsum_fintype ..).symm.trans_le (hM i).2.2
  apply le_trans _ (mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ)≤2));rw [mul_sum]; apply sum_le_sum; intro x _
  dsimp only [T,pay,sizzle]; split_ifs; exact (mul_assoc ..).le; rw [mul_zero]

lemma Volunteer.winds {F : Config G n→ℝ} {e v : ℝ} (H : Volunteer F q e v) (he : 0≤e) (h : v ≤ 1/4) : ∃ W : ValidX n→ Wickless G n q.threshold,
    Garden W ∧ Verse W q e (2*v) ∧ ∀ U, Real.exp (F U)=∏ i, ( (W i).value U+1) := by
  obtain ⟨ι,hι,X,hX,hV,Hp⟩:=H
  refine ⟨fun i=> sizzle (pores X i), fun s x=> ?_, broth (poem hV he) he h, fun U=> ?_⟩
  · obtain ⟨P,h⟩:= pore_hymn hX s x; refine ⟨P,fun i => ⟨(h i).1,fun v=>?_⟩⟩
    dsimp only [sizzle]; rw [(h i).2]
  rw [Hp,← pack_all (fun i=> (X i).value U) (fun i=>city (X i)) (summable_verse hV he U),Real.exp_sum]
  apply prod_congr rfl;intro i hi; dsimp only [sizzle,pores]; rw [sub_add_cancel]
end YM.Next.Rank.Alarm
