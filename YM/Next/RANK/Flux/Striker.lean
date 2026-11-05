import YM.Next.RANK.Flux.Radar
import YM.Next.RANK.Flux.Storm

/-!
# Aggregate support at owned marker. Ledger recipes for tag choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory
open scoped BigOperators Classical

variable {V ι κ α β : Type*} {G : Gauge} {n : Side} [DecidableEq V] [Fintype V] {ζ : V→ Site n} {t e a b y : ℝ}
variable (S : ι→ Plug G ζ t) (P : κ→Lining G ζ t)

-- generic pivot-report aggregation
section
variable [Fintype ι] [Fintype κ] (v : ι→ℝ) (w : κ→ℝ)
omit [Fintype ι] [Fintype κ] in
theorem promote (A : Finset ι) (B : Finset κ) (R : ι→κ→ Prop) (h : ∀ i∈A,0≤ v i) (he : ∀ i∈A, ∃ j∈B, R i j)
    (hp : ∀ j∈B,∀ s⊆A,(∀ i∈s,R i j)→ ∑ i∈s,v i ≤ w j) :
    ∑ i∈A,v i≤ ∑ j∈B,w j:= by
  let x (i : ι) (j : κ) := if R i j then v i else 0
  have ht:∑ i∈A,v i ≤ ∑ i∈A,∑ j∈B,x i j:= by
    refine sum_le_sum fun i hi=>?_; obtain ⟨j,hj,hQ⟩:=he i hi
    exact (le_trans (le_of_eq (show x i j=v i from if_pos hQ).symm) (single_le_sum (f:=x i) (fun t _=> by unfold x;split;exact h i hi; exact le_rfl) hj))
  apply ht.trans;rw [sum_comm]; refine sum_le_sum fun j hj=> ?_; unfold x;rw [← Finset.sum_filter]; exact hp j hj _ (filter_subset ..) (fun _ h=> (mem_filter.mp h).2)

lemma report1 (s : ι→ Plug G ζ t) (f : Party s P→ℝ) (g : ι ⊕ κ→ℝ) (h : ∀ i,0 ≤ f i) (A : Bright (panel s P)→Prop) (B : ι⊕κ → Prop) (m : BudgetPoint) (b : ℝ)
    (ht : ∀ i,A i → ∃ j∈i.val.val,B j) (hp : ∀ i,∀ L : Finset (Party s P),(∀ j∈L,i∈j.val)→
      ∑ j∈L,alarm (lamps s P) f m.B b j ≤ alarm (dish s P) g m.B (b+1) i) :
    strike (feet (sunny (panel s P))) (f ∘ Subtype.val) m A b ≤ strike (dish s P) g m B (b+1):= by
  let V:=panel s P; let Z:=univ.filter A; let w:=sunny V; let r:= alarm (feet w) (f ∘ Subtype.val) m.B b; change (∑ i∈Z,r i) ≤ _
  have hz (U : Finset (Bright V)) : ∑ i∈U,r i = ∑ j∈ U.image Subtype.val,alarm (lamps s P) f m.B b j:= by
    rw [sum_image Subtype.val_injective.injOn];apply sum_congr rfl;intro j _; have ht:(feet w j)=lamps s P j.val:= by
      have hv:=bright_valid V j; rw [← pan_extent];change _=(V j.val).extent; rw [hv];rfl
    dsimp only [r,alarm]; rw [ht];rfl
  refine promote r (alarm (dish s P) g m.B (b+1)) _ _ (fun i j=> j∈i.val.val) (fun i _=>alarm_pos (feet w) (f ∘ Subtype.val) _ b (fun i=> h i.val) _) (fun i hi=>?_) (fun j hj u hu H=>?_)
  · obtain ⟨j,hj,H⟩:=ht _ (mem_filter.mp hi).2; exact ⟨j,mem_filter.mpr ⟨mem_univ _,H⟩,hj⟩
  rw [hz];apply hp;intro i hi; obtain ⟨b,hp,rfl⟩:=mem_image.mp hi; exact H b hp
end
variable [Fintype ι]
section
variable [DecidableEq ι] (X : ι→ SourceAt G ζ) (p : ι→ℝ) (A : BudgetPoint)
-- raw LOG cap weights sans exponent

def hlog (s : MergeLog X):= ‖majesty (feet X) s.val‖ * ∏ i∈s.val,p i
lemma hlog_pos (h : ∀ i,0≤p i) s : 0 ≤ hlog X p s:= mul_nonneg (norm_nonneg _) (prod_nonneg fun _ _=>h _)
-- distinguish by consumes a member
lemma expire {R : ι→Prop} {F : MergeLog X→Prop} (H : ∀ i,F i →∃ j∈i.val,R j) (he : ∀ i,0 ≤ p i) (h : Hits (feet X) p A (e+1) y) (hz : ((A.B+A.B+1:ℕ):ℝ)^4*y ≤ 1) (hy : 0≤y) (hp : 0≤e) :
    strike (feet (Bond X)) (hlog X p) A F e ≤ strike (feet X) p A R (e+1):= by
  let B:=alarm (feet (Bond X)) (hlog X p) A.B e;let V:= univ.filter F
  apply promote B (alarm (feet X) p A.B (e+1)) V (univ.filter R) (fun i j=>j∈ i.val)
  · exact fun i _=>alarm_pos _ _ _ _ (hlog_pos X p he) i
  · intro i hi; obtain ⟨b,hb,hQ⟩:=H _ (mem_filter.mp hi).2; exact ⟨b,mem_filter.mpr ⟨mem_univ _,hQ⟩,hb⟩
  intro j _ T hT hh; let q:=honey (feet X) p A.B e
  apply le_trans (b:=∑ s∈T.image Subtype.val,q s)
  · rw [Finset.sum_image Subtype.val_injective.injOn];exact sum_le_sum fun i _=> flattened e A (feet X) i.val p he hp
  apply le_trans _ (all_marks (feet X) p A.B e univ j he (quotas (feet X) p A he h) hz hy); refine sum_le_sum_of_subset_of_nonneg ?_ fun i _ _=> honey_pos _ p _ _ he _
  intro i hi; obtain ⟨a,hb,rfl⟩:=mem_image.mp hi; exact mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),hh a hb⟩
end

lemma supple (X : ι→ Support n) (v : ι→ℝ) (m : BudgetPoint) (p q : ι→Prop) (e : ℝ) (h : ∀ i,p i → q i) (he : ∀ i,0 ≤ v i): strike X v m p e ≤ strike X v m q e:= sum_le_sum_of_subset_of_nonneg (fun i hx=>mem_filter.mpr ⟨mem_univ _,h i (mem_filter.mp hx).2⟩) (fun _ _ _=> alarm_pos X v m.B e he _)
lemma drill [Fintype κ] (X : ι→ Support n) (p : κ→ Support n) (f : ι→ℝ) (g : κ→ℝ) (A : BudgetPoint) (R : ι⊕κ→ Prop) :
    strike (Sum.elim X p) (Sum.elim f g) A R e = strike X f A (R ∘ Sum.inl) e+strike p g A (R ∘ Sum.inr) e:= by unfold strike; rw [Finset.sum_filter,Fintype.sum_sum_type,Finset.sum_filter,Finset.sum_filter]; congr
lemma locus [Fintype κ] (K : ι⊕κ→Support n) (f : ι⊕κ→ℝ) (A : BudgetPoint) (R : ι⊕κ→Prop): strike K f A R e = strike (K ∘ Sum.inl) (f∘ Sum.inl) A (R∘Sum.inl) e+strike (K∘ Sum.inr) (f∘ Sum.inr) A (R∘Sum.inr) e:= by unfold strike;rw [Finset.sum_filter,Fintype.sum_sum_type,Finset.sum_filter,Finset.sum_filter];congr
lemma subtype_strike (H W : ι→ Prop) (s : ι →Support n) (f : ι → ℝ) (A : BudgetPoint) (e : ℝ) [DecidablePred H] :
    strike (fun i:{i// H i}=> s i.val) (fun i : {i// H i}=> f i.val) A (W ∘ Subtype.val) e= strike s f A (fun i=>H i∧W i) e:= by
  unfold strike; rw [Finset.sum_filter]; let b j:= alarm s f A.B e j
  let F j:= if W j then b j else 0
  have he : (∑ i : {i// H i}, F i.val)=∑ i∈univ.filter H,F i:= (sum_subtype _ (fun _=>by simp) F).symm
  apply Eq.trans _ (Eq.trans he _);swap
  · unfold F;rw [← Finset.sum_filter]; apply sum_congr _ (fun i _=>rfl); ext; simp
  apply sum_congr rfl; intro i hi; simp only [Function.comp_apply];split_ifs with h <;> unfold F <;> simp only [h,↓reduceIte] ; rfl
end YM.Next.Rank.Flux
