import YM.UVExtension.Copse.Bole
import YM.Push.ABSOLUTE_SUMS.Clusters
/-! Any marked vertex in the full Ursell sum, with union cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Copse
open Function Lattice RG Push.AbsoluteSums Animals Ursell Trees Graph Relation Finset
open scoped Topology BigOperators Classical
variable {ι:Type*}{n:Side} (R:ι→ι→Prop) (X:ι→Support n)(B d:ℕ)
def priceV (u:ι→ℝ)(a:ℝ)(i:ι):= u i*worth d B a (X i)
lemma price_sign {u:ι→ℝ}(hu:∀ i,0≤u i)(a:ℝ)(i:ι) : 0≤priceV X B d u a i:=mul_nonneg (hu _) (Real.exp_pos _).le

private lemma test_none (ht : Tests R X) (m : ℕ) (z : Tuple ι m) (w u : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hu : ∀ i, 0 ≤ u i) (a : ℝ) :
    atVertex R (charge X B w a) (priceV X B d u a) none z ≤
      ∑ p : Fin m → Option (Fin m), hearth X B d w u a ⟨m,indexRoot z p⟩ := by
  let W := charge X B w a; let U := priceV X B d u a
  have hg := Graph.pay (pot R z)
  let P (p : Fin m → Option (Fin m)) : Prop := Graph.sprouts (pot R z) p
  let o := ∏ i : Option (Fin m), if i=none then U (z i) else W (z i)
  have he : o=U (z none)*∏ i : Fin m, W (z (some i)) := by simp [o,Fintype.prod_option]
  have hb : 0 ≤ o := he ▸ mul_nonneg (price_sign X B d hu ..) (prod_nonneg fun i _ => charge_pos X B hw ..)
  change |coefficient R z| * o/m.factorial ≤ _
  calc
    _ ≤ (∑ p, if P p then (1:ℝ) else 0)*o/m.factorial := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hg hb) (by positivity)
    _ ≤ _ := by
      rw [sum_mul,sum_div]; apply sum_le_sum; intro i _; split
      next h =>
        unfold hearth forestW; dsimp only; rw [forestWeight,if_pos (spanned R X ht h),Fintype.card_fin,
          he,one_mul,mul_div_assoc]; exact le_rfl
      next h => simpa only [zero_mul,zero_div] using hearth_nn X B d hw hu a ⟨m,indexRoot z i⟩

private lemma indexRoot_inj {m : ℕ} : Function.Injective
    (fun p : Tuple ι m × (Fin m → Option (Fin m)) => indexRoot p.1 p.2) := by
  rintro ⟨z,p⟩ ⟨w,q⟩ h
  have hp : p=q := congr_arg (fun x => x.2.1) h
  suffices he : z=w by rw [he,hp]
  funext i; cases i with
  | none => exact congr_arg (fun x => x.1) h
  | some j => exact congr_arg (fun x : RootAt ι m => x.2.2 j) h

private lemma budget_none (ht : Tests R X) {w u : ι → ℝ} {a γ δ q b : ℝ} (hu : ∀ i, 0 ≤ u i)
    (h : Ready X B w a γ δ q) (he : SumBudget (priceV X B d u (a+δ)) b)
    (m : ℕ) : SumBudget (fun z : Tuple ι m => atVertex R (charge X B w a) (priceV X B d u a) none z)
      (b*q^m) := by
  have hw := h.2.2.2.2.1
  have hh := budget_pull _ (@indexRoot_inj ι m) (hearth_k X B d hu h he m)
  let f := fun p : Tuple ι m × (Fin m → Option (Fin m)) => hearth X B d w u a ⟨m,indexRoot p.1 p.2⟩
  refine budget_of_sum (fun z => atVertex_pos R (charge_pos X B hw a) (price_sign X B d hu a) none z)
    fun s => ?_
  calc
    _ ≤ ∑ z∈s, ∑ p, f (z,p) := sum_le_sum fun z _ => test_none R X B d ht m z w u hw hu a
    _ = ∑ i∈s ×ˢ univ, f i := by rw [sum_product]
    _ ≤ _ := budget_sum hh _

lemma budget_root (ht : Tests R X) {w u : ι → ℝ} {a γ δ q b : ℝ} (hu : ∀ i, 0 ≤ u i)
    (h : Ready X B w a γ δ q) (he : SumBudget (priceV X B d u (a+δ)) b)
    (m : ℕ) (i : Option (Fin m)) :
    SumBudget (fun z : Tuple ι m => atVertex R (charge X B w a) (priceV X B d u a) i z) (b*q^m) := by
  let e := Equiv.swap i none
  let W := charge X B w a; let U := priceV X B d u a
  have he' : Function.Injective (fun z : Tuple ι m => z ∘ e) := fun z p h => by
    funext i; obtain ⟨i,rfl⟩ := e.surjective i; exact congr_fun h i
  have eq (z : Tuple ι m) : atVertex R W U i z = atVertex R W U none (z ∘ e) := by
    unfold atVertex
    rw [relabel R e z]; congr 2
    symm; apply Fintype.prod_equiv e; intro j
    by_cases h : j=none
    · rw [h]; simp [e]
    have he : e j ≠ i := by rw [← show e none=i by simp [e]]; exact e.injective.ne h
    simp only [h,he,↓reduceIte,Function.comp_apply]
  simp_rw [show ∀ z : Tuple ι m, atVertex R (charge X B w a) (priceV X B d u a) i z = _ from eq]
  exact budget_pull _ he' (budget_none R X B d ht hu h he m)


lemma pairpay {k:ℕ} (z:Tuple ι k)(j:Option (Fin k))(he:Tests R X) (hz:coefficient R z≠ 0): Copse.cover d B (unionOf X z) ≤ Copse.cover d B (X (z j))+ ∑ i∈univ.erase j, coverNumber B (X (z i)):= by
   apply Copse.priced d B (X ∘ z) _ (mem_univ j)
   let T:=pot R z; have hp:(connectedGroups T).Nonempty:=by
      by_contra hh; rw [not_nonempty_iff_eq_empty] at hh; exact hz (by change ∑ i∈connectedGroups T,_=(0:ℝ); rw [hh,sum_empty]) -- explicit
   obtain ⟨s,hs⟩:=hp; obtain ⟨hk,hs⟩:= belongs.mp hs; obtain ⟨p,g,hp⟩:= Breadth.build (Graph.link s) (fun _=>0) (hs none); have hh:Graph.sprouts T p:=⟨Breadth.growth_ranked hp.toGrowth,fun i=> ⟨(hp.edges i).1,hk (hp.edges i).2⟩⟩
   let S:=installed X (X (z none)) (z ∘ some); rw [show X∘z=S from funext fun k=> match k with | some _=> rfl| none=>rfl]; exact ⟨⟨none,mem_univ _⟩,fun i _ j _=> ReflTransGen.trans (Ac.swaps S (rooted_paths X (spanned R X he hh) i)) (rooted_paths X (spanned R X he hh) j)⟩
lemma convenience {k:ℕ} (z:Tuple ι k)(j:Option (Fin k)) (u w:ι→ℝ): atVertex R w u j z= |coefficient R z| *((∏ i∈univ.erase j,w (z i))*u (z j)) / (k.factorial:ℝ) :=by
  let f i:= if i=j then u (z i) else w (z i); change |coefficient R z| * (∏ i,f i)/_=_; rw [←Finset.prod_erase_mul _ _ (mem_univ j),show f j= _ from (if_pos rfl : f j=u (z j)),prod_congr rfl (show ∀ i∈univ.erase j, f i=w (z i) from fun i hi=> if_neg (ne_of_mem_erase hi))]
section
variable {f u:ι→ℝ} {a b δ γ q:ℝ} (he:Tests R X)(hh: Ready X B f a γ δ q)(ha:0≤ a)(hu:∀ i,0≤ u i) (hm:SumBudget (priceV X B d u (a+δ)) b)
include hh hu he ha
set_option quotPrecheck false
local notation "pA" => worth d B
lemma quoted {k:ℕ} (z:Tuple ι k)(j:Option (Fin k)): worth d B a (unionOf X z)*atVertex R f u j z ≤ atVertex R (charge X B f a) (priceV X B d u a) j z:=by
   rw [convenience,convenience,mul_div_assoc']; by_cases hP:coefficient R z=0; · simp [hP]
   let v:= ∏ i∈univ.erase j,f (z i); let r:= ∑ i∈univ.erase j,coverNumber B (X (z i)); let g:= |coefficient R z| * v * u (z j)
   unfold charge; rw [Finset.prod_mul_distrib]; apply div_le_div_of_nonneg_right _ (by positivity)
   have he' : pA a (unionOf X z) ≤ (∏ i∈ univ.erase j,currency B a (X (z i)))* pA a (X (z j)):= by
      unfold currency worth; rw [←Real.exp_sum,←Real.exp_add,←Finset.mul_sum,← mul_add]; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ ha; have hh:= Copse.pairpay R X B d z j he hP; rw [add_comm] at hh; exact_mod_cast hh
   have hf i:0≤f i:= hh.2.2.2.2.1 i
   unfold priceV; rw [show pA a (unionOf X z)*_=pA a (unionOf X z)*g from congr_arg (pA a _ *·) (by unfold g v; ring)]
   exact (mul_le_mul_of_nonneg_right he' (mul_nonneg (mul_nonneg (abs_nonneg _) (Finset.prod_nonneg (fun i _=> hf (z i)))) (hu _))).trans_eq (by ring)
-- coefficient derivative envelope
omit he hh ha hu
def center (f u:ι→ℝ) {k:ℕ} (z:Tuple ι k):=∑ j:Option (Fin k), atVertex R f u j z/ (k+1:ℕ)
lemma mid_pos {w :ι→ℝ}(hw:∀ i,0≤w i)(h:∀ i,0≤ u i) {k:ℕ}(z:Tuple ι k):0≤ center R w u z:= Finset.sum_nonneg (fun i _=> div_nonneg (atVertex_pos R hw h i z) (Nat.cast_nonneg _))
lemma tends (k:ℕ)(z:Tuple ι k)(f u:ι→ℝ) : center R f u z= |coefficient R z| *((k+1).factorial:ℝ)⁻¹ * ∑ i:Option (Fin k),(∏ j∈univ.erase i,f (z j))*u (z i):=by
   unfold center; rw [Finset.mul_sum]; simp_rw [convenience]; rw [Nat.factorial_succ]; push_cast; refine Finset.sum_congr rfl fun i _=>?_ ; field_simp
include hm hh hu he ha
lemma tangled : SumBudget (fun i:Clusters ι=>center R f u i.2*worth d B a (unionOf X i.2)) (b*(1-q)⁻¹):=by
   let g (j:Clusters ι):= center R f u j.2*worth d B a (unionOf X j.2)
   have hf i: 0≤ f i:= hh.2.2.2.2.1 i
   apply sigma_total g (fun n=> b*q^n) _ (budget_geometric (budget_nonneg hm) (ready_pos X B hh).le hh.2.2.2.1)
   intro k; let h j (z:Tuple ι k):= atVertex R (charge X B f a) (priceV X B d u a) j z; let N:ℝ:=(k+1:ℕ)
   have hN:0<N:=by unfold N; positivity
   refine budget_mono (budget_loosen (budget_scale (inv_pos.mpr hN).le (budget_over univ h (fun j=> b*q^k) (fun i _=>budget_root R X B d he hu hh hm k i))) ?_) (fun z=> mul_nonneg (mid_pos R hf hu z) (Real.exp_pos _).le) ?_
   · simp only [sum_const,card_univ,Fintype.card_option,Fintype.card_fin,nsmul_eq_mul]; exact (inv_mul_cancel_left₀ hN.ne' _).le
   intro z; unfold g h center; dsimp only; rw [Finset.sum_mul,mul_sum]; exact Finset.sum_le_sum (fun i _=> by rw [div_mul_eq_mul_div, mul_comm (atVertex R f u i z),inv_mul_eq_div]; exact div_le_div_of_nonneg_right (quoted R X B d he hh ha hu z i) hN.le)
end
end YM.UVExtension.Copse
