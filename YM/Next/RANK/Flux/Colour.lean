import YM.Next.RANK.Flux.Valor

/-! Isolating burnt contribution with ANY-marker contour. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes
open scoped BigOperators Classical

variable {V ι κ α β : Type} {G : Gauge} {n : Side} [DecidableEq V] [Fintype V] {ζ : V→ Site n} {t e a b x y z d : ℝ}
variable [Fintype ι] [Fintype κ] [Fintype α]
variable {Q : BudgetPoint}

lemma earns_here (s : ι→ SourceAt G ζ) (q : ι→ℝ) (v : ι→Prop) [DecidablePred v] (M : ℝ) (h : ∀ i,0≤ q i) (p : V →ℝ) (ht : 1 ≤ M) (hp : e≤b)
    (hR : ∀ i,v i →∀ U : Config G n,M*Poly.price p ((s i).amount Q.threshold U) ≤ q i)
    (H : ∀ i : V, strike (feet s) q Q (fun j=>i∈(s j).fires.val) b ≤ d) :
    Shine (fun i:{i// v i}=>s i.val) Q p e (d/M) := by
  let f i:= alarm (feet s) q Q.B e i; let w:= alarm (feet s) q Q.B b
  have hF i:0≤ f i:= alarm_pos _ q _ _ h _; have hh : 0 < M:= zero_lt_one.trans_le ht
  have hw i:f i≤w i:=mul_le_mul_of_nonneg_left (Real.exp_monotone (by apply mul_le_mul_of_nonneg_right hp;positivity)) (h i)
  refine ⟨fun i=> f i.val / M, fun i=> ⟨div_nonneg (hF _) hh.le,fun U he=> ?_⟩,fun i=>?_⟩
  · have hx:=hR i.val i.property U
    rw [SourceAt.amount,Poly.solo,masked_eq _ _ _ _ he] at hx
    apply (le_div_iff₀ hh).2;apply le_trans _ (mul_le_mul_of_nonneg_right hx (Real.exp_pos (e*coverNumber Q.B (feet s i.val))).le); unfold charge feet; exact le_of_eq (by ring)
  rw [← sum_filter, ← Finset.sum_div]; apply div_le_div_of_nonneg_right _ hh.le; apply le_trans _ (H i)
  let Z:= univ.filter fun b:{b//v b}=>i∈(s b.val).fires.val
  let U:= Z.map (Function.Embedding.subtype v)
  apply le_trans (b:=∑ j∈ U,w j); rw [Finset.sum_map]
  · apply sum_le_sum;intro j _; exact hw _
  rw [show strike (feet s) q Q (fun j=>i∈(s j).fires.val) b=∑ j∈ univ.filter (fun j=>i∈(s j).fires.val),w j from sum_congr (Finset.ext fun _=> by simp) (fun _ _=>rfl)]
  refine sum_le_sum_of_subset_of_nonneg (fun j hj=> ?_) fun j _ _=> alarm_pos _ q _ _ h _
  obtain ⟨u,hu,rfl⟩:= mem_map.mp hj; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hu).2⟩

variable (S : ι→ Plug G ζ Q.threshold) (P : κ → Lining G ζ Q.threshold) {F : α → CoverReads G ζ Q.threshold}
variable {f : ι⊕κ→ ℝ} {g : α→ℝ}
variable (u : ι→Prop) {r : V→ℝ} (hr : ∀ i,0 < r i) {M L : ℝ} (hM : 1 ≤ M) (hL : 1 ≤ L)

-- preserve type.F.Basis. Dirty test only on members with prior anchor

def rawclean (i : MergeLog (sunny (panel S P))) := ∀ j∈i.val,clean S P u j.val
variable (T : Tickets Q y) (hv : 0≤ e) (H' : flat P) (h : Authorship S P F f g u r e M L y z)
include hr hM hL hv T h H'

lemma heard : let X:= panel S P; let D:= sunny X; let B:=Bond D
    Shine (B ∘ Subtype.val (p:=rawclean S P u)) Q r e z ∧
      Shine (B ∘ Subtype.val (p:=fun i=>¬ rawclean S P u i)) Q r e (z/L):= by
  intro X D B
  let k:=e+1+1+1;let A:=Pay1 S P f; let W:=fun j:Bright X=> A j.val
  let q := hlog D W
  have hx :=budget_squeeze S P u f _ hL hM hr h.regular h.late; have ht i V : factor (¬ rawclean S P u i) L* Poly.price r ((Bond D i).amount Q.threshold V) ≤ q i:= by
    have hz := bond_factor (fun i:Bright X=> clean S P u i.val) D Q.threshold W r hr hL i V (fun i=> hx.1 i V)
    change factor (¬∀ j∈i.val,clean S P u j.val) L*_ ≤ _; exact hz
  have he i:0≤A i:=panda_pos S P _ _ h.earned;have hf i:0≤W i:=he _; have hq:=hlog_pos D W hf
  have hp:0≤k:=by unfold k;linarith only [hv]
  have hh (i:V) : strike (feet B) q Q (fun j=> i∈(B j).fires.val) k ≤ z:= by
    obtain ⟨hh,-⟩:=reaches S P Q f h.earned (show Hits (dish S P) f Q (k+1+1) y from h.cost) T.day (by linarith only [hp])
    have H: strike (feet D) W Q (fun j=> i∈(D j).fires.val) (k+1) ≤ z:= candles S P Q _ h.earned z H' (show Hits _ _ Q (k+1+1) y from h.cost) T.day (by linarith only [hp]) h.roots i
    apply le_trans _ H; apply expire D W Q (fun _ hx=>mem_biUnion.mp hx) hf hh T.total.grain T.total.day hp
  have hm:e≤k:=by unfold k; linarith only
  constructor
  · have hs i (hi : rawclean S P u i) V : 1*Poly.price r ((B i).amount Q.threshold V) ≤ q i:= by
      have hc:=ht i V; unfold factor at hc;rw [if_neg (show ¬¬ _ from not_not_intro hi)] at hc;exact hc
    rw [← div_one z]; exact earns_here B q (rawclean S P u) 1 hq r le_rfl hm hs hh
  refine earns_here B q (fun j=> ¬rawclean _ _ u j) L hq r hL hm ?_ hh
  intro i hi U; have h:=ht i U; unfold factor at h; rw [if_pos hi] at h; exact h
end YM.Next.Rank.Flux
