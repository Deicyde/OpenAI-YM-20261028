import YM.WilsonBulk.Transit.Bureau

set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical BigOperators ENNReal
open Function Filter Finset Pert.Bulk Lattice
variable {X Y : Type} {D : Rule X} {E : Rule Y} {σ θ p q δ M : ℝ} {e n : ℕ}
variable {d A B : Duct X Y} {F F' : Legs (Duct X Y) (n+1)} {u v : Page X (n+1)}

lemma overline (g : Geometry D E θ σ d) (he : ∀ i, AuditLine (F i) d (n+1) p q) (hf : ∀ i, AuditLine (F' i) d (n+1) p q)
    (i : Fin (n+1)) (hi : AuditLine (F i-F' i) d (n+1) (p*δ) (q*δ))
    (hh : ∀ j, j≠i→ F j= F' j) (hu : Within D θ M u) (hs : 0≤σ) : Within E σ (q*p^n*M*δ) (tele F u-tele F' u) := by
  rw [tele_sub_line g he hf hu hs i hh]
  let d' : Fin (n+1)→ℝ := Pi.mulSingle i δ
  let r (j : Fin (n+1)) := p*d' j; let t (j:Fin (n+1)):=q*d' j
  have e (j:Fin (n+1)): AuditLine ((Function.update F i (F i-F' i)) j) d (n+1) (r j) (t j):= by
    unfold r t; by_cases h : j=i
    · subst j; simpa [d']
    simpa [d',h] using he j
  refine fare g e hu fun j=>Eq.le ?_
  have hz (i : Fin (n+1)) : (univ.erase i).card=n:= by rw [card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin]; omega
  have hv : d' j * (∏ i∈univ.erase j,d' i)=δ := by rw [mul_prod_erase _ _ (mem_univ j)]; simp [d']
  unfold r t; rw [prod_mul_distrib,prod_const,hz,← hv]; -- avoid rewrite d' changes inside
  ring

def blend (F F' : Legs (Duct X Y) n) (s : Finset (Fin n)) : Legs (Duct X Y) n := fun i=> if i∈s then F i else F' i
lemma tele_delta (g : Geometry D E θ σ d) (he : ∀ i, AuditLine (F i) d (n+1) p q) (hf : ∀ i, AuditLine (F' i) d (n+1) p q)
    (h : ∀ i, AuditLine (F i-F' i) d (n+1) (p*δ) (q*δ)) (hu : Within D θ M u) (hs : 0≤σ) : Within E σ (((n+1:ℕ):ℝ)*(q*p^n*M*δ)) (tele F u-tele F' u) := by
  let s := q*p^n*M*δ
  have hr (t : Finset (Fin (n+1))) (i : Fin (n+1)) : AuditLine (blend F F' t i) d (n+1) p q := by unfold blend; split; exacts [he _,hf _]
  suffices ∀ t : Finset (Fin (n+1)), Within E σ ((t.card:ℝ)*s) (tele (blend F F' t) u-tele F' u) by simpa [s,show blend F F' univ=F from funext fun i=>if_pos (mem_univ i)] using this univ
  intro t; induction t using Finset.induction with
  | empty=> simp only [show blend F F' ∅= F' from funext fun i=> if_neg (notMem_empty i), sub_self, card_empty,Nat.cast_zero,zero_mul]; exact Within.zero le_rfl
  | insert a t ht ih =>
    have hi : AuditLine (blend F F' (insert a t) a-blend F F' t a) d (n+1) (p*δ) (q*δ) := by simpa [blend,ht] using h a
    have hh := overline g (hr (insert a t)) (hr t) a hi (by intro j hj;simp [blend,hj]) hu hs -- metavars
    rw [card_insert_of_notMem ht,Nat.cast_add,Nat.cast_one,add_mul,one_mul];
    exact Eq.mp (congr_arg (Within E σ ((t.card:ℝ)*s+s)) (show _ = _ from (add_comm (tele (blend F F' t) u - tele F' u) (tele (blend F F' (insert a t)) u - tele (blend F F' t) u)).trans (sub_add_sub_cancel ..))) (ih.add hh)
lemma options_tele (g : Geometry D E θ σ d) (he : ∀ i, AuditLine (F i) d (n+1) p q) (hf : ∀ i, AuditLine (F' i) d (n+1) p q)
    (h : ∀ i, AuditLine (F i-F' i) d (n+1) (p*δ) (q*δ)) (hu : Options D θ δ M u v) (hs : 0≤σ) : Options E σ δ (((n+2:ℕ):ℝ)*(q*p^n*M)) (tele F u) (tele F' v) := by
  let a : ℝ := q*p^n*M
  have hc : a ≤ ((n+2:ℕ):ℝ)*a := le_mul_of_one_le_left (mul_nonneg (mul_nonneg (he 0).floor (pow_nonneg (he 0).height _)) hu.baseline) (by norm_cast; omega)
  refine ⟨hu.nonneg,(fare_const g he hu.plus).mono le_rfl hc,(fare_const g hf hu.minus).mono le_rfl hc,?_⟩
  rw [show δ*_ = q*p^n*(δ*M) + ((n+1:ℕ):ℝ)*(q*p^n*M*δ) by push_cast;ring,← sub_add_sub_cancel (tele F u) (tele F v) _, ← tele_sub g he hu.plus hu.minus hs]; exact (fare_const g he hu.variation).add (tele_delta g he hf h hu.minus hs)
end YM.WilsonBulk.Sheet
