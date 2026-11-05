import YM.RG08.Forms.Pontoon

noncomputable section
namespace YM.RG08.Forms
open Pert.Bulk Packets Finset Function
open scoped BigOperators Topology ENNReal Classical
set_option autoImplicit false
variable {I J:Type}{n:ℕ}

def crossfire (K K':Cables n I J) (i:Fin n):Cables n I J:=fun j=>if j=i then K j-K' j else if j < i then K' j else K j

theorem firing (K K':Cables n I J)(F F':Flake n I)(y:Tape n J)(x:Tape n I) : vat K F y x-vat K' F' y x= vat K (F-F') y x +∑ i,vat (crossfire K K' i) F' y x:=by
 have he:=Finset.prod_sub_ordered (univ:Finset (Fin n)) (fun i=> K i (x i) (y i)) (fun i=> (K-K') i (x i) (y i))
 dsimp only [Pi.sub_apply] at he
 simp only [sub_sub_cancel] at he
 let h K (i:Fin n):ℝ:= (K:Cables n I J) i (x i) (y i)
 have hh (i:Fin n):design (crossfire K K' i) x y=(h K i-h K' i)* (∏ j∈univ.filter (fun j=>j < i),h K' j) * ∏ j∈univ.filter (fun j:Fin n=>i<j), h K j:=by
   unfold design;rw [←mul_prod_erase _ _ (mem_univ i)]
   let s:=univ.erase i
   have hl:univ.filter (fun j:Fin n=>j < i)= s.filter (fun j:Fin n=>j < i):=by ext j;simp [s];exact fun h=>ne_of_lt h
   have hr:univ.filter (fun j:Fin n=>i<j)= s.filter (fun j:Fin n=> ¬j < i):=by
     ext j;simp [s];constructor
     · intro he; exact ⟨ne_of_gt he,he.le⟩
     rintro ⟨he,hj⟩;exact lt_of_le_of_ne hj (Ne.symm he)
   have hs:(∏ j∈s,crossfire K K' i j (x j) (y j))=(∏ j∈s,if j < i then h K' j else h K j):=prod_congr rfl fun j hj=>by by_cases hc:j < i<;>simp [hc] <;>simp [crossfire,h,hc,(mem_erase.mp hj).1]
   simp only [← show s=univ.erase i from rfl,hl,hr]
   rw [hs,Finset.prod_ite];simp only [crossfire,h,ite_true, Pi.sub_apply,mul_assoc]
 unfold vat;change F x * (design K x y) - F' x * (design K' x y)=_+∑ i,F' x*design (crossfire K K' i) x y
 simp_rw [hh,←Finset.mul_sum]
 dsimp [h,design] at *
 rw [he];ring

variable {K K' E:Cables n I J}{d:Ground I}{D:Ground J}{σ τ δ C P:ℝ}{F F':Flake n I}
/-- geometry checked also on mixed and difference lines; easier to state by disjunction in
positions. -/
def shows (d:Ground I)(D:Ground J)(σ τ :ℝ)(E K K':Cables n I J):Prop:=∀ A:Cables n I J,(∀ i x y,A i x y≠0→K i x y≠0∨K' i x y≠0) → lighthouse d D σ τ E A

structure Alley (d:Ground I)(D:Ground J)(σ τ δ P:ℝ)(E K K':Cables n I J):Prop where
 gain : 0≤P
 near : street E K fun _=>P
 far : street E K' fun _=>P
 change : street E (K-K') fun _=>P*δ
 lights : shows d D σ τ E K K'

lemma Alley.self (h:Alley d D σ τ δ P E K K') : lighthouse d D σ τ E K:=h.lights _ fun _ _ _ he=>Or.inl he
lemma Alley.other(h:Alley d D σ τ δ P E K K'):lighthouse d D σ τ E K':=h.lights _ fun _ _ _ he=>Or.inr he
lemma Alley.fire(h:Alley d D σ τ δ P E K K')(i:Fin n):lighthouse d D σ τ E (crossfire K K' i) := by
 apply h.lights; intro j x y; unfold crossfire; split_ifs
 · contrapose!; simp_all
 · exact Or.inr
 exact Or.inl
lemma Alley.street(h:Alley d D σ τ δ P E K K')(i:Fin n) : street E (crossfire K K' i) fun j=> if j=i then P*δ else P:=by
 intro j; obtain rfl|hz:=eq_or_ne j i; · simpa [crossfire] using h.change j
 by_cases hh:j < i
 · simpa [crossfire,hz,hh] using h.far j
 simpa [crossfire,hz,hh] using h.near j

lemma Cot.rafts (hn : 0<n)(hc:Cot d σ δ C F F')(hk:Alley d D σ τ δ P E K K')(hδ:0≤δ):
    raft K F-raft K' F'=raft K (F-F')+∑ i,raft (crossfire K K' i) F':=by
 ext y
 have he: Summable (vat K F y):=(raft_sum hn hc.near hc.gain hk.self hk.near y).of_norm
 have hf: Summable (vat K' F' y):=(raft_sum hn hc.far hc.gain hk.other hk.far y).of_norm
 have hd:Summable (vat K (F-F') y):=(raft_sum hn hc.compare (mul_nonneg hc.gain hδ) hk.self hk.near y).of_norm
 have hs (i):Summable (vat (crossfire K K' i) F' y):=(raft_sum hn hc.far hc.gain (hk.fire i) (hk.street i) y).of_norm
 unfold raft;rw [Pi.sub_apply,Pi.add_apply,Finset.sum_apply,← he.tsum_sub hf]
 change (∑' x,(vat K F y x-vat K' F' y x))=(∑' x,vat K (F-F') y x)+∑ i,∑' x,vat (crossfire K K' i) F' y x
 rw [← Summable.tsum_finsetSum (fun i _=>hs i)] -- ?
 simp_rw [firing]
 have ht:=summable_sum (s:=univ) fun i _=>hs i -- ?
 exact hd.tsum_add ht

lemma Cot.raft (hc:Cot d σ δ C F F')(hk:Alley d D σ τ δ P E K K')(hδ:0≤δ): Cot D τ δ ((n+1)*C*P^n) (raft K F) (raft K' F'):=by
 have he:=hc.gain;have hv:=hk.gain
 rcases eq_or_ne n 0 with hh|hh
 · subst hh;exact Cot.scalar _ (by positivity)
 have ha:C*∏ _: Fin n,P ≤ ((n:ℝ)+1)*C*P^n:=by simp;nlinarith [mul_nonneg he (pow_nonneg hv n),Nat.cast_nonneg (α:=ℝ) n]
 refine ⟨by positivity,(hc.near.raft he hk.self hk.near).mono le_rfl ha (fun _=>le_rfl),(hc.far.raft he hk.other hk.far).mono le_rfl ha (fun _=>le_rfl),?_⟩
 rw [hc.rafts (Nat.pos_of_ne_zero hh) hk hδ] -- args?
 let A:ℝ:=C*P^n*δ
 have hA:0≤A:=by unfold A;positivity
 have hx : Held D τ A (Forms.raft K (F-F')):=by
   convert hc.compare.raft (mul_nonneg hc.gain hδ) hk.self hk.near using 1;simp [A];ring
 have ht (i):Held D τ A (Forms.raft (crossfire K K' i) F'):=by
   convert hc.far.raft he (hk.fire i) (hk.street i) using 1
   unfold A; rw [←mul_prod_erase _ (fun j=> if j=i then P*δ else P) (mem_univ i)]
   rw [if_pos rfl,prod_eq_pow_card (b:=P) (by intro j hj;exact if_neg (mem_erase.mp hj).1),card_erase_of_mem (mem_univ ..),card_univ,Fintype.card_fin]
   nth_rw 1 [show n=n-1+1 by omega]
   rw [pow_succ];ring
 convert hx.add (Held.sum univ _ _ (fun _ _=>hA) (fun i _=>ht i)) hA (Finset.sum_nonneg fun _ _=>hA) using 1;simp [A];ring

end YM.RG08.Forms
