import YM.RG08.Arc.Linen
/-! # Arity conventions with t² foreground extracted. Positive grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f m : Side} (S : StepData c f) {G : Gauge} (T : Forest S.ratio) {n : ℕ}
variable {F : Air G}
lemma decks_z (h : Decked F) (r) : F 0 r=0 := not_ne_iff.mp (mt (h 0 r) fun hh=> (Nat.lt_irrefl _ hh.1).elim)
lemma sector_l (Q : Pot G 2) (h : Decked F) : sector Q F 0 1=0 := decks_z h _
lemma sector_t (Q : Pot G 2) (F : Air G) : sector Q F 0 2= Q := by simp [sector,prolong_self]
lemma sector_unique (Q : Pot G 2) (F : Air G) {j q e : ℕ} (h : 0<e) (hp : 0<j) (hg : j+2*q=e+2) : sector Q F q j=F e j := by
  match j with
  | 0=> omega
  | 1=> unfold sector; rw [show 1+2*q-2=e by omega]
  | j+2=> simp only [sector, if_neg (show ¬ j+2*q=0 by omega)]; rw [show j+2*q=e by omega]
lemma mnemonic (F : Pot G n) (t : ℝ) (z : Link G m) : stanza F m (t•z)=t^n * stanza F m z:= Tensor.homogeneous ..

def oblige (Q : Pot G 2) (F : Air G) (k : ℕ) (t : ℝ) (x : Link G m) := stanza Q m x + ∑ e∈range (k+1), t^e * grand (e+2) (F e) m x

def trimmed (k q : ℕ) := (range (k+2+1)).filter fun j => j+2*q ≤ k+2

lemma loopCount (Q : Pot G 2) (k : ℕ)(h : Decked F) (hg : Halt F) (t : ℝ) (x : Link G m) :
    ∑ q∈range (k+2+1), t^(2*q)*(∑ j∈trimmed k q, stanza (sector Q F q j) m (t•x)) = t^2 * oblige Q F k t x := by
  let P:= (range (k+2+1)) ×ˢ (range (k+2+1)); let L:=P.filter fun z:ℕ×ℕ=> z.2+2*z.1 ≤ k+2
  let s (p : ℕ×ℕ):= t^(p.2+2*p.1)* stanza (sector Q F p.1 p.2) m x
  rw [show ∑ q∈range (k+2+1), t^(2*q)*(∑ j∈trimmed k q, stanza (sector Q F q j) m (t•x))=∑ p∈L,s p from ?_]; swap
  · symm; unfold L P; rw [sum_filter, sum_product] -- not eq see
    apply sum_congr rfl; intro i hi
    unfold trimmed; rw [Finset.mul_sum, sum_filter]; apply sum_congr rfl; intro j hj; split; next hx=> unfold s; rw [mnemonic]; dsimp only; rw [pow_add]; ring
    next hx=>rfl
  let Y:= fun i:ℕ=> L.filter fun p=> p.2+2*p.1=i
  rw [← sum_fiberwise_of_maps_to (show ∀ p∈L,p.2+2*p.1∈ range (k+2+1) from fun p hp=>mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hp).2)) s]
  change ∑ i∈range (k+2+1), (∑ p∈Y i,s p)= _
  have hh i (hi:i<2) : ∑ p∈Y i, s p=0 := by
    apply sum_eq_zero; intro p hp; have hx:= (mem_filter.mp hp).2; obtain ⟨e,j⟩:=p; unfold s; dsimp only at *
    cases j with
    | zero=> rw [sector,stanza_zero]; simp only [Pi.zero_apply,mul_zero]
    | succ j=> rw [show e=0 by omega,show j=0 by omega,show 0+1=1 from rfl,sector_l _ h,stanza_zero]; simp only [Pi.zero_apply,mul_zero]
  have he : ∑ p∈Y 2,s p=t^2*stanza Q m x := by
    rw [sum_eq_single_of_mem (0,2) (show (0,2)∈Y 2 by simp [Y,L,P])]; unfold s; rw [sector_t]
    rfl
    intro i hi hv; have h:= (mem_filter.mp hi).2; obtain ⟨i,j⟩:=i
    have hh : j=0 := by dsimp only at h; by_contra hk; exact hv (Prod.ext (by dsimp;omega) (by dsimp; omega))
    rw [hh]; unfold s; dsimp only; rw [sector,stanza_zero]; simp only [Pi.zero_apply,mul_zero]
  rw [Finset.sum_range_succ', Finset.sum_range_succ', hh 0 (by omega),hh (0+1) (by omega), add_zero,add_zero]
  rw [oblige,mul_add,Finset.mul_sum,sum_range_succ',sum_range_succ',he,show grand (0+2) (F 0) m=0 by unfold grand; simp_rw [decks_z h]; simp,pow_zero]
  simp only [Pi.zero_apply,mul_zero,add_zero]; rw [add_comm,add_right_inj]
  apply sum_congr rfl; intro i hi
  let n:=i+1; let J:=Y (n+2)
  have hs : n ≤ k := (mem_range.mp hi)
  have hw p (hp:p∈J): p.2∈range (n+2+1):= mem_range.mpr (by have ht:=(mem_filter.mp hp).2; omega)
  change ∑ p∈J,s p=t^2*(t^n * (∑ j∈range (n+2+1), stanza (F n j) m) x)
  rw [← sum_fiberwise_of_maps_to hw s,Finset.sum_apply, Finset.mul_sum,Finset.mul_sum]
  apply sum_congr rfl; intro j hj
  by_cases hx : F n j ≠ 0
  · obtain ⟨hk,q,hq⟩:= h n j hx
    have hZ : 0<j := Nat.pos_of_ne_zero (by rintro rfl; exact hx (hg _))
    rw [sum_eq_single_of_mem (q,j) (show (q,j) ∈ J.filter (fun i=>i.2=j) by simp only [J,Y,L,P,mem_filter,mem_product, mem_range]; exact ⟨⟨⟨⟨by omega,by omega⟩,by omega⟩,hq.symm⟩, trivial⟩)]
    · unfold s; dsimp only; rw [sector_unique _ _ hk hZ hq.symm, ←hq,pow_add]; ring
    intro p hp hh; apply False.elim; obtain ⟨hv,hp⟩:=mem_filter.mp hp; have hj':=(mem_filter.mp hv).2; exact hh (Prod.ext (by dsimp; omega) hp)
  rw [not_ne_iff.mp hx, stanza_zero, Pi.zero_apply,mul_zero,mul_zero]; apply sum_eq_zero; intro p hp
  obtain ⟨ht,hl⟩:= mem_filter.mp hp; obtain hp:= (mem_filter.mp ht).2
  by_cases hh : j=0
  · unfold s; rw [hl,hh,sector,stanza_zero]; simp only [Pi.zero_apply,mul_zero]
  unfold s; rw [sector_unique _ _ (by unfold n; omega) (by omega) hp,hl,not_ne_iff.mp hx,stanza_zero]; simp only [Pi.zero_apply,mul_zero]
end YM.RG08.Reflect
