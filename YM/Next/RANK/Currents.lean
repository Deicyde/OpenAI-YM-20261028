import YM.Next.RANK.Camps
import YM.Next.RANK.Crust
import YM.Next.RANK.Walked

/-!
# Survival on W shapes through cuts
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Cells Station Ac Alarm Thirst Corona Value Finset
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {S : Schedule} {C : Family G} {A : Levels G} {i k l j m p q n D N d : ℕ}
variable (x : Points n) {s : ℝ} (R : Lead G A.S p)

structure Mote (R : Lead G A.S p) (i : ℕ) : Prop where
  foley j u : (R i).Q.cov j u ≠ 0 → separation (((A.clock.op i p).ratio).parent j.1) (((A.clock.op i p).ratio).parent u.1) ≤ (walls (clim A i))
  pole j t : t∈ ((R i).H j).support → separation (((A.clock.op i p).ratio).parent j.1) t.1 ≤ (walls (clim A i))

variable (P : Fin n→ poly (Chamber G A.S k p)) (h : roomTest A s k p d q) (hi : middle A s k ≤ j)
variable (hd : ∀ i,middle A s k ≤ i → i < k → Mote (A:=A) R i)
variable (hp : ∀ i,∀ f∈(P i).vars, fog A x s p 8 ((walls (clim A k))) (show k≤k from le_rfl) i f)

-- nonzero single has base stencil big; step shrinks even when j→j-1 near Δ stage. store two bounds whole payload

include h hd hp hi
lemma axis_room (hk : j≤k) (u : Fin n) : ∀ f∈(polygon R P hk (Sum.inl u)).vars, fog A x s p 8 ((walls (clim A j))) hk u f:= by
  induction hk using Nat.decreasingInduction with
  | self=> intro i hh; rw [polygon,oneRoot,center_shelf] at hh; exact hp u i hh
  | of_succ j hj ih=>
    have hz : middle A s k ≤ j+1:= hi.trans (Nat.le_succ _)
    let V:= R j; let a := (fun (z : Chamber G A.S j p) => fog A x s p 8 ((walls (clim A j))) hj.le u z); let F:=univ.filter a
    let U := polygon R P (show j+1≤k from hj) (Sum.inl u)
    rw [page R P hj]
    intro i hH; apply And.right (a:=i∈ (univ : Finset _))
    apply mem_filter.mp; apply pipe_vars V.H V.Q U F _ hH; intro i hw v hv; refine mem_filter.mpr ⟨mem_univ _,?_⟩
    let O:= core A x s p (show j+1≤k from hj) u
    change separation _ _ ≤ 8*_ ; rw [itinerary _ _ _ p hj]
    have he := ih hz i hw
    let b:= ((walls (clim A (j+1)))); have hh:separation O i.1≤ q*b:= le_trans he (Nat.mul_le_mul_right _ (le_trans (Nat.le_trans (by norm_num : 8 ≤ 10) h.parent) ((Nat.le_add_right d 10).trans h.radius)))
    have hp:=spends_aloft A h hj hi O i.1 hh
    have hf:=separation_triangle (((A.clock.op j p).ratio).parent O) (((A.clock.op j p).ratio).parent i.1) v.1
    apply hf.trans ((add_le_add hp ((hd j hi hj).pole i v hv)).trans ?_); omega

-- pair interactions independent at a step if far, and remain near if inherited pair existed.
set_option maxHeartbeats 500000 in
lemma pole_room (hk : j≤k) (t : Twin n) :
    let F:= polygon R P hk (Sum.inr t)
    (¬cozy A x s p d ((walls (clim A j))) hk (Sum.inr t) → F=0)∧ ∀ f∈ F.vars, fog A x s p (d+8) ((walls (clim A j))) hk t.val.1 f:= by
  induction hk using Nat.decreasingInduction with
  | self=> simp only [polygon,twoRoot,oneRoot,center_shelf,sub_self,vars_0,notMem_empty,false_imp_iff,and_self, imp_true_iff]
  | of_succ j hj ih=>
    let g:j+1≤k:=hj; let W:=polygon R P g; let H:= polygon R P hj.le; let w:=t.val.1; let v:=t.val.2
    intro F
    have hz:= hi.trans (Nat.le_succ _); obtain ⟨h1,h2⟩:= ih hz
    let ξ:= core A x s p g; let η:=core A x s p hj.le; let l:=(A.clock.op j p).ratio; let b:=(walls (clim A j)); let B:= (walls (clim A (j+1)))
    have he a:η a=l.parent (ξ a):=itinerary A x s _ hj _
    let Q:= R j
    have hW:F= Q.read (W (.inr t)) + Q.read (W (.inl w)*W (.inl v)) - H (.inl w) * H (.inl v):= second_page R P hj t
    have h₁:d+8 ≤q:= (show d+8≤d+10 by omega).trans h.radius
    have hV a r (hB : separation (ξ a) r ≤ (d+8)*B) : separation (η a) (l.parent r) ≤ b:= he a ▸ spends_aloft _ h hj hi _ _ (hB.trans (Nat.mul_le_mul_right _ h₁))
    have hx a i (hb : i∈(W (.inl a)).vars) : separation (η a) (l.parent i.1) ≤ b:= by
      have he':=axis_room (A:=A) x R P h hz hd hp g a i hb
      exact hV a _ (le_trans he' (Nat.mul_le_mul_right _ (Nat.le_add_left ..)))
    by_cases hh:cozy A x s p d b hj.le (.inr t)
    swap
    · have hF : F=0:= by
        have hf:d*b< separation (η w) (η v):= lt_of_not_ge hh
        have hD:=h.parent
        have hh : ¬cozy A x s p d B g (.inr t):= by
          intro HH
          have hv := hV w (ξ v) (le_trans HH (Nat.mul_le_mul_right _ (Nat.le_add_right d 8)))
          rw [← he v] at hv; exact hf.not_ge (hv.trans (Nat.le_mul_of_pos_left b (by omega)))
        have hpY a : H (.inl a)= Q.read (W (.inl a)):= page R P hj a
        rw [hW, show W (.inr t)=0 from h1 hh,map_zero,zero_add,hpY w,hpY v,show Q.read (W _ * W _) = Q.read (W (.inl w)) * Q.read (W (.inl v)) from ?_, sub_self]
        apply bridge; intro i hI ξj hJ; by_contra H'
        have hs:= (hd _ hi hj).foley i ξj H'
        have hi' := hx w i hI;have hj' := hx v ξj hJ; rw [separation_comm] at hj'
        have hv:=separation_triangle (η w) (l.parent i.1) (η v);have ht:=separation_triangle (l.parent i.1) (l.parent ξj.1) (η v)
        change separation _ _ ≤ b at hs; linarith only [hf,hs,hv,ht,hi',hj',Nat.mul_le_mul_right b hD]
      rw [hF,vars_0]; exact ⟨fun _=>rfl,fun i hi=>False.elim (notMem_empty _ hi)⟩
    refine ⟨fun h=>(h hh).elim,fun i hI=> ?_⟩
    let A₀:=(univ (α:= Chamber G A.S j p)).filter fun i=> separation (η w) i.1≤(d+8)*b
    have hc a (hQ : separation (η w) (η a)≤d*b) (f : Chamber G A.S j p) (hf : separation (η a) f.1≤ 8*b) : f ∈ A₀:= mem_filter.mpr ⟨mem_univ _, (separation_triangle (η w) (η a) f.1).trans ((add_le_add hQ hf).trans_eq (by ring))⟩
    have ht : F.vars⊆A₀:= by
      rw [hW]; apply Finset.Subset.trans (vars_minus ..); apply union_subset
      · apply Finset.Subset.trans (vars_add_subset ..); apply union_subset
        · apply pipe_vars; intro t hb u hu
          have hx' := hV w t.1 (h2 t hb)
          apply hc w (by rw [separation_self]; exact Nat.zero_le _) ; exact (separation_triangle (η w) (l.parent t.1) u.1).trans ((add_le_add hx' ((hd _ hi hj).pole _ _ hu)).trans (by unfold b; omega))
        apply pipe_vars; intro t ht ζ hζ
        have hg {a : Fin n} (hs : t∈(W (.inl a)).vars) : separation (η a) ζ.1≤ 8*b:=
          (separation_triangle (η a) (l.parent t.1) ζ.1).trans ((add_le_add (hx a _ hs) ((hd _ hi hj).pole _ _ hζ)).trans (by unfold b; omega))
        rcases mem_union.mp (vars_mul _ _ ht) with H|H
        · apply hc w (by rw [separation_self]; exact Nat.zero_le _) _ (hg H)
        apply hc v hh _ (hg H)
      apply Finset.Subset.trans (vars_mul ..); apply union_subset
      · intro i hx; exact hc w (by rw [separation_self]; exact Nat.zero_le _) i (axis_room (A:=A) x R P h hi hd hp hj.le _ i hx)
      intro i hx; exact hc v hh i (axis_room (A:=A) x R P h hi hd hp hj.le _ i hx)
    exact (mem_filter.mp (ht hI)).2
end YM.Next.Rank.Tapes
