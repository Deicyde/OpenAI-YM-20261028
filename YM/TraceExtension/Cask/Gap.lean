import YM.TraceExtension.Cask.Committee
import YM.Work.I01
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker MeasureTheory Wilson Push Function
open scoped Classical
variable {V L W:Type}[DecidableEq V][DecidableEq L][DecidableEq W]{n:Side}[Fintype V][Fintype L][Fintype W]{G:Gauge}{R:Rep G n}(C:TourC R V L W)
lemma billgap (N:ℕ)(hN:1 ≤ N)(b:ℕ)(hb:1 ≤ b) (q:V→Site n)(Z:Finset V)(hZ:2≤Z.card)(hx:∀ i∈Z,∀ j∈Z,i≠j→ 64*b*N+2*b ≤ separation (q i) (q j)) (P:Support n)(hp: Z.image q⊆P) : N * Z.card ≤ coverNumber b P:=by
   obtain ⟨i,hi,hu⟩:= coverNumber_realized b P
   obtain ⟨m,hm,s,H,hs⟩:= Corona.ring_path _ (Corona.halo_ship b hi.2)
   have hz(i':V)(hv:i'∈Z):∃ j:ℕ,j ≤ m ∧ separation (s j) (q i') ≤ b:=by
      obtain ⟨p,hp,ht⟩:= halo_spec.mp (hi.1 (hp (mem_image_of_mem _ hv))); obtain ⟨j,hj,e⟩:= hs p hp; exact ⟨_,hj,e.symm ▸ ht⟩
   choose! t ht hn using hz
   let g:=64*b*N;have hg:0<g:= by unfold g; positivity
   have h(x)(h₁:x∈Z)(y)(h₂:y∈Z)(hi:x≠y)(he:t x ≤ t y): t x+g≤ t y:=by
      have h:= Corona.path_span H (t x) (t y) he (ht y h₂)
      have h₃:= separation_triangle (q x) (s (t x)) (q y); have h₄:=separation_triangle (s (t x)) (s (t y)) (q y); rw [separation_comm (q x) (s (t x))] at h₃; have h5:= hn x h₁; have h6:= hn y h₂; have h7:= hx x h₁ y h₂ hi
      change g+2*b≤ _ at h7; omega
   let u(x):=t x/g
   have hg' (x)(hx:x∈Z) y (hy:y∈Z)(he:x≠y)(hh:t x ≤ t y): u x<u y:=by
       have h:= Nat.div_le_div_right (c:=g) (h x hx y hy he hh); rw [Nat.add_div_right (t x) hg] at h; exact h
   have hv: Z.card ≤ m/g+1:=by
       let J:=Finset.range (m/g+1); have hV: Z.card ≤ J.card:=by
          apply Finset.card_le_card_of_injOn u
          · exact fun i hi=> Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (c:=g) (ht i hi)))
          intro i hi j hj h; exact not_not.mp (fun hu=> (le_total (t i) (t j)).elim (fun H=>(hg' i hi j hj hu H).ne h) (fun H=> (hg' j hj i hi (Ne.symm hu) H).ne h.symm))
       simpa [J] using hV
   have hh: (Z.card-1)*g≤ m:= (Nat.le_div_iff_mul_le hg).mp (by omega)
   have hf: g*Z.card ≤2*((Z.card-1)*g):= (Nat.mul_le_mul_left g (show Z.card ≤2*(Z.card-1) by omega)).trans_eq (by ac_rfl)
   have hz : 2*m ≤64*b*i.card:=by
       have ht:= Nat.mul_le_mul_left 2 hm; nlinarith only [ht,Nat.mul_le_mul_left i.card (show 2*((b+b+1)+(b+b+1)) ≤ 64*b by omega)]
   rw [← hu]; refine Nat.le_of_mul_le_mul_left (a:=N*Z.card) ?_ (show 0<64*b by omega); rw [← Nat.mul_assoc]; exact hf.trans ((Nat.mul_le_mul_left 2 hh).trans hz)
lemma bill_b (s:Finset V) (p: Support n) (hp:s ⊆ deer C p) (b l:ℕ)(hl:∀ i,coverNumber b (C.cap i) ≤ l): coverNumber b (bud C s p) ≤ coverNumber b p + l*s.card:=by
    induction s using Finset.induction with
    | empty=>simp [bud]
    | insert i s hi IH=>
       have hx:= IH ((subset_insert ..).trans hp); let X:= bud C s p; have hz : C.tie i∈X:= mem_union_left _ (mem_filter.mp (hp (mem_insert_self ..))).2
       rw [show bud C (insert i s) p=X ∪ C.cap i from by unfold X bud; rw [biUnion_insert,union_comm (C.cap i),← union_assoc],card_insert_of_notMem hi]; exact (Corona.meets_sum hz (C.centre i) b).trans ((add_le_add hx (hl i)).trans (show _ ≤ _ by rw[mul_add,mul_one,← add_assoc]))
end YM.Trace.Cask
