import YM.MultipleContact.Multi.Store
/-! Converting loss of one cancellation into grid-step power at sufficiently high internal derivative order. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 50000
noncomputable section
namespace YM.MultipleContact.Joins
open Filter Set Function MeasureTheory Extraction Table Ward MergeProof Acme Ribbons Cells Next.UVStress Wilson Lattice Arbor
open Script Scene Bunching
open Accent Matching
open RG Bunching.Cord
open Drama ScheduleRow
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}
variable {b:ℕ}{n d:Fin b→ℕ} {V:∀i:Fin b,Fin (n i)→S.Tag} {D:∀i:Fin b,Detector S (d i)} {p:Fin b → Mode}
variable [hn:∀i,Inhabited (Fin (n i))]
variable (P:DiffPlan S)(hA:Acme.Aroma C){θ δ:ℝ} (j:ℕ→ℕ)(τ:ℝ)(n' : ℕ)
variable (ht:1 < τ) (hj:Tendsto j atTop atTop) (hJ:Tendsto (fun m:ℕ=>C.S.scale (j m)/C.S.scale m) atTop (𝓝 τ))
omit hn in
lemma exponent_step (V:Fin n' → S.Tag) (t:Axis)(i:Fin n')(l:ℕ) : massOf (Line.tags V P i t l)=massOf V+l:=by
       unfold massOf totalDeg; simp only [Line.tags]; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),update_self]
       nth_rw 1 [← Finset.add_sum_erase (Finset.univ:Finset (Fin n')) (fun i=> (V i).fst) (Finset.mem_univ i)] -- select
       rw [trek_h]; have he:(∑ a∈(Finset.univ).erase i, (fun j=> (update V i (trek P t (V i) l) j).fst) a)=∑ a∈Finset.univ.erase i,(V a).fst:=by exact Finset.sum_congr rfl (fun a ha=>(by dsimp only; rw [update_of_ne (Finset.mem_erase.mp ha).1]))
       rw [he]; exact Nat.add_right_comm ..
include hA ht hj hJ
omit hn in
lemma airfare (x:ℝ):∃ A:ℕ, ∀ᶠ m:ℕ in atTop, ∀ r:ℝ,0<r → tail C r m→ C.S.a (j m)^A ≤ r^(A+x) ∧ Cord.radius n' A * C.S.a (j m) ≤ Cord.tolerates n' r :=by
      have hw':Tendsto (fun k:ℕ=>(k:ℝ)*(τ-1)) atTop atTop:= Tendsto.atTop_mul_const (sub_pos.mpr ht) tendsto_natCast_atTop_atTop
      obtain ⟨A,hA'⟩:= (hw'.eventually_ge_atTop (x+1)).exists
      have hpD:Note C.S (C.S.a∘ j) (-τ):=((Note.note_a C.S).relay j hj hJ).swapP (by ring)
      have hA0: (A:ℝ)*(-τ) < -((A:ℝ)+x):= by change _ ≤ _ at hA'; linarith only [hA']
      have he₁:= (hpD.powerN A).outweigh (hA.notes.powr ((A:ℝ)+x)) (hA0.trans_le (by linarith))
      have he₂:= (hpD.powerN A).outweigh ((Local.topNote hA.notes).powr (A+x:ℝ)) (by linarith)
      have he₃:= ((Note.notes C.S _ (show 0<Cord.radius n' A from Cord.radius_pos _ _)).mills hpD).outweigh (hA.notes.splits (Note.notes C.S _ (show 0< 16*((8*n':ℕ)+1:ℝ) by positivity))) (by linarith)
      refine ⟨A, ((he₁.and (he₂.and he₃)).mono ?_)⟩
      intro m ⟨ha,hb,hc⟩ r hr h
      constructor; swap
      · exact hc.trans (div_le_div_of_nonneg_right h.1 (by positivity)) -- tolerates
      by_cases hx:0 ≤ (A:ℝ)+x
      · exact ha.trans (Real.rpow_le_rpow (hA.notes.pos _|>.le) h.1 hx)
      exact hb.trans (Real.rpow_le_rpow_of_nonpos hr h.2 (not_le.mp hx).le)
omit hA hj ht hJ
lemma due_step {k:Fin b}(hp:p k=.signed)(l:ℕ)(i:Fin (n k)×Axis) {ρ:Fin b→ℝ}{r:ℝ}(hrho':∀a:Fin b,0 < ρ a)(hρ:0<ρ k)(ε:ℝ)(hr:0<r)(hs:r^l ≤ (ρ k)^((l:ℝ)+((d k:ℝ)+1/64+ε))):let T:= Function.update V k (Line.tags (V k) P i.1 i.2 l);
           r^l * due T D (update p k .raw) ρ ε ≤ due V D p ρ ε:=by
              intro T
              let f i:=(ρ i)^(weight p V D ε i); let g i:=(ρ i)^(weight (update p k .raw) T D ε i)
              change r^l *(∏ i:Fin b,g i) ≤ ∏ i:Fin b,f i
              rw [← Finset.mul_prod_erase _ g (Finset.mem_univ k), ← Finset.mul_prod_erase _ f (Finset.mem_univ k), ← mul_assoc (r^l)]
              have hEq: (Finset.univ.erase k).prod g=(Finset.univ.erase k).prod f:=by
                 apply Finset.prod_congr rfl
                 intro j hj; unfold g f weight T; rw [update_of_ne (Finset.mem_erase.mp hj).1, update_of_ne (Finset.mem_erase.mp hj).1]
              rw [hEq]
              apply mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg (s:=Finset.univ.erase k) fun a _=>(by change 0 ≤ (ρ a)^_; apply Real.rpow_nonneg; exact (show 0<ρ a from hrho' a)|>.le))
              unfold f g weight T; rw [hp, update_self, update_self, exponent_step] -- replace
              refine (mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hρ.le _)).trans_eq ?_
              rw [← Real.rpow_add hρ]; congr 1; push_cast; linarith only
end YM.MultipleContact.Joins
