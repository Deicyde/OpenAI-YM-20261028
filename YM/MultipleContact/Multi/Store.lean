import YM.MultipleContact.Multi.Apply
/-! Estimates over strict collars, parametrized by count of simultaneous detector residuals. This is not yet a contact distribution. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
noncomputable section
namespace YM.MultipleContact.Joins
open Filter Set Function MeasureTheory Extraction Table Ward MergeProof Acme Ribbons Cells Next.UVStress Wilson Lattice Arbor
open Script Scene Bunching
open Accent Matching
open RG Bunching.Cord
open Drama ScheduleRow
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}
variable {b:ℕ}{n d:Fin b→ℕ} (V:∀i:Fin b,Fin (n i)→S.Tag) (D:∀i:Fin b,Detector S (d i)) (p:Fin b → Mode)
variable [hn:∀i,Inhabited (Fin (n i))]
def weight {b:ℕ} (p : Fin b → Mode){n d:Fin b→ℕ}(V:∀i:Fin b,Fin (n i)→ S.Tag) (D:∀i:Fin b,Detector S (d i)) (ε:ℝ):Fin b → ℝ:=fun i=>match p i with
    | .signed => -(massOf (n':=n i) (V i):ℝ)+(d i)+1/64
    | .raw=> -(massOf (V i):ℝ)-ε
    | .fused=>0
-- Note instance binder not in definition. Designating D makes grade explicit.
def due (ρ:Fin b→ℝ):= fun (ε:ℝ)=> ∏ i:Fin b,(ρ i)^(weight p V D ε i)
def Close (z:Fin b→ E4)(κ:ℝ):Prop:=∀i j:Fin b, i ≠ j → κ ≤ ‖z i-z j‖
def Store (S:Table C.book)(k:ℕ):Prop:= ∀ (b:ℕ)(n:Fin b→ℕ)[_i:∀i:Fin b,Inhabited (Fin (n i))] (V:∀ (i:Fin b),Fin (n i)→ S.Tag) (d:Fin b→ℕ) (D:∀i:Fin b,Detector S (d i)) (p:Fin b → Mode), (Finset.univ.filter fun i=>p i=.signed).card ≤ k → ∀κ ε:ℝ,0 <κ→0<ε→∀ L:Lattice.Side,∃ (A r:ℝ),0 < A ∧ 0< r ∧ ∀ z:Fin b → E4,Close z κ → ∀ρ:Fin b → ℝ, (∀i,0<ρ i ∧ ρ i < r)→ ∀ y:∀i:Fin b,Fin (n i) → E4,(∀i:Fin b,p i ≠.fused → Cord.Near (n i) L (ρ i) (y i)) →∀w:∀i:Fin b,S.Field (d i),(∀i:Fin b,p i=.fused→‖w i‖≤1)→
     ‖evaluation S (planted p V D z w y)‖ ≤ A*due V D p ρ ε
lemma banded {k:ℕ} (h:Store S k) (N:Lattice.Side)(hb:(Finset.univ.filter fun i=>p i=.signed).card ≤ k) (κ ε:ℝ)(hc:0<κ)(hε:0<ε):∃ (A r:ℝ),0 < A ∧ 0< r ∧ ∀ z:Fin b → E4, Close z κ → ∀ρ:Fin b → ℝ, (∀i,0<ρ i ∧ ρ i < r)→ ∀ y:∀i:Fin b,Fin (n i) → E4,(∀i:Fin b,p i ≠.fused → Cord.Band (n i) N (ρ i) (y i)) →∀w:∀i:Fin b,S.Field (d i),(∀i:Fin b,p i=.fused→‖w i‖≤1)→
     ‖evaluation S (planted p V D z w y)‖ ≤ A*due V D p ρ ε:=by
        let w:=weight p V D ε
        obtain ⟨A1,r,hA,h0,hL⟩:=h _ _ V _ D p hb κ ε hc hε (expand N 31)
        let A0:=(∏ i:Fin b,(1/8:ℝ)^(w i))
        have h0':0 < A0:= Finset.prod_pos fun i _=>Real.rpow_pos_of_pos (by positivity) _
        refine ⟨A1*A0,r,mul_pos hA h0',h0,fun z hz ρ hr y hy w' hw=>?_⟩
        apply (hL z hz (fun i=>ρ i/8) (fun i=>by obtain ⟨h,h'⟩:=hr i;exact ⟨by positivity,by linarith only [h,h']⟩) y (fun i hi=>spread N (hy i hi) (hr i).1) w' hw).trans_eq
        rw [mul_assoc]; congr 1; unfold due A0; rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl
        intro i hi; dsimp only; rw [show ρ i/8=(1/8:ℝ)*ρ i from by ring,Real.mul_rpow (by norm_num) (hr i).1.le]
lemma card_mask (k:Fin b)(hc:p k=.signed)(q:Mode)(hq:q≠.signed):
    (Finset.univ.filter (fun i=>update p k q i=.signed)).card +1=(Finset.univ.filter fun i=>p i=.signed).card:=by
         let T:=Finset.univ.filter fun i=>p i=.signed
         have ht:(Finset.univ.filter (fun i=>update p k q i=.signed))= T.erase k:=by
             ext i; by_cases h:i=k <;> simp [T,h,hq,update_of_ne,hc]
         rw [ht]; apply Finset.card_erase_add_one; exact (Finset.mem_filter.mpr ⟨Finset.mem_univ k,hc⟩)
lemma weight_pos (ρ:Fin b→ℝ){ε:ℝ}(hr:∀i,0<ρ i):0<due V D p ρ ε:=Finset.prod_pos fun _ _=>Real.rpow_pos_of_pos (hr _) _
-- replacing raw at k by fused
lemma weight_split {k:Fin b}(hc:p k=.raw) (ρ:Fin b→ℝ)(ε:ℝ): due V D p ρ ε = (ρ k)^(-(massOf (V k):ℝ)-ε) * due V D (update p k .fused) ρ ε :=by
          unfold due; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase (Finset.univ:Finset (Fin b)) (fun i=>(ρ i)^ (weight (update p k .fused) V D ε i)) _,show weight (update p k .fused) V D ε k=0 by simp [weight],Real.rpow_zero,one_mul,weight,hc]; congr 1
          exact Finset.prod_congr rfl fun i hi=>(by rw [weight,weight,update_of_ne (Finset.mem_erase.mp hi).1])
          exact Finset.mem_univ k

def rest (k:Fin b)(z:Fin b→E4)(u:∀i:Fin b,S.Field (d i))(xe:∀i:Fin b,Fin (n i) → E4):= ∏ i∈Finset.univ.erase k, scaledBranch (p i) (V i) (D i) 1 (z i) (xe i) (u i)
lemma split_product (k:Fin b)(q:Mode)(z:Fin b→ E4)(u:∀i,S.Field (d i))(h:S.Field (d k))(xe:∀i:Fin b,Fin (n i) → E4):
    planted (update p k q) V D z (update u k h) xe = scaledBranch q (V k) (D k) 1 (z k) (xe k) h * rest V D p k z u xe:=by
          rw [planted,← Finset.mul_prod_erase _ _ (Finset.mem_univ k), update_self,update_self]; congr 1
          exact Finset.prod_congr rfl fun i hi=> by rw [update_of_ne (Finset.mem_erase.mp hi).1,update_of_ne (Finset.mem_erase.mp hi).1]
end YM.MultipleContact.Joins
