import YM.RG08.Taste.Broth
/-! # Multi-scalar coefficients between variants. Budget relative to joint amplitude.
Supports against actual weighting windows. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Taste
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I J W:Type} {e k n:ℕ} {A B D D' U V C y p q δ v: I→ℝ}
structure Tonic (y p δ A B:I→ℝ) : Prop where
   one: Dig y p A
   two: Dig y p B
   both: Dig y (δ*p) (A-B)
lemma Dig.payMul (h:Dig y δ C)(hp: Dig y p D) (_:0≤p): Dig y (δ*p) (C*D):= by
  obtain ⟨A,hA,H⟩:=h.asset; obtain ⟨B,hB,H'⟩:=hp.asset; exact ⟨_,hA.times hB,fun i=> by rw [Pi.mul_apply,norm_mul]; exact (mul_le_mul (H i) (H' i) (norm_nonneg _) ( (norm_nonneg _).trans (H i))).trans_eq (mul_mul_mul_comm ..)⟩
lemma Tonic.ofL (h:Lease y δ A B) : Tonic y 1 δ A B:= ⟨Dig.of_rate h.has,Dig.of_rate h.also,by rw [mul_one]; exact Door.Dig.of_lease h⟩
lemma Tonic.giveL (h:Tonic y 1 δ A B) : Lease y δ A B:=⟨h.one.rates,h.two.rates,by have he:=h.both; rw [mul_one] at he; exact he.asset⟩
lemma Tonic.more (h:Tonic y p δ A B)(hv:Tonic y p δ C D)(he:Audience y): Tonic y p δ (A+C) (B+D):= ⟨h.one.plus hv.one he,h.two.plus hv.two he,by rw [show A+C-(B+D)= A-B+(C-D) by abel]; exact h.both.plus hv.both he⟩
lemma Tonic.timesL (h:Tonic y p δ A B)(hp:Lease y δ C D)(hT:Audience y)(he:0≤p)(hx:0 ≤δ): Tonic y p δ (C*A) (D*B):= by
    have h' := Tonic.ofL hp; refine ⟨(by simpa only [one_mul] using Dig.payMul h'.one h.one he), (by simpa only [one_mul] using Dig.payMul h'.two h.two he),?_⟩
    have he:= Dig.payMul (Door.Dig.of_lease hp) h.one he; have ht:= Dig.payMul h'.two h.both (fun i=>mul_nonneg (hx i) (‹0≤p› i)); rw [one_mul] at ht; rw [show C*A-D*B =(C-D)*A+D*(A-B) by ring]; exact he.plus ht hT
lemma Tonic.sums {A B : J→I→ℝ} (S:Finset J)(h:∀ i∈S,Tonic y p δ (A i) (B i))(he:Audience y) : Tonic y p δ (fun i=>∑ j∈S,A j i) (fun i=>∑ j∈S,B j i):= by
  classical
  induction S using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact ⟨Dig.zero,Dig.zero,by rw [sub_self]; exact Dig.zero⟩
  | insert i S hi ih=> simp_rw [sum_insert hi]; exact Tonic.more (h i (mem_insert_self ..)) (ih fun j hj=> h j (mem_insert_of_mem hj)) he
lemma Dig.payNeg (h:Dig y δ A) : Dig y δ (-A):= by obtain ⟨B,hB,H⟩:=h.asset; exact ⟨_,hB,fun i=>by simp only [Pi.neg_apply,norm_neg]; exact H i⟩
lemma Dig.riseD (h: Dig y p A)(hp:p≤q): Dig y q A:=⟨_,h.asset.choose_spec.1,fun i=>(h.asset.choose_spec.2 i).trans (mul_le_mul_of_nonneg_left (hp _) (h.asset.choose_spec.1.positive _))⟩
lemma Tonic.payLess (h:Tonic y p δ A B)(hp:Tonic y p δ C D)(he:Audience y): Tonic y p δ (A-C) (B-D) := by
   rw [sub_eq_add_neg A,sub_eq_add_neg B]; apply Tonic.more h _ he; exact ⟨Dig.payNeg hp.one,Dig.payNeg hp.two,by rw [show -C- -D= -(C-D) by abel]; exact Dig.payNeg hp.both⟩
lemma Tonic.rises (h:Tonic y p δ A B)(he:p≤q)(hp:0≤δ): Tonic y q δ A B:= ⟨Dig.riseD h.one he,Dig.riseD h.two he,Dig.riseD h.both ((fun i=>mul_le_mul_of_nonneg_left (he i) (hp i)))⟩
lemma Tonic.viaD (h:Tonic y p δ A B)(b:J→I): Tonic (fun i=>y (b i)) (fun i=>p (b i)) (fun i=>δ (b i)) (fun i=>A (b i)) (fun i=>B (b i)):= by
   have hx {v A}(h:Dig y v A): Dig (fun i=>y (b i)) (fun i=>v (b i)) (fun i=>A (b i)):= ⟨_,h.asset.choose_spec.1.transfer b,fun i=>h.asset.choose_spec.2 (b i)⟩
   exact ⟨hx h.one,hx h.two,hx h.both⟩
section pc
variable {L M H Z : I→PowerSeries ℝ}
lemma Tonic.moat (h:∀ i≤e,Tonic y p δ (fun j=>coeff i (H j)) (fun j=>coeff i (Z j)))(hp:∀ i≤e, Lease y δ (fun j=>coeff i (L j)) (fun j=>coeff i (M j)))(he:Audience y)(h1:0≤p)(hx:0≤δ): Tonic y p δ (fun i=> coeff e ((L i)*(H i))) (fun i=> coeff e (M i*Z i)) := by
   simp_rw [PowerSeries.coeff_mul]; apply Tonic.sums _ _ he; intro j hj; have he:=mem_antidiagonal.mp hj; exact (h j.2 (by omega)).timesL (hp j.1 (by omega)) (‹Audience y›) h1 hx
lemma Tonic.ferry (h:∀ i≤e,Tonic y p δ (fun j=>coeff i (H j)) (fun j=>coeff i (Z j)))(hp:∀ i≤e, Lease y δ (fun j=>coeff i (L j)) (fun j=>coeff i (M j)))(he:Audience y)(h1:0≤ p)(hx:0≤δ): Tonic y p δ (fun i=> coeff e (PowerSeries.subst (PowerSeries.X*L i) (H i))) (fun i=> coeff e (PowerSeries.subst (PowerSeries.X*M i) (Z i))) := by
   simp_rw [stencilSub, mul_comm (coeff _ (H _)) (coeff _ (L _^_)),mul_comm (coeff _ (Z _)) (coeff _ (M _^_))]; apply Tonic.sums _ _ he; intro j hj; exact (h j (mem_range_succ_iff.mp hj)).timesL (power_paid hp (Nat.sub_le ..) he j) he h1 hx
variable [Fintype J]{M N:I→ Session J}{Q X: I→ Native J}
lemma Tonic.thrum (hm : ∀ i≤e,∀ a b, Lease y δ (fun j=>coeff i (M j a b)) (fun j=>coeff i (N j a b)))(hp:∀ i≤e,∀ a,Tonic y p δ (fun j=>coeff i (Q j a)) (fun j=>coeff i (X j a)))(he:Audience y)(h1:0 ≤ p)(hx:0≤δ)(a:J): Tonic y p δ (fun i=> coeff e ((M i*ᵥ Q i) a)) (fun i=> coeff e ((N i*ᵥ X i) a)):= by
   simp_rw [mulVec,dotProduct,_root_.map_sum]; exact Tonic.sums _ (fun j _=> Tonic.moat (fun i hi=>hp i hi j) (fun i hi=> hm i hi a j) he h1 hx) he
end pc
-- Dig.sum timing course. variable number but age weight. invoked after hp orientation
lemma Dig.swing (N:I→ℕ){P:I→ℕ→ℝ}(h:Dig (fun i:DeckSeat N 1=>y i.i) (fun i=>p i.i) (fun i=>P i.i i.k))(he: Weighed y (fun i=> (N i:ℝ)))(hz:0≤p)(hp:Audience y): Dig y p (fun i=> ∑ j∈range (N i),P i j) := by
   obtain ⟨A,⟨B,k,hB,HB⟩,H⟩:=h.asset; refine ⟨_, (he.times (Weighed.constant y hB)).times (Weighed.power y hp k),fun i=>?_⟩
   apply le_trans (norm_sum_le ..); apply le_trans (sum_le_sum (g:=fun _=>B*y i^k *p i) (fun j hj=>?_))
   · simp only [sum_const,card_range,nsmul_eq_mul,Pi.mul_apply,Pi.pow_apply]; linarith
   let a:DeckSeat N 1:= ⟨i,j,mem_range.mp hj⟩; exact (H a).trans (mul_le_mul_of_nonneg_right (HB a|>.2) (hz i))
lemma Tonic.swing (N:I→ℕ){P Q:I→ℕ→ℝ}(h:Tonic (fun i:DeckSeat N 1=> y i.i) (fun i=>p i.i) (fun i=>δ i.i) (fun i=>P i.i i.k) (fun i=>Q i.i i.k))(he:Weighed y (fun i=>(N i:ℝ)))(hz:0≤p)(hx:0≤δ)(hp:Audience y): Tonic y p δ (fun i=> ∑ j∈ range (N i),P i j) (fun i=>∑ j∈range (N i),Q i j):= by
    constructor
    · exact Dig.swing N h.one he hz hp
    · exact Dig.swing N h.two he hz hp
    rw [show ((fun i=>∑ j∈range (N i),P i j) - (fun i=>∑ j∈range (N i),Q i j))=(fun i=>∑ j∈range (N i),(P i j-Q i j)) from funext fun i=> by simp only [Pi.sub_apply,sum_sub_distrib]]; exact Dig.swing N h.both he (fun i=>mul_nonneg (hx i) (hz i)) hp
end YM.RG08.Taste
