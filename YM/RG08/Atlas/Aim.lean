import YM.RG08.Atlas.Eaves

/-!
# Coupled stock in packed incidence alphabet. Explicit ex-Haar series; comparisons in same β/G.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Mount
open Filter Lattice RG Wilson Forms Pert.Bulk Isles Camera Carrel Glyph Room Exterior Function
open Stationary Bloch Laurent Precision Line Finset Bid Work.F03 Matrix
open Tack Rudder Aggregate Symmetry Steam Cairn Cloud
open scoped BigOperators Classical ContDiff Topology Matrix Matrix.Norms.Frobenius NNReal InnerProductSpace PowerSeries
variable {G:Gauge}{c f:Side}{S:StepData c f}{P:Patch}{K:KernelChoices}{I J:Type}{n e:ℕ}{C:Castle G}
-- per-origin amounts supplied by generic trace receipts. For arbitrary sums pay at ANY width,
-- include cutoffs and lift prices. Below use lower capacity but don't assert rates yet.

lemma court (C:Castle G)(h:Stable C)(s k r e:ℕ):∃ τ c:ℝ,0 < τ∧0  ≤  c∧ Held (carpet _) τ c (flight r s (C r s) e k):=by
 unfold flight;split
 · obtain ⟨D,hD,H⟩:=completed_held G k (stick r) (h.dial r s);have ht:= (H _ (h.weight r s) (h.hold r s)).1
   exact ⟨_,_, by have hh:=h.dial r s;dsimp [rank]; positivity, mul_nonneg hD (h.weight ..),ht⟩
 exact ⟨1,0,zero_lt_one,le_rfl,zero_held⟩
-- choose common fee over a finite range
lemma docket {ι:Type}(s:Finset ι)(t w:ι→ℝ)(ht:∀ i∈s,0 < t i)(hw:∀ i∈s,0 ≤ w i): ∃ α C:ℝ,0 < α ∧ 0 ≤ C ∧ ∀ i∈s,α ≤ t i ∧ w i ≤ C:=by
 induction s using Finset.induction_on with
 | empty=>refine ⟨1,1,zero_lt_one,zero_le_one,?_⟩; simp
 | insert a s ha he=>
   obtain ⟨u,W,hu,hW,H⟩:= he (fun i hi=>ht _ (mem_insert_of_mem hi)) (fun i hi=>hw _ (mem_insert_of_mem hi))
   exact ⟨min u (t a),max W (w a),lt_min hu (ht a (mem_insert_self ..)),hW.trans (le_max_left ..),fun i hi=>by
     rcases mem_insert.mp hi with rfl|hi; exact ⟨min_le_right ..,le_max_right ..⟩; exact ⟨(min_le_left ..).trans (H _ hi).1,(H _ hi).2.trans (le_max_left ..)⟩⟩
lemma packet (C:Castle G) (h:Stable C)(k n:ℕ): ∃ τ p:ℝ, 0 < τ ∧ 0 ≤ p ∧ ∀ s r:ℕ,s  ≤  k→ r  ≤  s→ Held (carpet _) τ p (flight r s (C r s) k n):=by
 choose t w ht hw hE using fun y:ℕ × ℕ=>court C h y.1 n y.2 k
 let S:Finset (ℕ×ℕ):=range (k+1) ×ˢ range (k+1)
 obtain ⟨a,b,ha,hb,H⟩:=docket S _ _ (fun i _=>ht i) (fun i _=>hw i)
 refine ⟨a,b,ha,hb,fun s r hs hr=>?_⟩; obtain ⟨A,B⟩:= H (s,r) (by simp [S,hs,hr.trans hs]); exact (hE (s,r)).mono A B (fun _=>le_rfl)
lemma carpet_demand (C:Castle G)(h:Stable C)(k n:ℕ):∃ τ p:ℝ, 0 < τ∧0 ≤ p∧Held (carpet _) τ p (demand C k n):=by
 obtain ⟨a,b,ha,hb,H⟩:=packet C h k n; refine ⟨a,_,ha,?_,Held.sum _ _ (fun i=> (∑ _∈range (i+1),b)) (fun _ _=>Finset.sum_nonneg (fun i _=>hb)) fun i hi=> Held.sum _ _ _ (fun _ _=>hb) (fun _ hz=>H i _ (by simpa using hi) (by simpa using hz))⟩
 exact Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun i _=>hb))

lemma demand_sum (C:Castle G)(h:Stable C)(k n:ℕ)(i:Fin n): parley (pour (P:=c) (demand C k n) i)=∑ s∈range (k+1),∑ r∈range (s+1), parley (pour (P:=c) (flight r s (C r s) k n) i):=by
 obtain ⟨a,b,ha,hb,H⟩:=packet C h k n
 rw [demand, flow i _ _ (fun t=> ∑ _∈range (t+1),b) a ha.le (fun j hj=> Held.sum _ _ _ (fun _ _=> hb) (fun _ hr=>H _ _ (by simpa using hj) (by simpa using hr))),parley_sum]
 apply Finset.sum_congr rfl;intro j hj; rw [flow i _ _ _ _ ha.le (fun _ hr=>H _ _ (by simpa using hj) (by simpa using hr)),parley_sum]

/-- Exact input expo sans quadratic/haar at all periods. -/
def china (h:S.patch.Branches S.kernel G)(C:Castle G):=stock (unveil (sweep h C) c)
lemma bow_castle (h:Stable C)(k n)(o:Fin n): parley (pour (P:=c) (castle S.patch C k n) o)= MvPolynomial.rename (lowSlot S) (∑ s∈range (k+1),∑ r∈range (s+1), parley (pour (P:=f) (flight r s (C r s) k n) o)):=by
 rw [← demand_sum C h k n o, castle,low_poly S _ (demand_solid h k n).1]
lemma concur (h:Stable C)(k s r:ℕ)(hs:s  ≤  k)(hr:r  ≤  s):
    showV (fun i n=> if he:0 < n then pour (P:=f) (flight r s (C r s) i n) ⟨0,he⟩ else 0) k= tap k (PowerSeries.X^s*tax (rank r) (booked (C r s) (stick r) f)):=by
 obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hs
 have he:= h.hold r s; have hd:=h.dial r s
 let p:=d+s;have hq:p-s=d:=by unfold p;omega
 let N:=d+rank r;have hn:0 < N:=Nat.zero_lt_succ _
 have hm :N∈range (p+3):=by simp only [mem_range,p,N,rank];omega
 rw [tap, add_comm s d, PowerSeries.coeff_X_pow_mul]
 unfold showV; change (∑ n∈range (p+3),parley (if hj:0 < n then pour (P:=f) (flight r s (C r s) p n) ⟨0,hj⟩ else 0))=tap d _
 rw [Finset.sum_eq_single_of_mem N hm ?_, dif_pos hn,flight,if_pos (by rw [hq];exact ⟨by dsimp [p]; omega,rfl⟩),Camera.audited,reserve (stick r) (n:=rank r) (k:=d+rank r) ⟨0,hn⟩ (h.banner r s).path he (h.weight r s) hd]
 intro b _ hh;split
 next h0=>rw [flight,hq,if_neg (by rintro ⟨_,H⟩;exact hh H.symm),blank _ _ rfl,parley_zero]
 exact parley_zero

lemma castle_sum (S:StepData c f){C:Castle G}(h:Stable C)(e:ℕ): showV (unveil (castle S.patch C) c) e= ∑ i∈range (e+1),∑ r∈range (i+1),tap e (leaf S (C r i) (stick r) i):=by
 unfold showV
 have hf(n:ℕ):parley (unveil (castle S.patch C) c e n)=∑ i∈range (e+1),∑ r∈range (i+1), MvPolynomial.rename (lowSlot S) (parley (if hi:0 < n then pour (P:=f) (flight r i (C r i) e n) ⟨0,hi⟩ else 0)):=by
   by_cases he:0 < n
   · simp only [unveil,dif_pos he,bow_castle h,map_sum]
   simp [unveil,he,parley_zero]
 simp_rw [hf]; rw [sum_comm]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [sum_comm]; refine Finset.sum_congr rfl fun r hr=>?_
 rw [← _root_.map_sum, leaf, ←belt_g (fun i=>Room.rod (lowSlot S i)), ← _root_.map_pow,←_root_.map_mul,Cairn.censor,←concur h e i r (by simpa using hi) (by simpa using hr)];rfl
end YM.RG08.Mount
