import YM.RG08.Scale.Surface
/-! # Composable charges over paths with variable length. No multiplicative
 loss over unbounded windows through any admitted order. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Conductor
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Push.AbsoluteSums UVExtension.Free PowerSeries
open scoped BigOperators Topology Real Classical
variable {I : Type} {y δ : I→ℝ} {r s E : ℕ}

-- independent glides along edge-local analytic data W. No V data assumed (other than kinematics).
structure DeckSeat (L : I→ℕ) (t:ℕ) where
   i : I
   k : ℕ
   hw : k+t≤ L i
namespace DeckSeat
variable {f g:I→ℕ→ℝ} {L:I→ℕ}
def stepUp (t:DeckSeat L 1): DeckSeat L 0:=⟨t.i,t.k+1,t.hw⟩
def down (t:DeckSeat L 1): DeckSeat L 0:=⟨t.i,t.k,Nat.le_trans (Nat.le_succ _) t.hw⟩
def windowCharge (f:I→ℕ→ℝ)(t:DeckSeat L 0) := ∑ i∈range t.k, f t.i i
lemma folds (hv:Weighed y (fun i=>((L i):ℝ))) (h : Lease (fun i:DeckSeat L 1=> y i.i) (fun i=> δ i.i) (fun i=>f i.i i.k) (fun i=> g i.i i.k)) (he:Audience y)(hp:0 ≤ δ) : Lease (fun i:DeckSeat L 0=>y i.i) (fun i=>δ i.i) (windowCharge f) (windowCharge g) := by
  let z t:= ((DeckSeat.k (L:=L) (t:=0) t):ℝ); let μ t:= y (DeckSeat.i (L:=L) (t:=0) t)
  have ht: Audience μ:= fun t=>he _
  have hz: Weighed μ z := (hv.transfer i).mono (fun i=> Nat.cast_nonneg _) (fun t=> Nat.cast_le.mpr t.hw)
  have hf (F : I→ℕ→ℝ)(hh : Weighed (fun i:DeckSeat L 1=>y i.i) (fun i=> ‖F i.i i.k‖)): Weighed μ (fun i=> ‖windowCharge F i‖) := by
    obtain ⟨A,p,hA,H⟩:=hh
    refine (hz.times ((Weighed.constant μ hA).times ((Weighed.power μ ht p)))).mono (fun i=> norm_nonneg _) fun i=>?_ 
    apply le_trans (norm_sum_le ..); rw [Pi.mul_apply,Pi.mul_apply,Pi.pow_apply]
    calc
      _ ≤ ∑ k∈ range i.k,A*μ i^p := sum_le_sum (fun k hk=> (H ⟨i.i,k,le_trans (mem_range.mp hk) i.hw⟩).2) -- lt vs le
      _ = _ := by simp [z]
  refine ⟨hf _ h.has,hf _ h.also,?_⟩
  obtain ⟨C,⟨B,q,hB,H⟩,hk⟩:= h.asset
  refine ⟨_,(hz.times ((Weighed.constant μ hB).times (Weighed.power μ ht q))),fun i=>?_⟩
  rw [Pi.mul_apply,Pi.mul_apply,Pi.pow_apply, mul_assoc (z i),windowCharge,windowCharge,← sum_sub_distrib];
  apply (norm_sum_le ..).trans
  have hh (k) (ht:k∈range i.k): k+1 ≤ L i.i:= le_trans (mem_range.mp ht) i.hw
  calc
   _ ≤ ∑ k∈ range i.k, B*μ i^q*δ i.i := sum_le_sum (fun k hm=> by apply le_trans (hk ⟨i.i,k,hh k hm⟩); exact mul_le_mul_of_nonneg_right (H ⟨i.i,k,hh k hm⟩).2 (hp _))
   _ = _ := by simp [z]
end DeckSeat

private abbrev lensV : Cues := fun i=> coeff i (1:PowerSeries ℝ)
def paths (f : ℕ→Cues) (n : ℕ) : Cues := match n with
  | 0=> lensV
  | j+1=> glide (paths f j) (f j)
lemma route_one (f:ℕ→Cues) (n)(h : ∀ i<n, f i 0=1) : paths f n 0=1 := by
  induction n with | zero=> rw [paths]; simp [lensV] | succ n ih=> rw [paths]; exact glide_tall (h _ (Nat.lt_succ_self _)) (ih fun i hi=> h _ (by omega))
lemma route_paid {L : I→ℕ}{F H:I→ℕ→Cues}(h: ∀ b k,k<L b→ F b k 0=1)(p:∀ b k,k<L b→H b k 0=1)(he:Audience y)(hp:0≤δ)(hv:Weighed y (fun i=>((L i):ℝ))) (hh:∀ e≤ E, Lease (fun i:DeckSeat L 1=> y i.i) (fun i=>δ i.i) (fun i=> F i.i i.k e) (fun i=> H i.i i.k e)) (hs:r≤E) : Lease (fun i:DeckSeat L 0=> y i.i) (fun i=>δ i.i) (fun i=> paths (F i.i) i.k r) (fun i=> paths (H i.i) i.k r) := by
  let μ (i:DeckSeat L 0):= y i.i; let v (i:DeckSeat L 0):=δ i.i
  let W (i : DeckSeat L 0) := paths (F i.i) i.k; let S (i:DeckSeat L 0) := paths (H i.i) i.k
  have ht (i : DeckSeat L 0): W i 0=1∧ S i 0=1:= ⟨route_one _ _ fun b hb=> h _ _ (Nat.lt_of_lt_of_le hb i.hw),route_one _ _ fun b hb=> p _ _ (Nat.lt_of_lt_of_le hb i.hw)⟩
  have hB : Audience μ:= fun i=> he i.i
  change Lease μ v (fun i=> W i r) (fun i=> S i r)
  induction r using Nat.caseStrongRecOn with
  | zero=> simp_rw [(ht _).1,(ht _).2]; exact Lease.const ..
  | ind r ih=>
    have hz (j) (hh:j≤r):= Summit.Lease.whirls (ih j hh (by omega)) (DeckSeat.down (L:=L))
    let G (F:I→ℕ→Cues)(i:I)(j:ℕ):= glide (paths (F i) j) (F i j) (r+1)-paths (F i) j (r+1)
    have hx : Lease μ v (DeckSeat.windowCharge (G F)) (DeckSeat.windowCharge (G H)) := DeckSeat.folds hv (grad_lease (r:=r) (y:=fun i:DeckSeat L 1=> y i.i) (δ:=fun i:DeckSeat L 1=>δ i.i) (F:= W ∘ DeckSeat.down) (H:= S ∘ DeckSeat.down) (W:=fun i=> F i.i i.k) (V:=fun i=> H i.i i.k) (fun i=> h _ _ i.hw) (fun i=> p _ _ i.hw) (fun i=> he _) hz (fun i hi=> hh i (by omega))) he hp
    have hj (F:I→ℕ→Cues) (i:DeckSeat L 0): DeckSeat.windowCharge (G F) i=paths (F i.i) i.k (r+1):= by
      unfold DeckSeat.windowCharge
      simp_rw [G,show ∀ j, glide (paths (F i.i) j) (F i.i j)=paths (F i.i) (j+1) from fun j=>by rw [paths]]; rw [Finset.sum_range_sub (fun k=>paths (F i.i) k (r+1))]; simp [paths,lensV] -- telescoping name
    have hv i : paths (F i.i) i.k (r+1)=W i (r+1):= rfl
    rw [funext (hj F),funext (hj H)] at hx -- does not infer
    exact hx
end YM.RG08.Conductor
