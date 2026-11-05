import YM.RG08.Atlas.Birds

/-! # Install full library into warmed chart. Verified g-valuations and capped views; constitutive
 precision proof is supplied separately, not assumed of lower coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Mount
open Filter Lattice RG Wilson Forms Pert.Bulk Isles Camera Carrel Glyph Room Exterior Function
open Stationary Bloch Laurent Precision Line Finset Bid Work.F03 Matrix
open Tack Rudder Aggregate Symmetry Steam Cairn
open scoped BigOperators Classical ContDiff Topology Matrix Matrix.Norms.Frobenius NNReal InnerProductSpace PowerSeries
variable {G:Gauge}{c f:Side}{S:StepData c f}{P:Patch}{K:KernelChoices}{I J:Type}{n e:ℕ}
open scoped Classical
lemma flight_out {C:Rudder.Raw G.ColorIndex (rank n)}{m k:ℕ}(hf:flight n e C m k≠0): e ≤ m ∧ m-e+rank n=k ∧ C≠0:=by
 by_cases ht:e ≤ m∧m-e+rank n=k
 · refine ⟨ht.1,ht.2,fun h=>?_⟩;subst h;rcases k with _|k
   · have he:=ht.2;dsimp only [rank] at *;omega
   apply hf;rw [flight,if_pos ht,completed_null]
 exact (hf (if_neg ht)).elim
lemma demand_out {C:Castle G}{m k:ℕ}(h:Stable C)(hf:demand C m k ≠0): 0 < k ∧ Even (m+k) ∧ k ≤ m+2:=by
 by_contra hk
 apply hf; unfold demand; refine Finset.sum_eq_zero fun i hi=> Finset.sum_eq_zero fun j hj=>?_
 by_contra H
 obtain ⟨ah,bh,hT⟩ := flight_out H
 obtain ⟨hr,p,hp⟩:= show Live j i from Classical.not_not.mp (fun H3=>hT (h.dark j i H3))
 apply hk;dsimp only [rank] at *;refine ⟨by omega, ⟨m-i+p+1,?_⟩,by omega⟩;omega

lemma box_nil (P:Patch)(k:ℕ):Cairn.box (G:=G) P (0:Flake k _)=0:=by rw [show (0:Flake k _)= (0:Flake k _)-0 by simp,Cairn.box_sub];simp only [sub_self] -- simp ignores func

def castle (P:Patch)(C:Castle G):Grain (Market (Head P G)):=fun e k=> Cairn.box _ (demand C e k)
lemma castle_out {P:Patch}{C:Castle G}{m k:ℕ}(h:Stable C)(hf:castle P C m k≠0): 0 < k ∧ Even (m+k) ∧ k ≤ m+2:= demand_out h fun he=>hf (by unfold castle;rw [he,box_nil])
def dusk (P:Patch)(B:ChartRatio G):Grain (Market (Head P G)):=fun e k=> if 0 < e ∧ e=k then Cairn.box P (vanity B k) else 0
private lemma dusk_out {P:Patch}{B:ChartRatio G}{m k:ℕ}(hf:dusk P B m k≠0): 0 < k ∧ Even (m+k) ∧ k ≤ m+2:=by
 unfold dusk at hf;split at hf
 next H=> exact ⟨by omega,⟨k,by omega⟩,by omega⟩
 exfalso;apply hf rfl

def bell (h:P.Branches K G):Grain (Market (Head P G)):=fun e k=> if k=e+2 then parade h k else 0
private lemma bell_out {h:P.Branches K G}{m k:ℕ}(hf:bell h m k≠0): 0 < k ∧ Even (m+k) ∧ k ≤ m+2:=by
 unfold bell at hf;split at hf
 next H=>exact ⟨by omega,⟨m+1,by omega⟩,by omega⟩
 exfalso; apply hf rfl

/-- Full analytic law, sign conventions for exponent not cost. `ghost=0` hair fee outside
 to compare across gauge/turn transforms. -/
def sweep (h:P.Branches K G)(C:Castle G) : Grain (Market (Head P G)):=-(castle P C+bell h)
def ghost (h:P.Branches K G)(C:Castle G) (B:ChartRatio G) : Grain (Market (Head P G)):=sweep h C + dusk P B
def inlet (h:P.Branches K G)(C:Castle G) (B:ChartRatio G) : Grain (Market (Head P G)):=fun i=> if 0 < i then ghost h C B i else 0

lemma inlet_eligible (h:P.Branches K G){C:Castle G}(B)(hh:Stable C):Eligible (inlet h C B):=by
 have he i k (ht: inlet h C B i k≠0): 0 < k ∧ Even (i+k) ∧ k ≤ i+2:=by
    by_contra H;apply ht
    have hx:castle P C i k=0:=Classical.byContradiction (fun hz=>H (castle_out hh hz)) -- H pushed
    have hv:dusk P B i k=0:=Classical.byContradiction (fun hz=>H (dusk_out hz))
    have hu:bell h i k=0:=Classical.byContradiction (fun hz=>H (bell_out hz))
    unfold inlet;split;next=>change -(castle P C i k+bell h i k)+dusk P B i k=0;rw [hx,hv,hu];simp
    rfl
 exact ⟨by unfold inlet;rw [if_neg (Nat.lt_irrefl _)],fun _ _ ht=> (he _ _ ht).2.2,fun _ _ ht=> (he _ _ ht).2.1⟩
lemma unveiled_eligible (F:Grain (Market I))(h:Eligible F)(P:Side):Eligible (unveil F P):=by
 refine ⟨funext (fun n=>by rw [unblocked _ _ n (by rw [h.dark];rfl)];rfl),fun e k hf=>h.head _ _ (fun ht=>hf (unblocked _ _ k ht)),fun e k hf=>h.foot _ _ (fun ht=>hf (unblocked _ _ k ht))⟩

def legal (U:Grain (Market I)):=∀ e n,Cohort (U e n)∧Forms.Sym (U e n)
lemma legal_castle (P:Patch){C:Castle G}(hs:Stable C):legal (castle P C):=fun e n=> box_sym (demand_solid hs e n).1 (demand_solid hs e n).2 P
lemma legal_dusk (P:Patch)(B:ChartRatio G):legal (dusk P B):=fun e n=>by unfold dusk;split; exact box_sym (vanity_bill B n (σ:=1)).2.2 (vanity_bill B n (σ:=1)).2.1 _;exact ⟨fun _ _=>rfl,Forms.Sym.zero⟩
lemma legal_bell (h:P.Branches K G):legal (bell h):=fun e n=>by unfold bell;split; exact ⟨(parade_bill h n (σ:=1)).2.2,(parade_bill h n (σ:=1)).2.1⟩;exact ⟨fun _ _=>rfl,Forms.Sym.zero⟩
lemma Cohort.negate {V:Flake n (Market I)}(h:Cohort V):Cohort (-V):=fun s a=>by rw [Pi.neg_apply,Pi.neg_apply,h]
lemma legal_sweep (h:P.Branches K G){C:Castle G}(hs:Stable C):legal (sweep h C):=by
 intro e k;rcases legal_castle _ hs e k with ⟨i,j⟩;rcases legal_bell h e k with ⟨v,w⟩;exact ⟨Mount.Cohort.negate (i.add v),by intro x;ext k;unfold sweep woven;simp only [Pi.neg_apply,Pi.add_apply];rw [show castle P C e _ (k ∘ x)=_ from congrFun (j x) k, show bell h e _ (k ∘ x)=_ from congrFun (w x) k]⟩
lemma legal_inlet (h:P.Branches K G){C:Castle G}(B:ChartRatio G)(hs:Stable C):legal (inlet h C B):=by
 intro e k; unfold inlet; split
 · obtain ⟨i,j⟩:=legal_dusk P B e k; obtain ⟨v,w⟩:=legal_sweep h hs e k;exact ⟨v.add i,w.add j⟩
 exact ⟨fun _ _=>rfl,Forms.Sym.zero⟩
lemma unsealed_wax [Fintype I]{F:Grain (Market I)}(h:legal F)(P:Side):waxed (unveil F P):=by
 intro e k;unfold unveil;split  <;>rename_i hk
 · intro i;rw [ordered _ _ _ (h _ _).1,(h _ _).2]
 exact Forms.Sym.zero
end YM.RG08.Mount
