import YM.MergeProof.North.Aeolus
import YM.MergeProof.North.Thunder




set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
section
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}
variable (H:History G) {N m p k:ℕ}(u δ:ℕ→ℝ)(r:ℕ→ℕ)
    (D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m))
variable (E:∀ m:ℕ,V→Site (H.S.side m p))(o:∀ m:ℕ,Name V→Site (H.S.side m p))(P:V→ Motion)(v:V)(w:ℕ→Bool→ℝ)(B:V→Equiv.Perm V)
   (F:∀ m:ℕ,Name V→ Config G (H.S.side m p)→ℂ)(L:∀ m:ℕ,Name V→ℕ→ Config G (H.S.side m p)→ℂ)(a:Name V→ Config G (H.S.side N p)→ℂ)
set_option quotPrecheck false
local notation "Ξ"=> (Aged V)
local notation "f!"=> (fun i=> F i)
local notation "P'"=> H.levels.budget
local notation "ω"=> (fun i (j:Name V)=> w i j.2)
local notation "R"=> H.rep N p
local notation "Q"=> R N
variable (h:H.Selected) (h':Moonlit H r δ u D)(ht:Matchup H r δ p N k o (fun i (j:Name V)=> w i j.2) (Aged V))
    (hs:∀ (j:Bool), Stately H u k N p (fun i=>o i (v,j)) (fun i=> w i j) (fun i=>F i (v,j)) (fun i=> L i (v,j)) (a (v,j)) D)
    (hP:∀ j,j≠v→B j v=j)(hV:∀ j,j≠v→∀ b:Bool,a (j,b)=stepUp (P j) (E N j) (a (v,b)))
local notation "Ω"=> manifest H p N F L
local notation "y"=> tapes H p N L
variable (hM:∀ m:ℕ, k ≤ m→ m≤N→∀ i,Dominated (L m i)) (hT:∀ m:ℕ, k ≤ m→m≤N→∀ i,i≠v→∀ j:Bool,F m (i,j)=stepUp (P i) (E m i) (F m (v,j))∧ tapes H p N L m (i,j)=floatUp (P i) (E m i) (tapes H p N L m (v,j))∧o m (i,j)=affine (P i).1 (E m i) (o m (v,j)))
variable (σ χ:ℕ→ℝ)
variable {S:∀ m:ℕ,m≤N→ Config G (H.S.side m p)→Poly (Aged V)}
    {μ:ℕ}(hr:Thor H δ r D σ χ μ)(ht':μ≤k)(hQ: Migrating H k p N E)
    (hΔ: ∀ m:ℕ, k ≤ m→∀ hm:m<N, S m hm.le=(H.levels.clock.op m p).push ((H.rep N p (m+1)).beta) (S (m+1) hm))
    (hΩ:S N le_rfl=birth (Aged V) (H.rep N p N) a) (hp:∀ m:ℕ,k ≤ m→∀ hm:m≤N,Integrable (S m hm) (prior G _))
local notation "W"=> (fun i (j:Name V)=>δ i*w (i+1) j.2)
include h ht hP hV hΩ hp hΔ hr ht' hQ h'
lemma tidal (hk:k<N)(hX:∀ i:Bool,∃ φ:∀ m:ℕ,Config G (H.S.side m p)→ℂ,∃ β:∀ m:ℕ,ℕ → Config G (H.S.side m p)→ℂ,Stately H u k N p (fun m=>o m (v,i)) (fun m=>w m i) φ β (a (v,i)) D) (hy:∀ m:ℕ, k ≤ m→m≤N→∀ i,i≠v→∀ j:Bool,o m (i,j)=affine (P i).1 (E m i) (o m (v,j))) : ∃ l:Name V→ℂ, ∃ g: Name V→ Config G (H.S.side k p)→ℂ,∃ L':Name V→ℕ→ Config G (H.S.side k p)→ℂ, (∀ i,W k i*‖l i‖≤1) ∧ (∀ i,i≠v→ ∀ j:Bool,l (i,j)=scalar (P i) (l (v,j))) ∧ Arc (R k) g L' (S k hk.le) v P (E k) B (o k) (W k) ((P' k).supportExponent+1/2) ((P' k).supportExponent+1) 1 (χ k) (δ k) l:=by
    choose f β hL using hX
    let F' (m:ℕ)(j:Name V):= if j.1=v then f j.2 m else stepUp (P j.1) (E m j.1) (f j.2 m)
    let π m (he:m≤N) j:= ((h.represents N p m he).good.labels.moves (P j).1 (E m j)).some
    let L' (m:ℕ)(j:Name V):= if j.1=v then β j.2 m else if h:m≤N then fun i=>stepUp (P j.1) (E m j.1) (β j.2 m ((π m h j.1).kp.symm i)) else β j.2 m
    have hM(m:ℕ)(he:k ≤ m)(hp:m≤N)(j:Name V):Dominated (L' m j):=by unfold L'; split; exact (hL j.2).stocked m he hp; exact conduits _ _ _ ((hL j.2).stocked _ he hp) (π m hp j.1)
    have hT(m)(he:k ≤ m)(hm:m≤N)(i)(ha:i≠v)(j:Bool): F' m (i,j)=stepUp (P i) (E m i) (F' m (v,j)) ∧ tapes H p N L' m (i,j)=floatUp (P i) (E m i) (tapes H p N L' m (v,j)) ∧ o m (i,j)= affine (P i).1 (E m i) (o m (v,j)):=by
       refine ⟨by unfold F'; simp [ha], ?_,hy m he hm i ha j⟩; unfold tapes L'; simp only [if_true,if_neg ha,dif_pos hm]; apply roam _ _ (π m hm i); intro k U;simp
    have hs b : Stately H u k N p (fun m=>o m (v,b)) (fun m=>w m b) (fun m=>F' m (v,b)) (fun m=>L' m (v,b)) (a (v,b)) D:=by simp only [F',L',if_pos rfl]; exact hL b
    have hY(m)(hi:k ≤ m)(hm:m≤N): Serves (R m) (F' m) (tapes H p N L' m) (S m hm) v P (E m) B (o m) (ω m) (topPitch H N m) 1:=by
       induction hm using Nat.decreasingInduction with
       | self=> rw [hΩ]; exact penumbra H u δ r D E o P v w B F' L' a h h' ht hs hP hV hM hT hk.le
       | of_succ m hm IH=> obtain ⟨l,H,-⟩:= uprising H u δ r D E o P v w B F' L' a h ht hs hP hM hT σ χ hr ht' hQ hΔ hp hi hm (IH (hi.trans m.le_succ)); exact H
    obtain ⟨l,hZ,ht⟩:= uprising H u δ r D E o P v w B F' L' a h ht hs hP hM hT σ χ hr ht' hQ hΔ hp le_rfl hk (hY (k+1) k.le_succ hk); exact ⟨l,F' k,L' k,ht⟩
end
end YM.MergeProof.Ribbons
