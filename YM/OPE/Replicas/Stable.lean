import YM.MergeProof.North.Stable
import YM.OPE.Replicas.Antique
import YM.OPE.Replicas.Apiary

/-!
# Many slots per cell: port of YM/MergeProof/North/Stable.lean

Most of the proof can be shared verbatim with that for pairs. Costs at every step
use the same register though the group being transported can now be quite different.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {slotsZ : Type}[Fintype slotsZ][DecidableEq slotsZ] {V : Type}[Fintype V][DecidableEq V]{G:Gauge}
variable (A:RG.History G) (N m p:ℕ)
local notation "f"=> A.S.side (m+1) p
local notation "c"=> A.S.side m p
local notation "X0"=> A.rep N p m
local notation "X1"=> A.rep N p (m+1)
local notation "Z"=> A.levels.clock.op m p
local notation "P0"=> (A.levels.budget m)
local notation "P1"=> (A.levels.budget (m+1))
variable {x d t u w :ℝ} {I: (V×slotsZ)→ℝ} {J:(V×slotsZ)→ℝ}
    {θ:Config G (A.S.side (m+1) p)→Poly (Names V slotsZ)} {o:(V×slotsZ)→Site (A.S.side (m+1) p)}
    {F: (V×slotsZ)→ Config G (A.S.side (m+1) p)→ℂ} {L: (V×slotsZ)→ Res G (A.S.side (m+1) p)}
    {F': (V×slotsZ)→ Config G (A.S.side m p)→ℂ} {L': (V×slotsZ)→ℕ→ Config G (A.S.side m p)→ℂ}
    {D:GaugeDoor (A.rep N p (m+1)) (A.rep N p m)} (C:ℕ→ℕ)
    {P:V→Motion}{E:V→Site (A.S.side m p)}{v:V}{B:V→Equiv.Perm V}
set_option quotPrecheck false
local notation "Ω"=> (Z).ratio.parent ∘ o
local notation "ρ"=> (Z).push (X1).beta θ
-- S contract. station Law.
lemma freshArc (h:A.Selected)(hm:m<N)(hu:Duty A C m d t u)(H:Volant Z D (C m) ((P1).supportExponent-4) t ((P0).supportExponent+1/2) ((P0).supportExponent+1) 1 u)(hr:Unites Z D (C m) ((P1).supportExponent-4) t ((P0).supportExponent+1/2) ((P0).supportExponent+1) 1 u)
    (hI:∀ i,0<I i)(h':Serves (X1) F L θ v P (fun i=>(Z).ratio.embed (E i)) B o I w 1)(hX:(P1).supportExponent-4≤w)(hO:Occupancy o (C m))(hO':Occupancy ((Z).ratio.parent ∘ o) (C m)) (hT:∀ i,i≠v→∀ j:slotsZ,I (i,j)=I (v,j)) {s r:slotsZ→ℝ}{δ:(V×slotsZ)→ℂ}(hc:∀ i:(V×slotsZ),2*I i*s i.2 ≤ 1)(hy:∀ i:(V×slotsZ),I i*r i.2≤1)
    (hK:∀ i:slotsZ,let y: (V×slotsZ):=(v,i);∃ p:Set Wing,p.Finite∧ Tale p (o y) (Ω y) 1 (F y) (L y) (profile (X0).activities (L' y)) (δ y) (s i) (r i) D)
    (hp:chimes v P E B o (Ω) F L (fun i=>profile (X0).activities (L' i)) δ Z) (hH:∀ i,Nonempty ((X1).activities.Moves (P i).1 ((Z).ratio.embed (E i)))) :
    Arc X0 F' L' (ρ) v P E B (Ω) (fun i=>d*I i) ((P0).supportExponent+1/2) ((P0).supportExponent+1) 1 u d δ :=by
    let T:= fun i=> d*I i; have ht i:0 < T i:=mul_pos hu.hats.1 (hI i)
    have hK': (P0)=(X0).p:=(h.represents N p m hm.le).vac.symm; have hk:(P1)=(X1).p:=(h.represents N p _ hm).vac.symm
    have hh := h'.prune (e:=d) hI ht (slighter hI ht (w:=d) (by intro i;rfl) hu.hats.1.le hu.hats.2) hu.hats.1.le (show (P1).supportExponent-4+0≤ w from by rwa [add_zero]) (le_of_eq (mul_one d))
    apply ranch (d:=d) H.tunes H.propagate hp (fun i=>(hH i).some) ht (fun i hi j=> congr_arg (d*·) (hT _ hi j)) hK hO hu.hats.1.le ?_ ?_ ?_ ?_ (h.represents N p _ hm).good hh ?_ H.contact (A.levels.transition_mass ..) hO' hr
    · rw [← hk]; exact hu.copper
    · rw [← hk];linarith only
    · intro i; change 2* (d* _) * _ ≤ _; calc _ = d*(2*I i*s i.2):= by ring
                                               _ ≤ _ := mul_le_of_le_one_right hu.hats.1.le (hc i)
    · intro i; exact (le_of_eq (mul_assoc ..)).trans (mul_le_of_le_one_right hu.hats.1.le (hy i))
    · rw [← hK']; linarith only
    linarith only [hu.exp.2]
lemma descended (h:A.Selected)(hm:m<N)(hu:Duty A C m d t u)(hI:∀ i,0<I i)(hJ:∀ i,0<J i)(hT:Occupancy (Ω) (C m)) (hv: Repegs (Ω) (P0).B (fun i=>d*I i) J (1/2) 1 (Names V slotsZ)) {δ:(V×slotsZ)→ℂ} (hr:Arc (X0) F' L' (ρ) v P E B (Ω) (fun i=>d*I i) ((P0).supportExponent+1/2) ((P0).supportExponent+1) 1 u d δ) (hy:∀ i,Dominated (L' i))(hz:∀ i U,((ρ) U).part ((Names V slotsZ).fire i)=coin (X0) (F' i) (L' i) U): Serves (X0) F' (fun i=>profile (X0).activities (L' i)) (ρ) v P E B (Ω) J (P0).supportExponent 1:=by
    have hA:= h.represents N p m hm.le
    apply thru («Z»:=1) hr hA.good.labels (fun i=>mul_pos hu.hats.1 (hI _)) hu.hats.1.le hT (by linarith only [hu.exp.1]) ?_ hJ (hA.vac ▸ hv) zero_le_one (by simp) ?_ hz hy (fun U=>(Tour.bright A h N p m hm.le U).ne')
    · rw [hA.vac]; exact hu.stakes.1.trans_eq (by ring)
    rw [hA.vac,one_mul]; exact hu.stakes.2
end YM.MergeProof.Ribbons.ManyCopies
