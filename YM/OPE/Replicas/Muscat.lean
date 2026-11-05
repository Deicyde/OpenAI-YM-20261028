import YM.MergeProof.North.Muscat
import YM.OPE.Replicas.Thunder

/-!
# Many slots per cell: port of YM/MergeProof/North/Muscat.lean

Most of the proof can be shared verbatim with that for pairs. Costs at every step
use the same register though the group being transported can now be quite different.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
section
variable {slotsZ : Type}[Fintype slotsZ][DecidableEq slotsZ] {V : Type}[Fintype V][DecidableEq V]{G:Gauge}
variable (H:History G) {N m p k:ℕ}(δ:ℕ→ℝ)(r:ℕ→ℕ)
    (D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m))
variable (E:∀ m:ℕ,V→Site (H.S.side m p))(o:∀ m:ℕ,(V×slotsZ)→Site (H.S.side m p))(P:V→ Motion)(v:V)(w:ℕ→slotsZ→ℝ)(B:V→Equiv.Perm V)
set_option quotPrecheck false
local notation "Ξ"=> (Names V slotsZ)
local notation "P'"=> H.levels.budget
local notation "ω"=> (fun i (j:(V×slotsZ))=> w i j.2)
local notation "R"=> H.rep N p
local notation "Q"=> R N
variable {l:(V×slotsZ)→ℂ}(σ χ:ℕ→ℝ){μ j:ℕ}
    {S:∀ m:ℕ,m≤N→ Config G (H.S.side m p)→Poly (Names V slotsZ)}
    (h:H.Selected) (hr:Thor H δ r D σ χ μ)(ht':μ≤k)(hQ: Migrating H k p N E)
    (hΔ: ∀ m:ℕ, k ≤ m→∀ hm:m<N, S m hm.le=(H.levels.clock.op m p).push ((H.rep N p (m+1)).beta) (S (m+1) hm))
    (hp:∀ m:ℕ,k ≤ m→∀ hm:m≤N,Integrable (S m hm) (prior G _))
    (ht:Matchup H r δ p j k o (fun i (j:(V×slotsZ))=> w i j.2) (Names V slotsZ)) (hO:∀ m:ℕ, k ≤ m→m≤j→∀ i,i≠v→∀ b:slotsZ,o m (i,b)=affine (P i).1 (E m i) (o m (v,b)))
local notation "W"=> (fun i (j:(V×slotsZ))=>δ i*w (i+1) j.2)
variable (x:ℕ→ℝ)
include h hr ht' hQ hΔ hp ht hO
local notation "d'"=> (fun i (b:slotsZ)=> (1:ℝ)/(2*w i b))
structure Sprout (i:ℕ)(hn:i≤N) : Prop where
    flor : ∃ g:(V×slotsZ)→ Config G (H.S.side i p)→ℂ,∃ K:(V×slotsZ)→ℕ→ Config G (H.S.side i p)→ℂ, (∀ b:slotsZ,Blade (R i) (o i (v,b)) (g (v,b)) (profile (R i).activities (K (v,b))) (l (v,b)) (d' i b)) ∧ (∀ j,Dominated (K j)) ∧ May v P (E i) B g (fun j=> profile (R i).activities (K j)) l ∧ Serves (R i) g (fun j=> profile (R i).activities (K j)) (S i hn) v P (E i) B (o i) (ω i) ((P' i).supportExponent) 1
local notation "X"=> Sprout H E o P v w B (S:=S) (l:=l)
variable (hN:j≤N)(hY:∀ m:ℕ,k ≤ m→∀ hi:m<j, MergeProof.Float.Runs (D N p m (hi.trans_le hN)) (H.levels.clock.op m p) (x m)) (hX:∀ m:ℕ,k ≤ m→ m<j → 0 ≤ x m)(hf:∀ m:ℕ,k ≤ m→m<j→∀ i,x m*w m i ≤ w (m+1) i)
include hY hN hX hf
lemma musky (hk:k ≤ m)(hm:m<j)(hc:X (m+1) (hm.trans_le hN)) : ∃ g K, Arc (R m) g K (S m (hm.le.trans hN)) v P (E m) B (o m) (W m) ((P' m).supportExponent+1/2) ((P' m).supportExponent+1) 1 (χ m) (δ m) l ∧ X m (hm.le.trans hN):=by
    have hi:k ≤ m+1:= hk.trans m.le_succ; have hx:= hm.trans_le hN; obtain ⟨g,K,hb,hd,he,hR⟩:=hc.flor
    have hA:= hr.suns m (ht'.trans hk); obtain ⟨hK,hh⟩:= hr.moon N p m (ht'.trans hk) hx
    let Z:=H.levels.clock.op m p; have hP: (H.levels.clock.op m p).ratio.parent ∘ o (m+1)=o m:= ht.pins m hk hm
    have hS:E (m+1)= fun i=> (H.levels.clock.op m p).ratio.embed (E m i):= (hQ.mare m hk hx).symm
    have hv(i:(V×slotsZ)):2*w (m+1) i.2*d' (m+1) i.snd ≤1:= by rw [mul_div_cancel₀ _ (by have he:0<w (m+1) i.2:= ht.pos (m+1) hi hm i; positivity)]; -- edit
    obtain ⟨G,F,hG,hF,hφ,hC,hU⟩:= flaring H r h hx hA hK hh (ht.pos (m+1) hi hm) (hS ▸ hR) (by linarith only) (ht.next m hk hm) (hP.symm ▸ ht.occ m hk hm.le) (fun _ _ _=>rfl) (fun i he j=> by rw [show _ = E (m+1) i from (congr_fun hS i).symm]; exact hO (m+1) hi hm i he j) (hS ▸ he) hd hb hv (hY m hk hm) (hX _ hk hm) (hp _ hi hx)
    have hT := descended H N m p r h hx hA (ht.pos _ hi hm) (ht.pos m hk hm.le) (hP.symm ▸ ht.occ m hk hm.le) (hP.symm ▸ ht.runs m hk hm) hU hG hF
    rw [hP,← hΔ m hk hx] at hU hT
    refine ⟨G,F,hU,⟨G,F,fun i=>?_ ,hG,hφ,hT⟩⟩
    have he:=hC i; rw [hP] at he; apply he.more
    change x m*(1/(2*w (m+1) i)) ≤ 1/(2*w m i); rw [← mul_div_assoc]; have hP:0 < w (m+1) i:= ht.pos (m+1) hi hm (v,i);have ht:0 < w m i:=ht.pos m hk hm.le (v,i); exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by linarith only [hf m hk hm i])
end
end YM.MergeProof.Ribbons.ManyCopies
