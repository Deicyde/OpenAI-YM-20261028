import YM.MergeProof.North.Thunder
import YM.OPE.Replicas.Belvedere

/-!
# Many slots per cell: port of YM/MergeProof/North/Thunder.lean

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
variable (H:History G) {N m p k:ℕ}(u δ:ℕ→ℝ)(r:ℕ→ℕ)
    (D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m))
variable (E:∀ m:ℕ,V→Site (H.S.side m p))(o:∀ m:ℕ,(V×slotsZ)→Site (H.S.side m p))(P:V→ Motion)(v:V)(w:ℕ→slotsZ→ℝ)(B:V→Equiv.Perm V)
   (F:∀ m:ℕ,(V×slotsZ)→ Config G (H.S.side m p)→ℂ)(L:∀ m:ℕ,(V×slotsZ)→ℕ→ Config G (H.S.side m p)→ℂ)(a:(V×slotsZ)→ Config G (H.S.side N p)→ℂ)
set_option quotPrecheck false
local notation "Ξ"=> (Names V slotsZ)
local notation "f!"=> (fun i=> F i)
local notation "P'"=> H.levels.budget
local notation "ω"=> (fun i (j:(V×slotsZ))=> w i j.2)
local notation "R"=> H.rep N p
local notation "Q"=> R N
variable (h:H.Selected) (h':Moonlit H r δ u D)(ht:Matchup H r δ p N k o (fun i (j:(V×slotsZ))=> w i j.2) (Names V slotsZ))
    (hs:∀ (j:slotsZ), Stately H u k N p (fun i=>o i (v,j)) (fun i=> w i j) (fun i=>F i (v,j)) (fun i=> L i (v,j)) (a (v,j)) D)
    (hP:∀ j,j≠v→B j v=j)(hV:∀ j,j≠v→∀ b:slotsZ,a (j,b)=stepUp (P j) (E N j) (a (v,b)))
local notation "Ω"=> manifest H p N F L
local notation "y"=> tapes H p N L
variable (hM:∀ m:ℕ, k ≤ m→ m≤N→∀ i,Dominated (L m i)) (hT:∀ m:ℕ, k ≤ m→m≤N→∀ i,i≠v→∀ j:slotsZ,F m (i,j)=stepUp (P i) (E m i) (F m (v,j))∧ tapes H p N L m (i,j)=floatUp (P i) (E m i) (tapes H p N L m (v,j))∧o m (i,j)=affine (P i).1 (E m i) (o m (v,j)))
variable (σ χ:ℕ→ℝ)
-- package explicit.Seen.
structure Thor (k:ℕ):Prop where
    moon (N p i:ℕ): k ≤ i→∀ (h:i<N), Volant (H.levels.clock.op i p) (D N p i h) (r i) ((H.levels.budget (i+1)).supportExponent-4) (σ i) ((H.levels.budget i).supportExponent+1/2) ((H.levels.budget i).supportExponent+1) 1 (χ i) ∧ Unites (H.levels.clock.op i p) (D N p i h) (r i) ((H.levels.budget (i+1)).supportExponent-4) (σ i) ((H.levels.budget i).supportExponent+1/2) ((H.levels.budget i).supportExponent+1) 1 (χ i)
    suns (i):k ≤ i→ Duty H r i (δ i) (σ i) (χ i)
local notation "Z"=> (H.levels.clock.op m p)
variable {S:∀ m:ℕ,m≤N→ Config G (H.S.side m p)→Poly (Names V slotsZ)}
    {μ:ℕ}(hr:Thor H δ r D σ χ μ)(ht':μ≤k)(hQ: Migrating H k p N E)
    (hΔ: ∀ m:ℕ, k ≤ m→∀ hm:m<N, S m hm.le=(H.levels.clock.op m p).push ((H.rep N p (m+1)).beta) (S (m+1) hm))
    (hΩ:S N le_rfl=birth (Names V slotsZ) (H.rep N p N) a) (hp:∀ m:ℕ,k ≤ m→∀ hm:m≤N,Integrable (S m hm) (prior G _))
-- duplicate h' edit
local notation "W"=> (fun i (j:(V×slotsZ))=>δ i*w (i+1) j.2)
include h ht hs hP hT hM hr ht' hQ hΔ hp
lemma uprising (hi:k ≤ m)(hm:m<N)(htR:Serves (R (m+1)) (F (m+1)) (y (m+1)) (S (m+1) hm) v P (E (m+1)) B (o (m+1)) (ω (m+1)) (topPitch H N (m+1)) 1):∃ l:(V×slotsZ)→ℂ, (Serves (R m) (F m) (y m) (S m hm.le) v P (E m) B (o m) (ω m) (topPitch H N m) 1 ∧ (∀ i,W m i*‖l i‖≤1) ∧ (∀ i,i≠v→ ∀ j:slotsZ,l (i,j)=scalar (P i) (l (v,j))) ∧ Arc (R m) (F m) (L m) (S m hm.le) v P (E m) B (o m) (W m) ((P' m).supportExponent+1/2) ((P' m).supportExponent+1) 1 (χ m) (δ m) l):=by
    have hx:= hi.trans m.le_succ ; choose c ε s t hξ he hy hh hK using fun i=>(hs i).sways m hi hm; let l (i:(V×slotsZ)):= if i.1=v then ε i.2 else scalar (P i.fst) (ε i.2)
    have hz(i:V)(hp:i≠v)(j): l (i,j)=scalar (P i) (l (v,j)):=by simp [l,hp]
    obtain ⟨hY,hM'⟩:= hr.moon N p m (ht'.trans hi) hm; have hb:= hr.suns m (ht'.trans hi); let x':=(Z).ratio.parent ∘ o (m+1)
    have hP':(Z).ratio.parent ∘ o (m+1)=o m:= ht.pins m hi hm
    have hF:E (m+1)=(fun i=>(Z).ratio.embed (E m i)):= (hQ.mare m hi hm).symm
    have hA:(P' (m+1)).supportExponent-4 ≤ topPitch H N (m+1):=by unfold topPitch;split <;> linarith only
    have hU:Arc (R m) (F m) (L m) ((Z).push ((R (m+1)).beta) (S (m+1) hm)) v P (E m) B x' (W m) ((P' m).supportExponent+1/2) ((P' m).supportExponent+1) 1 (χ m) (δ m) l:=by
       apply freshArc H N m p r h hm hb hY hM' (ht.pos (m+1) hx hm) (hF ▸ htR) hA (ht.next m hi hm) (hP'.symm ▸ (ht.occ m hi hm.le)) (fun i _ j=> rfl) (s:=s) (r:=t) (fun i=> he _) (fun i=>hy _)
       · intro i ; refine ⟨c i,hξ i,?_⟩; change Tale _ _ (x' (v,i)) _ _ _ _ (l (v,i)) _ _ _; rw [show x'=o m from hP',show l (v,i)=ε i from if_pos rfl]; exact hK i
       · refine chimes_parent H (fun i ha j=>?_) (v:=v) (fun i ha=>⟨hP i ha,fun j=>?_⟩) (fun i ha j=> (hT m hi hm.le i ha j).2.1)
         · have he:= (hT (m+1) hx hm i ha j).2.2; rw [hF] at he; exact he
         have he:=hT (m+1) hx hm i ha j; rw [hF] at he; exact ⟨he.1,he.2.1,hz i ha j⟩
       exact fun i=>(h.represents N p (m+1) hm).good.labels.moves _ _
    rw [hΔ m hi hm]; refine ⟨l,?_,fun i=>?_,hz,hP' ▸ (show Arc _ _ _ _ _ _ _ _ ((Z).ratio.parent ∘ o (m+1)) _ _ _ _ _ _ _ from hU)⟩
    · have hI := hp (m+1) hx hm; have hχ(i) :(fun U=> (S (m+1) hm U).part ((Names V slotsZ).fire i))=Ω (m+1) i:= funext (fun U=> htR.sold.relay (hM (m+1) hx hm) ((h.represents N p (m+1) hm).good.labels) U |>.1 i)
      have hχ'(i:(V×slotsZ)):(fun U=> (((Z).push ((R (m+1)).beta) (S (m+1) hm)) U).part ((Names V slotsZ).fire i))=Ω m i:=by
          rw [push_get (H.levels.transition_mass ..) hI,hχ]; rcases i with ⟨i,j⟩; by_cases hc:i=v
          · subst i; exact ((hs j).feeds m hi hm).symm
          have hϕ (x:ℕ)(hx': k ≤ x)(hm':x≤N): Ω x (i,j)= stepUp (P i) (E x i) (Ω x (v,j)):=by
             unfold manifest; rw [(hT x hx' hm' i hc j).1]; exact opals (P i) H h hm' (E x i) _ ((h.represents N p x hm').good.labels.moves _ _).some (hM _ hx' hm' _) (hM _ hx' hm' _) (hT _ hx' hm' i hc j|>.2.1)
          rw [hϕ (m+1) hx hm, hϕ m hi hm.le,hF]; have hβ : Integrable (Ω (m+1) (v,j)) (prior G _):=by
             rw [← hχ]; exact ((Poly.get ((Names V slotsZ).fire (v,j))).restrictScalars ℝ).integrable_comp hI
          have h':=unison (P i) H m N p 0 (E m i) (Ω (m+1) (v,j)) hβ; simp only [blast,pow_zero,one_smul] at h'; exact h'.trans (congr_arg _ ((hs j).feeds m hi hm).symm)
      rw [← hP',show topPitch H N m=(P' m).supportExponent from if_neg hm.ne]; exact descended H N m p r h hm hb (ht.pos _ hx hm) (ht.pos m hi hm.le) (hP'.symm ▸ ht.occ m hi hm.le) (hP'.symm ▸ ht.runs m hi hm) hU (hM m hi hm.le) (fun i U=> congr_fun (hχ' i) U)
    have he : ‖l i‖=‖ε i.2‖:=by unfold l; split; rfl; exact norm_scalar ..
    rw [he]; exact le_trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (ht.pos _ hx hm i|>.le) hb.hats.2) (norm_nonneg _)) (hh i.snd)
end
end YM.MergeProof.Ribbons.ManyCopies
