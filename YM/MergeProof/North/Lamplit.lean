import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Mercury
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Leibniz
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Movement
import YM.MergeProof.North.Shasta
import YM.MergeProof.North.Tan
import YM.MergeProof.North.Verve
import YM.MergeProof.South.Admit
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Courier
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.RibbonRise
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.TwoMasks
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Blueprint
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.TagsHood
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Stage.Iris
import YM.UVNext.COUPLING_RESET.Tuning


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Source Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}
variable (H:RG.History G) (d:ℕ) {N m p:ℕ}
set_option quotPrecheck false
local notation "F"=> (Labels.frames G).level d
local notation "B"=> Next.Foundations.localSection G d
local notation "A"=> Next.Foundations.hol G
local notation "f"=> H.S.side (m+1) p
local notation "c"=> H.S.side m p
local notation "X0"=> H.rep N p m
local notation "X1"=> H.rep N p (m+1)
local notation "Z"=> H.levels.clock.op m p
local notation "L"=> (H.S.block m)
local notation "χ"=> ((↑(H.S.block m).val:ℂ)^d)
local notation "P0"=> (H.levels.budget m)
local notation "P1"=> (H.levels.budget (m+1))
variable {x e t u w a y :ℝ} {I: V→ℝ} {J:V→ℝ}
    {θ:Config G (H.S.side (m+1) p)→Poly (Bud V)} {o:V→Site (H.S.side (m+1) p)}
    {G': V→ Config G (H.S.side (m+1) p)→ℂ} {K: V→ℕ→ Config G (H.S.side (m+1) p)→ℂ}
    {D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)} (C:ℕ→ℕ)
    {P:V→Motion}{E:V→Site (H.S.side m p)}{v:V}
    {l:V→ℂ}
set_option quotPrecheck false
local notation "Ω"=> (Z).ratio.parent ∘ o
local notation "ρ"=> (Z).push (X1).beta θ
local notation "T"=> fun i=> (Z).ratio.embed (E i)
local notation "kp"=> fun i=> profile (X1).activities (K i)
-- No P v base assumption because symmetry from replicas explicitly ALL i says not trivial but drives proof at v too. uses actual budget.Y.S.
lemma fuseNext (h:H.Selected)(hm:m<N)(hD:Duty H C m e t u)(ht:Volant Z D (C m) ((P1).supportExponent-4) t ((P0).supportExponent+1/2) ((P0).supportExponent+1) 1 u)
    (hI:∀ i,0<I i)(hJ:∀ i,0<J i)(hs:Served (X1) G' (kp) θ o I w 1)(hX:(P1).supportExponent-4≤w)(hO:Occupancy o (C m))(hO':Occupancy ((Z).ratio.parent ∘ o) (C m)) (hk:∀ i,Dominated (K i))
    (hr:Blade (X1) 0 (G' v) (kp v) 0 a)(ho:o=T) (hp:∀ i,G' i=stepUp (P i) ((Z).ratio.embed (E i)) (G' v) ∧ kp i=floatUp (P i) ((Z).ratio.embed (E i)) (kp v))
    (hR:Throws H N p m D A B x)(hx:0≤x)
    (hC:∀ i,2*I i*(2*a)≤1)(hq:∀ i,I i*(‖χ⁻¹‖*(x*a))≤1) (hy:Repegs E (P0).B (fun i=>e*I i) J (1/2) 1 (Bud V))(hθ:Integrable θ (prior G _)) :
    ∃ Q : Coefficient F c, Q.Format 0 A (X0) ∧ Q.remBound 0 (X0) (kappa H m) (x*a) ∧ (F).coeffSize Q.x ≤ x*a ∧
       Served (X0) (fun i=> radiant (χ⁻¹) (P i) (E i) (Q.exponentialEntry 0 B (X0))) (fun i=> sunny X0 Q.forced (P i) (E i) (χ⁻¹)) (ρ) E J ((P0).supportExponent) 1:=by
    obtain ⟨s,hS,Q,hQ,hY⟩:= tossing H B A hr (hk v) h hm hx ht.propagate hR; have hb:= h.represents N p _ hm; let f':= G' v; have hP:(Ω)=E:=by funext i; dsimp only [Function.comp_apply]; rw [ho]; exact (Z).ratio.embed_parent _
    choose K' hF hK hh using fun i=> sparkling H _ B Q (P i) (E i) (χ⁻¹) h 0 hm.le (Next.Foundations.sound G d) hQ.format hQ.bound
    let a'(i):= radiant (χ⁻¹) (P i) (E i) (Q.exponentialEntry 0 B (X0)); let t':= ρ
    have hy'(i): (fun U=> (ρ U).part ((Bud V).fire i))=coin (X0) (a' i) (K' i):=by
       rw [push_get (H.levels.transition_mass m p (X1).beta) hθ]; rw [show (fun U=>(θ U).part ((Bud V).fire i))=coin (X1) (G' i) (K i) from (funext fun U => hs.relay hk hb.good.labels U |>.1 i)] -- timeout?
       obtain ⟨k⟩:= hb.good.labels.moves (P i).1 (T i)
       let f':= coin (X1) (G' v) (K v); have hx': coin (X1) (G' i) (K i)=stepUp (P i) (T i) f':= by rw [(hp i).1]; exact MergeProof.Float.opals (P i) H h hm (T i) _ k (hk v) (hk i) (hp i|>.2)
       rw [hx',show coin (X0) (a' i) (K' i)= _ from hh i]; have he:= starship H (P i) (E i) (χ⁻¹) f' d hQ.agrees (MergeProof.Float.spill_in hr hb.good (hk _)) _ (show (1:ℂ)=χ*χ⁻¹ from (mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast (L).pos.ne'))).symm)
       unfold radiant at he; rw [one_smul] at he; exact he.symm
    have hT(i):∃ s:Set Wing,s.Finite∧Tale s (o i) ((Z).ratio.parent (o i)) 1 (G' i) (profile (X1).activities (K i)) (profile (X0).activities (K' i)) 0 (2*a) (‖χ⁻¹‖ * (x*a)) D:=by
       obtain ⟨π⟩:=hb.good.labels.moves (P i).1 (T i); have hh := hY.gain ht.propagate (P i) (E i) π (show scalar (P i) χ=χ from by unfold Motion.scalar; split <;> simp) |>.pitch 1 (χ⁻¹) (show (1:ℂ)=χ*χ⁻¹ from (mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast (L).pos.ne'))).symm)
       refine ⟨_,hS.image (Wing.labelRoute π),?_⟩
       rw [show (Z).ratio.parent (o i)= _ from congr_fun hP i,(hp i).1, (show profile (X1).activities (K i)=_ from (hp i).2),← hF,ho]; simp only [scalar_z, one_mul,norm_one,one_smul,show affine (P i).1 (E i) 0=E i from by simp [affine],show affine (P i).1 ((Z).ratio.embed (E i)) 0=(Z).ratio.embed (E i) from by simp [affine]] at hh
       exact hh -- affine simp
    have he:= Duty.pre (δ:=0) (s:=fun _=>2*a) (r:=fun _=>‖χ⁻¹‖*(x*a)) H N m p C h hm hD ht hI hJ hs hX hO hO' (hP.symm ▸ hy) hK (fun U i=> congr_fun (hy' i) U) hC hq hT
    rw [hP] at he; refine ⟨Q,hQ.format,hQ.bound,?_,?_⟩
    · have he:=hQ.leadP; rw [sub_zero] at he; exact (le_mul_of_one_le_left (Work.G08.size_nonneg ..) (orbitCost_one_le ..)).trans he
    rw [show (fun i=> sunny X0 Q.forced (P i) (E i) χ⁻¹)=_ from (funext hF)]; exact he
end YM.MergeProof.Ribbons
