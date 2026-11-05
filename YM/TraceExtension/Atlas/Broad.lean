import YM.TraceExtension.Atlas.Pose
import YM.TraceExtension.Atlas.Film
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East Next.Rank
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S){H:(Bel C.book).Hierarchy}
local notation "F₀"=> Bel C.book
variable (h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{J:Scaling S}{V:∀ i,Vane C i}{Z:Arch C}
variable (h₁:Scribe X J V Z F.sector 𝓛 F.room.kernel H)

def ActA (S:Table C.book) := (Active (F₀))≃ₗ[ℂ] Active S
-- lifted.NT
structure Favor (K:S.Hierarchy)(H:(Bel C.book).Hierarchy)(U:(Active (F₀))≃ₗ[ℂ] Active S):Prop where
    bar (x): U (starA H x)=starA K (U x)
    twist (s x): U (swingA H s x)= swingA K s (U x)
lemma center_f(K:S.Hierarchy)(U:change S 4) (hx:realH K.spin H.spin U)(p:(Active (F₀))≃ₗ[ℂ] Active S)(ht:∀ v: Active (F₀),p v=man K (U v.val)): Favor K H p :=by
   constructor
   · intro x; apply Subtype.ext; rw[ht,star_act,ht,star_act,hx.2];exact (conj_center K _).symm
   intro s x; apply Subtype.ext; rw [ht,swing_act,ht,swing_act,hx.1]; exact (mirror_center K _ _).symm
include h h₁
-- lifts of normalized cover.H
set_option maxHeartbeats 700000 in
lemma firstL : ∃ p:ℕ→ Active (F₀) ≃ₗ[ℂ] Active S, (∀ i,Favor F.room.kernel H (p i)) ∧ Tendsto (fun i=> moveV (S:=S) 4 (J.U i 4) (coverV H F.room.kernel (p i))) atTop (𝓝 1) :=by
    let K:= F.room.kernel
    obtain ⟨T,q,hK,hJ,hκ,hT⟩:= stages (C:=C) h
    have hx:∀ᶠ i:ℕ in atTop, ∃ p:Active (F₀)≃ₗ[ℂ] Active S,Favor K H p ∧ ∀ v:Active (F₀),p v=man K ((J.U i 4) v.val):=by
       filter_upwards [h₁.monorail.units 4] with i hi;obtain ⟨p,hp⟩:= centerV H K _ hi.2;exact ⟨p,center_f K _ ⟨hi.1.signed,hi.1.stars⟩ p hp,hp⟩
    obtain ⟨w,p,hp,hu⟩:=hx.exists
    let P (i) := if he:∃ p:Active (F₀)≃ₗ[ℂ] Active S,Favor K H p∧ ∀ v:Active (F₀),p v=man K ((J.U i 4) v.val) then he.choose else p
    refine ⟨P,fun i=> by unfold P; split; rename_i he; exact he.choose_spec.1; exact hp,?_⟩
    apply Work.A05.clm_convergence; intro x; let v:=man H x
    have he:Tendsto (fun i=> expectation S 4 (J.U i 4 v.val)) atTop (𝓝 0):=by
        have hz:= center_expect K F.phase.transport.derivatives T.hT T.lit.pales J h₁.monorail.approach _ v.val (tendsto_const_nhds (f:=atTop (α:=ℕ)))
        rw [show expectation (F₀) 4 v.val=0 from v.property] at hz; exact hz
    have hZ:Tendsto (fun i=>x-expectation S 4 (J.U i 4 v.val) • ((Bel C.book).unit 4)) atTop (𝓝 x):=by simpa only [zero_smul,sub_zero] using! (tendsto_const_nhds (x:=x)).sub (he.smul (tendsto_const_nhds (x:=(Bel C.book).unit 4)))
    apply hZ.congr'
    filter_upwards [hx,h₁.monorail.units 4] with i hi hk; let U:= J.U i 4;change _= U.symm (coverV H _ (P i) x); have hv:P i v=man K (U v.val):=by unfold P; rw [dif_pos hi]; exact hi.choose_spec.2 _
    apply U.injective; rw[U.apply_symm_apply,coverV_at,hv,map_sub,map_smul,hk.2]; change U _-_= centering S 4 (U v.val)+ _; rw [value_center, show v.val= x-expectation (F₀) 4 x • ((F₀).unit 4) from rfl,map_sub,map_smul,hk.2]; abel
lemma weak_p {n}(P: ℕ→ change S 4) (hp:Tendsto (fun i=>moveV (S:=S) 4 (J.U i 4) (P i)) atTop (𝓝 1)) (v: Fin n→ (Bel C.book).Field 4)(k:ℕ) (ε:ℝ)(he:0 < ε)(s:Set (Points n))(hs:IsCompact s)(hS:s ⊆ conf n): ∀ᶠ i in atTop,∀ x∈s, ‖iteratedFDeriv ℝ k (fun q=>S.classMoment S (fun _=>4) (J.r i • q) (fun j=>P i (v j))) x-iteratedFDeriv ℝ k (fun q=>(F₀).classMoment (F₀) (fun _=>4) q v) x‖ ≤ ε:=by
    let M(i)(j):=(moveV (S:=S) 4 (J.U i 4) (P i)) (v j); let u:=J.U
    have hh(j):Tendsto (fun i=> M i j) atTop (𝓝 (v j)):= Dash.arcing hp (tendsto_const_nhds (x:=v j))
    obtain ⟨T,q,hK,hJ,hκ,hT⟩:= stages (C:=C) h; have hz:= travels_jet F.room.kernel F.phase.transport.derivatives H T.lit.pales J h₁.monorail.approach (t:=fun _ : Fin n=>4) M v hh k s hs hS ε he
    filter_upwards [hz] with i hi x hx; have ht(j): J.U i 4 (M i j)=P i (v j):= LinearEquiv.apply_symm_apply ..
    simp_rw[← ht]; exact hi x hx
lemma uv_p(P:ℕ→change S 4)(hp:Tendsto (fun i=>moveV (S:=S) 4 (J.U i 4) (P i)) atTop (𝓝 1)) {n}(v:Fin n→ (Bel C.book).Field 4)(x:Points n)(hx:x∈conf _): Tendsto (fun i=> S.classMoment S (fun _=>4) (J.r i • x) (fun j=> P i (v j))) atTop (𝓝 ((F₀).classMoment (F₀) (fun _=>4) x v)):=by
    apply Metric.tendsto_nhds.mpr; intro ε he
    filter_upwards [weak_p F h h₁ P hp v 0 (ε/2) (half_pos he) {x} isCompact_singleton (singleton_subset_iff.mpr hx)] with i hi; specialize hi x (mem_singleton x); rw [dist_eq_norm]; apply lt_of_le_of_lt _ (half_lt_self he)
    rw [show ∀ F G:Points n→ℂ, iteratedFDeriv ℝ 0 F x-iteratedFDeriv ℝ 0 G x= iteratedFDeriv ℝ 0 (F-G) x from fun f g=>ContinuousMultilinearMap.ext (fun p=>by simp),norm_iteratedFDeriv_zero] at hi; exact hi
end YM.Trace.Pilot
