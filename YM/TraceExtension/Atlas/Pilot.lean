import YM.TraceExtension.Chart.Line
import YM.Next.MAXWELL.Lit
/-!
   Alignment of measuring frame: SO(4) actually predicted from angular shell flux. Orbit hymns. Local position.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction OS OS.Ground Spec MeasureTheory Wilson
open RG Terrace MergeProof.East Next.Rank Next.Rank.East Next.UVStress Further.CorrectedLift Climb
open Analysis TraceExtension Boundary Over Org Work.A05 Table
open scoped Topology BigOperators InnerProductSpace Classical ContDiff
variable {G: Gauge} {C: Family G}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book} (F:Final C f S)
variable {H:(Cells.standard C).Hierarchy}{J:Scaling S}{V:∀ i,Vane C i}
variable {Z:Terrace.Arch C}(hb:(𝓛:Filter _) ≤ f.fuse)
local notation "F₀"=> Bel C.book
abbrev standard4(C:Family G):= Shelves.materialB C none
abbrev turns(C:Family G):= Maxwell.Free.gear C.book.grid
open UVNext.FreeStress
lemma stages (h:G.Simple):∃ Q: Org.MaxwellData C,Q.T.W=Maxwell.Free.scheme C.book.grid ∧ Q.T.K=turns C∧ Q.T.J=standard4 C ∧ Q.T.κ=1∧ Tensorial Q.T.K Q.T.J:=by
    obtain ⟨P,hP,hK⟩:= Maxwell.Free.maxwell_supplies C h 1 one_ne_zero
    obtain ⟨Q,hQ,hE,hW,hV,ht,hR,hL⟩:= UVNext.FreeStress.names (-1) h P (by norm_num)
    norm_num at hE
    refine ⟨Q,hV.trans ?_,ht.trans ?_, hQ.trans Over.canonical_meter.symm,hE,ht.symm ▸ hR⟩<;>rw[hP]<;>rfl
lemma left_meter (H:S.Hierarchy)(X:Spec.Algebra S)(h:Spec.Locals X H.spin): StressLaws S (reCenter S X.energy) X.derivatives.deriv X.turns.lie:=by
    let t(i j:Axis):= -(expectation S 4 (X.energy i j))
    have hp : ∀ i j,t i j=t j i:=by intro i j; unfold t; rw[h.conserved.symmetric i j]
    have hc : reCenter S X.energy=X.energy+UVNext.FreeStress.fossil t:=by funext i j; change centering S 4 (X.energy i j)=X.energy i j+t i j • _;rw [value_center]; unfold t; rw [neg_smul];abel
    rw [hc]; exact UVNext.FreeStress.add_unit H h.charges t hp
section
variable {L:Register G}{S:Table L}{J₀:S.Stress} {U:DiffPlan S}{R:S.Rotation}
lemma sling (HE:S.Smooth)(g:StressLaws S J₀ U.deriv R.lie)(H:Lighthouse L)(HH : Table.Hierarchy (Bel L))(hk:H.Goes L HH.spin)(X:Scaling S)(hf:X.meter J₀ H.J)(hz: ∀ N D (M:ℝ),1≤M→X.jets N D 0 M)(d:ℕ)(j:Spin.Ind) :
    Tendsto (fun k=> (X.xi k)⁻¹ • Spin.transport R.lie (X.U k d) j) atTop (𝓝 (H.κ • Spin.attach H.K d j)):=by
    obtain ⟨t,ht⟩:= Observer.exists_reads HH d; obtain ⟨D,N,M,hM,hB⟩:= Observer.enough_all t d
    let hv:=hz N D M hM; apply clm_convergence; intro x
    refine recover_on t (fun o=> o.test d) ht (fun o k=> o.moving X d k) ?_ _ _ ?_
    · intro o ho v; have ht:= hB D le_rfl N le_rfl M le_rfl o ho
      exact o.reads_converge X hv ((Nat.le_succ _).trans ht.total) ht.rest ht.fits d ((Nat.le_succ d).trans ht.caps) v
    intro o ho; exact o.gets_rotation HE H HH.smooth hk g X (hB D le_rfl N le_rfl M le_rfl o ho) hv hf j x
end
set_option maxHeartbeats 800000 in
lemma stagesL (h:G.Simple)(h₁:Scribe f J V Z F.sector 𝓛 F.room.kernel H)(d:ℕ)(j:Spin.Ind):
    Tendsto (fun k=> Spin.transport F.sector.turns.lie (J.U k d) j) atTop (𝓝 (Spin.attach (turns C) d j)):=by
    obtain ⟨P,q,hK,hJ,hκ,hT⟩:= stages (C:=C) h
    let W:Scaling S:=⟨J.U,fun _=>1,J.r,fun _=>one_pos,J.positive,J.later,J.drips⟩
    let R:= F.room.kernel;let U:= F.sector.derivatives; let Y:= reCenter S F.sector.energy
    have hp: W.meter Y P.T.J :=by
       intro a b; rw [hJ];refine (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h₁.main a) b).congr (fun k=>?_)
       let f:= (J.U k 4).symm;let r:=J.r k; change (r^ (4:ℕ)) • f (Y a b)= f ((↑((1:ℝ)⁻¹ * r^4):ℂ) • Y a b); rw[inv_one,one_mul,map_smul]; exact RCLike.real_smul_eq_coe_smul _ _
    have hh (N D M) (hv:1 ≤ M): W.jets N D 0 M:= comparison_jets R F.phase.transport.derivatives P.hT P.lit.pales _ h₁.monorail.approach N D 0 M (zero_lt_one.trans_le hv)
    have ht:= sling R.smooth (left_meter R F.sector F.phase.transport) P.T P.hT P.lit W hp hh d j
    rw[hK,hκ,one_smul] at ht; exact ht.congr (fun i=>by rw[show W.xi i=1 from rfl,inv_one,one_smul])
end YM.Trace.Pilot
