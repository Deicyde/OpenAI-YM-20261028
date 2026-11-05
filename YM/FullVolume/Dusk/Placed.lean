import YM.MergeProof.Glacier
import YM.FullVolume.Dusk.Mauve
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Exponential
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V} {G:Gauge}(C:Family G)(N k m p d:ℕ)
local notation "R"=> C.path.rep N p
variable (H:C.Makes) {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Ponds C W u ψ φ δ (fly C.path.levels) r D p k N)
variable (o:∀ i:ℕ,V→Site (C.side i p))(s:V→ C.label d)(t:V→Motion)
set_option quotPrecheck false
local notation "U"=> (fun i:V=> item C d N p (s i) (fun j=>o j i) (t i))
variable {w:V→ℝ}
include h H
lemma occursT {B:Census V} (hQ:k<N)(hK:C.ref d≤k)(hw:∀ i,0<w i)(hr:∀ i,w i*moneys C d k N p (s i)≤ fly C.path.levels d k)
    (hp:Migrating C.path k p N o)(hv:Occupancy (o k) (r k))(hx: Drake B (C.path.levels.budget k).B (o k))(i:B.Mode): ‖C.omega N p (fun V=> ∏ j∈ i.val,U j V)‖* Poly.toll w i ≤ Real.exp (Fintype.card (Site (C.side k p))* Vac.treasury C.path.levels k+ Fintype.card V*(6:ℝ)):=by
    let τ : Course C N p k:= ⟨C.path.β N p,hQ.le,fun i _ _=>rfl,fun i h=> Overlay.beta_positive H.wilson h⟩; let b:= Accent.birth B (R N) U; let q:=τ.flow b
    have hq:∀ i:ℕ,k ≤ i→∀ h:i<N,q i h.le=(C.path.levels.clock.op i p).push ((R (i+1)).beta) (q (i+1) h):=by
       intro i hi hj; unfold q; rw [τ.flow_step _ i hj,τ.same (i+1) (hi.trans i.le_succ) hj]
    have hN:q N le_rfl=b:=τ.flow_self b
    have ha: Integrable (q N le_rfl) (prior G (C.side N p)):=by
       rw [hN]; exact ((hatCont C N p U (generics C N p d o s t) (show Continuous (R N).eval by rw [(H.wilson.starts ..).2]; exact bare_cont _) B).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    let P:=h
    have hj:= P.past C (fun _=>d) N k p W u ψ φ δ (fly C.path.levels) r D s o t w H.wilson (fun _=>H.sections d) (fun _=>hK) hQ.le hv hp hx (fun i=>(mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (paid_pos ..) (col_ge C k)) (hw i|>.le)).trans (hr i)) hw
    obtain ⟨F,hF,hx'⟩:=hj
    have hS:= (Frost.upper _ _ _ _ D p N _ (march w φ k) _ F _ H.wilson hQ.le (desal C.path r k p N δ φ o w hw h.stay B hp hx h.mom hv) h.night hF hq hN ha k le_rfl hQ.le).2.2; rw [hx' k le_rfl hQ.le] at hS
    have he : topPitch C.path N k=(C.path.levels.budget k).supportExponent:= if_neg hQ.ne; rw [marines k φ w hw,he] at hS
    have hi:=punctual C N k p d s t H hK hQ.le (o:=o) (fun j=>(hr j).trans (fly_le C k d)) hw
    refine (vista _ B N p k U hq hN ha H.wilson hQ.le i (continuous_integrable _ (continuous_finsetProd _ fun i _=> generics C N p d o s t i)) hS hi hw (C.path.levels.budget k|>.exponent_pos.le)).trans_eq ?_
    ring_nf
end YM.MergeProof.Accent
#print axioms YM.MergeProof.Accent.occursT
