import YM.MergeProof.Caprese
import YM.FullVolume.Fields.Tarry
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
variable (o:∀ i:ℕ,V→Site (C.side i p))(s:V→ C.label d)(t:V→Motion)
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "Y!"=> C.ref d
local notation "F!"=> C.labels.level d
local notation "s!"=> C.localSection d
local notation "P!"=> C.path.levels.budget
variable (b:Config G (C.side N p)→ℂ)
    (Z:∀ i:ℕ, Coefficient (C.labels.level d) (C.side i p)) (a:ℕ→ℝ)(w:ℝ)(ζ:ℕ→ℝ)
local notation "U"=>fun i=> stepUp (t i) (o N i) b
include H
-- actual. purchase simply w march. protect E layered.op
lemma caking {B:Census V}(hQ:k<N)(hK:C.ref d≤k)(hw:0<w) (he:Yeast C.path C.params s! ζ u ψ k N p (fun i=> march (fun _:Unit=>w) φ k i ()) b D Z a)
    (hf:Fiesta C.path F! ζ ψ k)(hN: Retain C.path r δ u D N p k)(hi:∀ i,k ≤ i→ φ i ≤1)(hr:Brine C.path k δ φ)(hR:Monotone r)(hc:Continuous b)
    (hp:Migrating C.path k p N o)(hv:Occupancy (o k) (r k))(hx: Drake B (C.path.levels.budget k).B (o k))(i:B.Mode): ‖C.omega N p (fun V=> ∏ j∈ i.val,(U) j V)‖* Poly.toll (fun _=>w) i ≤ Real.exp (Fintype.card (Site (C.side k p))* Vac.treasury C.path.levels k+ Fintype.card V*(5:ℝ)):=by
    let τ : Course C N p k:= ⟨C.path.β N p,hQ.le,fun i _ _=>rfl,fun i h=> Overlay.beta_positive H.wilson h⟩; let F:= Accent.birth B (R N) (U); let q:=τ.flow F
    have hq:∀ i:ℕ,k ≤ i→∀ h:i<N,q i h.le=(C.path.levels.clock.op i p).push ((R (i+1)).beta) (q (i+1) h):=by
       intro i hi hj; unfold q; rw [τ.flow_step _ i hj,τ.same (i+1) (hi.trans i.le_succ) hj]
    have hN':q N le_rfl=F:=τ.flow_self F; have hk(j:V):Continuous ((U) j):=by unfold stepUp Motion.scalar;dsimp only;split;exact (hc.comp (continuous_pull ..)).star; exact hc.comp (continuous_pull ..)
    have ha: Integrable (q N le_rfl) (prior G (C.side N p)):=by
       rw [hN']; exact ((hatCont C N p (U) hk (show Continuous (R N).eval by rw [(H.wilson.starts ..).2]; exact bare_cont _) B).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    let v i:= march (fun _:Unit=>w) φ k i (); let x:= march (fun _:V=>w) φ k; have hX:=desal C.path r k p N δ φ o (fun _=>w) (fun _=>hw) hr B hp hx hR hv
    have h'(j:V): (fun i=>x i j)=v:=by
        funext i; induction i with
        | zero=> rfl
        | succ i IH=> by_cases h:k ≤ i
                      · exact (show x (i+1) j=φ i*x i j from by simp only [x,march,h,if_true]).trans ((congr_arg (φ i*·) IH).trans (show φ i*v i=v (i+1) from by simp only [v,march,h,if_true]))
                      unfold x v; simp [march,h]
    let f i j:= liftF C.path s! N p (t j) (fun m=>o m j) Z i; let g i j:= liftK C.path N p (t j) (fun m=>o m j) Z i
    have hw' i (h:k ≤ i): 0 < v i:= march_pos _ _ _ _ _ (fun _=>hw) hr i h _
    have hz(j:V): ∃ u':∀ i:ℕ,ℕ → Config G (C.side i p)→ℂ, Wild C.path u k N p (fun m=>o m j) (fun i=>x i j) (fun i=>f i j) u' ((U) j) D ∧ ∀ i:ℕ,k ≤ i → i≤N→ profile (R i).activities (u' i)=g i j:=by
       rw [h' j]; apply baker C.path C.params s! ζ u ψ k N p (t j) (fun m=>o m j) v b D Z a H.wilson (H.sections d) he hQ.le (fun i h _=> hw' i h) (fun i h _=> ?_) hf (fun m h hx=> (congr_fun (hp.mare _ h hx) j).symm) (fun m h hx=>?_)
       · rw [show v (i+1)=φ i * v i by simp only [v,march,h,if_true]]; exact mul_le_of_le_one_left ((hw' i h).le) (hi i h)
       obtain ⟨u,z,h',ht'⟩:= hN.days m h hx; exact h'.propagate
    choose u' hL hZ using hz
    let K m (j:V):=u' j m; have ht(j:V): Nectar C.path u D p N k o x f K (U) j := by obtain ⟨h1,h2,h3,h4,h5⟩:=hL j; exact ⟨h1,h2,h3,h4,h5⟩
    have hS:=Accent.Frost.upper C.path r δ u D p N o x f K (U) H.wilson hQ.le hX hN ht hq hN' ha k le_rfl hQ.le|>.2.2
    have hh:v k=w:=by unfold v; rw [marines k φ (fun _:Unit=>w) (fun _=>hw)]
    rw [show x k=(fun _=>w) from marines k φ _ (fun _=>hw),show tapes _ p N K k=g k from funext fun j=>hZ j k le_rfl hQ.le, show topPitch C.path N k=(P! k).supportExponent from if_neg hQ.ne] at hS
    have hE:=he.rates k le_rfl hQ.le; rw [show march (fun _:Unit=>w) φ k k ()=w from hh] at hE
    have HV (i:V)(V':Config G (C.side k p)):= toasted C N k p d H Z ζ hK hQ.le (t i) (o k i) ((he.ticks k le_rfl hQ.le).2) hw.le hE (hf.coin k le_rfl) V'
    have Hi:Vault (fun _:V=> w) (f k) (g k) 2 1:=⟨fun i V=>(HV i V).1,fun i V=> by simp_rw [← Finset.mul_sum]; exact (HV i V).2⟩
    refine (vista _ B N p k (U) hq hN' ha H.wilson hQ.le i (continuous_integrable _ (continuous_finsetProd _ fun i _=> hk i)) hS Hi (fun _=>hw) (C.path.levels.budget k|>.exponent_pos.le)).trans_eq ?_
    ring_nf
end YM.MergeProof.Accent
#print axioms YM.MergeProof.Accent.caking
