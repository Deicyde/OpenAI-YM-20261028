import YM.MergeProof.South.Loft
import YM.MergeProof.South.Swing
import YM.Next.UV_STRESS.Toward
/-!
 # true budget of discrepancy via Wilson.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open GridApprox.Joint GridApprox
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V} {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
variable (L:C.label d)(X:Extra.Histories.Music (C.labels.level d) C.path N p)
local notation "ζ!"=> ζ d
variable (h:Scrim C W u ψ φ δ ζ r D){b:C.label d}{Z:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}{g:ℕ→ℝ} {Q:ℝ}
    (J:ℕ) (K:Stock.Tabs C.path.levels)
local notation "a"=> lens C N k p d L
local notation "U!"=> C.O N p ((s!).terminal b) 0
include H
set_option maxHeartbeats 400000 in
lemma spiker {V:Type}[Fintype V][DecidableEq V]{X:Census V}{x y:ℝ}{w:V→ℝ}{k₁:V→ Config G (C.side k p)→ℂ}{k₂:V→ Box (C.side k p)→ Config G (C.side k p)→ℂ} {o:V→Site (C.side k p)}{f:Config G (C.side k p)→ Marker.Poly X} (s:X.Mode) (M:ℂ)
    (hN:k≤N)(hw:∀ i,0 < w i)(hS:Served (R k) k₁ k₂ f o w (T|>.levels.budget k).supportExponent 1)(hv:Vault w k₁ k₂ x y)(hi:Integrable f (prior G _)) (he:(∫ U,(f U).part s∂prior G _)=(Wilson.partition G (C.side N p) (C.beta N p):ℂ)*M):‖M‖*Poly.toll w s ≤ Real.exp (Fintype.card (Site (C.side k p))* Vac.treasury C.path.levels k+ Fintype.card V*(x+y+2*1)):=by
    let Z':= Fintype.card V; let B:=C.path.rep N p k; let T':= C.path.levels; let Q:= T'.clock; have hb:=H.wilson.represents N p k hN; have h':0<Q.hatCoupling k:= inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (T'.fits.delayed k)))
    have he' : Q.hatCoupling k ≤ B.p.threshold:=by
       rw [show B.p=T'.budget k from hb.vac]; exact le_mul_of_one_le_right h'.le (Real.one_le_exp (sq_nonneg _))
    have hg := (sail hw hS hb.good (Overlay.beta_positive H.wilson hN).le hv (C.path.levels.budget _|>.exponent_pos.le) s hi _ h' he' (History.nonnegative C.path H.wilson N p k hN)).trans (Real.exp_monotone (Vac.suffices_bill H.wilson hN Z' ..))
    rw [he,History.partition_eq T H.wilson N p k hN,norm_mul,Complex.norm_real,Real.norm_of_nonneg (partition_pos _).le,mul_comm (Wilson.partition ..),show (Wilson.partition G (C.path.S.side N p) (C.path.β N p N))=Wilson.partition G (C.side N p) (C.beta N p) from rfl,mul_div_cancel_right₀ _ (partition_pos _).ne',mul_one] at hg; exact hg
include h K
set_option maxHeartbeats 800000 in
lemma quakes (hN:k<N)(hK:C.ref d ≤ m) (hk:m ≤ k)(hw:0<w)(hX:Embrace (φ:=φ) (ζ:=ζ) (D:=D) (ψ:=ψ) C N k m p d L X Q w Z g b hN.le)(hL: Sung Y! T N p C.params W ℓ X) (hp:∀ i:ℕ,C.ref d ≤ i→∀ hi:i<N, Carol Y! T N p i (D N p i hi) (X.tone (i+1)) (X.tone i) (ψ i)) (hi:∀ b',profile (R N).activities ((X.tone N).plays b').forced=hook (R N).activities (R N).p.threshold (booster Y! (R N) 0 b'))
    (hV:Stock.Tabs.opens C.path.levels 1 J m) (n:ℕ) (hc:GridApprox.room C.path.levels J k n)(hh:Interior (GridApprox.window 0 n) (a)) : (center C.S p (hV.1.trans (hk.trans hN.le)) 0).rootTest (C.beta N p) (backTo T N p hN.le a-U!) ≤ stakes C J m/w:=by
    let t : J≤k:= hV.1.trans hk; let h':J≤N:= t.trans hN.le; let V':= (Site (C.side J p)); let X':=(center C.S p h' 0); let Z':= (center C.S p t 0); let B':= Stock.census V'
    let f := fun i=>Mix.camp C p J i; let ν (i:V'):=dye (X'.omega i) (X'.hand i)
    have hp':Migrating T m p N f:= ⟨fun j hj _=> funext fun i=> Work.I03.camp_step C p (hV.1.trans hj) i⟩
    have h₀:= Work.I03.answer G C 1 le_rfl K J m hV N (hk.trans hN.le) p h'
    have hA(s)(he:m ≤ s)(hw:s ≤ N): Edition.Spaced (C.path.levels.budget s|>.B) (f s):= fun i j hij=> by
       have ht:= h₀.2.2 s he hw i j hij; rw [mul_one] at ht; exact_mod_cast ht
    let U:=U!; let Tq:=a; let v (i:V') := stepUp (ν i) (f N i) (initial Y! T N p (-b) 0); let q (i:V'):= -X'.copy i U; let q'(i:V'):= stepUp (ν i) (f k i) (Tq); let s':=Stock.final V'
    let A:=birth B' (R N) q; let T':=couple (gust T N p N A k hN.le) (fun i=>Z'.copy i Tq)
    let G':=gust T N p k T' m hk
    have hEq(i:V') : (s!).terminal.symm (-((s!).terminal b))=-b:=by rw [map_neg,LinearEquiv.symm_apply_apply]
    have hz : v=q:=by
       funext i V; let g' := -((s!).terminal b); have he: initial Y! T N p (-b) 0= -U:= Eq.trans (show initial Y! T N p (-b) 0=C.O N p g' 0 from by unfold Family.O TransferData.cylinder; rw [hEq i]) ((C.linearO N p d 0).mk' _ |>.map_neg _)
       have hh' : f N i= X'.copyMap i 0:= (h₀.1 i).symm
       have ht:X'.copyMap i 0=X'.translateBy i:=by change (X'.omega i).act 0+_= _; simp
       unfold v stepUp; rw [he,hh',ht]; change scalar (ν i) (- U (pull _ _ V))= - X'.copy i U V
       dsimp only [ν]; simp_rw [calling]; change dot _ _= - dot _ _; unfold dot; split <;> simp <;> rfl
    have ht : q'=fun i=> Z'.copy i Tq:=by
       have hP:= Work.I03.answer G C 1 le_rfl K J m hV k hk p t; funext i V; have hh' : f k i= Z'.copyMap i 0:= (hP.1 i).symm
       have ht:Z'.copyMap i 0=Z'.translateBy i:=by change (Z'.omega i).act 0+_= _; simp
       unfold q' stepUp; rw [hh',ht]; change scalar (ν i) _= _; dsimp only [ν]; rw [calling]; rfl
    have hv : Continuous U:= C.continuousO ..
    have H' : Integrable A (prior G _):=by
       apply (Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)); refine hatCont C N p q ?_ (by rw [(H.wilson.starts ..).2]; exact bare_cont _) B'
       intro i; unfold q; refine Continuous.neg ?_; unfold Tiling.copy; by_cases hx:X'.hand i <;>simp only [hx, ↓reduceIte]; exact (hv.comp (continuous_pull ..)).star; exact hv.comp (continuous_pull ..)
    have hq':Integrable T' (prior G _):=comes T N p t hN.le U Tq H.wilson H' (Envelope.compactC hv) (cylinder_env hh)
    obtain ⟨Hq,Hv⟩:= embracing C N k m p d H f ν w L X h hN hK hk hw hX hL hp hi hp' (fun i=> (Extra.Multi.Occupancy.of_injective (Edition.injected _ _ (C.path.levels.budget m|>.B_pos) (hA m le_rfl (hk.trans hN.le))) i).trans (h.back m)) (show Drake B' _ (f m) from ⟨fun _ _ i _ j _=> hA m le_rfl (hk.trans hN.le) i j⟩) (show Drake B' _ (f k) from ⟨fun _ _ i _ j _=> hA k hk hN.le i j⟩) (show Integrable (birth B' (R N) v) _ from by rw [hz]; exact H') (show Integrable (couple (gust _ _ _ _ (birth B' (R N) v) k hN.le) q') _ from by rw [hz,ht]; exact hq')
    have hE :G' = gust T N p k (couple (gust T N p N (birth B' (R N) (fun i=>v i)) k hN.le) (fun i=>q' i)) m hk := by rw [hz,ht]
    have hS := spiker C N m p H s' (moment (C.beta N p) (Joint.cutoff T N p t hN.le U Tq s'.val)) (hk.trans hN.le) (fun _=>hw) (hE.symm ▸ Hq) Hv (show Integrable G' (prior G _) from gust_live _ _ _ _ _ hq' hk) (conducts T N p t hN.le U Tq H.wilson H' (Envelope.compactC hv) hh hc s' m hk)
    let c:=(C.S.a J/C.S.a m)^4*Vac.treasury (T).levels m+ (5:ℝ); let Xp:= Fintype.card V'
    let W':=moment (C.beta N p) (Joint.cutoff T N p t hN.le U Tq s'.val)
    unfold Tiling.rootTest; refine Stock.spacer ‖W'‖ c w Xp (norm_nonneg _) hw Fintype.card_pos ?_
    rw [show Poly.toll (fun _ : V'=>w) s'=w^Xp from by simp [Poly.toll,Xp,s',Stock.final],show (Fintype.card (Site (C.side m p)):ℝ)*Vac.treasury C.path.levels m+(Xp:ℝ)*(2+1+2*1)=Xp*c from by rw [Stock.tallies C.S J m p]; unfold c Xp V'; ring] at hS; exact hS
end YM.MergeProof.Accent
