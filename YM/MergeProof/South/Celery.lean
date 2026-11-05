import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tensors
import YM.MergeProof.South.Block
import YM.MergeProof.South.Hearth
import YM.MergeProof.South.Lens
import YM.MergeProof.South.Lush
import YM.MergeProof.South.Rapt
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Emit




set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
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
local notation "ζ!"=> ζ d
section
open GridApprox
variable (h:Scrim C W u ψ φ δ ζ r D) (L:Stock.Tabs C.path.levels)
variable (J:ℕ) (hV : Stock.Tabs.opens C.path.levels 1 J m) {hk:m≤k}{hN:k<N}
local notation "o"=> fun i=> Mix.camp C p J i
local notation "V"=> Site (C.side J p)
local notation "Bt"=> Stock.census V
local notation "u'"=> hands C p J
local notation "α'"=> march (fun _ : V=> w) φ m k
local notation "h!"=> center C.S p (hV.1.trans (hk.trans hN.le)) 0
variable (f:Config G (C.side N p)→ℂ) (Q:Coefficient (C.labels.level d) (C.side k p)) {c t E:ℝ}
include H h L
local notation "xp"=> C.path.levels.params k
set_option maxHeartbeats 1000000 in
lemma celeri (ht:C.ref d ≤ m){hk:m ≤ k}(hN:k<N)(hR:GridApprox.room C.path.levels J k (lensScope C d))
   (hf : Continuous f)(E:ℝ)(hw:0 < w)(hp:0 < E)(X:Extra.Histories.Music (C.labels.level d) C.path N p)
   (hL:Sung Y! T N p C.params W ℓ X) (P:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p))(b:C.label d)(x:ℕ→ℝ)(Z:(F).Index→ ∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p))(e:(F).Index → C.label d)(g:(F).Index →ℕ→ℝ)
   (hK:Club T C.params Y! (ζ d) ψ m k N p (stair φ (2*w) m) D P x hN.le)
   (hU:(P k).exponentialEntry 0 Y! (R k)= Q.exponentialEntry 0 Y! (R k) + ((X.tone k).plays (-b)).exponentialEntry 0 Y! (R k))
   (hB:profile (R k).activities (P k).forced=profile (R k).activities Q.forced+profile (R k).activities ((X.tone k).plays (-b)).forced) (s:C.label d) (hs:b=∑ i,s i • e i)(hΨ:∀ i, Embrace (φ:=φ) (ζ:=ζ) (D:=D) (ψ:=ψ) C N k m p d (Size.axis F i) X 1 (8*E*w) (Z i) (g i) (e i) hN.le)
   (hβ:(∑ i, ‖s i‖) ≤ 4*E)(hW:Interior (GridApprox.window 0 (lensScope C d)) (∑ i,(-s i) • lens C N k p d (Size.axis F i)))
    (hZ:Served (R k) (fun i=> radiant (alto T k d) (u' i) (o k i) (Q.exponentialEntry 0 Y! (R k))) (fun i=>sunny (R k) Q.forced (u' i) (o k i) (alto T k d)) (gust T N p N (birth (Bt) (R N) (fun i=> (center C.S p (hV.1.trans (hk.trans hN.le)) 0).copy i f)) k hN.le) (o k) (α') (C.path.levels.budget k).supportExponent 1) : (center C.S p (hV.1.trans (hk.trans hN.le)) 0).rootTest (C.beta N p) (backTo T N p hN.le (∑ i,(-s i) • lens C N k p d (Size.axis F i))-(-f)) ≤ stakes C J m / w:=by
    let I:=Option (F).Index
    let q:= Size.axis F; let a':= 2*w; let v' := 8*E*w; have h':0 < v':=by unfold v'; positivity
    let W₀:= center C.S p (hV.1.trans (hk.trans hN.le)) 0; let b' i:=(s!).terminal (e i); let n:=lensScope C d; let y i:= lens C N k p d (q i); let ℓ':= ∑ i,(-s i) • y i; let r':= backTo T N p hN.le ℓ'
    let J' := hV.1.trans hk; let V':= -f; let S:= stakes C J m/w
    let w' (i:V):= -W₀.copy i V'; let K':=birth (Bt) (R N) w'
    let A:=gust T N p N K' k hN.le; let Y:= couple A (fun i=> (center C.S p J' 0).copy i ℓ')
    let U':= gust T N p k Y m hk
    have hi : Integrable K' (prior G _):=by
       apply (Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)); apply hatCont C N p w' _ (by rw [(H.wilson.starts ..).2]; exact bare_cont _) (Bt); intro i; rw [show w' i=W₀.copy i f from handneg C N p J _ _ i]
       unfold Tiling.copy; by_cases ht:W₀.hand i <;>simp only [ht, ↓reduceIte]; exact (hf.comp (continuous_pull ..)).star; exact hf.comp (continuous_pull ..)
    have hZ': Integrable Y (prior G _):=comes T N p J' hN.le V' ℓ' H.wilson hi (Envelope.compactC hf.neg) (cylinder_env hW)
    have hη:Migrating T m p k o:= ⟨fun j hj _=> funext fun i=> Work.I03.camp_step C p (hV.1.trans hj) i⟩
    have h₀:= Work.I03.answer G C 1 le_rfl L J m hV k hk p J'
    have hA: Edition.Spaced (C.path.levels.budget m|>.B) (o m):= fun i j hij=> by
       have ht:= h₀.2.2 m le_rfl hk i j hij; rw [mul_one] at ht; exact_mod_cast ht
    let D' (i:V) (j:I):=Option.elim j (1:ℂ) (fun l=>Motion.scalar (hands C p J i) (-s l)); let Z' (i:I):=Option.elim i P Z; let g' (i:I):=Option.elim i x g; let x' (i:I):=Option.elim i a' (fun _=>v')
    have hh: ∀ i:I,Club T C.params Y! (ζ d) ψ m k N p (stair φ (x' i) m) D (Z' i) (g' i) hN.le:=fun i=>by cases i;exact hK;exact (hΨ _).descent
    have hy'(i:V): (∑ j,D' i j • liftF T Y! N p (u' i) (fun l=>o l i) (Z' j) k)= radiant (alto T k d) (u' i) (o k i) (Q.exponentialEntry 0 Y! (R k))+(center C.S p J' 0).copy i ℓ' ∧ (∑ j,D' i j • liftK T N p (u' i) (fun l=>o l i) (Z' j) k)=sunny (R k) Q.forced (u' i) (o k i) (alto T k d):=by
       rw [← handmove C k p J J']; exact plush C N k p d X Z' e (fun i=>s i) b q Q (u' i) (fun l=>Mix.camp C p J l i) (ht.trans hk) hN.le hL hs hU (fun i=> (hΨ i).exp) hB (fun i=>(hΨ i).tank)
    obtain ⟨hL',hV'⟩:= prolonged C N k m p d H w h o u' D' Z' hN.le ht hk hZ' hη (fun i=> (Extra.Multi.Occupancy.of_injective (Edition.injected _ _ (C.path.levels.budget m|>.B_pos) hA) i).trans (h.back m)) (show Drake (Bt) _ (o m) from ⟨fun _ _ i _ j _=> hA i j⟩) hh (by
       have hx' : (fun i=> W₀.copy i f)= w':= funext fun i=> (handneg C N p J _ _ i).symm
       let Y' (i:V):= (center C.S p J' 0).copy i ℓ'
       have hZc:= (hZ.jelly (L:=Y')); rw [show birth (Bt) (R N) (fun i=> (center C.S p (hV.1.trans (hk.trans hN.le)) 0).copy i f) = K' from congr_arg (birth (Bt) (R N)) hx'] at hZc
       let xF:=fun i=> radiant (alto T k d) (hands C p J i) (Mix.camp C p J k i) (Q.exponentialEntry 0 Y! (R k)); let xK:= fun i=>sunny (R k) Q.forced (hands C p J i) (Mix.camp C p J k i) (alto T k d)
       have hF : (fun i=>∑ j,D' i j • liftF T Y! N p (u' i) (fun l=> o l i) (Z' j) k) = xF+Y':=funext fun i=> (hy' i).1
       have hT : (fun i=>∑ j,D' i j • liftK T N p (u' i) (fun l=> o l i) (Z' j) k)=xK:=funext fun i=> (hy' i).2
       dsimp only; erw [hF,hT]; exact hZc) hw (fun i=>by cases i; exact mul_pos (by norm_num) hw;exact h') (by
       intro i; change ∑ j: Option (F).Index, w*_/_≤ _; rw [Fintype.sum_option]; simp only [x',D',Option.elim, norm_one,mul_one,norm_scalar,norm_neg]
       rw [show w/a'=(1:ℝ)/2 from by unfold a'; field_simp, ← Finset.sum_div,← Finset.mul_sum]; linarith only [(show w*(∑ i,‖s i‖)/v'≤ 1/2 from le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hβ hw.le) h'.le) (le_of_eq (by unfold v';field_simp;norm_num)))])
    let s':=Stock.final V; let W':= moment (C.beta N p) (Joint.cutoff T N p J' hN.le V' ℓ' s'.val)
    have hS:=spiker C N m p H s' W' (hk.trans hN.le) (fun _=>hw) hL' hV' (show Integrable U' (prior G _) from gust_live _ _ _ _ _ hZ' hk) (conducts T N p J' hN.le V' ℓ' H.wilson hi (Envelope.compactC hf.neg) hW hR s' m hk)
    let t:=(C.S.a J/C.S.a m)^4*Vac.treasury (T).levels m+ (5:ℝ); let Xp:= Fintype.card V
    unfold Tiling.rootTest; refine Stock.spacer ‖W'‖ t w Xp (norm_nonneg _) hw Fintype.card_pos ?_
    rw [show Poly.toll (fun _ : (V)=>w) s'=w^Xp from by simp [Poly.toll,Xp,s',Stock.final], show (Fintype.card (Site (C.side m p)):ℝ)*Vac.treasury C.path.levels m+(Xp:ℝ)*(2+1+2*1)=Xp*t from by rw [Stock.tallies C.S J m p]; unfold t Xp; ring] at hS; exact hS
end
end YM.MergeProof
