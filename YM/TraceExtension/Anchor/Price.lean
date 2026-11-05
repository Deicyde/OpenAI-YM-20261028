import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Installation
import YM.TraceExtension.Anchor.Read
import YM.MergeProof.South.Window
import YM.Next.RANK.Rifle

/-! Generalize South/Swing to arbitrary masked kernels. on replicated joint/coarse at m stop. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open GridApprox.Joint GridApprox
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V} {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (o:∀ i:ℕ,V→Site (C.side i p))(s:V→ C.label d)(t:V→Motion)(w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
variable (L:Coefficient (C.labels.level d) (C.side k p))(X:Extra.Histories.Music (C.labels.level d) C.path N p)
local notation "ζ!"=> ζ d
variable (h:Scrim C W u ψ φ δ ζ r D){b:C.label d}{Z:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}{g:ℕ→ℝ} {Q:ℝ}
local notation "U₀"=> fun i:V=>stepUp (t i) (o N i) (initial Y! T N p (-b) 0)
local notation "τ"=> march (fun _:V=>w) φ m
local notation "V₁"=> fun i:V=>stepUp (t i) (o k i) (relayProbe C N k p d L)
local notation "v"=> birth B (R N) U₀
local notation "M!"=> (fun hm:k≤N=> couple (gust T N p N (birth (B) (R N) U₀) k hm) V₁)
local notation "f!"=> (fun i j=>liftF T Y! N p (t j) (fun x=>o x j) Z i)
local notation "λ!"=> (fun i j=>liftK T N p (t j) (fun x=>o x j) Z i)
include H h
lemma core_escent (hN:k<N)(hK:C.ref d ≤ m) (hk:m ≤ k)(hw:0<w)(hX:FReach (φ:=φ) (ζ:=ζ) (D:=D) (ψ:=ψ) C N k m p d L X Q w Z g b hN.le)(hL: Sung Y! T N p C.params W ℓ X) (hp:∀ i:ℕ,C.ref d ≤ i→∀ hi:i<N, Carol Y! T N p i (D N p i hi) (X.tone (i+1)) (X.tone i) (ψ i)) (hfK:profile (C.path.rep N p k).activities L.forced=0) (hi:∀ b',profile (R N).activities ((X.tone N).plays b').forced=hook (R N).activities (R N).p.threshold (booster Y! (R N) 0 b'))
    (hO:Migrating T m p N o)(hd:Occupancy (o m) (r m))(hh:Drake B (T|>.levels.budget m).B (o m))(hE:Drake B (T|>.levels.budget k).B (o k))
    (hf':Integrable v (prior G _))(hZ:Integrable ((M!) hN.le) (prior G _)) :
      Served (R m) (f! m) (λ! m) (gust T N p k (M! hN.le) m hk) (o m) (fun _=>w) (T|>.levels.budget m).supportExponent 1 ∧ Vault (fun _:V=>w) (f! m) (λ! m) 2 1:=by
    have hF:Brine C.path m δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=> h.costs.stay.support _ (Nat.zero_le i)⟩
    have hG:Brine C.path k δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=> h.costs.stay.support _ (Nat.zero_le i)⟩
    let β:= -b; let x i:= march (fun _:Unit=>w) φ m i (); have hp' i (he:m ≤ i): 0 < x i:= march_pos _ _ _ _ _ (fun _=>hw) hF i he _
    obtain ⟨Y,hF',hX',hP,hV,hI⟩:= h.costs.heights d k N p (hK.trans hk) hN.le
    have hm :Migrating T m p k o:= ⟨fun i hi hp' => hO.mare i hi (hp'.trans hN)⟩
    have hy :Migrating T k p N o:= ⟨fun i hi hp' => hO.mare i (hk.trans hi) hp'⟩
    have hM:=desal C.path r m p N δ φ o (fun _=>w) (fun _=>hw) hF B hO hh h.costs.mom hd
    let Q:=gust T N p N v
    have ht:∀ i:ℕ,k ≤ i→∀ h:i<N, Q i h.le=(T|>.levels.clock.op i p).push (T|>.β N p (i+1)) (Q (i+1) h):=fun i _ h=>gust_step _ _ _ _ _ h
    have he:Q N le_rfl=v:=gust_base ..
    have ha:=pollinate T C.params W φ ψ (ζ d) u δ r D p N k (Y!) X t (fun _ : V=>β) o (τ k) H.wilson h.costs.cost h.costs.back hN.le (hM.pos k hk hN.le) (H.sections d) (show Sung Y! T N p C.params W k X from ⟨hL.head,hN.le,fun i hi=>hL.earned _ (hK.trans (hk.trans hi)),fun i hi=>hL.step _ (hK.trans (hk.trans hi))⟩) hG hX' h.costs.mom (hM.occ k hk hN.le) hy hE h.costs.night hF' hP (by
      intro j; refine le_trans ?_ hX.pay; change (τ k j)*bond T N p X k β ≤ (march (fun _:Unit=>w) φ m k ())*bond T N p X k β; suffices ∀ i:ℕ,τ i j=x i by apply le_of_eq (congr_arg (· * _) (this k))
      intro i; induction i with
      | zero=> rfl
      | succ i IH=> unfold x march; split
                    next hx=> change φ i*_ = _; exact congr_arg (φ i * ·) IH
                    next=> rfl) hV hI (fun i hi=>hp i (hK.trans (hk.trans hi))) hi ht he (he.symm ▸ hf') k le_rfl hN.le
    rw [marines k φ (τ k) (hM.pos k hk hN.le), show topPitch C.path N k=_ from (if_neg (show ¬k=N from hN.ne):topPitch C.path N k=(T|>.levels.budget k).supportExponent)] at ha
    have h':=(ha.jelly (L:=V₁)); let f':= f!; let L':=λ!
    have hl: Served (R k) (f' k) (L' k) ((M!) hN.le) (o k) (τ k) (T|>.levels.budget k).supportExponent 1:=by
       convert! h' using 1
       · funext j U; let f:= (o k j); let d':=(t j); unfold f' liftF radiant; rw [hX.exp]; unfold stepUp; simp_rw [Pi.smul_apply,Pi.add_apply]; rw [scalar_add]; unfold soarF radiant stepUp relayProbe; simp only [Pi.smul_apply,Motion.scalar_mul]; change (_:ℂ)*_= (_:ℂ)*_+_
         rw [show Motion.scalar d' (alto T k d)=alto T k d from by unfold Motion.scalar alto; split <;> simp]; unfold β; ring
       funext i; unfold L' liftK soarK sunny; rw [hX.tank,hfK,zero_add]
    obtain ⟨Y,hΛ,hγ,_⟩:= h.costs.heights d m N p hK (hk.trans hN.le)
    have H' i: (fun j=>τ j i)=x:=by
       funext j; induction j with
       | zero=>rfl
       | succ j IH=> unfold x march; split
                     next hj=> exact congr_arg (φ j * ·) IH
                     next=>rfl
    have hT(i:V) : ∃ g, Wakes T m k N p (fun j=>o j i) (fun j=>τ j i) (fun j=>f' j i) g D hN.le ∧ ∀ j:ℕ,m ≤ j→ j≤k→ profile (R j).activities (g j)=L' j i:= by
       rw [H']; exact chapter T C.params Y! (ζ d) ψ m k N p (t i) (fun j=>o j i) x D Z g H.wilson (H.sections d) hN.le hX.descent (fun j hj _=> hp' _ hj) (fun j hj _=> by rw [show x (j+1)=φ j*x j from by unfold x; rw [march,if_pos hj]]; exact mul_le_of_le_one_left (hp' _ hj|>.le) (hγ.level j hj)) hΛ (fun j hj hk'=> (congr_fun (hO.mare j hj (hk'.trans hN)) i).symm) (fun j hj hk'=> by obtain ⟨w,p,hx,hv⟩:=h.costs.night.days N p j (hk'.trans hN); exact hx.propagate)
    choose G' HG hQ using hT; let Y' m (i:V):= G' i m
    have hG' i (hi:m ≤ i) (hk':i≤k): L' i=tapes T p N Y' i:= funext fun t=> hQ t i hi hk'|>.symm
    rw [hG' k hk le_rfl] at hl; have H':=Accent.window T r δ u D N p hN.le o τ f' Y' H.wilson (desal C.path r m p k δ φ o (fun _=>w) (fun _=>hw) hF B hm hh h.costs.mom hd) h.costs.night HG hl hZ m le_rfl hk
    rw [← hG' m le_rfl hk, marines m φ (fun _=>w) (fun _=>hw)] at H'
    have hE:=hX.descent.rates m le_rfl hk; rw [marines m φ _ (fun _=>hw)] at hE
    have hΖ(i:V)(U):= toasted C N m p d H Z (ζ d) hK (hk.trans hN.le) (t i) (o m i) (hX.descent.ticks _ le_rfl hk|>.2) hw.le hE (hΛ.coin m le_rfl) U
    exact ⟨H',⟨fun i U=> (hΖ i U).1,fun i U=> by rw [← Finset.mul_sum]; exact (hΖ i U).2⟩⟩
end YM.MergeProof.Accent
