import YM.PhysicalNext.FLAT_PUSH_RESPONSE.Pocket
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Tangent
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Vells
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Prism.Space
import YM.Push.GRID_APPROXIMATION.Checks
/-! # Conjugate actual `earning` physical offsets of bare oriented X.Camera
    all bookkeeping AFTER Cut kernel lift. Mini h uses light Spin.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f C F:Side} {P : Patch} {M : ℕ}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} (hC : C.val=c.val*M) (he:2 ≤ c.val)
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
set_option quotPrecheck false
local notation "W" => Macrame.Window.links (L).low
local notation "U" => Macrame.Window.links (L).high
-- quotation elaborator
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {t : ℝ} {Pt:Teller G}
  (ht:T'=re T) (hX : Room Pt (stepped Q h) T t) (hY : Room Pt (stepped Q H) T' t) (V:Config G c)
include hC he ht hX hY
open Pressure.Tube
local notation "Zu" => Pressure.Stores.till t

lemma runs (hG : 2* (Zu) < c.val) :
    let x:= dip (L).high.cut; let y:= curr (L).low.cut
    let v':=W V; let K:=v'
    T'.Mv (Zu) (Pressure.temp t) K=T.Mv (Zu) (Pressure.temp t) V ∘ x ∧
    T'.Mw (Zu) (Pressure.temp t) K=T.Mw (Zu) (Pressure.temp t) V ∘ y ∧
    ∀ z,SliceRows.guide T' t K z=SliceRows.guide T t V (Deck.rod (L) z):= by
  intro x y v K; obtain ⟨hf,hK,hv⟩:= whistle hC he V ht hX.accepted hY.accepted hG
  have hz: T'.vision (Zu) (Pressure.temp t) v=T.vision (Zu) (Pressure.temp t) V ∘ dip (L).low.cut:= by
    subst T'; exact funext fun z=> volt (divides hC) hC V T.down T.low (Zu) P.L.val (temp_nonneg _) z -- arity
  have hh := funext (hf.sails _ _ hz); have hm':= funext (hK.sails _ _ hz)
  exact ⟨hh,hm',fun z=> by cases z with | inl z=>exact congr_fun hh z|inr z=>exact congr_fun hm' z⟩
lemma req (hG : 2 * (Zu) < c.val) (z : Rod C F) (s:Signed) (k:(S).Choices) : request T' t (choice s ((L).pullTag Q k)) (pull s 0 (W V)) z=request T t (choice s k) (pull s 0 V) (Deck.rod (L) z) := by
  let y:= L; let U' :=replica (S).ratio V; let V₀:=pull s 0 V
  have hv : pull s 0 (W V)=W V₀:=constellation hC s V -- arg
  have hb := spun (H:=H) hC he U' k s (SectorMeasure.funds_branch hX.accepted); unfold request; rw [hv,(runs hC he ht hX hY V₀ hG).2.2]
  have hL : replica (S).ratio V₀=pull s 0 U':= Eq.symm (Channel.pulls_replica ..) -- inspect
  have hf: replica (Y).ratio (W V₀)=pull s 0 (U U'):= by rw [← hv, ← Channel.pulls_replica]; congr 1; exact Lace.Fitted.replicate ..
  unfold baseStroke entryCost; rw [hL,hf,hb]; rcases z with z|z
  · suffices A: Xf T' (Zu) (pull s 0 (U U')) z=Xf T (Zu) (pull s 0 U') (dip y.high.cut z) from congr_arg₂ HSub.hSub A rfl
    rw [show pull s 0 (U U')=U (pull s 0 U') from constellation (fineP h H hC) s U']; exact vele hC he ht ..
  rfl
-- Mini.Momentum: NO Period assumption on arbitrary envelopes. Only projected from V
abbrev spo (v : Lace h H M) : Coat.Spot C F→ Coat.Spot c f:= Sum.map (curr v.high.cut) (Sum.map (curr v.low.cut) (Sum.map (curr v.low.cut) (curr v.low.cut)))
lemma stems (hp : 2* Zu < c.val) (z : Spot C F) (U': Config G f) {k:(Y).Choices} {k':(S).Choices} (hv: (Y).prediction (U U') k=W ((S).prediction U' k')) : Coat.yielding T' t (U U') (W V) k z= Coat.yielding T t U' V k' (Deck.spo (L) z):= by
  subst T'; let Y':= L; let U':=U'; let S':= re (H:=H) T; let s:=Pressure.temp t; let W₀:=W V
  obtain ⟨ha,hb,hh⟩:= runs hC he (T':=S') rfl hX hY V hp -- arg
  obtain ⟨hc,hV,hN⟩:= whistle hC he V (A:=S') rfl hX.accepted hY.accepted hp -- arg
  let TQ:= (S).prediction U' k'
  let p (u:Coat.Spot C F):= Deck.spo Y' u; let Y₀:= U U'; let f:=dip Y'.high.cut; let v:=dip Y'.low.cut; let w : Bond C → Bond c:=curr Y'.low.cut
  have hT : S'.Xf Zu Y₀ = T.Xf Zu U' ∘ f:= funext fun q=> vele hC he rfl U' _ _ q
  have hζ : S'.vision Zu s W₀=T.vision Zu s V ∘ v:= funext fun q=> volt (divides hC) hC V T.down T.low Zu P.L.val (temp_nonneg _) q
  have hj : Tube.Z (Y) ((Y).prediction Y₀ k) W₀= Tube.Z (S) TQ V ∘ w:=by rw [hv]; rfl
  rcases z with z|z|z|z
  · unfold Coat.yielding; change soft S' t _ _ _ z= soft T t _ _ _ _; unfold soft
    refine congr_arg₂ HAdd.hAdd (congr_arg (fun x:G.El=> T.high.direct*flaw x) (Y'.high.traveller ..)) (Finset.sum_congr rfl fun i _=>?_)
    unfold SliceRows.bill; rw [hh]; exact congr_arg (fun g:G.Color=> ‖g- guide T t V (Deck.rod Y' (.inl (z,i)))‖^2/2) (congr_fun hT (z,i))
  · change S'.workI Zu _ _ _ _=T.workI Zu _ _ _ _; rw [hv]; unfold Tube.workI; rw [hb]; rfl
  · change (S'.workC Zu W₀ s z+(S'.workL Zu Y₀ _ W₀ s z+ S'.workD Zu W₀ s z))=_
    have hm z' : S'.workC Zu W₀ s z'= T.workC Zu V s (curr Y'.low.cut z') := by
      unfold workC
      have hX i:S'.Xn Zu W₀ (z',i) = T.Xn Zu V (curr Y'.low.cut z',i):= fasces (divides hC) hC V T.down T.low (Zu) P.L.val (z',i)
      apply congr_arg₂ HSub.hSub (Finset.sum_congr rfl (fun j _=>?_)) ?_
      swap
      · rw [hX,hζ]; rfl
      have hc : shorten T.down Zu P.L.val W₀ z'=shorten T.down Zu P.L.val V (curr Y'.low.cut z'):= by have hh:= fasces (divides hC) hC V T.down T.low Zu P.L.val (z',true); simp [plotted] at hh; exact hh
      change Pressure.crown T.down T.low Zu P.L.val (Pressure.temp t) ((normal (divides hC) hC).links V) z'= _; unfold Pressure.crown Pressure.trunk; rw [mirror, shot _ hC V T.low (temp_nonneg _)]
      change (if PathData.kept T.low _ (curr Y'.low.cut z').1 V then _ else _) + _ = (if PathData.kept _ _ _ V then _ else _) + _
      rw [show shorten T.down Zu P.L.val ((normal (divides hC) hC).links V) z'= _ from hc]; rfl
    have hx:S'.workL Zu Y₀ ((Y).prediction Y₀ k) W₀ s z=T.workL Zu U' TQ V s (curr Y'.low.cut z):= by
      unfold workL; apply sum_congr rfl; intro i _
      rw [hc.recedes _ _ hT,hV.recedes _ _ hj,hζ, show S'.Xn Zu W₀ (z,i)= T.Xn Zu V (curr Y'.low.cut z,i) from fasces (divides hC) hC V T.down T.low Zu P.L.val _]; rfl
    have hΩ:S'.workD Zu W₀ s z = T.workD Zu V s (curr Y'.low.cut z):= by
      unfold workD; apply sum_congr rfl; intro i _; rw [hc.recedes _ _ ha, hV.recedes _ _ hb, hN.recedes _ (Pressure.zip (T.N Zu V) (T.vision Zu s V)) (funext (hN.sails _ _ hζ)), hζ]; rfl
    rw [hm,hx,hΩ]; rfl
  change S'.workN Zu W₀ s z=T.workN Zu V s _
  exact congr_arg (fun p:G.Color=> ‖p‖^2/2) (hN.sails _ _ hζ z)
end YM.PhysicalNext.Repeat.Deck
