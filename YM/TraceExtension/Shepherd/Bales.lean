import YM.TraceExtension.Shepherd.Cant
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function
open scoped Topology BigOperators Classical ContDiff
variable {V I:Type}{G:Gauge}{n:Side}
variable (R:Rep G n) {σ A u v e:ℝ} (hp:R.Lawful σ A u v e)
local notation "P!"=> R.p
local notation "C!"=>R.path
local notation "η"=>R.p.threshold
local notation "U!"=>R.activities
lemma masks_on (P:Support n)(F:Config G n→ℝ)(t:ℝ)(h:LocalOn P F) (hf:GaugeInvariant F)(he:Measurable F): Measurable (masked t P F)∧GaugeInvariant (masked t P F)∧ UsesFinal t P (masked t P F):=by
   refine ⟨masked_measurable _ _ _ he,fun i U=> ?_,fun U V hu hv=>?_⟩
   · have hv : Healthy t P (Lattice.gauge i U) ↔ Healthy t P U:=by unfold Healthy; rw[gauge_flags]
     by_cases hh:Healthy t P U
     · rw[masked_eq _ _ _ _ (hv.2 hh),masked_eq _ _ _ _ hh,hf]
     rw[masked_ne _ _ _ _ (mt hv.mp hh),masked_ne _ _ _ _ hh]
   have he: Healthy t P U↔ Healthy t P V:=by simp only[Healthy,Finset.disjoint_iff_inter_eq_empty,hv]
   by_cases hx:Healthy t P U
   · rw[masked_eq _ _ _ _ hx,masked_eq _ _ _ _ (he.1 hx),h _ _ hu]
   rw[masked_ne _ _ _ _ hx,masked_ne _ _ _ _ (mt he.mpr hx)]
lemma tug (p:Seat n) (F : Config G n→ℝ)(X:Support n)(b:ℝ)(ht: UsesFinal b X F): UsesFinal b (p.spread X) (F ∘ p.view):=by
   intro U V hu hv; apply ht; exact Push.Local.agrees_pull p.1 p.2 hu
   apply Finset.image_injective (f:=affine p.1 p.2) (fun u v h=> p.1.act_injective (add_right_cancel h)); rw [Finset.image_inter _,Finset.image_inter _]
   · simpa only[Seat.view, Work.H03.flags_send] using! hv
   all_goals exact fun u v h=> p.1.act_injective (add_right_cancel h)
include hp
lemma bare_not {q:Badge n}(h: WilsonStartup.Decent R.clip R.p) : Measurable (pieceC R q) ∧ GaugeInvariant (pieceC R q)∧UsesFinal η (boothC R q) (pieceC R q):=by
   rcases q with ⟨x,i⟩|i
   · have he : Measurable (coal R i) ∧ GaugeInvariant (coal R i) ∧ UsesFinal η (fort R i) (coal R i):=by
        rcases i with i|i
        · exact ⟨Low.live_meas ..,Low.live_gauge _ _ i _,fun U V hu _=> Low.live_local _ _ _ h _ U V hu⟩
        have hx: (tooth R i).Invariant:=by cases i; exact High.invariant R.path _ hp.paths; exact (hp.paths.invariant _).1
        have hs:= Extra.Iteration.Derivs.canonical_regular (tooth R i) (0:Site n) R.p hx; exact masks_on _ _ _ hs.sites hs.symmetry hs.borel
     have hv : GaugeInvariant (coal R i ∘ x.view):= by intro g U; unfold Seat.view; simp only[comp_apply]; rw [Push.Local.pull_gauge]; exact he.2.1 _ _
     refine ⟨measurable_const.mul (measurable_const.mul (he.1.comp (continuous_pull ..).measurable)),fun i U=>congr_arg₂ (· * ·) rfl (congr_arg₂ (·*·) rfl (hv ..)),fun U V hu hV=>congr_arg₂ (· * ·) rfl (congr_arg₂ (· * ·) rfl (tug _ _ _ _ he.2.2 U V hu hV)) ⟩
   obtain hh:=hp.labels.regular.smooth i; obtain ⟨hx,hY,hU⟩:=masks_on _ _ η hh.sites hh.symmetry hh.borel; exact ⟨hx.neg,fun k U=> congr_arg Neg.neg (hY k U),fun U V hu hv=>congr_arg Neg.neg (hU _ _ hu hv)⟩
lemma bustle (x:Seat n): ∃ e:Equiv.Perm (Badge n),∀ i,boothC R (e i)= x.spread (boothC R i) ∧ pieceC R (e i) = pieceC R i ∘ x.view:=by
   obtain ⟨M⟩:=hp.labels.moves x.1 x.2; refine ⟨Equiv.sumCongr (Equiv.prodCongr (Seat.move x.1 x.2) (Equiv.refl _)) M.ep,fun i=>?_⟩
   rcases i with ⟨p,j⟩|j
   · refine ⟨p.spread_move ..,funext fun U=> congr_arg (-VerifiedReset.factor *·) (congr_arg (chore R j) (congr_fun (p.view_move x.1 x.2) U))⟩
   have he := M.reg_support j; refine ⟨he,funext fun U=>?_⟩; change -masked _ _ (R.activities.E (M.ep j)) U= -masked _ _ _ (x.view U); rw [he, show R.activities.E (M.ep j)=R.activities.E j ∘ x.view from funext (M.valuesE j), show image _ _= x.spread _ from (rfl : x.spread _= _),x.distribute]; rfl

variable (h: VerifiedReset.Geo.Width R.p R.clip σ)
def stockC (X:Support n)(U:Config G n):= cram (boothC R) (fun i=>pieceC R i U) X
lemma stock_turn (x : Seat n) (q:Support n) : stockC R (x.spread q)= stockC R q ∘ x.view:=by
   obtain ⟨v,hv⟩:= bustle R hp x; funext U; unfold stockC; simp only[comp_apply,expand_eq]; rw[← Equiv.tsum_eq v]; exact tsum_congr (fun i=> by simp only [(hv i).1,(hv i).2, show x.spread (boothC R i)=x.spread q ↔ boothC R i=q from (Finset.image_injective (f:=affine x.1 x.2) (fun u v h=> x.1.act_injective (add_right_cancel h))).eq_iff]; rfl)
lemma stock_pay (x:Support n)(h:WilsonStartup.Decent R.clip R.p) : Measurable (stockC R x)∧GaugeInvariant (stockC R x)∧UsesFinal η x (stockC R x):=by
   refine ⟨Measurable.tsum (fun i=> (bare_not R hp (q:=i.val) h).1),fun g U=> tsum_congr (fun i=>(bare_not R hp (q:=i.val) h).2.1 g U),fun U V hu hv=> tsum_congr (fun i=>(bare_not R hp (q:=i.val) h).2.2 U V (by rw[i.property];exact hu) (by rw[i.property];exact hv))⟩
include h
lemma shores (U:Config G n): R.exponent U= R.v * Fintype.card (Site n)+(∑ i,stockC R i U):= by
    have ht := heavy (boothC R) (f:=fun i=>pieceC R i U) (songE R hp h _) |>.tsum_eq; rw [tsum_fintype] at ht; rw[seedE R hp h U,← ht];rfl
end YM.Trace.Shepherd
