import YM.Next.RANK.Flux.Conductor
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Baritone
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Epigram
/-!
# Combining low reformat with all the other marked data at one physical poll

Low correspondence (Reform) input is on full masked values at every field --
a genuine condition not assumed to be cheap at arbitrary P0. Then the full
higher part STILL required for the multilinear work; use `Reform.placed` to
preserve on this whole interrogation, then invest both and `lodge` the big
Score (weights raised and discounted on multi-tags only).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Weaver
open Lattice Wilson Pressure RG MeasureTheory Function Matrix Finset Next.SectorChange
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid Precision Display Edition Thirst Docking Alarm Exponential
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {V ι κ α β ψ ρ : Type} {M : Tube G S} {x t p r e y v w : ℝ}
    [DecidableEq V] [Fintype V] {θ : V→ Site f} {Φ : V→Site c}
section key
variable {E : veil V} (Q : Rep G c)
def unison (a : V→ℂ) : veil V:=∑ i : V,Poly.send (slot i) (a i)
lemma abstem (a : V→ℂ) : (unison a).part (quiet V)=0:= by unfold unison; rw [Poly.part_sum]; exact Finset.sum_eq_zero fun i _=> Flux.asleep _ (singleton_nonempty i) _
structure Partone (Q : Rep G c) (Φ : V→Site c) where
  H : Type
  [hH : Fintype H]
  K : Type
  [hK : Fintype K]
  m : H→SourceAt G Φ
  p : K→Lifted G Φ Q.p.threshold
  same : Background Q p
  solo i : (m i).fires.val.card=1
  small i : (p i).fires.val.card≤1
  scalar : V→ℂ
attribute [instance] Partone.hH Partone.hK
variable (o : Partone Q Φ) (F : ι→CoverReads G Φ Q.p.threshold)
variable [Fintype ι] (P : κ→Plug G Φ Q.p.threshold) (X : Flux.Vac Φ Q) [Fintype κ]
local notation "D"=> Flux.Bond (sunny (panel P (measureH X)))
local notation "K"=> after P (measureH X) X.pay

-- stencils Issue. Do not assert as arbitrary oracle on RHS credentials.
structure Reform (Q : Rep G c) (o : Partone Q Φ) (P : κ→ Plug G Φ Q.p.threshold) (X : Flux.Vac Φ Q) (s : V→ℂ) (F : ι→CoverReads G Φ Q.p.threshold) : Prop where
  flags : flagWorks F
  exponents U : unison s+basso (Flux.Bond (sunny (panel P (measureH X)))) Q.p.threshold U = unison o.scalar + ∑ i,(o.m i).amount Q.p.threshold U + ∑ i,(F i).covets U
  marked i (h : (i: Gel.Setting Φ).val.2.val.card≤1) : Gel.freezeKey (toRain (after P (measureH X) X.pay) (witness F)) i= Gel.freezeKey o.p i
variable {P0 : α→ Plug G Φ Q.p.threshold} {s : V→ℂ} [Fintype α]

end key
section offer
variable {Q : Rep G c} (o : Partone Q Φ)
def airSor (f : ι→ SourceAt G Φ) (t : ℝ) [Fintype ι] (U : Config G c) := ∑ i,(f i).amount t U
lemma airSor_blank (f : ι→ SourceAt G Φ) [Fintype ι] (t U) : (airSor f t U).part (quiet V)=0:= by unfold airSor; rw [Poly.part_sum];exact Finset.sum_eq_zero fun i _=>Flux.asleep _ (f i).chosen _
def syndic (H : ι→ SourceAt G Φ) (K : κ→Lifted G Φ Q.p.threshold) [Fintype ι] [Fintype κ] (U : Config G c) := Poly.pass (unison o.scalar)*Value.dust Q (Sum.elim o.m H) (Sum.elim o.p K) U
variable [Fintype ι] [Fintype κ] (P : κ→ Plug G Φ Q.p.threshold) (X : Flux.Vac Φ Q) (F : ι→CoverReads G Φ Q.p.threshold)
    {p b z y s : ℝ} {f : V→ℂ} (ht : Reform Q o P X f F)
    {W : Config G c→veil V}
local notation "D"=> Flux.Bond (sunny (panel P (measureH X)))
local notation "K"=> toRain (after P (measureH X) X.pay) (witness F)

include ht in
lemma familiar (he : Matric X P W) (U : Config G c) : Poly.pass (unison f)* W U=syndic o (fun i: Priced D=> D i.val) (fun i : Piqued K=> K i.val) U :=by
  let H:= fun i: Priced D=> D i.val;let B:= after P (measureH X) X.pay; let C':= Sum.elim o.p (fun i : Piqued K=> K i.val)
  have ha : unison f+airSor D Q.p.threshold U = unison o.scalar+ airSor (Sum.elim o.m H) Q.p.threshold U+∑ i,(F i).covets U:= by
    unfold airSor; rw [dark D Q.p.threshold U, Fintype.sum_sum_type,←add_assoc,ht.exponents]; dsimp only [Sum.elim_inl,Sum.elim_inr,H]; abel
  have hx : (∑ i,((F i).covets U).part (quiet V))=0:= by
    refine Finset.sum_eq_zero fun i _=>?_ ; exact Flux.asleep _ (card_pos.mp ((ht.flags.1 i) ▸ one_pos)) _
  have hj : Poly.pass (unison f)*Poly.pass (airSor D Q.p.threshold U)=Poly.pass (unison o.scalar)*Poly.pass (airSor (Sum.elim o.m H) Q.p.threshold U)*Poly.pass (∑ i,(F i).covets U):= by
    rw [← Exponential.pass_add _ _ (abstem _) (airSor_blank ..),ha, Exponential.pass_add _ _ (by rw [Poly.part_plus,abstem,airSor_blank]; simp) (by rw [Poly.part_sum]; exact hx), Exponential.pass_add _ _ (abstem _) (airSor_blank ..)]
  unfold syndic Value.dust; rw [(show W U=_ from (by exact he.passed U))]
  rw [Flux.placed P _ X.pay U X.boundary]
  let α:ℂ:= Real.exp (Q.exponent U)
  change Poly.pass _ * (α • (Poly.pass (airSor D Q.p.threshold U)*RAIDage B U))=Poly.pass _ * (α • (Poly.pass (airSor (Sum.elim o.m H) Q.p.threshold U)*RAIDage (Sum.elim o.p (fun i : Piqued K=> K i.val)) U))
  rw [← opus (toRain (after P (measureH X) X.pay) (witness F)) o.p o.small ht.marked U,← corps B F U ht.flags,mul_smul_comm,mul_smul_comm,← mul_assoc,hj]; apply congr_arg; ring

-- transfer authentic Master Low projection. No birth/free label.
structure Score (o : Partone Q Φ) (b e d : ℝ) (f : Config G c→veil V) : Prop where
  frame : ∃ ι κ:Type,∃ (_ : Fintype ι) (_ : Fintype κ),∃ (H : ι→ SourceAt G Φ) (I : κ→Lifted G Φ Q.p.threshold), f=syndic o H I∧
    (∀ i,2 ≤ (H i).fires.val.card) ∧ (∀ i,2 ≤ (I i).fires.val.card) ∧ Light Q H I (fun _=>b) e d d
lemma factual (p : ℝ) (e z : ℝ) (P' : κ→Prop) {r : V→ℝ} (he : Shine (downstairs X P P') Q.p r e p) (hv : Shine (upstairs X P P') Q.p r e z) : Shine D Q.p r e (p+z):= by
  let Γ :=MergeLog (sunny (panel P (measureH X)))
  let v:= Flux.rawclean (Q:=Q.p) P (measureH X) P'; let T':= Sum.elim (downstairs X P P') (upstairs X P P')
  let m := (Equiv.sumCompl v).symm.trans (Equiv.sumComm ..)
  have hh i:T' (m i) = D i:= by
    obtain ⟨j,rfl⟩ := m.symm.surjective i
    rw [Equiv.apply_symm_apply];cases j<;>rfl
  obtain ⟨k,hk,h⟩:= Shine.plus _ _ he hv
  refine ⟨fun i=>k (m i),fun i=> hh i ▸ hk (m i),fun i=>?_⟩
  apply le_trans (b:=_) _ (h i); apply le_of_eq
  refine Fintype.sum_equiv m _ _ fun i=>?_
  rw [← show _=D i from hh i]
include ht in
theorem lodge (P' : κ→Prop) (he : Matric X P W) (hb : Spaced Q.p.B Φ) (hf : 8 ≤ Q.p.B) (hr : 0<p) (hv : 0 ≤ b) (hq : b ≤ Real.exp ((Q.p.B:ℝ)/256)*p)
    {δ x M u : ℝ} (hx : rawRadii X P P' p (Q.p.supportExponent+1) M 1 s x) (hp : Tickets Q.p s) (hm : 1 ≤ M)
    (hF : Custody Q.p F (fun _=>p) (Q.p.supportExponent+1+1) u) (hV : 1/M + u ≤ y) (H : Risible Q.p.B y)
    (hD : Real.exp (-(Q.p.B:ℝ)/128)*(x+x) ≤ δ) (hZ : Real.exp (-(Q.p.B:ℝ)/128)*(Real.exp y-1) ≤ δ) :
    Score o b Q.p.supportExponent δ (fun U=> Poly.pass (unison f)* W U):= by
  let H₁ := fun i: Priced D=> D i.val
  let H₂ := fun i : Piqued K => K i.val
  have hn : 0 ≤ Q.p.supportExponent+1:=by linarith [Q.p.exponent_pos]
  obtain ⟨hL,hB,hK⟩:= authenticity X P P' (fun _=>p) (fun _=>hr) hm (show (1:ℝ)≤1 from le_rfl) hn hp hx
  rw [div_one] at hL
  have he' : Stripes Q.p K (fun _=>p) (Q.p.supportExponent+1) (Real.exp y-1):= pay_custody _ _ F _ (fun _=>hr) hn hK hF H hV
  obtain ⟨ha,h⟩:= ferveur hf hb hr.le hv hq (T:=Q) («K»:=K) (H:=D) (Light.mk (factual P X x _ x P' hL hB) he')
  exact ⟨_,_,inferInstance,inferInstance,H₁,H₂,(funext (familiar o P X F ht he)),fun i=> i.property,fun i=>i.property,⟨Shine.loose (H:=H₁) ha hD, Stripes.loose (H:=H₂) h hZ⟩⟩
end offer
end YM.PhysicalNext.InteractingRank.Weaver
