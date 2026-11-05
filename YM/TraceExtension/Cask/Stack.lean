import YM.MergeProof.Bungalow
import YM.TraceExtension.Cask.Bower
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker MeasureTheory Wilson Push Function
open scoped Classical
variable {I V:Type}[DecidableEq I][DecidableEq V]{n:Side}[Fintype V]{G:Gauge}[Fintype I]
def flore (R:Rep G n)(p:Box n)(U:Config G n):= profile R.activities (fun i=> Complex.ofReal ∘ R.activities.K i) p U
variable (R:Rep G n) {a b:ℝ} (H:R.activities.Valid R.p a b)
local notation "A!"=> Stock.census Unit
local notation "Y"=> R.activities
local notation "p₀"=> R.p
include H
private lemma stm (s:Box n) (U:Config G n): flore R s U=(exclaim Y A! s U).part (A!|>.quiet):=by simp [flore,exclaim,bar,Poly.bead]
lemma florid (p:Box n) : UsesFinal R.p.threshold p.1 (flore R p)∧Measurable (flore R p)∧GaugeInvariant (flore R p)∧∀ U:Config G n,flore R p U≠0→p.1∩flags R.p.threshold U=p.2 ∧ Sure p:=by
    have hx:= granular Y p₀ A! (o:=fun _:Unit=> (0:Site n)) H p; have ht:= stm R H p
    exact ⟨fun U V hu hv=>by rw [ht,ht,hx.home U V hu hv], (funext ht).symm ▸ hx.me _,fun k U=>by rw [ht,ht,hx.turns],fun U hv=>hx.permits U (fun hp=> hv ((ht U).trans (congr_arg (fun x:Marker.Poly A!=>x.part _) hp)))⟩
lemma florW : ∃ f:Box n→ℝ,(∀ p,0≤f p∧∀ U:Config G n,‖flore R p U‖ ≤ f p) ∧ Hit Prod.fst R.p.B f R.p.supportExponent b:=by
    obtain ⟨a,hA,hp,h⟩:= vacant Y R.p A! H (fun _=>1) (fun _=>zero_lt_one); refine ⟨a,fun p=>⟨(h p|>.fares (fun _=>zero_lt_one)).1,fun U=>?_⟩,hp⟩; have ht:= (h p|>.fares (fun _=>zero_lt_one)).2 U; simpa only[flore,exclaim,bar,Poly.bead,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk,Poly.solo,Poly.quiet_toll,one_mul] using ht
lemma florist (U:Config G n): hushK (flags R.p.threshold U) (fun i=>flore R i U)= ↑(R.activities.gas R.p U):=by
    let Q:=Poly.bead A!; let v i:= flore R i U; let b:= flags R.p.threshold U
    have hx: Q (hushK b v)= Accent.field (fun i=>exclaim Y A! i U) b:=by unfold hushK Accent.field; rw[map_sum]; refine sum_congr rfl fun p _=> ?_; unfold grid; split; rw [map_prod];rfl; exact map_zero Q
    have hy := hx.trans (hawk Y R.p A! H U); exact (if_pos rfl|>.symm.trans ((Poly.part_send ..).symm.trans ((congr_arg (fun x:Marker.Poly A!=>x.part (A!|>.quiet)) hy).trans ((Poly.part_send ..).trans (if_pos rfl)))))
end YM.Trace.Cask
