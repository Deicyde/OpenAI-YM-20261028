import YM.RemainderComparison.Ethereal.Oracle
import YM.RemainderComparison.Jolt.Revel
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Ethereal
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration
open Push Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Lacuna Vowel PhysicalNext.Repeat Jolt Flues
variable {G: Gauge}{n:Side}{ι : Type} {α:Type*}
variable (T:Vowel G n ℕ)(H:Yard ι α G n) (u:Set ι) (b:α) (p:BudgetPoint) (ρ: ι→Support n)
variable {B C σ τ w : ℝ}{k:ℕ}
-- projection preserve

def dusk (i:ℕ):= if Jolt.phase H u i then H.glow b i else 0
def gaze : Listing G n:= ⟨T.sign,H.more⟩
-- sign contained in T! use earlier negation convention
def vesp : Collection.Source G n:= ⟨T.stanza, Ethereal.dusk H u b⟩
def manor : Activities G n:= (gaze T H).read (vesp T H u b)
local notation "L₁"=> Ethereal.gaze T H
local notation "Y"=> Ethereal.manor T H u b
local notation "Xʼ"=> Ethereal.vesp T H u b
lemma festive (U:Config G n) : (Y).additive p U = T.overlay p U:=rfl
lemma speaks (hp:H.Sounds p ρ) : Activities.ForcedFamily Y p:=by
    have he:= hp.families b
    have hh i : UsesFinal p.threshold (H.more i).support ((Y).K i) ∧ GaugeInvariant ((Y).K i)∧ Measurable ((Y).K i)∧ ∀ U,(Y).K i U ≠0→ (H.more i).eligible p.threshold U:=by
        by_cases h:Jolt.phase H u i
        · rw [show (Y).K i =H.glow b i from if_pos h]; exact ⟨he.reads i, he.sym i,he.meas i,he.permit i⟩
        rw [show (Y).K i=0 from if_neg h]; exact ⟨fun _ _ _ _=>rfl,fun _ _=>rfl, measurable_const,fun _ hz=> (hz rfl).elim⟩
    exact ⟨fun i=> (hh i).2.1,he.symtest, fun i=> (hh i).2.2.1,he.meas_test,fun i=> (hh i).1,he.reads_test,fun i=> (hh i).2.2.2⟩
lemma quiescent (h : Jolt.Orbit H u) (he:T.Moves) s t : Nonempty ((Y).Moves s t):=by
    obtain ⟨e,hE⟩:=he.continual s t; obtain ⟨f,hF⟩:=h.spins s t
    refine ⟨⟨e,f,fun i=>congr_arg RegularAddress.site (hE i).1,fun i=> congr_arg RegularAddress.support (hE i).1,fun i=> congr_arg ForcedAddress.support (hF i).2.1, fun i=> congr_arg ForcedAddress.inventory (hF i).2.1,?_,fun i V=> congr_fun (hE i).2 _,?_⟩⟩
    · exact fun i=>(Jolt.valids ..|>.mp (hF i).2.1.symm).2.2
    intro i V; by_cases ht:Jolt.phase H u i
    · rw [show (Y).K i= _ from if_pos ht,show (Y).K (f i)=_ from if_pos ((hF i).1.2 ht)]; exact (hF i).2.2 ht V b
    rw [show (Y).K i=0 from if_neg ht,show (Y).K (f i)=0 from if_neg ((hF i).1.not.mpr ht)]; rfl
lemma furrows (hp:H.Pays u k p.B σ B): ∃ f:ℕ→ℝ, (∀ i,0≤ f i∧∀ U, ‖(Y).K i U‖≤ f i) ∧ Ac.Hit (fun i=> ((Y).forced i).support) p.B f σ B:=by
    obtain ⟨f,h,hv,hp'⟩:=hp.wages; refine ⟨f,fun i=> ⟨h i,?_⟩,hv⟩
    intro U; by_cases ht: Jolt.phase H u i; · rw [show (Y).K i=_ from if_pos ht]; exact hp' i (show _≤k from (show Mosaic.Verse.load u _=0 from ht).trans_le (Nat.zero_le _)) b U
    rw [show (Y).K i=0 from if_neg ht]; simpa using h i
lemma guarded (hp:T.Pricings p p.supportExponent τ) (hv:Normal T p)(hh:H.Sounds p ρ)(h:H.Pays u k p.B p.supportExponent w)(hq:Jolt.Orbit H u): Activities.Valid Y p τ w:=by
    refine ⟨Ethereal.retinue T p _ rfl rfl hv,Ethereal.speaks T H u b p ρ hh,Ethereal.quiescent T H u b hq hv.moves,Ethereal.burns T p Y rfl rfl le_rfl hp,?_⟩
    obtain ⟨f,hf,hH⟩:= Ethereal.furrows T H u b p h; refine ⟨f,hf,fun i=> ?_⟩
    have he:= hH i; convert he using 2 with j; unfold BudgetPoint.mass; split<;> ring
variable (he:T.Pricings p (Ethereal.mid p) C)
variable (h:H.Sounds p ρ)(hx:H.Pays u k p.B (p.supportExponent+1) w)(hp:T.Moves) (hz:Jolt.Orbit H u)
include he h hx hp hz
lemma qual : ∃ x, Collection.Local (Ethereal.gaze T H) p (vesp T H u b) x w :=by
    obtain ⟨f,hf,hP⟩:=he.marks; obtain ⟨z,hz'⟩:=Ethereal.slip _ _ f (fun i=> (hf i).2.1) hP
    exact ⟨z,fun i=> (hf i).1,Ethereal.speaks T H u b p ρ h, Ethereal.quiescent T H u b hz hp,⟨f,fun i=> (hf i).2,hz'⟩, Ethereal.furrows T H u b p hx⟩
omit h hx hp hz
open UVNext.CouplingReset
lemma funded : Averaging.Projects Y p C:=by obtain ⟨f,h,hV⟩:= he.marks; exact ⟨fun i=> (h i).1,⟨f,fun i=> (h i).2,Ethereal.loft _ (fun i=>(h i).2.1) hV⟩⟩
lemma tenor (x:ℝ) : ‖Collection.vac Xʼ x - x‖ ≤ C:=by
    have h:= Ethereal.accounted T p he (show 0≤ mid p from by unfold mid; linarith [p.exponent_pos]) (1:Config G n)
    have hh : (∑' i,(Xʼ).logRead i 1)= T.overlay p 1:=by
       unfold overlay; refine tsum_congr fun i=>?_ ; unfold Vowel.ray; rw [masked_eq _ _ _ _ (by unfold Healthy; rw [flags_one]; simp)]; rfl
    rw [Collection.vac,hh,sub_sub_cancel_left,norm_neg,norm_div,Real.norm_of_nonneg (sites_pos n).le]; exact (div_le_iff₀ (sites_pos _)).2 ((norm_tsum_le_tsum_norm h.2.1).trans (h.2.2.trans_eq (mul_comm _ _)))
end YM.RemainderComparison.Ethereal
