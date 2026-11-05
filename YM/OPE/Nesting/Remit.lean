import YM.OPE.Nesting.Sensors

/-! Exact readout at the new hypothesis after both averages and the knife,
as a fixed finite collection of the paid readers. Purely pointwise before taking
rates (integral identities only whenever whole orbits fit the docks). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting.Sensor
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
attribute [local instance] Orbits.measO Orbits.borelO Orbits.hμ
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
variable {L I:Type} {l:Filter L}{a:L→ℝ}{o:L→E4}{z:L→I→E4}
local notation "P₀" => R.port
local notation "Q" => U.sector.derivatives
local notation "X" => U.sector.turns
local notation "ρ" => U.room.kernel.spin

variable (A A':Menu S L)
def realAtom (p:Atom S L)(m:ℕ)(o:L→E4)(s:L):S.Field m:=p.amp s • checkReal P₀ R.law R.continuum m (p.place s) (o s) (voices p.tags)
def realMenu (p:Menu S L)(m:ℕ)(o:L→E4)(s:L):= ∑ q:p.Draw, realAtom U R (p.pick q) m o s

lemma convertAtom (p:Atom S L)(m:ℕ)(s:L): (2:ℝ)⁻¹ • (avgAtom U R p m o s + (conjugateR ρ m) (avgAtom U R (Atom.shadowed ρ p) m o s))=realAtom U R p m o s:=by
     let f:=averageV P₀ X m (p.place s) (o s) (d:=degrees p.tags); let w:= voices p.tags; let v':=averageV P₀ X m ((p.shadowed ρ).place s) (o s) (voices (p.shadowed ρ |>.tags))
     have hv:v'=f (bar ρ w):=rfl
     have he:= checkValue (P:=R.port) m R.law R.continuum (p.place s) (o s) w
     change (2:ℝ)⁻¹ • (p.amp s • f w + S.conj ρ m ((starRingEnd ℂ) (p.amp s) • v'))=p.amp s • _
     rw [hv]; rw [he,smul_comm (p.amp s) (2:ℝ)⁻¹]; simp only [smul_add,map_smulₛₗ,show (starRingEnd ℂ) ((starRingEnd ℂ) (p.amp s))=p.amp s from star_star _]; rfl
lemma convertMenu (m:ℕ)(s:L): (2:ℝ)⁻¹ • (avgMenu U R A m o s + (conjugateR ρ m) (avgMenu U R (Menu.shadowed ρ A) m o s))=realMenu U R A m o s:=by
     unfold avgMenu; rw [map_sum]; change (2:ℝ)⁻¹ • ((∑ q:A.Draw,avgAtom U R (A.pick q) m o s)+∑ q:A.Draw,(conjugateR ρ m) (avgAtom U R (Atom.shadowed ρ (A.pick q)) m o s))=_
     rw [← Finset.sum_add_distrib,Finset.smul_sum]; exact Finset.sum_congr rfl (fun i _=>convertAtom U R ..)
def classifier (m:ℕ)(h:R.channels m):S.Field m→ₗ[ℂ] ℂ:= (R.basis m).coord h ∘ₗ ((R.knife m).codRestrict (R.stratum m) (fun z=>R.knife_mem m z))
lemma convertIssues (m:ℕ)(h:R.channels m)(s:L) :(classifier U R m h) (realMenu U R A m o s)= A.charge R m h o s:=by
     unfold realMenu Menu.charge; rw [map_sum]; refine Finset.sum_congr rfl fun i _=>?_
     rw [realAtom,map_smul]; rfl

variable [Fintype I] [l.NeBot] {b u W γ:ℝ}{m:ℕ}
include R
lemma agreeInk (hw:affordable U R m W)(hA:Tendsto a l atTop)(he:Agrees U l a z u b W γ A A') (h₁:Eligible l a z b A)(h₂:Eligible l a z b A')(hz:Tendsto (fun i=>away (z i) (o i)) l (𝓝 0))(hb:0≤u)(hc:u≤b) : RateLE l a (fun s=>avgMenu U R A m o s-avgMenu U R A' m o s) γ:=by
    refine ink U R A A' ?_ hw hA h₁ h₂ hz
    intro j hj e h' he' k
    let y(s:L):=swung e (k s) (o s)
    have hh:=toSensors U R hA hz hb k e
    apply move_cost (fun _=>S) (fun _=>U.room.kernel) (expo e) hh ((shrinking_port (o:=o) hA e k).1.mono (hb.trans hc)) hc (fun w hw=>he w y (fun _=>none) hw hh ((shrinking_port (o:=o) hA e k).1.mono (hb.trans hc))) hA he' h₁ h₂ _ (turn_port_rate hA R.law e k)
set_option maxHeartbeats 800000 in
lemma remit (h:R.channels m) (hw:affordable U R m W)(hA:Tendsto a l atTop)(he:Agrees U l a z u b W γ A A') (h₁:Eligible l a z b A)(h₂:Eligible l a z b A')(hz:Tendsto (fun i=>away (z i) (o i)) l (𝓝 0)) (hb:0≤u)(hc:u≤b): RateLE l a (fun s=>A.charge R m h o s - A'.charge R m h o s) γ:=by
    let cor := (classifier U R m h).restrictScalars ℝ; let V (A:Menu S L):= realMenu U R A m o
    apply (pay_fixed (a:=γ) (x:=fun s=>V A s-V A' s) hA cor ?_).congr
    · exact Eventually.of_forall fun s=> by change classifier U R m h (_-_) = _-_; rw [map_sub]; exact congr_arg₂ _ (convertIssues U R A m h s) (convertIssues U R A' m h s)
    let A₁:= Menu.shadowed ρ A; let A'₁ := A'.shadowed ρ
    let f:=fun (A:Menu S L)=>avgMenu U R A m o
    have hh:Agrees U l a z u b W γ A₁ A'₁:=(agree_shadow U ρ (fun {J} _ w=> by apply he) h₁ h₂ hc)
    have hv:= agreeInk U R A₁ A'₁ hw hA (by exact hh) (A.shadowed_ok ρ h₁) (A'.shadowed_ok ρ h₂) hz hb hc
    have hv:= (agreeInk U R A A' hw hA he h₁ h₂ hz hb hc).add (pay_fixed hA (conjugateR ρ m) hv) hA
    refine (((RateLE.const (2:ℝ)⁻¹ hA).smul hv).congr (?_)).mono (zero_add _|>.le); refine Eventually.of_forall fun s=>?_
    change (2:ℝ)⁻¹ • ((_ - _)+(conjugateR ρ m) (_-_))= realMenu _ _ _ _ _ _ - realMenu _ _ _ _ _ _
    rw [← convertMenu,← convertMenu,← smul_sub,map_sub]; apply congr_arg; abel
end YM.OPE.Nesting.Sensor
