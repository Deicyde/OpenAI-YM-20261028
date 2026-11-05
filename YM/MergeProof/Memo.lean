import YM.MergeProof.Ballad
import YM.MergeProof.Relive
/-! Retain d+3 door trace. Inputs as exact E+bar/outputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{f c:Side}{D:ℕ}{F:Labels.Frame G D}{B:SectionData F}
    {R:Rep G f}{E:Rep G c}{P:Coefficient F c}{L:Side}{ι:Type}
def Tale (X:Wing→Prop)(o:Site f)(b:Site c)(v:ℂ)(α:Config G f→ℂ)(ωs:Res G f)(β:Res G c)(δ:ℂ) (t u:ℝ) (H:GaugeDoor R E):Prop:=
   ∃ (ι:Type), Countable ι ∧ ∃ M:ι→Lotus.Leaf R,∃ s ψ, Odyssey X o b v α ωs β δ t u H M s ψ
variable {X:Wing→Prop}{o:Site f}{b:Site c}{v δ:ℂ}{α:Config G f→ℂ}{ωs:Res G f}{β:Res G c}{t u a w:ℝ}{M:ι→Lotus.Leaf R}{s:ι→ℂ}{ψ:Response G c}{H:GaugeDoor R E}
lemma Odyssey.tale [Countable ι](h:Odyssey X o b v α ωs β δ t u H M s ψ): Tale X o b v α ωs β δ t u H:=⟨ι,inferInstance,M,s,ψ,h⟩
lemma taped (ht:0≤ t)(hx:0≤u):Tale X o b v (fun _=>δ) 0 0 δ t u H:=by
   have h: Odyssey X o b v (fun _=>δ) 0 0 δ t u H (Empty.elim) (fun _=>0) 0:=by
     refine ⟨fun i=> i.elim,?_, stackFee (Attainment.blank _) hx,?_,?_,?_⟩
     · exact ⟨fun i=> i.elim, Summable.of_finite,by simpa using ht⟩
     · intro U; simp
     · intro j U; simp
     intro j U; simp [hook]
   exact h.tale
namespace Tale
variable (h:Tale X o b v α ωs β δ t u H)
include h
lemma travel (x:ℂ): Tale X o b v (x • α) (x • ωs) (x • β) (x*δ) (‖x‖*t) (‖x‖*u) H :=by obtain ⟨ι,h',M,s,ψ,h⟩:=h; exact (h.quaver x).tale
lemma climb {Y:Wing→Prop}(hp:X≤Y)(hx:t≤a)(hv:u≤w):Tale Y o b v α ωs β δ a w H:=by obtain ⟨ι,h',M,s,ψ,h⟩:=h; exact (h.elevate hp hx hv).tale
lemma gain {S:StepData c f}(hp: SoundDoor S H)(m:Motion)(x: Site c) (π:R.activities.Moves m.1 (S.ratio.embed x))(hv:scalar m v=v): Tale (Set.image (Wing.labelRoute π) X) (affine m.1 (S.ratio.embed x) o) (affine m.1 x b) v (stepUp m (S.ratio.embed x) α) (floatUp m (S.ratio.embed x) ωs) (floatUp m x β) (scalar m δ) t u H:=by obtain ⟨ι,h',M,s,ψ,h⟩:=h; exact (Odyssey.dancing m x h hp π hv).tale -- edit
omit h in
lemma upon [Countable ι]{p:ι → Config G f→ℂ}{q:ι→Res G f}{r:ι→Res G c}{w':ι→ℂ}{e k:ι→ℝ}{S:StepData c f}(hs:SoundDoor S H)(h:∀ i:ι, Tale X o b v (p i) (q i) (r i) (w' i) (e i) (k i) H)(hp:∀ i,HasSum (fun j=>p j i) (α i))(hq:∀ i U,HasSum (fun j=>q j i U) (ωs i U))(hr:∀ i U,HasSum (fun j=>r j i U) (β i U))(hδ:HasSum w' δ)(ht: SumBudget e t)(hu:SumBudget k u): Tale X o b v α ωs β δ t u H:=by
   choose Ξ h M s ψ h' using h
   exact (symbolize H hs h' hp hq hr hδ ht hu).tale
end Tale
end YM.MergeProof
