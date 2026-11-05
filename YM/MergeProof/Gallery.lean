import YM.MergeProof.Orchestra
import YM.MergeProof.Routes

/-! Stronger calibration: each step *fixed vacuum processor*, reusable receipts. Witness alignment in space of E exponential and forced support/inventory profile, with even zero outputs covered. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{f c:Side}
abbrev Res (G:Gauge)(f:Side):= Box f→ Config G f→ℂ
structure GaugeDoor (R:Rep G f)(E:Rep G c) where
   hinge : Lotus.Leaf R → ℕ → Config G c →ℝ
variable {R:Rep G f}{E:Rep G c}(H:GaugeDoor R E)
   {ι:Type}{m:Motion}
def entry (M:Lotus.Leaf R) (i:Box f) (U:Config G f) : ℂ:= match M.turn with
   | .gasKey j=> if barcode R.activities j=i then M.ingredient U else 0
   | .logKey _=> 0
def prose (M:Lotus.Leaf R) (U:Config G f) : ℂ:= match M.turn with
   | .gasKey _=> 0
   | .logKey _=> M.ingredient U
def quoted (M:Lotus.Leaf R) := profile E.activities (fun i=> Complex.ofReal ∘ H.hinge M i)
def load (M:Lotus.Leaf R) := R.p.mass M.crest M.weight
-- separation part of consumer. wing cap price. unit constant not priced!
structure Odyssey (X:Wing→Prop)(o:Site f)(b:Site c) (v:ℂ)(α:Config G f→ℂ)(ωs:Res G f)(β:Res G c)(δ:ℂ) (t u:ℝ) (H:GaugeDoor R E) (M:ι→Leaf R)(s:ι→ℂ)(ψ:Response G c):Prop where
   member i:o∈ (M i).crest ∧ X (M i).turn
   purchase : SumBudget (fun i=> ‖s i‖*load (M i)) t
   cost : Attainment E.p b ψ u
   lyric U: HasSum (fun i=> s i* prose (M i) U) (α U-δ)
   old j U: HasSum (fun i=> s i*entry (M i) j U) (ωs j U)
   grants j U: HasSum (fun i=> v*s i*quoted H (M i) j U) (β j U-hook E.activities E.p.threshold ψ j U)
-- qualitative/operator budget
structure SoundDoor (S:StepData c f) (H:GaugeDoor R E):Prop where
   volume:∃ w:ℝ,∀ M,ForceCost E.p E.activities (fun i=> Complex.ofReal ∘ H.hinge M i) (w* load M)
   conduct(s:Motion)(x:Site c)(π:R.activities.Moves s.1 (S.ratio.embed x)):
    ∃ u:E.activities.Moves s.1 x,∀ i j U,H.hinge (Leaf.route π i) (u.kp j) U= H.hinge i j (pull s.1 x U)
namespace Odyssey
variable {X:Wing→Prop}{o:Site f}{b:Site c}{v δ:ℂ}{α:Config G f→ℂ}{ωs:Res G f}{β:Res G c}{t u a w:ℝ}{M:ι→Lotus.Leaf R}{s:ι→ℂ}{ψ:Response G c}{L:Side}
    {H:GaugeDoor R E}(h:Odyssey X o b v α ωs β δ t u H M s ψ)
include h

lemma quaver (a:ℂ): Odyssey X o b v (a • α) (a • ωs) (a • β) (a*δ) (‖a‖*t) (‖a‖*u) H M (a • s) (a • ψ):=by
   refine ⟨h.member,?_ ,stack_of h.cost a,fun U=>?_,fun j U=> ?_,fun j U=>?_⟩
   · simp_rw [Pi.smul_apply,norm_smul,mul_assoc]; exact Local.sumBudget_mul_left h.purchase (norm_nonneg _)
   · simpa only [Pi.smul_apply,smul_eq_mul, ← mul_sub,mul_assoc] using! ((h.lyric U).mul_left a)
   · simpa only [Pi.smul_apply,smul_eq_mul,mul_assoc] using! ((h.old j U).mul_left a)
   simp_rw [hook_scale, Pi.smul_apply,smul_eq_mul, ← mul_sub]; exact ((h.grants j U).mul_left a).congr_fun (fun i => by ring)
lemma elevate {Y:Wing→Prop} (hp:X≤Y) (he:t≤a)(hu:u≤w): Odyssey Y o b v α ωs β δ a w H M s ψ:=⟨fun i=> ⟨(h.member i).1,hp _ (h.member i).2⟩,⟨h.purchase.1,h.purchase.2.1,h.purchase.2.2.trans he⟩,stackFee h.cost hu,h.lyric,h.old,h.grants⟩
end Odyssey
end YM.MergeProof
