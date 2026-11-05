import YM.MergeProof.Ballet
import YM.MergeProof.Cashew
import YM.MergeProof.Switch
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Festal
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Garter

/-! Reseated singleton (ANY affine and conjugation), retain conditional. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories Ac Local
open Planned.GuardedAtom Accent PhysicalNext.Repeat.Lotus Motion
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{d:ℕ} {n:Side}(A:History G) (T:Hol G)
variable {F:Labels.Frame G d}(V:SectionData F){N m p:ℕ} (P:Coefficient F (A.S.side m p))(a:Motion)(y : Site (A.S.side m p))
local notation "K"=> A.levels
local notation "R"=> (A.rep N p m)
set_option quotPrecheck false
variable (ξ:ℂ)(h:A.Selected)
-- epoch-free. P(·) at ANY anchor. transformed.Exp global.ever
variable (o:Site (A.S.side m p)) {lambda w:ℝ}
def sunny (Rt:Rep G n)(u: ℕ→ Config G n→ℂ) (m:Motion)(x:Site n)(z:ℂ):= z • floatUp m x (profile Rt.activities u)
def radiant (z:ℂ)(m:Motion)(x: Site n)(f:Config G n→ℂ):= z • stepUp m x f
lemma rainbow {I:Type*}{u:I → Config G n→ℂ}(H:Dominated u)(x:ℂ): Dominated (x • u):=by
    obtain ⟨v,hP,hV⟩:= H; exact ⟨_,hP.mul_left ‖x‖,fun i U=> by simp only [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (hV i U) (norm_nonneg _)⟩
include h
lemma sparkling (ht:m≤N)(he:V.Sound T)(hf:P.Format o T R)(hg:P.remBound o R lambda w):∃ k:ℕ → Config G (A.S.side m p)→ℂ,sunny R P.forced a y ξ=profile (R).activities k ∧
    Dominated k ∧ coin R (radiant ξ a y (P.exponentialEntry o V R)) k= radiant ξ a y (P.density o V R):=by
    obtain ⟨b,c,hx,hK⟩:=rem_tabs.mp hg; obtain ⟨π⟩:= (h.represents N p m ht).good.labels.moves a.1 y
    let Q:= audition π P; obtain ⟨hv,hc,hD⟩:= audition_turn a y π ((by decide: 2≤ 4).trans (Next.Foundations.actual_side_ge A.S m p)) he hf hx
    refine ⟨ξ • Q.forced,?_,rainbow (rem_dominated (hc.bound le_rfl)) _,?_⟩
    · rw [profile_scale]; unfold sunny Q; rw [foyer]
    unfold radiant; rw [coin_mul,← bow a P y he π] -- order? bow : ... aga
    exact congr_arg (ξ • ·) ((coin_primary (R) V _ _).trans hD)
omit h
-- propagator normalized f path
section tick
local notation "o'" => (A.levels.clock.op m p)
local notation "R'"=> (A.rep N p (m+1))
variable (f:Config G (A.S.side (m+1) p)→ℂ)(D:ℕ)
lemma tint (z:Motion)(x: Site n) (F : Config G n→ℂ)(hF:Integrable F (prior G n)): Integrable (stepUp z x F) (prior G n):=by
   have he:(MeasurePreserving (pull z.1 x) (prior G n) (prior G n)):= prior_pull ..
   have hv: Integrable (F ∘ pull z.1 x) (prior G n):= (he.integrable_comp hF.aestronglyMeasurable).mpr hF
   unfold stepUp Motion.scalar;cases z.2 with
   | true=> exact (starL' ℝ (A:=ℂ)).toContinuousLinearMap.integrable_comp hv -- check
   | false=> exact hv
lemma starship {g:Config G (A.S.side m p)→ℂ}(he:g=blast A N p m D f)(hf:Integrable f (prior G _)) (η:ℂ)(hx:η=((A.S.block m).val:ℂ)^D*ξ):
    radiant ξ a y g=(o').push (R').beta (radiant η a ((o').ratio.embed y) f):=by
    unfold radiant; rw [StepData.push_smul _ _ _ _ (tint a _ _ hf), he, ← unison a A m N p D]; unfold blast; rw [smul_smul,hx,mul_comm ξ]; exact hf
end tick
end YM.MergeProof
