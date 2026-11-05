import YM.TraceExtension.Soot.Loom
import YM.TraceExtension.Anchor.Price
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V : Type} [Fintype V][DecidableEq V]{B:Census V}{G:Gauge}
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi Bid Accent Planned.GuardedAtom
variable {C:Family G} (hw:C.Makes) {N k m p d:ℕ}
local notation "R"=>C.path.rep N p k
local notation "Z"=>C.path
local notation "γ"=> (C.path.levels.clock.forcedAllowance k)
local notation "u"=>Real.sqrt (C.path.levels.clock.forcedAllowance k)
local notation "F"=>C.labels.level d
local notation "Y"=>C.localSection d
local notation "a"=>alto C.path k d
variable (X:Coefficient (C.labels.level d) (C.side k p)){t:ℝ}
set_option quotPrecheck false
open Motion Relay
include hw
lemma bornK (h:k ≤ N)(he:X.Format 0 C.params R) (hh:X.remBound 0 R u t) (v:Motion)(p':Site (C.side k p)): ∃ f:ℕ→ Config G (C.side k p)→ℂ, ForceFormat (R|>.p) (R|>.activities) p' f ∧ ForceCost (R|>.p) (R|>.activities) f (‖a‖*(u*t)) ∧ sunny R X.forced v p' a=profile (R|>.activities) f:=by
    obtain ⟨π⟩:= (hw.wilson.represents N p k h).good.labels.moves v.1 p'; obtain ⟨x,y,hx,hx'⟩:= rem_tabs.mp hh
    let q:=audition π X; obtain ⟨hy,hc,hr⟩:= audition_turn v p' π ((by decide:2 ≤ 4).trans (Next.Foundations.actual_side_ge C.path.S k p)) (hw.sections d) he hx
    let f:=a • q.forced; have hp:= hc.forced; change q.Format _ _ _ at hy; rw [show affine v.1 p' 0=p' from by simp [affine]] at hy
    refine ⟨f,⟨fun i U h=> ?_,fun i h=> ?_,fun i g U=> congr_arg (a • ·) (hy.invariant ..),fun i U V hu hv=> congr_arg (a • ·) (hy.supported i U V hu hv),fun i=> (hy.borel i).const_smul a⟩,?_,?_⟩
    · exact hy.forcing _ _ fun ht=> h (by simp[f,ht])
    · exact hy.carried i fun ht=>h (by simp[f,ht])
    · obtain ⟨b,hb,H⟩:= hp; refine ⟨fun i=> ‖a‖*b i,?_,fun i=> ⟨mul_nonneg (norm_nonneg _) (H _|>.1),fun U=> ?_⟩⟩
      · have ht:= Local.sumBudget_mul_left hb (norm_nonneg a); apply Budget.mono ht; exact fun i=> mul_nonneg (Real.exp_pos _).le (mul_nonneg (norm_nonneg _) ((H i).1)); intro i; unfold BudgetPoint.mass; rw [mul_left_comm]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left hx.first).trans hx') (Real.sqrt_nonneg _)) (norm_nonneg _)
      change ‖a * q.forced i U‖ ≤ _; rw[norm_mul]; exact mul_le_mul_of_nonneg_left ((H _).2 U) (norm_nonneg _)
    rw[show profile _ f=_ from profile_scale ..]; unfold sunny q; rw[foyer]
lemma fellK {z w:ℝ}{M:Extra.Histories.Music (C.labels.level d) C.path N p} (v:C.label d) (hh:Heard Y Z N p C.params k (M.tone k)) (hr:0≤w)(hx:w*bond C.path N p M k v≤z) (hp:z* (C.path.levels.params k).columns ≤ 1) : w*(‖a‖ * (u*(M.tone k).charge v)) ≤ u:=by
   have h := hh.cone v; let Q:=F; let P:=C.path.levels.params k|>.columns; let q:= M.tone k; let V:=q.index v; let y:=Q.coeffSize V; let t:= q.charge v
   have hz:0 ≤ P:= zero_le_one.trans (C.path.levels.params k|>.columns_ge)
   have he: t ≤ P*y:= h.trans (mul_le_mul_of_nonneg_left (show Q.coeffSize (Q.core V) ≤ y from by
       unfold Labels.Frame.coeffSize; refine sum_le_sum fun i _=> ?_; change ‖Function.update V 0 0 i‖≤‖V i‖; by_cases h:i=0<;>simp[h]) hz)
   have ht: w*‖a‖*t≤1:=by
       apply (mul_le_mul_of_nonneg_left he (mul_nonneg hr (norm_nonneg a))).trans; change w*(‖a‖*y) ≤ z at hx; linarith only [mul_le_mul_of_nonneg_right hx hz,hp]
   linarith only [mul_le_mul_of_nonneg_right ht (Real.sqrt_nonneg γ)]
lemma floated_add (i : Motion)(j:Site (C.side k p))(f g: Res G (C.side k p)): floatUp i j (f+g)=floatUp i j f + floatUp i j g:=by funext Q V; unfold floatUp; exact Motion.scalar_add i _ _
-- independent clutch
structure Buff (f:Config G (C.side k p)→ℂ)(L : MergeProof.Response G (C.side k p))(v:ℝ) (X: Coefficient (C.labels.level d) (C.side k p))(r:ℝ):Prop where
   shell : X.Format 0 C.params (C.path.rep N p k)
   sound : X.remBound 0 (C.path.rep N p k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) v
   fuel : Attainment (R|>.p) 0 L r
   foam : profile (R|>.activities) X.forced = hook (R|>.activities) (R|>.p.threshold) L
   hit : ∀ U, alto C.path k d* X.density 0 Y R U=(R|>.eval U:ℂ)*f U
lemma boost (G':Config G (C.side k p)→ℂ)(L : MergeProof.Response G (C.side k p)) (r:ℝ) (h: Buff (N:=N) G' L t X r) (hm:k≤N) (m:Motion) (v:Site (C.side k p)): let b:=radiant a m v (X.exponentialEntry 0 Y R); let q:=stepUp m v G';∃ K L',
    Dominated K ∧ profile (R|>.activities) K= hook (R|>.activities) (R|>.p.threshold) L' ∧ profile (R|>.activities) K=sunny R X.forced m v a∧Attainment (R|>.p) v L' (‖a‖*r) ∧ ∀ U,coin R b K U=((R|>.eval U):ℂ)*q U:=by
    intro b q; obtain ⟨g,hg,hG,hQ⟩:=sparkling Z C.params Y X m v a hw.wilson 0 hm (hw.sections d) h.shell h.sound
    obtain ⟨π⟩:= (hw.wilson.represents N p k hm).good.labels.moves m.1 v; let p:=upwards m v L; have hv:= rise m v h.fuel; rw [show affine m.1 v 0=v from by simp[affine]] at hv
    refine ⟨g,a • p,hG,?_,hg.symm,stack_of hv _,fun U=>?_⟩
    · rw [← hg,hook_scale, show hook _ _ p = _ from hooked m v π _ L]; unfold sunny; rw [h.foam]
    let V':=pull m.1 v U; rw[show coin R b g U= _ from congr_fun hQ U]; change a * scalar m (_)=_*scalar m (G' V'); rw[← lept,show a*_ =_ from h.hit V', scalar_mul, (show (R|>.eval V':ℂ)= _ from vac_pull Z N _ k hw.wilson hm m.1 v U)]; cases hx:m.2 <;> simp [liftVac,Motion.scalar,hx]
end YM.MergeProof.Accent
