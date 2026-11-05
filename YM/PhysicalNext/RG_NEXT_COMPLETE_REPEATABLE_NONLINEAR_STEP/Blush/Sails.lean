import Mathlib.Data.Set.Finite.List
import YM.Extra.SOURCE_HISTORIES.LocalDebt
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Postcards
import YM.Progress.DIRECTED_RECIPE.Pellets


/-!
 # Single-marker physical queries from envelopes.X.U at ACTUAL.Support.P. Bill names never spare needs on Z.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Blush
open Function Filter Lattice RG Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums  Ovens ConnectedActivityE6   Lotus
open Extra.Histories Progress.DirectedRecipe Next.Foundations
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c n: Side}
variable (R:Rep G n){V:Config G n} (o:Site n) (X : Support n) (h: o∈X)
variable (s : ℕ)
-- select index *dependence only on shape*. no arbitrary history modifications. Blank enough.
abbrev reg : RegularAddress n:= ⟨o,X,h⟩
def found := blankRow n (reg o X h,0)
lemma latch (hs : HasSlots R.p R.activities): R.activities.reg (Blush.found o X h) = reg o X h:= by rw [hs.reg]; exact congr_arg Prod.fst (recorded _ _ _)

variable (f:Config G n→ℂ) (u:ℝ) (hv:R.p.Regular X f)(hp:R.p.supBounds o X f u)(hu:∀ U,‖f U‖≤u)(hw: SlotFit R o s f)
variable (A : ℂ→L[ℝ] ℝ) (hc : ∀ t:ℂ, ‖A t‖ ≤ ‖t‖)
-- Posterior selection at K

def firth: Leaf R := ⟨Wing.gasKey s,A ∘ f,fun U V h hF=> congr_arg A (hw.read U V h hF),fun U h=>hw.permits U (fun hp=> h (by simp only [Function.comp_apply,hp,map_zero])),trivial,u,fun i=>(hc _).trans (hu i),fun i U=>congr_arg A (hw.invariant i U),A.continuous.measurable.comp hw.borel⟩

def cove (hs: HasSlots R.p R.activities) : Leaf R:=by
  let t:=found o X h
  let F:=masked R.p.threshold X f
  have hh: R.activities.reg t=reg o X h:=latch R o X h hs
  refine ⟨Wing.logKey t,A ∘ F,?_,?_,hs.regular _,u,fun i=>?_,?_,A.continuous.measurable.comp (masked_measurable _ _ _ hv.borel)⟩
  · change UsesFinal _ (R.activities.reg t).support _; rw [hh]; intro U V h hM
    have hk:Healthy R.p.threshold X U↔Healthy R.p.threshold X V:=by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,show X ∩_= X ∩ flags R.p.threshold V from hM, Finset.disjoint_iff_inter_eq_empty]
    apply congr_arg A; by_cases ht:Healthy R.p.threshold X U; rw [show F U=_ from masked_eq _ _ f _ ht,show F V=_ from masked_eq _ _ f _ (hk.mp ht),hv.sites U V h]; exact (masked_ne _ _ _ _ ht).trans (masked_ne _ _ _ _ (mt hk.mpr ht)).symm
  · change ∀ U,(A ∘ F) U≠0→Healthy R.p.threshold (R.activities.reg t).support U; rw [hh]; intro U ht; by_contra hu; exact ht (by change A (F U)=0; rw [show F U=0 from masked_ne _ _ _ _ hu,map_zero])
  · refine (hc (F i)).trans ?_; unfold F; by_cases he : Healthy R.p.threshold X i; rw [masked_eq _ _ _ _ he]; exact hp.2 i he [] (by simp) (by simp); rw [masked_ne _ _ _ _ he, norm_zero]; exact hp.1
  · intro t U; change A (F _)=A (F U); apply congr_arg A; have hz : Healthy R.p.threshold X (gauge t U) ↔ Healthy R.p.threshold X U:=by unfold Healthy; rw [gauge_flags]
    unfold F; by_cases h: Healthy R.p.threshold X U; rw [masked_eq _ _ _ _ (hz.2 h),masked_eq _ _ _ _ h,hv.symmetry t U]; rw [masked_ne _ _ _ _ (mt hz.1 h),masked_ne _ _ _ _ h]
lemma maskStar (a:ℂ)(f : Config G n→ℂ)(U: Config G n)(X:Support n)(b:ℝ): masked b X (a • f) U=a*masked b X f U:= by by_cases ht: Healthy b X U<;> simp [ht]
variable (U : Config G n)
-- integrability irrespective of no positive lower.WZero
lemma cliff (t:Leaf R)(he:t.turn= Wing.logKey s) : t.cicada U= R.eval U * t.ingredient U:=by
  have hb i : t.bun i U= R.activities.gasOccurrence R.p i U * t.ingredient U:=by unfold Leaf.bun Leaf.bill Activities.gasOccurrence; split; rw [he,if_pos (show Wing.Occupied (.logKey _) _ from trivial)]; exact mul_comm ..; simp
  unfold Leaf.cicada; simp_rw [hb,tsum_mul_right]; unfold Rep.eval Activities.gas; rw [← mul_assoc]
lemma fords (t : Leaf R)(he:t.turn=Wing.gasKey s) : (t.cicada U : ℂ)= Extra.Histories.fare R s (fun U => (t.ingredient U:ℂ)) U:=by
  have hb i : (t.bun i U:ℂ)=(t.ingredient U:ℂ)* Extra.Histories.coat R s i U:=by
    unfold Extra.Histories.coat; by_cases h:R.activities.admissible R.p U i<;> by_cases hv:s∈i <;> simp [Leaf.bun,h,Leaf.bill,he,Wing.Occupied,hv,Wing.remaining]
  simp only [Leaf.cicada, Complex.ofReal_mul,Complex.ofReal_tsum,hb,tsum_mul_left]; rfl
lemma juror (z:ℂ): ‖Complex.reCLM z‖ ≤ ‖z‖:=Complex.abs_re_le_norm _
lemma jurorI (z:ℂ) :‖Complex.imCLM z‖ ≤‖z‖:=Complex.abs_im_le_norm _
-- exact given input prep guardians. record Weight crest/turn equal for Re/Im.Might make Inter separate.Coeff equality for PPX.
def frev:=firth R o s f u hu hw Complex.reCLM juror
def fim:=firth R o s f u hu hw Complex.imCLM jurorI
lemma rose : Extra.Histories.fare R s f= (Complex.ofReal ∘ (frev R o s f u hu hw).cicada ) + Complex.I • (Complex.ofReal ∘ (fim R o s f u hu hw).cicada) :=by
   funext i; simp only [Pi.add_apply,Pi.smul_apply,Function.comp_apply,smul_eq_mul]; rw [fords R s i (frev R o s f u hu hw) rfl,fords R s i (fim R o s f u hu hw) rfl]; unfold fare; let D:= dressed R s i
   let t:= Real.exp (R.exponent i); change (t:ℂ) *(f i*D)=(t:ℂ)*(((f i).re:ℂ)*D)+Complex.I*((t:ℂ)*(((f i).im:ℂ)*D)); nth_rw 1 [← Complex.re_add_im (f i)]; ring
variable (hs: HasSlots R.p R.activities)
def crev := cove R o X h f u hv hp Complex.reCLM juror hs
def cim:= cove R o X h f u hv hp Complex.imCLM jurorI hs
lemma balm : Extra.Histories.salary R X f=(Complex.ofReal ∘ (crev R o X h f u hv hp hs).cicada)+Complex.I • (Complex.ofReal ∘ (cim R o X h f u hv hp hs).cicada):=by
   funext i; let X':= crev R o X h f u hv hp hs; let Y:=cim R o X h f u hv hp hs
   change _ = (X'.cicada i:ℂ)+Complex.I*(Y.cicada i:ℂ); let A:= Wing.logKey (found o X h); have hz : X'.turn=A:=rfl; have hQ : Y.turn=A:=rfl
   rw [cliff R _ i X' hz,cliff R _ i Y hQ,Complex.ofReal_mul,Complex.ofReal_mul]; let v:=R.eval i; let u:=masked R.p.threshold X f i
   change (v:ℂ)*u=v*(u.re:ℂ)+Complex.I*((v:ℂ)*(u.im:ℂ)); nth_rw 1 [← Complex.re_add_im u]; ring

-- K/E mark coefficients inhabit fixed common structure, only join amplitudes after proof. Keep DP schedule.Weight factor.
structure Cloud (R : Rep G n) where
   live : Leaf R
   pale : Leaf R
   together : live.turn = pale.turn
   rates : live.weight = pale.weight

def fan : Cloud R := ⟨frev R o s f u hu hw,fim R o s f u hu hw,rfl,rfl⟩
def float : Cloud R:=⟨crev R o X h f u hv hp hs,cim R o X h f u hv hp hs,rfl,rfl⟩
namespace Cloud
variable {R}
def milk (S : Cloud R) := (Complex.ofReal ∘ S.live.cicada)+Complex.I • (Complex.ofReal ∘ S.pale.cicada)
lemma turnout (t:Cloud R) : t.live.crest=t.pale.crest:=congr_arg (fun i=>Wing.support i R) t.together
lemma painted (Q : StepData c n)(β:ℝ)(U : Config G c)(t: Config G n→ℝ): Q.push β (Complex.ofReal ∘ t) U=((Q.push β t U :ℝ):ℂ):=by
   unfold StepData.push; simp_rw [Function.comp_apply,Complex.real_smul,smul_eq_mul,← Complex.ofReal_mul, integral_complex_ofReal]
lemma breeze {a b c' d e:ℝ} {Q : StepData c n} (h : R.Lawful a b c' d e)(t : Cloud R)(hb: Q.IsKernel R.beta G) : Q.push R.beta t.milk=(Complex.ofReal ∘ Q.push R.beta t.live.cicada)+ Complex.I • (Complex.ofReal ∘ (Q.push R.beta t.pale.cicada)):=by
  have hk (i:Leaf R): Integrable (Complex.ofReal ∘ i.cicada) (prior G n):= (i.sells h|>.1.integrable _).ofReal
  unfold milk; rw [StepData.push_add hb _ _ (hk _) ((hk _).smul _),StepData.push_smul _ _ _ _ (hk _), funext (fun i=>Cloud.painted Q R.beta i t.live.cicada), funext (fun i=>Cloud.painted Q R.beta i t.pale.cicada)]; rfl -- might apply.type mismatch
end Cloud
end YM.PhysicalNext.Repeat.Blush
