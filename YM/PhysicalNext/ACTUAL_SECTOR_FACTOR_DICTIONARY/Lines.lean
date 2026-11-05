import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Rig
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Applications

/-! Both other correction entries of the multiplier. For the linear
entry preserve both legs of the mean estimate (& 1/g); one cannot infer
its analytic price just from the funding used here as locality rules!
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace Completion

namespace Voice
open Wires Geo 
variable {G : Gauge} {c f : Side} {S : StepData c f} (d : AnalyticBridge.LocalGaussian.Desk G S)
local notation "T" => d.tube
local notation "q" => d.broadCut
local notation "x" => d.betaHat
local notation "B" => radiusB d.betaHat

def mist (F : Forest S.ratio) (A : Stores S) (k : S.Choices) (V : Config G c) (Y : Config G f) :=
    tape.symm (outlook T x q d.radius k V Y A F)
def shaft (F : Forest S.ratio) (A : Stores S) (k : S.Choices) (V : Config G c) (Y : Config G f)
    (i : Full G f) := (-d.g⁻¹)*((beam T k V x A F *ᵥ mist d F A k V Y) i + debts T x q d.radius k V Y A F i)

def smoky (e : Bond f) : Formula G S ℝ := fun F A b k V l =>
    if Physical.openBond A F x e then ∑ a:G.ColorIndex,shaft d F A k V l.1 (e,a)*l.2 e a else 0

set_option maxHeartbeats 200000 in
lemma shaft_meas {P : Teller G} (hP : P.Funds S T) (h : Route.Badge.App d) (F : Forest S.ratio)
    (A : Stores S) (k : S.Choices) (i : Full G f) : Measurable (fun l : Config G c × Refs G f => shaft d F A k l.1 l.2.1 i) := by
  let Y (l : Config G c × Refs G f) := (l.1,l.2.1)
  have hy : Measurable Y := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hm (j : Full G f) := (measurable_pi_apply j).comp (tape.symm.measurable.comp
    ((herald T x q d.radius hP k A F h.valid.positive h.enough).comp hy))
  have hL : Measurable (fun w : Config G c × Refs G f=>debts T x q d.radius k w.1 w.2.1 A F i) :=
    (debts_meas T x q d.radius k A F hP h.valid.positive h.enough i).comp (f:=Y) hy
  have ht (j : Full G f) : Measurable (fun l : Config G c × Refs G f=>beam T k l.1 x A F i j * mist d F A k l.1 l.2.1 j) := by
    have hJ : Measurable (fun l : Config G c × Refs G f=> beam T k l.1 x A F i j) := (beam_meas T k x A F i j h.aperture.branched).comp measurable_fst
    exact hJ.mul (show Measurable (fun l : Config G c × Refs G f=>mist d F A k l.1 l.2.1 j) from hm j)
  have hf : Measurable (fun l : Config G c × Refs G f=>(beam T k l.1 x A F *ᵥ mist d F A k l.1 l.2.1) i) := by
    unfold mulVec dotProduct; exact Finset.measurable_fun_sum _ (fun j _ => ht j)
  exact (measurable_const (a:=-d.g⁻¹)).mul (hf.add hL)

theorem smoky_care (h : Route.Badge.App d) (e : Bond f) : Care d {portOf S e} (smoky d e) := by
  obtain ⟨P,hP⟩:=h.valid.funds
  constructor
  · intro F A b k; unfold smoky uncurry; split
    · refine Finset.measurable_fun_sum _ fun i _=> (shaft_meas d hP h F A k (e,i)).mul ?_
      have hp : Continuous (fun y : G.Color=> y i) := PiLp.continuous_apply ..
      exact hp.measurable.comp ((measurable_pi_apply e).comp (measurable_snd.comp measurable_snd))
    exact measurable_const
  intro F F' A A' b b' k k' V V' l l' H
  have hl := oxygen d h H e (Finset.mem_singleton_self _)
  unfold smoky; rw [hl.2]; split
  next ht =>
    refine Finset.sum_congr rfl fun i hi => ?_; rw [hl.1]
    let I : Full G f := (e,i); let X := ambient d {portOf S e}
    have hj : Shields X (Physical.place S I) (40*B) := covers_shield _ (Finset.mem_singleton_self _)
    have hf := h.aperture.spans
    have hv : (beam T k V x A F*ᵥ mist d F A k V l.1) I = (beam T k' V' x A' F'*ᵥmist d F' A' k' V' l'.1) I := by
      unfold mulVec dotProduct; refine Finset.sum_congr rfl fun j _=>?_; dsimp only
      by_cases hn : nearby (Physical.place S) (2*Next.SectorChange.span S.patch x) I j
      · unfold nearby at hn
        rw [beam_read T h.aperture H.fields _ _ (hj.shrink (by omega))]
        apply congr_arg (_ * ·)
        change outlook T x q d.radius k V l.1 A F j.1 j.2=outlook T x q d.radius k' V' l'.1 A' F' j.1 j.2
        exact congr_arg (fun v : G.Color=>v j.2) (beam_bias T x q d.radius H.fields h.aperture _ (hj.shift
          (show separation _ (Physical.place S j) + 18*B ≤ 40*B by omega)) H.input.frost)
      rw [range_limit T k V x A F h.aperture I j hn,range_limit T k' V' x A' F' h.aperture I j hn]; simp
    unfold shaft
    dsimp only [I,X] at hv hj
    rw [hv,debt_region T x q d.radius H.fields h.aperture (e,i) (hj.shrink (by omega)) H.input.frost]
  rfl

section actual
variable {F : Forest S.ratio} {A : Stores S} (h : Route.Badge.App d) (k : S.Choices) (V : Config G c)
    (hv : A.flags=RG.flags (temp d.betaHat) V) (p : Geo.Refs G f)
include h hv
lemma calibrated (i : Rows.In d.betaHat A F (G:=G)) : shaft d F A k V p.1 (active d.betaHat A F i)=
    let Y:=iced p.1 A d.betaHat F
    eta T x V k (shots S x) A F q d.radius Y (meanLog A F T x V k q d.radius Y) d.g i := by
  obtain ⟨M,hA⟩:=h.earns A F V hv
  obtain ⟨η,hη,hg⟩:=h.gaps A F V k hv
  dsimp only
  let I:=active d.betaHat A F (G:=G)
  have ht:=debt T x q d.radius h.aperture hA (k:=k) p.1 i
  have hh j := station T x q d.radius (k:=k) h.aperture hA hη hg p.1 j
  unfold shaft eta; rw [Pi.smul_apply,Pi.add_apply,smul_eq_mul,ht]; refine congr_arg₂ HMul.hMul rfl (congr_arg₂ HAdd.hAdd ?_ rfl)
  rw [beam_exact T k V d.betaHat A F h.aperture hA]
  let e := Completion.sorted A F (G:=G) («x»:=d.betaHat)
  let Q:=Rows.gram T x V k (shots S x) A F
  let U:=Completion.wide Q (1:Gaussian.Table (Completion.vacant A F x G))
  let Y:=iced p.1 A x F
  change ((U.submatrix e.symm e.symm)*ᵥ mist d F A k V p.1) (e (.inl i))=(Q*ᵥ meanLog A F T x V k q d.radius Y) i
  unfold mulVec dotProduct; rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply,U,Completion.wide,Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
    zero_mul,Finset.sum_const_zero,add_zero]
  apply Finset.sum_congr rfl; intro j _
  exact congr_arg₂ HMul.hMul rfl (hh j)

lemma clouded (b : Finset ℕ) (i : Active A x F) : smoky d i.val.val F A b k V p=
    let Y:=iced p.1 A x F; let z := (Print.see x A F p).2
    ∑ j:G.ColorIndex,(eta T x V k (shots S x) A F q d.radius Y (meanLog A F T x V k q d.radius Y) d.g (i,j))*z (i,j) := by
  dsimp only; unfold smoky
  rw [if_pos (show Physical.openBond A F x i.val.val from ⟨i,rfl⟩)]; refine Finset.sum_congr rfl fun j _ => ?_
  exact congr_arg₂ HMul.hMul (calibrated d h k V hv p (i,j)) rfl

lemma thin_paid (F' : Forest S.ratio) (i : Slots S) (b : Finset ℕ) :
    let u := Print.see d.betaHat A F' p
    ∑ j:G.ColorIndex,-(((direct T d.betaHat V k (shots S d.betaHat) A F' q d.radius u.1
      (meanLog A F' T d.betaHat V k q d.radius u.1)) (i,j))^2 /2)/d.g^2 =
      -(slip^2*debit d 0 i F' A b k V p)/d.g^2 := by
  obtain ⟨P,hP⟩:=h.valid.funds; obtain ⟨C,n,he,hl⟩:=hP.feeds
  intro y
  let a:=meanLog A F' T d.betaHat V k q d.radius y.1; let U := lands T d.betaHat V k (shots S d.betaHat) A F' q d.radius y.1 a
  let Z:= direct T d.betaHat V k (shots S d.betaHat) A F' q d.radius y.1 a; let D:= Rows.restrict x (shots S d.betaHat) A F' U i
  have hf := arrived T d.betaHat V k (shots S d.betaHat) A F' q d.radius y.1 he a
  have hg : ‖D‖^2 = ∑ j:G.ColorIndex, (Z (i,j))^2 := by
    have ht : D=tape Z i := (congr_fun hf i).symm
    rw [ht, EuclideanSpace.real_norm_sq_eq]; rfl
  rw [debits d h k V hv p 0 i b]
  change ∑ j, -((Z (i,j))^2/2)/_ = -(slip^2 * if keep .. then ‖lands _ _ _ _ _ _ _ _ _ _ _ i‖^2/2 else 0)/_
  rw [zero_smul,add_zero]

  calc
   _ = -((‖D‖^2 /2))/d.g^2 := by rw [hg, Finset.sum_div]; simp [Finset.sum_div, neg_div, Finset.sum_neg_distrib]
   _ = _ := ?_
  unfold D Rows.restrict; split <;> simp only [norm_smul,Real.norm_eq_abs,abs_of_pos slip_pos,norm_zero,zero_pow (show 2≠0 by omega), mul_zero, zero_div, U, a, y] <;> ring
end actual
end Voice
end YM.PhysicalNext.Dictionary
