import YM.RG08.Arc.Treble

/-! # As a function of extended chart with one pulse coordinate
Public vacuum kernel, log reps, amount scale subtracted. Along hold it gives the
actual exponential-branch germ with the Haar ratio amplitude. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f m : Side} (S : StepData c f) (G : Gauge) (T : Forest S.ratio)
variable (U : Matrix (Body 1 f) (Body 1 c) ℝ) (v : ℝ→ Link G c)
local notation "A" => FreeResolvent.Active G T →ℝ
local notation "J" => Alley G S.ratio
local notation "L" => T.Free → G.Color
local notation "Z" => (T.Free → G.Color) × ℝ

def tuneMean (t : ℝ) := (sprig S T G)ᵀ*ᵥ (riseM S G T U*ᵥ v t)
def shifting (t : ℝ) := t • (maplit G T (tuneMean S G T U v t))
@[simp] lemma shift_zero : shifting S G T U v 0= 0 := by unfold shifting; rw [zero_smul]
lemma living_mean (h : ContDiffAt ℝ ω v 0) : ContDiffAt ℝ ω (shifting S G T U v) 0 := by
  unfold shifting tuneMean; refine contDiffAt_id.smul ?_
  refine (ContDiffAt.comp (g:=(maplit G T)) _ (maplit G T|>.contDiff|>.contDiffAt) ?_)
  exact (sprig S T G)ᵀ.mulVecLin.toContinuousLinearMap.contDiff.contDiffAt.comp _ ((riseM S G T U).mulVecLin.toContinuousLinearMap.contDiff.contDiffAt.comp _ h)
lemma living_m (hp : Measurable v) : Measurable (shifting S G T U v) := by
  unfold shifting tuneMean; refine measurable_id.smul ((maplit G T).continuous.measurable.comp ?_)
  exact (sprig S T G)ᵀ.mulVecLin.toContinuousLinearMap.continuous.measurable.comp ((riseM S G T U).mulVecLin.toContinuousLinearMap.continuous.measurable.comp hp)

lemma lodge_l : (fun x : Link G f× Link G c=> lodgeP G S.ratio x.1 x.2)= (⇑(LinearMap.toContinuousLinearMap (𝕜:=ℝ) {
  toFun:= fun x : Link G f × Link G c=> lodgeP G S.ratio x.1 x.2
  map_add' := fun x y=> by funext p; unfold lodgeP; rcases p with ⟨k,i|j⟩ <;> rfl
  map_smul' := fun t x=> by funext p; unfold lodgeP; rcases p with ⟨k,i|j⟩ <;> rfl })) := rfl -- maybe concise different def instead.

def heated (t : ℝ) (x : A) := settler (chargeS S T G) (lodgeP G S.ratio (riseM S G T U*ᵥ v t) (v t)) x
lemma heat_pose (t) (x : A) : heated S G T U v t x=lodgeP G S.ratio ((riseM S G T U *ᵥ v t)+(sprig S T G*ᵥ x)) (v t) := by
  rw [heated,settler, mat_basis S T x]; funext i; rcases i with ⟨i,j|j⟩
  · exact add_comm ..
  exact zero_add ..
lemma heat_lamp (h : ContDiffAt ℝ ω v 0) (x : A) : ContDiffAt ℝ ω (fun t=> heated S G T U v t x) 0 := by
  let P := fun z:Link G f×Link G c=> lodgeP G S.ratio z.1 z.2
  have hp : ContDiff ℝ ω P := by unfold P; rw [lodge_l]; exact ContinuousLinearMap.contDiff _
  simp_rw [heat_pose]; exact hp.contDiffAt.comp _ ((((riseM S G T U).mulVecLin.toContinuousLinearMap.contDiff.contDiffAt.comp _ h).add contDiffAt_const).prodMk h)
lemma heat_eval (x : A) (t : ℝ) : fineL G S.ratio (heated S G T U v t x)=sprig S T G*ᵥ (x+tuneMean S G T U v t) ∧ coarseL G S.ratio (heated S G T U v t x)=v t := by
  rw [heat_pose,lodge_f,lodge_c]; refine ⟨?_,rfl⟩; rw [mulVec_add,add_comm]; congr 1
  exact Eq.symm (projects T _ (vanishes_mean S T U (v t)))

def chic (p : Z) : J := lodgeP G S.ratio (sprig S T G*ᵥ ((maplit G T).symm (p.1+shifting S G T U v p.2))) (p.2 • v p.2)
@[simp] lemma chic_zero : chic S G T U v 0=0 := by
  unfold chic; change lodgeP G S.ratio (_*ᵥ ((maplit G T).symm (0+shifting S G T U v 0))) (0 • v 0) = _
  rw [shift_zero,zero_add, zero_smul,map_zero,Matrix.mulVec_zero]; let D :=  fun z : Link G f × Link G c=> lodgeP G S.ratio z.1 z.2
  change D 0=_; funext i; rcases i with ⟨k,i|j⟩ <;> rfl
lemma chic_fit (h : ContDiffAt ℝ ω v 0) : ContDiffAt ℝ ω (chic S G T U v) 0 := by
  have hp : ContDiffAt ℝ ω (fun x: Z=> (maplit G T).symm (x.1 + shifting S G T U v x.2)) 0 := (maplit G T).symm.contDiff.contDiffAt.comp _ (contDiffAt_fst.add ((living_mean S G T U v h).comp (f:=Prod.snd) (0:Z) contDiffAt_snd))
  have hx := (sprig S T G).mulVecLin.toContinuousLinearMap.contDiff.contDiffAt.comp _ hp; have hv : ContDiffAt ℝ ω (fun x:Z=> x.2 • v x.2) 0 := contDiffAt_snd.smul (h.comp (f:=Prod.snd) (0:Z) contDiffAt_snd)
  let P := fun z:Link G f×Link G c=> lodgeP G S.ratio z.1 z.2
  have hF : ContDiff ℝ ω P := by unfold P; rw [lodge_l]; exact ContinuousLinearMap.contDiff _
  exact hF.contDiffAt.comp _ (hx.prodMk hv)
lemma chic_meas (hp : Measurable v) : Measurable (chic S G T U v) := by
  let P := fun z:Link G f×Link G c=> lodgeP G S.ratio z.1 z.2
  have hF : ContDiff ℝ ω P := by unfold P; rw [lodge_l]; exact ContinuousLinearMap.contDiff _
  have hx : Measurable (fun x:Z=> x.2 • v x.2) := measurable_snd.smul (hp.comp measurable_snd)
  exact hF.continuous.measurable.comp (((sprig S T G).mulVecLin.toContinuousLinearMap.continuous.measurable.comp ((maplit G T).symm.continuous.measurable.comp (measurable_fst.add ((living_m S G T U v hp).comp measurable_snd)))).prodMk hx)
lemma chic_ray (t : ℝ)(x : A) :
    chic S G T U v (t • plates G _ (maplit G T x))= t • heated S G T U v t x := by
  rw [← lodge_undo G S.ratio (t•heated S G T U v t x)]
  unfold chic
  simp only [show (t • plates G T.Free ((maplit G T) x)).2=t from mul_one t]; rw [map_smul (fineL G _),map_smul (coarseL G _), (heat_eval S G T U v x t).1,(heat_eval S G T U v x t).2, ← Matrix.mulVec_smul]; congr 2 -- solve
  simp [shifting,plates,smul_add]
section l
local notation "P" => chic S G T U v
variable (κ : S.Choices) (n : ℕ) (V : ℕ → Config G f → ℝ) (F : Air G) (K M : FreeResolvent.FaceRow) (i : G.ColorIndex)
local notation "Q" => YM.RG08.quad G (YM.RG08.hessian M)
-- day analytic/disc interpolation. public Hess convention

def regal (R' : Pot G 2) (p : Z) := laboratory S κ n V p.2 (input G c (coarseL G S.ratio (P p))) (input G f (fineL G S.ratio (P p))) + p.2^2 * (1- stanza R' c (v p.2))
include i in
lemma regal_fit (R' : Pot G 2) (h : ContDiffAt ℝ ω v 0) (hp : S.patch.Branches S.kernel G) (he : ∀ i,Caper (quad G (YM.RG08.hessian K)) F n i (V i)) : ContDiffAt ℝ ω (regal S G T U v κ n V R') 0 := by
  unfold regal; refine ContDiffAt.add ?_ ((contDiffAt_snd.pow _).mul (contDiffAt_const.sub ((stanza_smooth R' c).contDiffAt.comp (0:Z) (h.comp (f:=Prod.snd) (0:Z) contDiffAt_snd)))) -- arguments fix
  have hx:= chic_fit S G T U v h; let p := P; have hl : ContDiffAt ℝ ω (noiseLaw S κ (G:=G)) (p 0) := by unfold p; rw [chic_zero]; exact (blot_true S κ i hp 2).1.contDiffAt
  refine ContDiffAt.add (hl.comp _ hx) ?_
  refine ContDiffAt.sum (f:=fun i (x:Z)=> x.2^(2*i)* V i (input G f (fineL G S.ratio (p x)))) (fun j _=> (contDiffAt_snd.pow (2*j)).mul ?_)
  have hg : ContDiffAt ℝ ω (V j ∘ input G f) (fineL G S.ratio (p 0)) := by unfold p; rw [chic_zero,map_zero]; exact (he j).word.analytic.contDiffAt
  exact hg.comp (f:=fun x=>fineL G S.ratio (p x)) (0:Z) ((fineL G S.ratio).contDiff.contDiffAt.comp (0:Z) hx)
lemma regal_meas (R' : Pot G 2) (h : Measurable v) (hp : S.patch.Branches S.kernel G) (he : ∀ i,Measurable (V i)) : Measurable (regal S G T U v κ n V R') := by
  have hx : Measurable fun x: Z=> laboratory S κ n V x.2 (input G c (coarseL G S.ratio (P x))) (input G f (fineL G S.ratio (P x))) := labs_meas S he κ hp (Z) (input_cont.measurable.comp ((coarseL G S.ratio).continuous.measurable.comp (chic_meas S G T U v h))) (input_cont.measurable.comp ((fineL G S.ratio).continuous.measurable.comp (chic_meas S G T U v h))) measurable_snd n
  unfold regal; exact hx.add ((measurable_snd.pow_const _).mul (measurable_const.sub ((stanza_smooth R' c).continuous.measurable.comp (h.comp measurable_snd))))
end l
end YM.RG08.Reflect
