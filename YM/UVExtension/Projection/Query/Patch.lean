import YM.UVExtension.Projection.Query.Drive
import YM.Work.F04
import YM.Work.F05

/-! Generic joint critical equation; Hessian + relative-chart controls. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Filter Function Finset ContinuousLinearMap MenuView Module Matrix
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {I X Y E : Type} (P : MenuView I)
  [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup E] [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ E] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] [FiniteDimensional ℝ E]

lemma upwards {f : I→ X→ Y →E} {a s} (h : Run P a (s+1) (fun i=> uncurry (f i)) 0) : Run P a s (fun i (z:X × Y)=> fderiv ℝ (f i z.1) z.2) 0:=by
  -- held-x partial via fixed right projection
  let L:=(ContinuousLinearMap.compL ℝ Y (X×Y) E).flip (ContinuousLinearMap.inr ℝ X Y)
  refine (h.diff.cash L).germ (fun i=>?_)
  filter_upwards [(h.born i).eventually (by simp)] with z hz
  let d:= fderiv ℝ (uncurry (f i)) z
  have hp : HasFDerivAt (fun t:Y=> (z.1,t)) (ContinuousLinearMap.inr ℝ X Y) z.2:= (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  have he : HasFDerivAt (uncurry (f i)) d (z.1,z.2):= (hz.differentiableAt (by simp)).hasFDerivAt
  have hh: HasFDerivAt (f i z.1) (d.comp (ContinuousLinearMap.inr ℝ X Y)) z.2:= he.comp _ hp
  exact hh.fderiv
abbrev Loan (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] := Y→L[ℝ] Y→L[ℝ] ℝ
def houses (p : Y→ℝ) := {x : Loan Y| (∀ i,p i≤ x i i) ∧ ∀ i j,x i j=x j i}
omit [FiniteDimensional ℝ Y] in
lemma houses_closed (p:Y→ℝ):IsClosed (houses p):=by
  unfold houses; rw [Set.setOf_and]; apply IsClosed.inter
  · simp_rw [Set.setOf_forall]; exact isClosed_iInter (fun _=> isClosed_le continuous_const ((continuous_id.clm_apply continuous_const).clm_apply continuous_const))
  simp_rw [Set.setOf_forall]; refine isClosed_iInter fun i=> isClosed_iInter fun j=> ?_; exact isClosed_eq ((continuous_id.clm_apply continuous_const).clm_apply continuous_const) ((continuous_id.clm_apply continuous_const).clm_apply continuous_const)
lemma houseInvert (p:Y→ℝ)(he : ∀ y,y≠0→0 < p y) {x:Loan Y} (h:x∈houses p): x.IsInvertible:=
    Work.F04.form_invertible x ((injective_iff_map_eq_zero _).mpr fun z hz=> Classical.byContradiction fun hx=>
      (show 0<x z z from (he z hx).trans_le (h.1 z)).ne (hz ▸ rfl))
variable {d k : ℕ} {f : I→ X→Y→ℝ} {p:Y→ℝ}
def garage (B: X→ Y→ℝ) (x : X×Y): Loan Y:= fderiv ℝ (fderiv ℝ (B x.1)) x.2
def garageGate (B:X→Y→ℝ) : X×Y→ (Y→L[ℝ] ℝ) := fun x=> fderiv ℝ (B x.1) x.2

theorem carried (h: Run P 0 2 (fun i=> uncurry (f i)) 0) (hv : ∀ i (x:Y),p x ≤ iteratedFDeriv ℝ 2 (f i 0) 0 ![x,x]) : P.sees 0 (fun i=> fderiv ℝ (garageGate (f i)) 0) ∧ ∀ i, cannon (garageGate (f i))=garage (f i) 0 ∧ garage (f i) 0∈houses p := by
  have hx:=upwards P h
  refine ⟨laminate P _ fun x=> ?_,fun i=> ⟨?_,?_⟩⟩
  · have he:=hx.tests 1 le_rfl (fun _=> x); change P.sees _ (fun t=> iteratedFDeriv ℝ 1 (garageGate (f t)) 0 (fun _=> x)) at he; simpa only [iteratedFDeriv_one_apply] using he
  · let B:= garageGate (f i)
    let L:= ContinuousLinearMap.inr ℝ X Y
    have he: HasFDerivAt B (fderiv ℝ B 0) (L 0):= (show ContDiffAt ℝ ω B 0 from hx.born i).differentiableAt (by simp) |>.hasFDerivAt
    exact ((he.comp (0:Y) L.hasFDerivAt : HasFDerivAt (fderiv ℝ (f i 0)) _ 0)).fderiv.symm
  constructor
  · intro x; have hy:=hv i x; rw [iteratedFDeriv_two_apply] at hy; exact hy
  let B:=uncurry (f i); let L:=ContinuousLinearMap.inr ℝ X Y
  have hh:ContDiffAt ℝ ω (f i 0) 0:= (show ContDiffAt ℝ ω B (L 0) from h.born i).comp _ (L.contDiff.contDiffAt : ContDiffAt ℝ ω L 0)
  exact fun i j=> hh.isSymmSndFDerivAt (by simp) _ _

theorem cabin {U:I→ X→Y} (h0: Run P 0 2 (fun i=> uncurry (f i)) 0) (h : Run P d (k+1) (fun i=> uncurry (f i)) 0) (hr: ∀ i, U i 0=0) (hs:∀ i,ContDiffAt ℝ ω (U i) 0) (he : ∀ i, ∀ᶠ x in 𝓝 0, HasFDerivAt (f i x) (0:Y→L[ℝ] ℝ) (U i x)) (hh : ∀ i (x:Y),p x≤ iteratedFDeriv ℝ 2 (f i 0) 0 ![x,x]) (hu : ∀ y,y≠0→0 < p y): Run P (mast d k) k U 0:=by
  obtain ⟨ha,H⟩:=carried P h0 hh
  refine producing P (upwards P h) hs hr (houses p) (houses_closed _) (fun i=> (H i).1.symm ▸ (H i).2) (fun _ hh=> houseInvert _ hu hh) ha (fun i=> (he i).mono fun t hh=> ?_); exact hh.fderiv
variable {α : Type} [Fintype α] [DecidableEq α]
def lane (B : Basis α ℝ Y) (Q : Loan Y):= Real.log (LinearMap.toMatrix₂ B B Q.toLinearMap₁₂).det
omit [FiniteDimensional ℝ Y] in
lemma lane_valid (B : Basis α ℝ Y) (hp : ∀ y,y≠0→0 < p y) (x : Loan Y) (he : x∈houses p): ContDiffAt ℝ ω (lane B) x:=by
  let l:= fun x : Loan Y=> LinearMap.toMatrix₂ B B x.toLinearMap₁₂
  have hm : (l x).PosDef:= by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j; change star (l x j i)=_; rw [star_trivial]; unfold l; simp only [LinearMap.toMatrix₂_apply]; exact he.2 _ _
    intro v hv; rw [star_trivial]
    have ht: B.equivFun.symm v ≠0:=fun h=> hv (B.equivFun.symm.injective (h.trans (map_zero _).symm))
    have hj : v ⬝ᵥ l x *ᵥ v=x (B.equivFun.symm v) (B.equivFun.symm v):= dotProduct_toMatrix₂_mulVec B B x.toLinearMap₁₂ v v
    rw [hj]; exact (hp _ ht).trans_le (he.1 _)
  have hh:ContDiff ℝ ω fun x=> (l x).det:=by
    have hz i j: ContDiff ℝ ω (fun x=> l x i j):=by
      unfold l; simp only [LinearMap.toMatrix₂_apply,ContinuousLinearMap.toLinearMap₁₂_apply]; exact (contDiff_id.clm_apply contDiff_const).clm_apply contDiff_const
    simp_rw [Matrix.det_apply]; exact ContDiff.sum (fun i _=> ContDiff.const_smul _ (contDiff_prod (fun j _=> hz _ _)))
  exact ContDiffAt.log hh.contDiffAt hm.det_pos.ne'

lemma anchored (B : Basis α ℝ Y) (hp : ∀ y,y≠0→0 < p y) (f:I→ Loan Y)(hv: P.sees 0 f)(he:∀ i,f i∈houses p): Run P 0 k (fun _=>lane B) f:=by
  refine ⟨fun i=> lane_valid B hp _ (he i),fun i hi v=> crossing (g:=fun t=> iteratedFDeriv ℝ i (lane B) t v) hv he (houses_closed _) (fun x h=> ?_)⟩
  have hx:=(lane_valid B hp x h).continuousAt_iteratedFDeriv (k:=i) le_top
  exact (continuous_eval_const v |>.continuousAt |>.comp hx).continuousWithinAt

theorem lagoon (h0:Run P 0 2 (fun i=> uncurry (f i)) 0) (h: Run P d (k+1+1) (fun i=> uncurry (f i)) 0) (hh : ∀ i (x:Y),p x ≤ iteratedFDeriv ℝ 2 (f i 0) 0 ![x,x]) (hu : ∀ y,y≠0→0 < p y)(B : Basis α ℝ Y) : Run P (k*d) k (fun i=> lane B ∘ garage (f i)) 0:=by
  obtain ⟨hp,hP⟩:= carried P h0 hh
  have hg : Run P 0 0 (fun i=> garage (f i)) 0 := upwards P (f:=fun i x=> fderiv ℝ (f i x)) (upwards P h0)
  have ht : Run P d k (fun i=> garage (f i)) 0 := upwards P (f:=fun i x=> fderiv ℝ (f i x)) (upwards P h)
  exact ht.comp (anchored P B hu _ (hg.tests 0 le_rfl (fun _=>0)) (fun i=> (hP i).2))
end YM.UVExtension.Projection
