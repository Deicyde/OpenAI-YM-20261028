import YM.UVExtension.Projection.Query.Patch
import YM.UVExtension.Projection.Stage

/-! Actual leading and thermal scalar jets, at arbitrary fixed slices. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Lattice RG Exterior Precision Wilson Tree Bloch Laurent Stationary Filter Function Finset MenuView
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (t : S.Choices) {I:Type} [Nonempty I] (P : MenuView I) {p : Clip} (R : I → PathData G) (ρ : I → Bid.Dir G c → AxisChart G F)
variable {d k : ℕ} {σ C Λ η : ℝ}
structure SourceBasis {I:Type}(P : MenuView I)(R : I→ PathData G)(p : Clip)(f:Side)(n:ℕ): Prop where
    column : Run P 0 n (fun i=>inputSeries p (R i) (m:=f)) 0
    orbit : Run P 1 n (fun i=>turnSeries (R i).cubic (m:=f)+turnSeries (R i).quartic (m:=f)) 0
    thermal : Run P 1 n (fun i=>turnSeries (R i).loop (m:=f)) 0
lemma up_turn (h : SourceBasis P R p f k) : Run P 1 k (fun i=> intended p (R i) (m:=f)) 0:=by
  suffices he : _=fun i=> inputSeries p (R i) (m:=f)+(turnSeries (R i).cubic+turnSeries (R i).quartic) from
    Eq.mpr (congr_arg (fun F => Run P 1 k F 0) he) ((h.column.more (by decide) le_rfl).sum h.orbit)
  ext i z; rw [intent,add_assoc]
lemma low_turn (h : SourceBasis P R p f k) (he : 2 ≤ k) (hh : ∀ i,(R i).Bounds p σ C Λ): Run P 0 2 (fun i=> intended p (R i) (m:=f)) 0:= by
  refine ⟨(up_turn P R h).born,fun i hi v=>?_⟩; have hT j : Rays 3 (intended p (R j) (m:=f)-inputSeries p (R j)):= by
    rw [intent,add_assoc,add_sub_cancel_left]; exact (turns_low _ (hh j).width (hh j).three).add ((turns_low _ (hh j).width (hh j).four).weaker (by decide))
  have hx j: iteratedFDeriv ℝ i (intended p (R j) (m:=f)) 0=iteratedFDeriv ℝ i (inputSeries p (R j)) 0:= by
    have hg: ContDiffAt ℝ ω (intended p (R j) (m:=f)) 0:= (up_turn P R h).born j
    have ha:ContDiffAt ℝ ω (inputSeries p (R j) (m:=f)) 0:= h.column.born j
    have hp:= (rays_jet (hg.sub ha).analyticAt _).1 (hT j) i (by omega)
    change iteratedFDeriv ℝ i (intended p (R j) (m:=f)-inputSeries p (R j)) 0=0 at hp
    rw [iteratedFDeriv_sub_apply (hg.of_le le_top) (ha.of_le le_top)] at hp; exact sub_eq_zero.mp hp
  change P.sees 0 (fun j=> iteratedFDeriv ℝ i (intended p (R j) (m:=f)) 0 v); simp_rw [hx]; exact h.column.tests i (hi.trans he) v
abbrev Mount (G : Gauge)(F : Forest S.ratio):=Bid.Dir G c×AxisChart G F

def ascend (z : Mount G F): Link G f:= (arm G f 1).symm (Work.F03.axisLog F z)
lemma hilltop : ascend F (0:Mount G F)=0:=by
  unfold ascend; have he: Work.F03.axisLog F (0:Mount G F)=0:= congr_arg Prod.snd (Work.F03.inclusion_zero F); rw [he,map_zero]
lemma mount_an : ContDiffAt ℝ ω (ascend (G:=G) F) 0:= (arm G f 1).symm.contDiff.contDiffAt.comp _ (Work.F03.inclusion_smooth F).snd
lemma mount_boot : (fun z: Mount G F=> Work.F03.live F z)=ᶠ[𝓝 0] (fun z=> input G f (ascend F z)):= by
  simp_rw [ascend,input,(arm G f 1).apply_symm_apply]; exact (Work.F03.inclusion_works F).symm
lemma launched {d} {f₀ : I → Link G f →ℝ} (h : Run P d k f₀ 0) : Run P d k (fun i=> f₀ i ∘ ascend F) 0:= by
  have ht:=Run.fix (P:=P) _ _ k 0 (mount_an (G:=G) F); have hh:=ht.comp (G:=f₀) (by simpa only [hilltop,Pi.zero_def] using h)
  rw [mul_zero,zero_add] at hh; exact hh
lemma shadow (he : ∀ i,Critical F p (R i) (ρ i)) (h : Run P d k (fun i=>intended p (R i) (m:=f)) 0):Run P d k (fun i=> uncurry (tested F t p (R i))) 0:= by
  let W := fun z: Mount G F=> noiseTaylor S (represent z.1) (Work.F03.live F z) t
  let Q i:= intended p (R i) (m:=f) ∘ ascend F
  have hp: Run P d k Q 0:= launched F P h
  have hF i: uncurry (tested F t p (R i)) =ᶠ[𝓝 0] Q i+W := by
    filter_upwards [mount_boot (G:=G) F] with z hz
    change mainTerm p (R i) (Work.F03.live F z)+ W z=mainTerm _ _ _+ W z; rw [hz]
  let i:= Classical.arbitrary I
  have hh:ContDiffAt ℝ ω (Q i+W) 0:= ((he i).2.2 t).1.congr_of_eventuallyEq (hF _).symm
  have hx: ContDiffAt ℝ ω W 0:= by
    have ht:=hh.sub (show ContDiffAt ℝ ω (Q i) 0 from hp.born i); change ContDiffAt ℝ ω (Q i+W-Q i) 0 at ht; rwa [add_sub_cancel_left] at ht
  exact (hp.sum (Run.fix W _ k d hx)).germ hF

def dimPulse := mast 1 4
def wavePulse:= 4*dimPulse+4 -- bound fine irrespective of all men
lemma interview (A : SourceBasis P R p f 5) (hb : ∀ i,(R i).Bounds p σ C Λ) (h : ∀ i,Critical F p (R i) (ρ i)) (ht : ∀ i, PriceGap F p (R i) η) (hp : 0 < η) (Z : ChartRatio G)(he:LocalRatio Z): Run P dimPulse 4 ρ 0 ∧ Run P wavePulse 4 (fun i x=> tested F t p (R i) x (ρ i x)) 0 ∧ Run P wavePulse 2 (fun i=> thermal F t p (R i) (ρ i) Z) 0:=by
  let E:=fun i=>tested F t p (R i)
  let r:=(AxisChart G F); let R' := fun x : r=> η*∑ i:F.Free, ‖x i‖^2
  have hz:= shadow F t P R ρ h (up_turn P R A); have hh:= shadow F t P R ρ h (low_turn P R A (by decide) hb)
  have hr i (x:AxisChart G F): R' x≤ iteratedFDeriv ℝ 2 (E i 0) 0 ![x,x]:= ht i t x; have hE (x:AxisChart G F)(h:x≠0): 0 < R' x:= by
    obtain ⟨u,hu⟩ : ∃ i, x i≠0:= by simpa only [Ne,funext_iff,Pi.zero_apply,not_forall] using h
    exact mul_pos hp (sum_pos' (fun i _=> by positivity) ⟨u,mem_univ u,pow_pos (norm_pos_iff.mpr hu) _⟩)
  have hc:=cabin P hh hz (fun i=> (h i).1) (fun i=> (h i).2.1) (fun i=> ((h i).2.2 t).2) hr hE
  let b i (x:Bid.Dir G c): Mount G F:= (x,ρ i x)
  have hB: Run P dimPulse 4 b 0:= (Run.fix _ _ _ _ contDiffAt_id).party hc
  have h0 i : b i 0=0 := by unfold b; rw [(h i).1]; rfl
  have hu: Run P (4*dimPulse+1) 4 (fun i=> (uncurry (E i))∘ b i) 0:= hB.comp (by simp_rw [show ∀ i, b i ((0:I→ Bid.Dir G c) i)=_ from fun i=> h0 i]; exact hz.more le_rfl (by omega))
  refine ⟨hc,hu.more (by unfold wavePulse; omega) le_rfl,?_⟩
  let M:=fun i x=> Precision.loop (R i) (Work.F03.live F x)
  have hm : Run P 1 2 M 0 := by
    refine (launched F P (A.thermal.more le_rfl (by omega))).germ fun i=> ?_
    filter_upwards [mount_boot (G:=G) F] with x hh; unfold M; rw [hh]; rfl
  let J:= fun i=> lane (Work.F05.countingBasis F G) ∘ garage (E i)
  have hj : Run P 2 2 J 0:= lagoon P hh (hz.more le_rfl (by decide : 4 ≤ 5)) hr hE _
  let V:=fun x:Mount G F=> Real.log (∏ i:F.Free,Z.J (x.2 i))
  let Y:= ContinuousLinearMap.id ℝ ℝ
  have hv: Run P 2 2 (fun _=> V) 0:= by
    refine Run.fix V _ _ _ (ContDiffAt.log ?_ ?_)
    · refine contDiffAt_prod fun i _=> ?_
      have hf:= he.germ 0 (Metric.mem_ball_self he.patch)
      exact hf.comp (f:=fun x:Mount G F=> x.2 i) (0:Mount G F) ((contDiffAt_apply ℝ G.Color i (0:AxisChart G F)).comp (f:=Prod.snd) (0:Mount G F) contDiffAt_snd)
    simp [he.anchored]
  let X:= fun t=> M t+(1/2:ℝ) • J t-V
  have hX : Run P 2 2 X 0:= ((hm.more (by decide) le_rfl).sum (hj.cash ((1/2:ℝ) • Y))).sum (hv.cash (-Y)) -- defeq?
  have hh : Run P (2*dimPulse+2) 2 (fun i=> X i∘ b i) 0 := (hB.more le_rfl (by decide)).comp (G:=X) (by simp_rw [show ∀ i, b i ((0:I→ Bid.Dir G c) i)=_ from fun i=> h0 i]; exact hX)
  refine (hh.more (by unfold wavePulse; omega) le_rfl).germ (fun i=> Eventually.of_forall fun x=> ?_)
  simp only [thermal,Work.F05.hessian_eq]; rfl
end YM.UVExtension.Projection
