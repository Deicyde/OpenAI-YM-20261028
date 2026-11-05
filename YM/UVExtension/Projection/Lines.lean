import YM.UVExtension.Projection.Fumes

/-! Fixed-volume base form convergence, actual columns in nonlinear stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Lattice RG Exterior Precision Wilson Tree Bloch Laurent Stationary Filter Function Finset MenuView Work.F02 Metric
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {I E: Type} {p : Clip} {u w σ A Λ : ℝ} {R : PathData G} {m : Side} (S : ℕ → Slot)(f : Face (Per m))

def sweep (x : Site m) (f : ℕ→ ℝ) (U:Config G m) := ∑' i,f i • (S i).atSite U x
lemma speedway (x : Site m) (f:ℕ→ℝ)(h : Summable fun i=> ‖f i‖ * Real.exp (σ*(S i).length)) (hb : 0<σ) (U : Config G m): Summable fun i=> f i • (S i).atSite U x :=
    Summable.of_norm_bounded (h.mul_right 2) fun i=> (norm_smul (f i) _).trans_le (mul_le_mul (le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (by positivity))) (Slot.eval_norm ..) (norm_nonneg _) (by positivity))
variable [NormedAddCommGroup E] [NormedSpace ℝ E] {J:E→ Config G m}
lemma echoes (x:Site m)(f : ℕ→ℝ)(h:Summable fun i=> ‖f i‖*Real.exp (σ*(S i).length)) (hb:0<σ) (ha : ∀ i,ContDiffAt ℝ ω (fun y=> G.mat (J y i)) 0): ContDiffAt ℝ ω (fun y=> sweep S x f (J y)) 0:=by
  let L := fun M:Ambient G m=> ∑' i,f i • slotExt (S i) x M
  have hs : AnalyticAt ℂ L (physical (J 0)) := by
    refine analytic_series (fun i M=> f i • slotExt (S i) x M) (radius_pos hb) (fun i=> ?_) (h.mul_right (slotConst G)) (fun i z hh=> ?_)
    · exact ((slotExt_contDiff (S i) x).const_smul (f i)).differentiable (by simp)
    rw [norm_smul]; exact (mul_le_mul_of_nonneg_left (slotExt_bound (J 0) hb z (ball_subset_closedBall hh) _ _) (norm_nonneg _)).trans_eq (by ring)
  have hv : ContDiffAt ℝ ω L (physical (J 0)):= hs.contDiffAt.restrict_scalars ℝ
  have hp y : colorUp G (sweep S x f (J y))= L (physical (J y)) := by
    unfold sweep L; rw [(colorUp G).map_tsum (speedway S x f h hb _)]; simp_rw [map_smul,slotExt_physical]
  have hh:ContDiffAt ℝ ω (fun y=> L (physical (J y))) 0:= hv.comp (f:=fun y=> physical (J y)) _ (physical_contDiffAt ha)
  apply ((colorReal G).contDiff.contDiffAt.comp _ hh).congr_of_eventuallyEq
  exact Eventually.of_forall fun y=> ((colorReal_up (sweep S x f (J y))).symm.trans (congr_arg (colorReal G) (hp y)))

def pathsHere (i : ℕ) := walkSlot (addresses i).1 (addresses i).2

def yard (σ : ℝ) (i : ℕ) := Real.exp (σ*(pathsHere i).length)
lemma yard_gain {σ : ℝ} (h : 0 < σ): Summable (yard (-σ)):=by
  let u (p:PlaqAxes×Cover):= Real.exp (-σ*((size p.2:ℝ)+4))
  have hu : yard (-σ)=u ∘ addresses := by ext1 i; unfold yard u; simp only [Function.comp_apply,pathsHere,walkSlot_cost]; push_cast; rfl
  rw [hu]; apply addresses.summable_iff.mpr; rw [summable_prod_of_nonneg (fun i=> (Real.exp_pos _).le)]
  refine ⟨fun i=>?_,Summable.of_finite⟩; simp_rw [mul_add,Real.exp_add]; exact ((Width.compactPay σ h).2.1).mul_right _

def via (σ:ℝ) (z : Ortho ℕ) i := yard (-σ) i*z i
lemma pilot (z: Ortho ℕ) (h:0 < σ): Summable fun i=> ‖via σ z i‖*yard (σ/2) i:=by
  refine ( (yard_gain (half_pos h)).mul_right ‖z‖ ).of_nonneg_of_le (fun i=> mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) fun i=> ?_
  unfold via yard; rw [norm_mul,mul_right_comm, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [← Real.exp_add,show _ + σ/2*↑(pathsHere i).length = -(σ/2)* (pathsHere i).length by ring]; gcongr; exact lp.norm_apply_le_norm (by norm_num) _ _
lemma lodes (x:Site m) (U:Config G m)(h:0<σ):RLinear fun z=> sweep pathsHere x (via σ z) U:= by
  apply tsum_strike (P:=fun i z=> via σ z i • (pathsHere i).atSite U x) (fun z=> speedway pathsHere _ _ (pilot z h) (half_pos h) U) fun i=> ?_
  obtain ⟨L,hL⟩:= (RLinear.mk (lp.evalCLM ℝ (fun _ : ℕ=>ℝ) 2 i)).mul (yard (-σ) i)
  exact ⟨L.smulRight ((pathsHere i).atSite U x),funext fun z=> congr_arg (fun t:ℝ=> t • _) (congr_fun hL z)⟩

lemma driver {g : ℕ→ℕ→ℝ}(h : ∀ n,SumBudget (fun i=> ‖g n i‖*yard σ i) A)(he:Arrives g):∃ x:ℕ→Ortho ℕ, g=via σ ∘ x ∧ ∃ z,HLimit x z:=by
  let f n i:= yard σ i * g n i
  have hp n i: ‖f n i‖=‖g n i‖*yard σ i:= by unfold f yard; rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,mul_comm]
  have hv n : Summable fun i=> ‖f n i‖:=by simp_rw [hp]; exact (h n).2.1
  have hA : 0≤ A:= (tsum_nonneg (h 0).1).trans (h 0).2.2
  have hu n : (∑' i,‖f n i‖) ≤ A:= by simp_rw [hp]; exact (h n).2.2
  have hy n i: ‖f n i‖^(2:ENNReal).toReal≤‖f n i‖*A:= by
    have he:=mul_le_mul_of_nonneg_left (((hv n).le_tsum i (fun i _=>norm_nonneg (f n i))).trans (hu n)) (norm_nonneg (f n i)); norm_num [sq]; simpa [← sq] using he
  have hK n:= ((hv n).mul_right A).of_nonneg_of_le (fun i=> Real.rpow_nonneg (norm_nonneg _) _) (hy n)
  let x (n) : Ortho ℕ:= ⟨(f n:PreLp (fun _ : ℕ=>ℝ)),memℓp_gen (hK n)⟩
  have hk n: ‖x n‖ ≤ A:= by
    refine lp.norm_le_of_tsum_le (by norm_num) hA (((hK n).tsum_le_tsum (hy n) ((hv n).mul_right A)).trans ?_)
    rw [tsum_mul_right]; norm_num [sq]; exact mul_le_mul_of_nonneg_right (hu n) hA
  refine ⟨x,funext (fun n=> funext fun i=> ?_),?_⟩
  · change g n i=yard (-σ) i*f n i; unfold f yard; rw [neg_mul,Real.exp_neg, inv_mul_cancel_left₀ (by positivity)]
  have hh : Bornology.IsBounded (Set.range x) := (Metric.isBounded_closedBall (x:=0) (r:=A)).subset (Set.range_subset_iff.mpr fun i=> mem_closedBall.mpr ((dist_zero_right _).trans_le (hk i)))
  obtain ⟨z,hz⟩:= Arrives.columns (f:=f) fun i=> by
    obtain ⟨a,H⟩:=he; exact ⟨_,(tendsto_pi_nhds.mp H i).const_mul (yard σ i)⟩
  exact ⟨⟨(z:PreLp (fun _ : ℕ=>ℝ)),lp.memℓp_of_tendsto hh hz⟩,⟨A,Eventually.of_forall hk⟩,tendsto_pi_nhds.mp hz⟩

lemma onRows {T : ℕ→PathData G} {k : ℕ} (h: 0 < σ)(he:∀ t,(T t).Bounds p σ A Λ)(hf:∀ t i, ((T t).row f.2 i).2=pathsHere i)(hg: Arrives fun i j=> ((T i).row f.2 j).1) (ha : ∀ i, ContDiffAt ℝ ω (fun y => G.mat (J y i)) 0): Run limitView 0 k (fun i y=> (T i).ell (J y) f) 0:=by
  obtain ⟨x,hx,z,hz⟩:= driver (A:=A) (σ:=σ) (fun i=> (show SumBudget _ _ from by
    have hv := (he i).rows f.2; simp_rw [hf] at hv; exact hv)) hg
  · let F z y:= sweep pathsHere f.1 (via σ z) (J y)
    have hF z: ContDiffAt ℝ ω (F z) 0:= echoes _ _ _ (pilot z h) (half_pos h) ha
    have hp t: (fun y=> (T t).ell (J y) f)=F (x t):=by
      funext y; unfold F PathData.ell sweep PathData.ellTerms; apply tsum_congr; intro i; rw [hf,show ((T t).row f.2 i).1=via σ (x t) i from congr_fun (congr_fun hx t) i]
    refine ⟨fun i=> ell_contDiffAt (he i) f ha,fun i _ p=> travels.mpr ?_⟩
    change Arrives fun j=> iteratedFDeriv ℝ i (fun y=> (T j).ell (J y) f) 0 p; simp_rw [hp]
    exact ⟨_,hz.bids (RLinear.charge (F:=F) (fun _=> (hF _).analyticAt) (fun x=> lodes _ (J x) h) i p)⟩

lemma parade [FiniteDimensional ℝ E]{Q: MenuView I}{k d : ℕ}{α : Type*}(f : I→ α→ E → G.Color) (s:Finset α)(h : ∀ i∈s, Run Q d k (fun n=> f n i) 0): Run Q d k (fun p i=> ∑ j∈s,f p j i) 0:=by
  induction s using Finset.induction with
  | empty=> simp only [sum_empty]; exact Run.fix _ _ k d contDiffAt_const
  | insert i s hi ih=>simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).sum (ih fun i H=> h i (mem_insert_of_mem H))

private lemma parish [FiniteDimensional ℝ E]{Q: MenuView I}{k d : ℕ}{α : Type*}(f : I→ α→ E → ℝ) (s:Finset α)(h : ∀ i∈s, Run Q d k (fun n=> f n i) 0): Run Q d k (fun p i=> ∑ j∈s,f p j i) 0:=by
  induction s using Finset.induction with
  | empty=> simp only [sum_empty]; exact Run.fix _ _ k d contDiffAt_const
  | insert i s hi ih=>simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).sum (ih fun i H=> h i (mem_insert_of_mem H))
lemma before_copy (T: PathData G) (b: Face (Per m)): T.ell (1:Config G m) b=0:= by
  unfold PathData.ell; simp_rw [PathData.ellTerms,Slot.atSite,Slot.eval,show ∀ x:Site m, expandAt x (1:Config G m)=1 from fun _=> rfl]; simp [faceValue,Lattice.travel,square,Step.read]
lemma insideLine (k : ℕ) {B : ℕ→ Bed} {T : ℕ→ PathData G} (q:Clip) (h:∀ i,(T i).Bounds q σ A Λ)(hr:∀ i,(T i).row=rowPath (B i))(hp:Arrives (fun i=>(B i).roots)) : Run limitView 0 k (fun i=>inputSeries q (T i) (m:=m)) 0:=by
  let F i (s:Signed) (x:Link G m):= quadratic q (T i) (pull s 0 (input G m x))
  suffices he: ∀ v, Run limitView 0 k (fun i=> F i v) 0 from
    (parish F univ (fun s _=> he s)).cash ((Fintype.card Signed:ℝ)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  intro v; let g:= fun x:Link G m=> pull v 0 (input G m x); let a:= q.direct
  have hg : g 0=1:=by unfold g; rw [flip_links]; change input G m (orderTurn v 0)=_; rw [map_zero,input_zero]
  have hu (i): ContDiffAt ℝ ω (fun y=> G.mat (g y i)) 0:=by
    unfold g; simp_rw [flip_links]; exact (Work.F03.represent_smooth i).contDiffAt.comp 0 ((arm G m 1).contDiff.contDiffAt.comp (f:=⇑(orderTurn v)) 0 (orderTurn _).contDiff.contDiffAt)
  unfold F quadratic; refine parish _ _ (fun j _=>?_)
  let z i (y:Link G m):= (T i).ell (g y) j
  let l x:= a*G.price (faceValue (g x) j)
  have hL: ContDiffAt ℝ ω l 0:= by
    refine ContDiffAt.mul contDiffAt_const (Work.F03.price_smooth ?_); simp_rw [faceValue,← stringMat_physical]; exact ((stringMat_contDiff (G:=G) _ _).restrict_scalars ℝ).contDiffAt.comp (0:Link G m) (physical_contDiffAt hu)
  have he:Run limitView 0 k z 0:= onRows j ((h 0).width) h (fun i t=>by rw [hr]; rfl) (Arrives.columns fun r=>by
    obtain ⟨y,hy⟩:=hp; simp_rw [hr]; exact ⟨_,tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hy _) _) _⟩) hu
  have hv: Run limitView 0 k (fun i x=> ‖z i x‖^2/2) 0:= by
    let V:=fun x:G.Color => ‖x‖^2/2
    have hm:Run limitView 0 k (fun _=> V) (fun i=> z i 0):=by
      unfold z; simp_rw [hg,before_copy]; exact Run.fix _ _ _ _ ((contDiff_norm_sq ℝ).contDiffAt.div_const 2)
    have hp:=he.comp (G:=fun _=> V) hm; rw [mul_zero] at hp; exact hp
  exact (Run.fix l _ _ _ hL).sum hv
end YM.UVExtension.Projection
