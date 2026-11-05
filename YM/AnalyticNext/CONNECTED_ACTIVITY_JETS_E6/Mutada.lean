import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Castro
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Harmonic

/-!
# Flat sampling points may exit the manifest even on no-hole chart

Persist principal-window inverse jet fees when restricting to post-L chart
 of V log summer. Cannot demand Healthy when transferring these budgets!
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush Foramen Frond Gate   Tablet
variable {v z r Q s y η γ : ℝ} {j m : ℕ} {U : E → Config G c} {x : E}

def dry (X : Coat T F) (b : ZipP G c f) := vary X.blank (increment 1 b.1)

private lemma nearby {ι : Type} [Fintype ι] {a : ι→Site c} {p : E→Matrix ι ι ℝ}
    (h : Census m a) (M : ℕ) (hM : ∀ x, Thin a a (p x) M) (hx : ∀ x:E,x∈Metric.closedBall 0 v → Tablet j γ Q y p a a x)
    (hp : 1 ≤ j) (x:E) (hv : ‖x‖≤v) :
    Price a a (p x-p 0) (0:ℝ) ((ballCost M:ℕ)*m* (Q*y*v)) := by
  let s:= Metric.closedBall (0:E) v
  let H:= p x-p 0; have he : 0≤v := (norm_nonneg _).trans hv
  have h0 : (0:E)∈s:= Metric.mem_closedBall_self he
  have hu (i k) z (h:z∈s) := (hx _ h).singular i k
  have hz (i k) : |H i k| ≤ Q*y*v := by
    unfold H; rw [Matrix.sub_apply]
    let g x:= p x i k
    have he' (x:E) (hx:x∈s) := (hu i k x hx).smaller hp
    have hf x (hx : x∈s) : DifferentiableAt ℝ g x := (he' _ hx).smooth.differentiableAt (by simp)
    have hh x (hx : x∈s): ‖fderiv ℝ g x‖ ≤ Q*y := by simpa only [normJ,pow_one,g,norm_iteratedFDeriv_one] using! (hu i k x hx).order _ hp
    have hr := Convex.norm_image_sub_le_of_norm_fderiv_le hf hh (convex_closedBall _ _) h0 (mem_closedBall_zero_iff.mpr hv)
    rw [sub_zero] at hr; exact hr.trans (mul_le_mul_of_nonneg_left hv (mul_nonneg (he' 0 h0).nonneg (he' 0 h0).pos))
  let C:= Q*y*v
  have hk : 0 ≤ C:= mul_nonneg (mul_nonneg (hx 0 h0).basis (hx 0 h0).pos) he
  have h' i j (h : M<separation (a i) (a j)) : (p x-p 0) i j =0 := by rw [Matrix.sub_apply,hM x _ _ h,hM 0 _ _ h,sub_zero]
  have hh (A : Matrix ι ι ℝ) (hu : Thin a a A M) (p : ∀ i j,|A i j| ≤ C) : Rows a a A (0:ℝ) ((ballCost M:ℝ)*m*C) := by
    intro i; simp_rw [wt,zero_mul,Real.exp_zero,one_mul]
    rw [← Finset.sum_subset (Finset.subset_univ (withinH a (a i) M)) (fun j _ hj => ?_)]; swap
    · exact abs_eq_zero.mpr (hu i j (lt_of_not_ge fun hp=>hj ((joins ..).2 hp)))
    apply (sum_le_sum (fun j (_:j∈_)=> p i j)).trans
    rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast count_near h (a i) M) hk
  exact ⟨hh H h' hz, hh H.transpose (Thin.transpose h') fun i j=> hz j i⟩

omit x in
lemma quenched (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (k : ℕ) (hk : 1≤k) {p : ℝ→ℝ}
    (hv : Rate G L (-(1/2)) p) (hh : ∀ᶠ x in atTop,0≤p x) (η r Q : ℝ) (h : Torch η r Q) :
    ∃ X e q y : ℝ, ∃ V : ℝ → ℝ, 0<X ∧ 0<e ∧ 0< q ∧ 0 ≤ y ∧ Rate G L 0 V ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L x S T →
      ∀ (F : Forest S.ratio) (Y : Coat T F), Y.x=x → Allow Y.blank.plate (along S) (tubularPrice G L) η r Q →
      ∀ u : ZipP G c f, ‖u‖≤ p x → let A z:= (dry Y z).plate
      Allow (A u) (along S) (tubularPrice G L) e q X ∧
        Tablet k e X (V x) A (along S) (along S) u ∧ Tablet k e y (V x) (fun u=> (dry Y u).form) (aim S) (along S) u := by
  obtain ⟨R,v,hr,hhR,hz,H⟩:= dressed P D hD k
  obtain ⟨C,hC,hK⟩:= bounded_stencils P D hD
  let e:= P.top.width/2; have he : 0<e := half_pos P.top.width_pos
  let y := carat D P L e C
  let X:= y*y+1; let t x:= kernelGrowth (radiusB x) G v; let q x:= t x+t x
  have ht: Rate G L 0 t:=jet_growth G L (Rate.const _)
  let u := tubularPrice G L
  have hs:= width_rate G L 1 0; simp only [add_zero,one_mul] at hs
  have hc : Rate G L (-(1/2)) (fun x=> (Animals.ballCost (radiusB x):ℕ)* (u:ℝ)*(X*q x*p x)) := by
    convert (hs.mul_right (u:ℝ)).mul (((ht.add ht).mul_left X).mul hv) using 1; ring
  have hm:= h.spans
  refine ⟨X,e,r/2,y,q,(by have hv:= mul_self_nonneg y; unfold X; positivity),he,half_pos hm,le_max_left ..,ht.add ht,?_⟩
  filter_upwards [hv.below (by norm_num) R hr,room G P L,hh,hc.below (by norm_num) (r/2) (half_pos hm)]
    with x hp hx hh ht c f S T hd hw F Y hY hF z hz A
  subst x; have hg:=hK _ _ S T hd hw.funds
  let d:= Y.x; let B:=Y.B
  have hv v' : Thin (along S) (along S) (A v') B := fun i j h=>(dry Y v').span (hx c f S T hw) i j (by change B/2<_; omega)
  let U (x: ZipP G c f):= increment 1 x.1
  have he' : e<P.top.width:= by unfold e; linarith [P.top.width_pos]
  have ho v (hi : v∈Metric.closedBall 0 (p d)) := (H _ _ S T hw.funds hd v
    ((mem_closedBall_zero_iff.mp hi).trans ((le_abs_self _).trans hp)) Y.k).1
  have hj (v) (hi : v∈Metric.closedBall (0:ZipP G c f) (p d)) : Tablet k e X (q d) A (along S) (along S) v :=
    Gate.plates Y.blank D hd hw.length_eq (hx c f S T hw) (ho _ hi) C hC hg he.le he'
  have hp := hj z (mem_closedBall_zero_iff.mpr hz)
  have hb:= Gate.replicaM Y.blank D hd hw.length_eq (hx c f S T hw) (ho z (mem_closedBall_zero_iff.mpr hz)) C hC hg he.le he'
  have hd : A 0=Y.blank.plate := by
    unfold A dry; rw [Prod.fst_zero, Work.G07.at_zero_increment]; rfl
  refine ⟨⟨hF.census,(dry Y z).balanced, he, half_pos hm,?_,?_,?_⟩,hp,hb.tilt le_rfl
    (le_add_of_nonneg_right hb.pos) hp.scale le_rfl⟩
  · exact add_pos_of_nonneg_of_pos (mul_self_nonneg _) zero_lt_one
  · obtain ⟨W,H,hK⟩:= hp.shape
    intro i; apply le_trans _ (hK.1 i)
    exact sum_le_sum fun j _=> mul_le_mul_of_nonneg_left ((H i j).bound.trans (le_abs_self _)) (wt_pos ..).le
  have he := bilinear_floor (increase (nearby hF.census B hv hj hk z hz) le_rfl ((le_abs_self _).trans ht)) le_rfl
  rw [hd] at he; intro u
  have hx:=he u; rw [Matrix.sub_mulVec,dotProduct_sub] at hx
  linarith [hF.ground u]
end YM.ConnectedActivityE6.Blaze
