import YM.Next.STATIONARY.Shape.LocalOracle
import YM.Org.Theatre

set_option autoImplicit false
/-! Costed real analytic extension for each label of possibly unbounded length. -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics Metric NormedSpace
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {m : Side} {σ A R : ℝ} {n : ℕ}

lemma scene_le (x : Cover) : x∈box (size x) := by
  have ht (i : Axis) := single_le_sum (f:=fun i => (x i).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)
  rw [box_test]; constructor <;> intro i <;> unfold Laurent.size <;> specialize ht i <;> omega
lemma scene_lt {x : Cover} {a : ℕ} (h : size x≤a) : x∈box a := by
  have he := box_test.mp (scene_le x)
  rw [box_test]; constructor <;> intro i <;> [have hh:=he.1 i;have hh:=he.2 i] <;> omega

lemma price_vec (b : Step) : size (b.vec (R:=ℤ))=1 := by
  have hl : size (step b.dir:Cover)=1 := by unfold Laurent.size; rw [sum_eq_single b.dir] <;> simp_all
  unfold Step.vec; split <;> simp only [hl,size_neg]
lemma fees_end (w : Walk) (x : Cover) : size (stop x w)≤size x+w.length := by
  induction w generalizing x with
  | nil => simp [stop]
  | cons a l ih => rw [stop]; have h := ih (x+a.vec); have he := size_add x (a.vec (R:=ℤ)); rw [price_vec] at he; rw [List.length_cons]; omega
lemma fees_step (w : Walk) (x : Cover) {y : Cover} (h : y∈visits x w) : size y≤size x+w.length := by
  induction w generalizing x with
  | nil => simp [visits] at h; subst y; simp
  | cons a l ih =>
    simp only [visits,List.mem_cons] at h
    rcases h with h|h
    · rw [h]; omega
    have ht := ih (x+_) h; have he := size_add x (a.vec (R:=ℤ)); rw [price_vec] at he; rw [List.length_cons]; omega

lemma slot_weight (a : Slot) {x : Cover} (h : x∈a.stencil) : size x ≤ a.length := by
  have hz : size (0:Cover)=0 := by simp [Laurent.size]
  unfold Slot.length
  rcases mem_union.mp h with h|h
  · have he := fees_step _ _ (List.mem_toFinset.mp h); rw [hz] at he; omega
  have he := fees_step _ _ (List.mem_toFinset.mp h)
  have hv := fees_end a.walk 0; rw [hz,zero_add] at hv
  exact he.trans (Nat.add_le_add_right hv 4)

def aTerm (b : Atom G n) (U : CoverConfig G) := b.poly fun j => (b.leg j).eval U
lemma aTerm_at (b : Atom G n) : LocalOn ↑(box b.length) (aTerm b) := by
  intro U V h; unfold aTerm
  apply congr_arg b.poly; funext k
  have he : ((b.leg k).stencil : Set Cover) ⊆ (box b.length) := fun i hp => scene_lt
    ((slot_weight (b.leg k) hp).trans (single_le_sum (f:=fun k => (b.leg k).length) (fun _ _ => Nat.zero_le _) (mem_univ k)))
  exact (b.leg k).covered U V fun i hi hv => h _ (he hi) (he hv)

section extend
open Work.F02

-- complex coordinates at identity

def ambientInk (G : Gauge) : Phase G.ColorIndex →L[ℂ] G.Mat := LinearMap.toContinuousLinearMap
    (∑ i, (LinearMap.proj i : Phase G.ColorIndex →ₗ[ℂ] ℂ).smulRight (G.colorMat (EuclideanSpace.basisFun G.ColorIndex ℝ i)))
lemma ambient_real (v : G.Color) : ambientInk G (axes (WithLp.ofLp v))=G.colorMat v := by
  unfold ambientInk
  change (∑ i : G.ColorIndex, (LinearMap.proj i : Phase G.ColorIndex →ₗ[ℂ] ℂ).smulRight _) (axes v.ofLp) = _
  simp only [LinearMap.sum_apply,LinearMap.smulRight_apply,LinearMap.proj_apply]
  conv_rhs => rw [← (EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr v, map_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [axes,EuclideanSpace.basisFun_repr]

lemma ambient_hats (G : Gauge) : ContDiff ℂ ω (fun x => exp (ambientInk G x)) := by
  have hh : ContDiff ℂ ω (exp : G.Mat → G.Mat) := contDiff_iff_contDiffAt.mpr fun x =>
    (exp_analytic (𝕂:=ℂ) x).contDiffAt
  exact hh.comp (ambientInk G).contDiff

def brush (p : Phase (Lines G m 1)) : Ambient G m := fun x =>
    let a := fun i : G.ColorIndex => p (x.1,coord x.2,i)
    (exp (ambientInk G a),exp (ambientInk G (-a)))

lemma brush_physical (p : Link G m) : brush (G:=G) (m:=m) (axes p)=physical (input G m p) := by
  funext ⟨x,i⟩
  simp only [physical, encode_link]
  apply Prod.ext
  · rw [G.mat_lieExp]; exact congr_arg exp (ambient_real (arm _ _ _ p (x,coord i)))
  rw [← Work.F03.exp_neg_color,G.mat_lieExp]
  rw [G.mat_lieExp]; change exp (ambientInk G (-(axes (WithLp.ofLp (arm G m 1 p (x,coord i)))))) = _
  rw [map_neg,map_neg,ambient_real]

lemma brush_bounds (G : Gauge) (h : 0 < σ) : ∃ R : ℝ, 0 < R ∧ ∀ m (p : Phase (Lines G m 1)), ‖p‖<R →
    brush (G:=G) (m:=m) p ∈ closedBall (physical 1) (radius σ) := by
  have he : Continuous (fun x => exp (ambientInk G x)) := (ambient_hats G).continuous
  have ht := he.tendsto 0; simp only [map_zero,exp_zero] at ht
  obtain ⟨r,hr,hR⟩ := Metric.mem_nhds_iff.mp (ht (closedBall_mem_nhds (1:G.Mat) (radius_pos h)))
  refine ⟨r,hr,fun m p hp => ?_⟩
  rw [mem_closedBall, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (radius_pos h).le).mpr fun i => ?_
  let a := fun b : G.ColorIndex => p (i.1,coord i.2,b)
  have ha : ‖a‖ < r := lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr (fun b => norm_le_pi_norm p (i.1,coord i.2,b))) hp
  change ‖(exp (ambientInk G a),_) - (physical (1:Config G m) i)‖ ≤ _
  rw [Prod.norm_def,max_le_iff]
  have hA := hR (show a∈ball 0 r by simpa using ha)
  have hb := hR (show -a∈ball 0 r by simpa using ha)
  simp only [Set.mem_preimage, mem_closedBall, dist_eq_norm] at hA hb
  simp only [Prod.fst_sub,Prod.snd_sub,physical,Pi.one_apply,G.mat_one, inv_one]
  exact ⟨hA,hb⟩

lemma brush_smooth : ContDiff ℂ ω (brush (G:=G) (m:=m)) := by
  refine contDiff_pi.mpr fun x => ContDiff.prodMk ?_ ?_
  · exact (ambient_hats G).comp (f:=fun p : Phase (Lines G m 1) => fun i => p (x.1,coord x.2,i)) (by fun_prop)
  refine (ambient_hats G).comp (f:=fun p : Phase (Lines G m 1) => -(fun i => p (x.1,coord x.2,i))) ?_
  exact (contDiff_pi.mpr fun i => contDiff_apply ℂ ℂ _).neg

/-- The true length cap buys M tests directly, uniform in side. -/
theorem term_vault (G : Gauge) (h : 0<σ) : ∃ R : ℝ, 0<R ∧ ∀ n (b : Atom G n),
    VaultOn G (aTerm b) R (b.budget σ*(slotConst G)^n) := by
  obtain ⟨r,hr,hR⟩ := brush_bounds G h
  refine ⟨r,hr,fun n b m i => ⟨atomExt b i ∘ brush,(atomExt_contDiff _ _).comp brush_smooth,fun x hx => ?_,?_⟩⟩
  · exact atomExt_bound b _ h _ (hR _ _ (mem_ball_zero_iff.mp hx)) _
  funext p; simp only [Function.comp_apply,brush_physical,atomExt_physical]; rfl
end extend
end YM.Stationary
end

/-!
# Uniform unmasked action jets

Retain lengths in the budgets even when there are many paths to the very
same plaquette on the very same period. Stage prices, including for iteration,
will use these estimates *before* use of the next path.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics Metric
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {m : Side} {σ A R : ℝ} {n t : ℕ}

-- costNote factors may be absorbed once on the per-L part.
lemma note_pos {n} (h : 0 < R) : 0 ≤ costNote n R := mul_nonneg (by positivity) (circleTax_pos h n).le

lemma wx_split (σ : ℝ) (t : ℕ) (b : Atom G n) (η : ℝ) (he : (↑t+1 : ℝ)^2*η*4=σ/2) :
    b.budget (σ/2)*recitalScale t b.length η=b.budget σ := by
  unfold Atom.budget recitalScale
  rw [mul_assoc,← Real.exp_add]; congr 2; linear_combination b.length * he

section generic
variable (G n t)
open Work.F02

def priceSlot (G : Gauge) : ℝ := |slotConst G|
private lemma term_size_bank (G : Gauge) (h : 0<σ) : ∃ R : ℝ, 0<R ∧ ∀ n (b : Atom G n),
    VaultOn G (aTerm b) R (b.budget σ*(priceSlot G)^n) := by
  obtain ⟨r,hr,H⟩ := term_vault G h
  refine ⟨r,hr,fun n b m p => ?_⟩
  obtain ⟨g,hg,hv,ht⟩ := H n b m p
  refine ⟨g,hg,fun x hx => (hv _ hx).trans ?_,ht⟩
  apply mul_le_mul_of_nonneg_left _ (by unfold Atom.budget Atom.magnitude; positivity)
  exact le_abs_self (_^n) |>.trans_eq (abs_pow ..)

/-- Applies to the translational sum over arbitrary label sets as long as
there is only one age in this invocation. -/
lemma all_ages (hσ : 0 < σ) : ∃ η C : ℝ, 0<η ∧ 0≤C ∧ ∀ (ι : Type) (f : ι→Atom G n) (A : ℝ),
    SumBudget (fun i => (f i).budget σ) A →
    (∀ m : Side, AnalyticAt ℝ (chorus (fun i => aTerm (f i)) m) 0) ∧
     ∃ L : Picture G t, (∀ i j, Firm η (A*C) (L i j)) ∧ ∀ m, Recorded L (chorus (fun i => aTerm (f i)) m) 0 := by
  let η := σ/(2*(↑t+1)^2*4)
  have hp : 0<η := by unfold η; positivity
  have he : (↑t+1 : ℝ)^2*η*4=σ/2 := by unfold η; field_simp
  obtain ⟨R,hR,hV⟩ := term_size_bank G (σ:=σ/2) (half_pos hσ)
  let K := priceSlot G^n
  have hk : 0 ≤ K := by unfold K priceSlot; positivity
  refine ⟨η,K*costNote (t+1) R,hp,mul_nonneg hk (note_pos hR),fun ι f A H => ?_⟩
  let F j := aTerm (f j)
  let w i := (f i).budget (σ/2)*K
  have hu : SumBudget (fun i => w i*recitalScale t (f i).length η) (A*K) := by
    simp_rw [w,mul_right_comm _ K,wx_split σ t _ η he]
    refine ⟨fun _ => mul_nonneg (H.1 _) hk,H.2.1.mul_right _,?_⟩
    rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right H.2.2 hk
  have hw : Summable w := Summable.of_nonneg_of_le
    (fun i => mul_nonneg (by unfold Atom.budget Atom.magnitude; positivity) hk)
    (fun i => le_mul_of_one_le_right (show 0 ≤ w i from mul_nonneg (by unfold Atom.budget Atom.magnitude; positivity) hk)
       (Real.one_le_exp (by positivity : 0≤((t+1:ℝ)^2*η*(4*(f i).length))))) hu.2.1
  rw [← mul_assoc]; exact gathered F _ _ hw hp hR (fun i => hV n _) (fun i => aTerm_at _) _ hu

/-- Whole oriented atom summation, not kernel equivariance. -/
theorem orbit_cost (hσ : 0<σ) : ∃ η C : ℝ, 0<η ∧ 0≤C ∧ ∀ (f : ℕ→Atom G n) (A : ℝ), SumBudget (fun i => (f i).budget σ) A → ∃ P : Picture G t,
      (∀ i j,Firm η (A*C) (P i j)) ∧ ∀ m : Side, Recorded P (turnSeries f (m:=m)) 0 := by
  obtain ⟨η,C,hη,hC,h⟩ := all_ages G n t hσ
  refine ⟨η,reflectBill t η*C,hη,mul_nonneg (by unfold reflectBill; positivity) hC,fun f K hK => ?_⟩
  obtain ⟨hh,L,hl,he⟩ := h _ f K hK
  refine ⟨bleed L,fun i j => ?_,fun m => ?_⟩
  · rw [mul_left_comm]; exact bleed_cap hη hl _ _
  rw [funext (turns_frame f)]
  exact bleed_record (hh m) hl (he m)
end generic

-- treat ℓ² term as actual products of unmasked slots
section grams
variable (p : PathData G)

abbrev PairsIndex := PlaqAxes × (ℕ × ℕ)
def gramWeight (j : PairsIndex) := (p.row j.1 j.2.1).1*(p.row j.1 j.2.2).1/2
def gramPath (i : PairsIndex) : Atom G 2 :=
    ⟨![ (p.row i.1 i.2.1).2, (p.row i.1 i.2.2).2], fun j => if j 0=j 1 then gramWeight p i else 0⟩

lemma gram_size (j : PairsIndex) : (gramPath p j).length=(p.row j.1 j.2.1).2.length+(p.row j.1 j.2.2).2.length := by simp [Atom.length,gramPath,Fin.sum_univ_two]
lemma gram_charge (j : PairsIndex) : (gramPath p j).magnitude = Fintype.card G.ColorIndex *|gramWeight p j| := by
  unfold gramPath Atom.magnitude
  rw [← Equiv.sum_comp (finTwoArrowEquiv G.ColorIndex).symm]
  simp [Fintype.sum_prod_type,finTwoArrowEquiv,apply_ite abs]
lemma gram_eval (i : PairsIndex) (x : Site m) (U : Config G m) : aTerm (gramPath p i) (expandAt x U)=
    inner ℝ (p.ellTerms (x,i.1) i.2.1 U) (p.ellTerms (x,i.1) i.2.2 U)/2 := by
  unfold aTerm Atom.poly
  rw [← Equiv.sum_comp (finTwoArrowEquiv G.ColorIndex).symm,Work.F03.inner_color]
  simp only [Fintype.sum_prod_type,finTwoArrowEquiv,gramPath,Fin.prod_univ_two]
  simp [gramWeight,PathData.ellTerms,ite_mul,Finset.sum_div]
  apply Finset.sum_congr rfl; intro j _; unfold Slot.atSite; ring

def BankRows (p : PathData G) (σ A : ℝ) := ∀ x : PlaqAxes, SumBudget (fun i => |(p.row x i).1| * Real.exp (σ*(p.row x i).2.length)) A

def gramCost (G : Gauge) (A : ℝ) := (Fintype.card PlaqAxes : ℝ)*(A*A*(Fintype.card G.ColorIndex / 2))
lemma gram_budget (hw : BankRows p σ A) : SumBudget (fun j => (gramPath p j).budget σ) (gramCost G A) := by
  let k := (Fintype.card G.ColorIndex : ℝ)/2
  rw [show gramCost G A=∑ _ : PlaqAxes,A*A*k by simp [gramCost,k]]
  apply budget_prod_finite (A:=fun _ => _); intro a
  let f (i : ℕ) := |(p.row a i).1| * Real.exp (σ*(p.row a i).2.length)
  have hf : SumBudget f A := hw a
  rw [show (fun j : ℕ×ℕ => (gramPath p (a,j)).budget σ)=(fun j => (f j.1*f j.2)*k) by
    ext ⟨i,j⟩; rw [Atom.budget,gram_charge,gram_size]; unfold f k gramWeight
    simp only [Nat.cast_add,mul_add,Real.exp_add,abs_div,abs_mul,abs_two]; ring]
  have hk : 0≤k := by unfold k; positivity
  have hs := hf.2.1.mul_of_nonneg hf.2.1 hf.1 hf.1
  refine ⟨fun i => mul_nonneg (mul_nonneg (hf.1 _) (hf.1 _)) hk,hs.mul_right k,?_⟩
  calc
    _ = ((∑' i,f i)*(∑' i,f i))*k := by
      rw [tsum_mul_right,hs.tsum_prod]; simp_rw [tsum_mul_left,tsum_mul_right]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_self_le_mul_self (tsum_nonneg hf.1) hf.2.2) hk

lemma gram_sums {P : Clip} {K C : ℝ} (hp : p.Bounds P σ K C) (U : Config G m) (x : Site m) :
    (∑' b, aTerm (gramPath p b) (expandAt x U))= ∑ y, ‖p.ell U (x,y)‖^2/2 := by
  let v (i : PairsIndex) := gramPath p i
  have he : Summable (fun i => aTerm (v i) (expandAt x U)) := by
    have hw := gram_budget p (σ:=σ) (A:=K) (hp.rows)
    refine Summable.of_norm_bounded (hw.2.1.mul_right (2^2:ℝ)) fun i => ?_
    rw [Real.norm_eq_abs]; exact ((v i).unmasked_bound U x).trans (mul_le_mul_of_nonneg_right ((v i).lower_budget σ hp.width) (by positivity))
  change (∑' b,aTerm (v b) (expandAt x U))=_
  rw [he.tsum_prod,tsum_fintype]; refine sum_congr rfl fun i _ => ?_
  let f j := p.ellTerms (x,i) j U
  have h := he.prod_factor i
  have hf : Summable f := (p.ell_dominated hp (x,i)).summable U
  have hy (a : G.Color) := ((innerSL ℝ a).map_tsum hf)
  rw [h.tsum_prod]; unfold v; simp_rw [gram_eval]
  simp_rw [tsum_div_const]; congr 1
  rw [← real_inner_self_eq_norm_sq]; change (∑' a : ℕ, ∑' i, inner ℝ (f a) (f i))=inner ℝ (∑' i,f i) (∑' j, f j)
  simp_rw [show ∀ a, ∑' j, inner ℝ (f a) (f j) = inner ℝ (f a) (∑' b,f b) from fun a => (hy _).symm]
  conv_lhs => arg 1; intro i; rw [real_inner_comm]
  exact (hy _).symm
end grams
end YM.Stationary
end

/-! Unmasked kinetic bases & Wilson initialization inputs. -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics Metric
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {m : Side} {σ A R : ℝ} {n t : ℕ}

noncomputable section
open Work.F02

def orig (a : PlaqAxes) (U : CoverConfig G) := G.price (faceValue U (0,a))
lemma fixed_orig (a : PlaqAxes) : LocalOn ↑(box 4) (orig (G:=G) a) := by
  intro U V h
  have he {i : Cover} (hx : i∈visits (0:Cover) (square a.val.1 a.val.2)) : i∈box 4 := by
    apply scene_lt; apply (fees_step (x:=0) _ hx).trans
    simp [Laurent.size,square]
  exact congr_arg G.price (travel_local (0:Cover) _ U V (fun i ht hv => h i (he ht) (he hv)))
lemma fixed_identity (a : PlaqAxes) (x : Site m) (U : Config G m) : orig a (expandAt x U)=G.price (faceValue U (x,a)) := by
  unfold orig faceValue; rw [travel_at,map_zero,zero_add]

def pulseSize (G : Gauge) (A B : G.Mat) : ℂ := 1 - ((Matrix.trace A + Matrix.trace B)/2) / G.repDim
lemma pulsePrice (u : G.El) : pulseSize G (G.mat u) (G.mat u⁻¹)=(G.price u:ℂ) := by
  unfold pulseSize Gauge.price
  simp only [G.mat_inv,Matrix.star_eq_conjTranspose,Matrix.trace_conjTranspose,Complex.star_def,Complex.add_conj]
  push_cast; ring

lemma pulseCont (G : Gauge) : ContDiff ℂ ω (Function.uncurry (pulseSize G)) := by
  have he : ContDiff ℂ ω (Matrix.trace : G.Mat→ℂ) := (Matrix.traceLinearMap (Fin G.repDim) ℂ ℂ).toContinuousLinearMap.contDiff
  exact contDiff_const.sub (((he.comp contDiff_fst).add (he.comp contDiff_snd) |>.div_const _).div_const _)

lemma price_vault (G : Gauge) : ∃ R A, 0<R ∧ ∀ b, VaultOn G (orig b) R A := by
  obtain ⟨r,hr,h⟩ := brush_bounds G (show 0<(1:ℝ) from zero_lt_one)
  let w (a : PlaqAxes) := square a.val.1 a.val.2
  let T := (1+radius 1)^4*‖(1:G.Mat)‖
  let P := closedBall (0:G.Mat) T
  obtain ⟨A,hA⟩ := ((((isCompact_closedBall (0:G.Mat) T).prod (isCompact_closedBall (0:G.Mat) T)).image (pulseCont G).continuous).image continuous_norm).bddAbove
  refine ⟨r,A,hr,fun b m x => ?_⟩
  let p (v : Phase (Lines G m 1)) := stringMat (brush (G:=G) (m:=m) v) (w b) x
  let q (v : Phase (Lines G m 1)) := stringMat (brush (G:=G) (m:=m) v) (Lattice.reverse (w b)) (stop x (w b))
  refine ⟨fun v => pulseSize G (p v) (q v),(pulseCont G).comp (f:=fun v => (p v,q v)) (((stringMat_contDiff _ _).comp brush_smooth).prodMk ((stringMat_contDiff _ _).comp brush_smooth)),fun v hv => ?_,?_⟩
  · have ht (a : Walk) (i : Site m) (he : a.length = 4) : stringMat (brush (G:=G) (m:=m) v) a i∈P := by
      have hh := stringMat_bound (R:=radius 1) (1:Config G m) (radius_pos zero_lt_one).le _ (h m v (mem_ball_zero_iff.mp hv)) a i
      rw [mem_closedBall,dist_eq_norm, sub_zero]; rw [he] at hh; exact hh
    exact hA ⟨pulseSize G (p v) (q v), ⟨(p v,q v), ⟨ht _ _ rfl, ht _ _ (by simp only [w,Lattice.reverse,List.length_map,List.length_reverse]; rfl)⟩,rfl⟩,rfl⟩
  funext v
  simp only [Function.comp_apply,p,q,brush_physical,stringMat_physical,travel_reverse,pulsePrice,localAtom, fixed_identity]
  rfl
end

def WilsonQ (G : Gauge) (m : Side) (v : Link G m) := Wilson.energy (input G m v)
lemma bareChorus : chorus (orig (G:=G)) m=WilsonQ G m := by
  funext v; unfold chorus WilsonQ Wilson.energy; simp_rw [tsum_fintype,localAtom, fixed_identity,Fintype.sum_prod_type]

theorem Wilson_stream (G : Gauge) (t : ℕ) :
    (∀ m : Side, AnalyticAt ℝ (WilsonQ G m) 0) ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ L : Picture G t,
      (∀ i j,Firm 1 A (L i j)) ∧ ∀ m : Side, Recorded L (WilsonQ G m) 0 := by
  obtain ⟨R,A,hR,ha⟩ := price_vault G
  have hh : 0 ≤ A := by
    obtain ⟨_,_,h,_⟩ := ha ⟨(0,1),by decide⟩ 1 0
    exact (norm_nonneg _).trans (h _ (mem_ball_self hR))
  let v := A*recitalScale t 4 1
  let c := Fintype.card PlaqAxes*v
  have hv : 0 ≤ v := mul_nonneg hh (Real.exp_pos _).le
  have hx : SumBudget (fun _ : PlaqAxes => v) c := ⟨fun _ => hv,(hasSum_fintype _).summable,by rw [tsum_fintype]; simp [c]⟩
  obtain ⟨X,L,hL,H⟩ := gathered (orig (G:=G)) (fun _ => 4) (fun _ => A) (hasSum_fintype _).summable
    zero_lt_one hR ha (fun _ => fixed_orig _) t hx
  simp_rw [bareChorus] at X H
  exact ⟨X, _, mul_nonneg (by unfold c; positivity) (note_pos hR),L,hL,H⟩

lemma quadratic_write (F : PathData G) (p : Clip) {x z} (h : F.Bounds p σ x z) (a : Link G m) :
    quadratic p F (input G m a) = p.direct * WilsonQ G m a + chorus (fun i => aTerm (gramPath F i)) m a := by
  simp only [quadratic,chorus,localAtom,gram_sums _ h,WilsonQ,Wilson.energy,Fintype.sum_prod_type,mul_sum,sum_add_distrib]

theorem column_price (G : Gauge) (t : ℕ) {σ : ℝ} (C Z : ℝ) (hs : 0<σ) (hz : 0 ≤ Z) :
    ∃ η A, 0 < η ∧ 0 ≤ A ∧ ∀ (p : Clip) (R : PathData G) (u K Λ : ℝ), p.direct ≤ Z → R.Bounds p u K Λ → BankRows R σ C →
    (∀ m : Side, AnalyticAt ℝ (inputSeries p R (m:=m)) 0) ∧ ∃ L : Picture G t, (∀ i j, Firm η A (L i j)) ∧
        ∀ m : Side, Recorded L (inputSeries p R (m:=m)) 0 := by
  obtain ⟨x,B,hx,hB,H⟩ := all_ages G 2 t hs
  obtain ⟨h,b,hb,T,ht,Hu⟩ := Wilson_stream G t
  let γ := min 1 x
  have hG : 0 < γ := lt_min zero_lt_one hx
  let q := Z*b+gramCost G C*B
  have he : 0 ≤ gramCost G C := by unfold gramCost; rw [← sq C]; positivity
  refine ⟨γ, reflectBill t γ*q,hG,mul_nonneg (by unfold reflectBill; positivity) (add_nonneg (by positivity) (mul_nonneg he hB)),fun p R u K Λ hp hw hg => ?_⟩
  obtain ⟨V,L,Lh,HL⟩ := H _ (gramPath R) _ (gram_budget R hg)
  let a (m : Side) := p.direct • WilsonQ G m+chorus (fun i => aTerm (gramPath R i)) m
  let P := (p.direct:ℂ) • T+L
  have hh m : AnalyticAt ℝ (a m) 0 := (((analyticAt_const (v:=p.direct)).mul (h m)).add (V m))
  have hh' (i j) : Firm γ q (P i j) := by
    have Hx : ‖(p.direct:ℂ)‖=p.direct := by simp [abs_of_nonneg p.quadratic_pos.le]
    exact (((Firm.const hG (p.direct:ℂ)).mul ((ht _ _).mono hG (min_le_left ..) le_rfl)).mono hG le_rfl
      (mul_le_mul_of_nonneg_right (Hx.trans_le hp) hb)).add ((Lh _ _).mono hG (min_le_right ..) le_rfl)
  have Hq m (v : Link G m) : inputSeries p R v=Patch.average fun s => a m (orderTurn s v) := by
    unfold inputSeries secondTerm; simp_rw [flip_links,quadratic_write _ _ hw]; rfl
  refine ⟨fun m => ?_, bleed P, fun i j => bleed_cap hG hh' i j,fun m => ?_⟩
  · rw [funext (Hq m)]; unfold Patch.average; apply ContDiffAt.analyticAt
    refine ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun i _ => ?_)
    refine ContDiffAt.comp (f:=⇑(orderTurn (G:=G) (m:=m) i)) _ ?_ (orderTurn _).contDiff.contDiffAt
    rw [map_zero]; exact (hh m).contDiffAt
  rw [funext (Hq m)]; exact bleed_record (hh m) hh'
    ((((Hu m).weigh p.direct (h m))).both ((analyticAt_const (v:=p.direct)).mul (h m)) (V m) (HL m))
end YM.Stationary
end

/-!
# Receipts for subtracting the actual oriented bases
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics Metric
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {m : Side} {σ A R Λ : ℝ} {n t : ℕ}

structure Pointwise (F : Link G m → ℝ) : Prop where
    analytic : AnalyticAt ℝ F 0
    rotate (s : Signed) : F ∘ orderTurn (G:=G) (m:=m) s =ᶠ[𝓝 0] F
    stained : Stained G F
    guard : force F

namespace Pointwise
variable {F H : Link G m→ℝ} (h : Pointwise F)
include h
lemma sub (hf : Pointwise H) : Pointwise (F-H) := ⟨h.analytic.sub hf.analytic,fun i => (h.rotate i).sub (hf.rotate i),fun i => (h.stained i).sub (hf.stained i), h.guard.sub hf.guard⟩
lemma add (hf : Pointwise H) : Pointwise (F+H) := ⟨h.analytic.add hf.analytic,fun i => (h.rotate i).add (hf.rotate i),fun i => (h.stained i).add (hf.stained i), h.guard.add hf.guard⟩
lemma coin (w : ℝ) : Pointwise (w • F) where
  analytic := analyticAt_const.mul h.analytic
  rotate i := (h.rotate i).mono fun _ he => congr_arg (w*·) he
  stained i := (h.stained i).mono fun _ he => congr_arg (w*·) he
  guard := by have ht := h.guard; unfold force at *; exact ht.mono fun _ he => congr_arg (w*·) he
lemma lights : Lit n F := by
  intro s
  unfold noteAt beat; rw [((h.rotate s).iteratedFDeriv ℝ n).eq_of_nhds]
end Pointwise

lemma point_actual (F : Config G m→ℝ) (hf : AnalyticAt ℝ (F ∘ input G m) 0)
    (h : ∀ t U, F (Lattice.gauge t U) = F U) (hr : ∀ s U, F (pull s 0 U)=F U) : Pointwise (F ∘ input G m) := by
  refine ⟨hf, fun s => Eventually.of_forall (fun x => ?_), fun u => Eventually.of_forall (fun x => ?_),?_⟩
  · change F _= F _; exact (congr_arg F (flip_links s x).symm).trans (hr ..)
  · change F _= F _; rw [← stain_cons, h]
  refine moveField_germ.mono (fun x hx => ?_)
  exact (congr_arg F hx).trans (h ..)

lemma orbit_axis (f : Config G m → ℝ) (u) (s : Signed) :
    (Patch.average fun i : Signed => f (pull i 0 (pull s 0 u)))=(Patch.average fun i : Signed => f (pull i 0 u)) := by
  unfold Patch.average; congr 1
  simp_rw [pull_pull, affine, Signed.act_zero,add_zero]; exact Equiv.sum_comp (Equiv.mulLeft s) (fun i : Signed => f (pull i 0 u))

def orbitRaw (f : ℕ → Atom G n) (U : Config G m) := Patch.average fun i : Signed => uncut f (pull i 0 U)

theorem stain_ink (p : ℕ→ Atom G n) (hs : 0<σ) (h : SumBudget (fun i => (p i).budget σ) A) (hp : ∀ i,(p i).Invariant) : Pointwise (turnSeries p (m:=m)) := by
  apply point_actual (orbitRaw p) (turns_analytic _ hs h) _ (fun s U => orbit_axis _ U s)
  intro t U; simp only [orbitRaw,Work.F05.pull_gauge_zero, Work.F05.uncut_gauge p hp]
theorem stain_knit (p : PathData G) (u : Clip) (hf : p.Bounds u σ A Λ) : Pointwise (inputSeries u p (m:=m)) := by
  apply point_actual (secondTerm u p) _ _ (fun s U => orbit_axis _ U s)
  · obtain ⟨η,K,_,_,h⟩ := column_price G 2 A u.direct hf.width u.quadratic_pos.le
    exact (h u p σ A Λ le_rfl hf hf.rows).1 m
  intro t U; simp only [secondTerm, Work.F05.pull_gauge_zero, Work.F05.quadratic_gauge hf]
theorem Wilson_witness : Pointwise (WilsonQ G m) := point_actual Wilson.energy ((Wilson_stream G 2).1 _) (fun _ _ => energy_gauge ..) fun _ _ => energy_pull ..

def intended (p : Clip) (X : PathData G) (x : Link G m) := mainTerm p X (input G m x)
lemma intent (p : Clip) (X : PathData G) : intended p X (m:=m) = inputSeries p X+turnSeries X.cubic+turnSeries X.quartic := by
  funext v; simp only [intended,mainTerm,inputSeries,secondTerm,Patch.average,turnSeries,Pi.add_apply,sum_add_distrib,mul_add]

variable {F : Link G m → ℝ}

theorem low_columns {u : Clip} {B : Bed} {p : PathData G} {c d}
    (h : p.Bounds u σ A Λ) (hp : Attached B p) (hb : Floor B u m c d) (hy : Bid.Sworn B m G) :
    inputSeries u p (0:Link G m)=0 ∧ fderiv ℝ (inputSeries u p (m:=m)) 0=0 ∧
    ∀ x y, iteratedFDeriv ℝ 2 (inputSeries u p (m:=m)) 0 ![x,y] = Bid.gaugeFiscal B (arm G m 1 x) (arm G m 1 y) := by
  apply Work.F03.hessian_of_limit (Q:=fun x y => Bid.gaugeFiscal B (arm G m 1 x) (arm G m 1 y)) (stain_knit p u h).analytic.contDiffAt
  · intro x
    have he s := Work.F03.quadratic_limit h hp hb (Bid.pulled (arm G m 1 x) s)
    have H := (tendsto_finsetSum univ (fun s _ => he s)).const_mul ((Fintype.card Signed:ℝ)⁻¹)
    unfold inputSeries secondTerm input Patch.average; simp_rw [map_smul, Work.F03.represent_pulled,
      mul_div_assoc, Finset.sum_div]; unfold Bid.Sworn at hy; have hh : (Fintype.card Signed : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
    simpa only [hy,sum_const,card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ hh] using H
  · intro x y z; rw [map_add, Work.F03.gaugeFiscal_add]
  intro x y; unfold Bid.gaugeFiscal
  refine sum_congr rfl fun i _ => ?_; rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, show (Precision.K (B.metric.acts m)).transpose=_ from ?_, dotProduct_comm]
  unfold Precision.K; simp [hb.symmetric.1,Matrix.mul_assoc]

lemma top_Wilson {u : Clip} {B : Bed} {p : PathData G} {c d}
    (h : p.Bounds u σ A Λ) (hp : Attached B p) (hb : Floor B u m c d) (hy : Bid.Sworn B m G) (hz : B.diagonal.acts m=1) :
    Rays 3 (WilsonQ G m-inputSeries u p) := by
  have hh := low_columns h hp hb hy
  have he : AnalyticAt ℝ (WilsonQ G m) 0 := Wilson_witness.analytic
  have hu (x y : Link G m) : Bid.gaugeFiscal B (arm _ _ _ x) (arm _ _ _ y) = ∑ j : Face (Per m), inner ℝ (Work.F03.faceCurl j (arm G m 1 x)) (Work.F03.faceCurl j (arm _ _ _ y)) := by
    unfold Bid.gaugeFiscal; rw [Precision.K, Matrix.mul_assoc,hb.same,hz,Matrix.one_mul]
    simp_rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Work.F03.inner_color]
    rw [sum_comm]; apply sum_congr rfl; intro i _
    rw [← Matrix.dotProduct_mulVec]
    unfold dotProduct
    rw [← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site m)) plaqEquiv)]; rfl
  have H := Work.F03.hessian_of_limit (Q:=fun x y : Link G m => iteratedFDeriv ℝ 2 (inputSeries u p) 0 ![x,y]) he.contDiffAt (fun x => by
    rw [hh.2.2,hu]; unfold WilsonQ input Wilson.energy
    simp_rw [map_smul,Finset.sum_div,real_inner_self_eq_norm_sq]
    apply tendsto_finsetSum; intro j _
    apply Work.F03.price_limit (V:=fun t : ℝ => faceValue (represent (t • arm G m 1 x)) j) _
      (Work.F03.face_deriv j (arm G m 1 x))
    rw [zero_smul]; exact Push.stroll_zero ..) (fun x y z => by simp [iteratedFDeriv_two_apply])
    (Work.F03.hessian_symmetric (stain_knit p u h).analytic.contDiffAt)
  have hk := (stain_knit p u h (m:=m)).analytic
  apply (rays_jet (he.sub hk) 3).mpr
  intro i hi
  apply ContinuousMultilinearMap.ext
  intro v
  rw [iteratedFDeriv_sub_apply (he.contDiffAt) (hk.contDiffAt)]
  interval_cases i
  · simp [hh.1, H.1]
  · simp [iteratedFDeriv_one_apply,hh.2.1,H.2.1]
  have ht : v=![v 0,v 1] := by ext i; fin_cases i <;> simp
  rw [ht]; simp only [_root_.sub_apply, H.2.2,sub_self]; rfl
end YM.Stationary
end

/-!
# The cubic and quartic path-growth contract

The widths here do not depend on the supplied prices of the stationary
jets. The next computation will be of those stationary jets themselves, not
perturbative assumptions on the masked interaction. This contract already
handles the different strips (including the width for the fourth jet of the
newly emitted third).
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset Asymptotics Metric
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {m : Side} {σ A Λ : ℝ} {n t : ℕ}

def AtomWall (f : ℕ → Atom G n) (σ A : ℝ) : Prop := SumBudget (fun i => (f i).budget σ) A ∧ ∀ i,(f i).Invariant
lemma AtomWall.mono {f : ℕ → Atom G n} {τ B : ℝ} (h : AtomWall f σ A) (hp : τ ≤ σ) (he : A ≤ B) : AtomWall f τ B := by
  refine ⟨Work.F08.budget_minor ⟨h.1.1,h.1.2.1,h.1.2.2.trans he⟩ (fun i => ?_) fun i => ?_,h.2⟩
  · unfold Atom.budget Atom.magnitude; positivity
  unfold Atom.budget; apply mul_le_mul_of_nonneg_left _ (by unfold Atom.magnitude; positivity); gcongr


def HasRecord {m : ℕ → Side} (F : ∀ i, Link G (m i) → ℝ) (σ A : ℝ) (t : ℕ) :=
    ∃ K : Picture G t,(∀ i j, Firm σ A (K i j)) ∧ ∀ i, Recorded K (F i) 0

namespace HasRecord
variable {m : ℕ → Side} {F E : ∀ i, Link G (m i) → ℝ} {B δ : ℝ}
lemma mono (h : HasRecord F σ A t) (hh : 0<δ) (he : δ≤σ) (hg : A ≤ B) : HasRecord F δ B t := by
  obtain ⟨K,H,hK⟩ := h; exact ⟨K,fun i j => (H i j).mono hh he hg,hK⟩
lemma sub (h : HasRecord F σ A t) (hl : HasRecord E σ B t) (he : ∀ i, AnalyticAt ℝ (F i) 0) (hh : ∀ i, AnalyticAt ℝ (E i) 0) : HasRecord (F-E) σ (A+B) t := by
  obtain ⟨K,H,hK⟩ := h; obtain ⟨V,Y,hV⟩ := hl; exact ⟨K-V,fun i j => (H i j).sub (Y i j),fun i => (hK i).less (he i) (hh i) (hV i)⟩

end HasRecord

private lemma box_unit (G : Gauge) (σ : ℝ) (hs : 0<σ) (t : ℕ) [NeZero t] (ht : 2 ≤ t) :
    ∃ w D : ℝ, 0<w ∧ w≤σ ∧ 0 ≤ D ∧ ∀ m : ℕ → Side, Tendsto (fun i => (m i).val) atTop atTop →
    ∀ (F : ∀ i, Link G (m i) → ℝ) (A : ℝ), (∀ i, Pointwise (F i)) → (∀ i, Rays (t+1) (F i)) →
      0≤A → HasRecord F σ A t → ∃ a : ℕ→ Atom G (t+1), AtomWall a w (A*D) ∧ ∀ i,
        Rays (t+2) (F i-turnSeries a) := by
  obtain ⟨η,K,hp,he,hK,H⟩ := strokes G t ht σ hs
  refine ⟨η,K*inkCost G t η,hp,he,mul_nonneg hK (inkCost_nonneg ..),fun m hM F A hh ht ha hR => ?_⟩
  obtain ⟨L,hL,Hm⟩ := hR
  obtain ⟨a,g⟩ := H A L ha (withdrew hM (tendsto_const_nhds (x:=(0:ℝ))) hL (fun i => by simpa only [mul_zero] using (Hm i))
    (fun i => (hh i).analytic) (fun i => (hh i).stained) (fun i => (hh i).guard) (fun i j hj _ =>
      (rays_jet (hh i).analytic _).mp (ht i) j hj))
  obtain ⟨hi,hv⟩ := artery_funded g
  refine ⟨issue a, ⟨?_, hv⟩,fun i => ?_⟩
  · rw [← mul_assoc]; exact hi
  let R := F i-turnSeries (issue a)
  have hV := stain_ink (issue a) hp hi hv (m:=m i)
  have hX := ((hh i).sub hV).analytic
  have hlow : Rays (t+1) R := (ht i).sub (turns_low _ hp hi)
  refine (rays_jet hX _).2 fun j hj => ?_
  rcases eq_or_lt_of_le (Nat.le_of_lt_succ hj) with h|h
  · rw [h,iteratedFDeriv_sub_apply (hh i).analytic.contDiffAt hV.analytic.contDiffAt]
    exact sub_eq_zero.mpr (aperture_eq (colors_align (F i) (hh i).analytic (hh i).lights L a g hp (Hm i))).symm
  exact (rays_jet hX _).1 hlow j h

lemma orbit_gate (G : Gauge) (σ : ℝ) (hp : 0<σ) : ∃ η C : ℝ, 0 < η ∧ η≤σ ∧ 0 ≤ C ∧ ∀ m : ℕ → Side,
    Tendsto (fun i => (m i).val) atTop atTop → ∀ (F : ∀ i, Link G (m i)→ℝ),
      (∀ i, Pointwise (F i)) → (∀ i, Rays 3 (F i)) → ∀ A, 0 ≤ A → HasRecord F σ A 2 → HasRecord F σ A 3 →
    ∃ X : ℕ → Atom G 3, ∃ V : ℕ → Atom G 4, AtomWall X η (A*C) ∧ AtomWall V η (A*C) ∧
      ∀ i, Rays 5 (F i-turnSeries X-turnSeries V) := by
  obtain ⟨w,K,hk,hu,hK,H⟩ := box_unit G σ hp 2 (by decide)
  obtain ⟨τ,B,hτ,hB,I⟩ := orbit_cost G 3 3 hk
  let a := min σ τ
  have ha : 0<a := lt_min hp hτ
  obtain ⟨v,b,hv,hx,hb,L⟩ := box_unit G a ha 3 (by decide)
  let c := (1+K*B)*b
  have hc : 0 ≤ c := by unfold c; positivity
  refine ⟨min w v, K+c, lt_min hk hv,(min_le_left ..).trans hu,add_nonneg hK hc,fun m hm F hg hh A hA hF hG => ?_⟩
  obtain ⟨X,HX,Hz⟩ := H m hm F A hg hh hA hF
  obtain ⟨D,hd,HD⟩ := I X (A*K) HX.1
  let E i := turnSeries X (m:=m i)
  have he i : Pointwise (E i) := stain_ink X hk HX.1 HX.2
  have hy : HasRecord E a (A*K*B) 3 := HasRecord.mono (show HasRecord E τ (A*K*B) 3 from ⟨D,hd,fun i => HD _⟩) ha (min_le_right ..) le_rfl
  obtain ⟨Y,hY,U⟩ := L m hm (F-E) _ (fun i => (hg i).sub (he i)) Hz (by positivity)
    (((hG.mono ha (min_le_left ..) le_rfl)).sub hy (fun i => (hg i).analytic) (fun i => (he i).analytic))
  have hY' : AtomWall Y v (A*c) := by
    rw [show A*c=(A+A*K*B)*b by unfold c; ring]; exact hY
  exact ⟨X,Y,HX.mono (min_le_left ..) (by gcongr; linarith),hY'.mono (min_le_right ..) (by gcongr; linarith), U⟩

/-- Operates subtracting at same chart and real metric; buys support at the width
chosen from the target widths and free input H phase prices. `M≥1` is the jet
budget in sup. -/
lemma assembly (G : Gauge) (σ σ₀ : ℝ) (A Z : ℝ) (hs : 0<σ) (hσ : 0<σ₀) (hz : 0≤ Z) :
    ∃ τ C : ℝ, 0<τ ∧ τ≤σ ∧ 0≤C ∧ ∀ (m : ℕ → Side), Tendsto (fun i => (m i).val) atTop atTop →
      ∀ (B : Bed) (p : Clip) (a b : ℝ), B.roots.strip σ₀ A → Floor B p 1 a b → p.direct ≤ Z → ∀ E : ∀ i, Link G (m i) → ℝ, (∀ i, Pointwise (E i)) →
        (∀ i, Rays 3 (E i - inputSeries p (blank B G))) → ∀ M : ℝ, 1 ≤ M → HasRecord E σ M 2 → HasRecord E σ M 3 →
      ∃ X : ℕ → Atom G 3, ∃ V : ℕ → Atom G 4, AtomWall X τ (M*C) ∧ AtomWall V τ (M*C) ∧
        ∀ f : ℕ → Atom G 2, ∀ i, Rays 5 (E i - intended p (emitBase G B f X V)) := by
  let k := rowPrice σ₀ A
  obtain ⟨v,P,hv,hP,H⟩ := column_price G 2 k Z hσ hz
  obtain ⟨w,Q,hw,hQ,Y⟩ := column_price G 3 k Z hσ hz
  let a := min σ (min v w)
  have hb : a≤σ := min_le_left ..
  have hh : a≤v := (min_le_right ..).trans (min_le_left ..)
  have he : a≤w := (min_le_right ..).trans (min_le_right ..)
  have ha : 0 < a := lt_min hs (lt_min hv hw)
  obtain ⟨x,J,hx,hX,hJ,D⟩ := orbit_gate G a ha
  refine ⟨x,(1+(P+Q))*J,hx,hX.trans hb,by positivity,fun m hm B p b z hB hu hp E hE hl M hM HF HG => ?_⟩
  have h0 : 0≤M := zero_le_one.trans hM
  let W := blank B G
  have hW : W.Bounds p σ₀ k 0 := blank_cap hσ hB hu le_rfl le_rfl
  have hc : BankRows W σ₀ k := hW.rows
  obtain ⟨ht,U,hU,hU'⟩ := H p _ _ _ _ hp hW hc
  obtain ⟨hα,S,hS,hS'⟩ := Y p _ _ _ _ hp hW hc
  let F i := inputSeries p W (m:=m i)
  have hs i : Pointwise (F i) := stain_knit _ _ hW
  have hm' : HasRecord F v P 2 := ⟨U,hU,fun i => hU' _⟩
  have hm'' : HasRecord F w Q 3 := ⟨S,hS,fun i => hS' _⟩
  obtain ⟨X,V,h₁,h₂,h₃⟩ := D m hm (E-F) (fun i => (hE i).sub (hs i)) hl (M+P+Q) (by positivity)
    ((((HF.mono ha hb le_rfl)).sub (hm'.mono ha hh le_rfl) (fun i => (hE i).analytic) (fun i => (hs i).analytic)).mono ha le_rfl (by linarith))
    ((((HG.mono ha hb le_rfl)).sub (hm''.mono ha he le_rfl) (fun i => (hE i).analytic) (fun i => (hs i).analytic)).mono ha le_rfl (by linarith))
  have hC : (M+P+Q)*J ≤ M*((1+(P+Q))*J) := by rw [← mul_assoc]; gcongr; nlinarith [mul_nonneg (sub_nonneg.mpr hM) (add_nonneg hP hQ)]
  refine ⟨X,V,h₁.mono le_rfl hC,h₂.mono le_rfl hC,fun f i => ?_⟩
  rw [intent]
  convert h₃ i using 1
  change _- (F i + turnSeries X + turnSeries V)=E i-F i-_-_
  abel
end YM.Stationary
end
