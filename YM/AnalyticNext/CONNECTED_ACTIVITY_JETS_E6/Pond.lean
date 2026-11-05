import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Batch

/-!
# Marginals on one true reference
Sup-money input normalizations. Maps through finite bodies; keep
cochain. No borrowing independent arms. MeasureProduct even non-test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Pond
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel  Footprint Raw ProbabilityTheory Poll
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι]

def swim (i : Finset ι) (z : Body ι) : Body (↥i) := WithLp.toLp 2 fun j=>z j.val
def spill (i : Finset ι) (z : Body (↥i)) : Body ι := WithLp.toLp 2 fun j=> if h : j∈i then z ⟨j,h⟩ else 0

omit [Fintype ι] in
lemma settled (i : Finset ι) (z : Body (↥i)) : swim i (spill i z)=z := by ext j; simp [swim,spill]
omit [Fintype ι] [DecidableEq ι] in
lemma swim_m (i : Finset ι) : Measurable (swim i) := by unfold swim; fun_prop
omit [Fintype ι] in
lemma spill_m (i : Finset ι) : Measurable (spill i) := by
  refine (WithLp.measurable_toLp _ _).comp (measurable_pi_lambda _ (fun j=> ?_))
  by_cases h : j∈i
  · simp only [dif_pos h]; fun_prop
  simp only [dif_neg h]; fun_prop

def circuit (i : Finset ι) (A : Matrix ι ι ℝ) := A.submatrix (fun j : ↥i=>j.val) (fun j: ↥i=>j.val)
def arch (i : Finset ι) (A : Matrix ι ι ℝ) := sweep (circuit i A)
instance {i : Finset ι} {A : Matrix ι ι ℝ} : IsProbabilityMeasure (arch i A) := by unfold arch; infer_instance

private lemma plotted_i (i : Finset ι) (a : Body (↥i)) (y : ι→ℝ) :
    dotProduct (spill i a).ofLp y = dotProduct a.ofLp (fun j=> y j.val) := by
  unfold dotProduct
  have ht : ∑ j∈i, (spill i a) j*y j = _ := Finset.sum_subset (subset_univ i) (fun j _ hj=> by simp [spill,hj])
  change ∑ j,spill i a j * y j=_; rw [← ht,← Finset.sum_coe_sort i]
  exact sum_congr rfl fun j _=> by simp [spill,j.2]

private lemma norms_i {A : Matrix ι ι ℝ} (i j : Finset ι) (a : Body (↥i)) (b : Body (↥j)) :
    dotProduct (spill i a).ofLp (A *ᵥ (spill j b).ofLp) =
      dotProduct a.ofLp ((A.submatrix (fun a : ↥i=>a.val) (fun a : ↥j=>a.val)) *ᵥ b.ofLp) := by
  rw [plotted_i]; congr 1; ext k
  change dotProduct _ _=dotProduct _ _
  rw [dotProduct_comm, plotted_i,dotProduct_comm]; rfl

private lemma inner_i (i : Finset ι) (a : Body (↥i)) (y : Body ι) : inner ℝ (swim i y) a=inner ℝ y (spill i a) := by
  simp_rw [PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial]
  exact (plotted_i i a y.ofLp).symm

theorem orbit {A : Matrix ι ι ℝ} (h : A.PosSemidef) (i : Finset ι) : MeasurePreserving (swim i)
    (sweep A) (arch i A) := by
  refine ⟨swim_m i, Measure.ext_of_charFun ?_⟩
  funext t
  have he : charFun ((sweep A).map (swim i)) t=charFun (sweep A) (spill i t) := by
    rw [charFun_apply, integral_map (swim_m i).aemeasurable (by fun_prop)]; simp_rw [inner_i, ← charFun_apply]
  rw [he]; unfold arch sweep
  rw [charFun_multivariateGaussian h,charFun_multivariateGaussian (show (circuit i A).PosSemidef from h.submatrix _), norms_i]; simp [circuit]

theorem subdivision {A : Matrix ι ι ℝ} (h : A.PosSemidef) (i j : Finset ι)
    (hp : ∀ a∈i, ∀ b∈j, A a b=0) :
    MeasurePreserving (fun z=> (swim i z,swim j z)) (sweep A) ((arch i A).prod (arch j A)) := by
  let f z := (swim i z,swim j z); have hf : Measurable f := (swim_m i).prodMk (swim_m j)
  have hs (a b) : A a b=A b a := (by
    conv_lhs => rw [← h.isHermitian.eq]; rw [Matrix.conjTranspose_apply,star_trivial])
  refine ⟨hf,charFun_eq_prod_iff.mp ?_⟩; intro t
  let X := WithLp.ofLp t
  let u := spill i X.1; let v:=spill j X.2
  have he : charFun (((sweep A).map f).map (WithLp.toLp 2)) t=charFun (sweep A) (u+v) := by
    rw [charFun_apply, MeasureTheory.integral_map (by fun_prop) (by fun_prop), MeasureTheory.integral_map hf.aemeasurable (by fun_prop)]
    apply integral_congr_ae; filter_upwards with z
    rw [WithLp.prod_inner_apply]; dsimp only [f,WithLp.ofLp_toLp]; simp_rw [inner_i]; rw [inner_add_right]
  rw [he]; unfold arch sweep
  have h₁ : A.submatrix (fun k : ↥i=>k.val) (fun k: ↥j=>k.val)=0 := by ext k p; exact hp k.val k.2 p.val p.2
  have h₂ : A.submatrix (fun k : ↥j=>k.val) (fun k: ↥i=>k.val)=0 := by ext k p; exact (hs k.val p.val).trans (hp p.val p.2 k.val k.2)
  rw [charFun_multivariateGaussian h,charFun_multivariateGaussian (show (circuit i A).PosSemidef from h.submatrix _),
    charFun_multivariateGaussian (show (circuit j A).PosSemidef from h.submatrix _), ← Complex.exp_add]
  simp only [WithLp.ofLp_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  unfold u v; simp_rw [norms_i,h₁,h₂,zero_mulVec,dotProduct_zero]; simp [circuit,X]; ring_nf
end YM.ConnectedActivityE6.Pond
