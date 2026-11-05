import YM.AnalyticNext.CUBIC_MATCH.Lift.Pair
import YM.AnalyticNext.CUBIC_MATCH.Region.Sym


set_option warningAsError false

/-!
# Reanchor a compatible symmetric test

Pay for the loss of the translation origin at a universal amount only,
shrinking support width quoted before L. This yields true periodic equality
for all assignments without any shape/period/mesh losses at that step. No
such inference from per-torus sup budgets on SIZE of the jet alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter Lattice Laurent RG Wilson Precision Exterior Tree Tensor Bid Lift
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {n : Side} {μ : Type*} {A : TapSet G 3 → ℝ}
  {θ C : ℝ}

abbrev Keys3 := TypeFace 1 × TypeFace 1 × TypeFace 1
abbrev Index3 (G : Gauge) := Fin 3 → G.ColorIndex
abbrev Batch (G : Gauge) := Keys3 × (Couple × (Index3 G × Cover))

def released (H : Batch G) : TapSet G 3 :=
    let u := H.1
    let d := H.2.1
    let z := H.2.2.2
    let I := H.2.2.1
    ![(d.1+z,u.1,I 0),(d.2+z,u.2.1,I 1),(z,u.2.2,I 2)]
def storeBatch (u : TapSet G 3) : Batch G :=
  (((u 0).2.1,(u 1).2.1,(u 2).2.1),((u 0).1-(u 2).1,(u 1).1-(u 2).1),(fun i => (u i).2.2), (u 2).1)

def tiesBatch : Batch G ≃ TapSet G 3 where
  toFun := released
  invFun := storeBatch
  left_inv H := by
    rcases H with ⟨⟨i,j,k⟩,⟨a,b⟩,c,z⟩; unfold released storeBatch; dsimp
    simp only [add_sub_cancel_right]; congr 2; refine Prod.ext ?_ rfl; ext1 d; fin_cases d <;> rfl
  right_inv H := by
    ext1 i; unfold storeBatch released; dsimp only; fin_cases i <;>
      simp [sub_add_cancel]

def dropPrice (A : TapSet G 3 → ℝ) (K : Keys3) (t : Couple) (I : Index3 G) (z : Cover) := A (released (K,t,I,z))

/-- L1 shrink accommodates paying separately for origin. -/
lemma released_reach (H : Batch G) : length2 H.2.1 + size H.2.2.2 ≤ 4*reachOf (released H) := by
  rcases H with ⟨⟨i,j,k⟩,⟨a,b⟩,c,z⟩
  unfold reachOf; rw [Fin.sum_univ_three]
  change size a+size b+size z ≤ 4*(size (a+z)+size (b+z)+size z)
  have he (x : Cover) : size x ≤ size (x+z)+size z := by simpa only [add_neg_cancel_right,size_neg] using size_add (x+z) (-z)
  have hh := he a; have ht := he b; omega

lemma drop_cost (he : 0<θ) (h : Decay reachOf θ C A) (hC : 0 ≤ C) (i : Keys3) (x : Couple) (v : Index3 G) :
    Decay size (θ/4) (C*wanes (θ/4) (length2 x)) (dropPrice A i x v) := by
  intro a
  rw [mul_assoc,← wanes_splits]; refine (h (released _)).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) hC)
  have hh : (length2 x+size a:ℕ) ≤ 4 * reachOf (released (i,x,v,a)) := released_reach (i,x,v,a)
  have hx := mul_le_mul_of_nonneg_left (show ((length2 x+size a:ℕ):ℝ)≤4*(reachOf (released (i,x,v,a)):ℝ) by exact_mod_cast hh) he.le
  linarith

def covector (i : Index3 G) : Shades G := (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 3) ℝ).compContinuousLinearMap
   fun j => PiLp.proj (𝕜:=ℝ) 2 (fun _ => ℝ) (i j)
lemma covector_cost (i : Index3 G) : ‖covector i‖ ≤ 1 := by
  apply (ContinuousMultilinearMap.opNorm_le_iff zero_le_one).mpr
  intro m; change |(∏ j,m j (i j))| ≤ _
  rw [one_mul,Finset.abs_prod]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => ?_)
  simpa only [EuclideanSpace.basisFun_inner,OrthonormalBasis.norm_eq_one,one_mul]
    using (abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ (i j)) (m j))

/-- True relative tensor. -/
def anchored (A : TapSet G 3 → ℝ) : Three (Shades G) 1 1 1 := fun i j k x =>
    ∑ v : Index3 G, (∑' a : Cover,dropPrice A (i,j,k) x v a) • covector v

/-- cost only depends on color count and paid width. norm estimates need no explicit card > 0. -/
def exitFee (G : Gauge) (θ : ℝ) := (Fintype.card (Index3 G) : ℝ) * ∑' i : Cover,wanes (θ/4) (size i)
lemma exitFee_nonneg (G : Gauge) (θ : ℝ) : 0 ≤ exitFee G θ :=
  mul_nonneg (by positivity) (tsum_nonneg (fun i : Cover => (wanes_pos ..).le))

lemma anchored_price (he : 0 < θ) (h : Decay reachOf θ C A) (hC : 0 ≤ C) : Pace (θ/4) (exitFee G θ*C) (anchored A) := by
  intro i j k x
  have hg : 0 < θ/4 := by positivity
  have hh := wanes_summable hg; let M := ∑' i : Cover,wanes (θ/4) (size i)
  have hp (v : Index3 G) : ‖(∑' a : Cover,dropPrice A (i,j,k) x v a) • covector v‖ ≤ C*wanes (θ/4) (length2 x)*M := by
    have hu := drop_cost he h hC (i,j,k) x v; have ht := hu.summable_norm hh
    rw [norm_smul]; refine (mul_le_of_le_one_right (norm_nonneg _) (covector_cost _)).trans ((norm_tsum_le_tsum_norm ht).trans ?_)
    exact (ht.tsum_le_tsum hu (hh.mul_left _)).trans_eq (tsum_mul_left ..)
  unfold anchored
  exact (norm_sum_le ..).trans ((Finset.sum_le_sum fun z _ => hp z).trans_eq (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; unfold M exitFee; ring))

lemma batchList (x y b : Dir G n) (p : Site n) (H : Batch G) : verse p (released H) ![x,y,b]=
    covector H.2.2.1 (![x (wrap n H.2.1.1+(wrap n H.2.2.2+p), H.1.1),
      y (wrap n H.2.1.2+(wrap n H.2.2.2+p), H.1.2.1), b (wrap n H.2.2.2+p,H.1.2.2)]) := by
  rcases H with ⟨⟨i,j,k⟩,⟨t,z⟩,u,r⟩
  let a := wrap n r+p
  unfold verse; change _=∏ s, ![x (wrap n t+a,i),y (wrap n z+a,j),b (a,k)] s (u s)
  refine Finset.prod_congr rfl fun s _ => ?_
  fin_cases s
  · change x (wrap n (t+r)+p,i) (u 0)=x (wrap n t+a,i) _; rw [map_add,add_assoc]; rfl
  · change y (wrap n (z+r)+p,j) (u 1)=y (wrap n z+a,j) _; rw [map_add,add_assoc]; rfl
  rfl

private def delivered (p : Site n) (x y b : Dir G n) (k : Keys3) (t : Couple) : Shades G →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ => G.Color) ℝ (![x (wrap n t.1+p,k.1),y (wrap n t.2+p,k.2.1), b (p,k.2.2)])

private lemma invoiceK (he : 0<θ) (h : Decay reachOf θ C A) (hC : 0≤C) (x y b : Dir G n) (p : Site n) (K : Keys3) (t : Couple) :
    (∑' i : Index3 G × Cover, delivered p x y b K t (dropPrice A K t i.1 i.2 • covector i.1)) =
      delivered p x y b K t (anchored A K.1 K.2.1 K.2.2 t) := by
  have hz i := drop_cost he h hC K t i
  let v i := dropPrice A K t i
  let L := delivered p x y b K t
  let X (i : Index3 G × Cover) := v i.1 i.2 • covector i.1
  have hh i : Summable (v i) := ((hz i).summable_norm (wanes_summable (by positivity))).of_norm
  have ht : Summable X := by
    apply Summable.of_norm
    apply (summable_prod_of_nonneg (fun j => norm_nonneg (X j))).mpr; refine ⟨fun i => ?_, .of_finite⟩
    exact (((hz i).summable_norm (wanes_summable (by positivity))).mul_right ‖covector i‖).congr (fun j => (norm_smul _ _).symm)
  rw [(show Summable (fun i => L (X i)) from L.summable ht).tsum_prod, tsum_fintype,anchored,map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact ((L ∘L (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (covector i))).map_tsum (hh i)).symm

private lemma batchable (he : 0<θ) (h : Decay reachOf θ C A) (x y b : Dir G n) (p : Site n) :
    Summable fun i : Batch G => delivered p x y b i.1 i.2.1
      (dropPrice A i.1 i.2.1 i.2.2.1 i.2.2.2 • covector i.2.2.1) := by
  let X (i : Batch G) := delivered p x y b i.1 i.2.1 (dropPrice A i.1 i.2.1 i.2.2.1 i.2.2.2 • covector i.2.2.1)
  let M := ∏ i, ‖(![x,y,b]) i‖
  have hm : Summable fun i : Batch G => ‖A (released i)‖ := tiesBatch.summable_iff.mpr (h.summable_norm (taps_decay _ he))
  apply Summable.of_norm_bounded (hm.mul_left M); intro i
  let t := p-wrap n i.2.2.2
  change ‖X i‖ ≤ _
  have ht : X i=verse t (released i) ![x,y,b] * A (released i) := by
    unfold X; rw [map_smul, batchList,smul_eq_mul,mul_comm, show wrap n i.2.2.2+t=p from add_sub_cancel _ _]; cases i; rfl
  rw [ht,norm_mul]; exact mul_le_mul_of_nonneg_right (verse_bounded ..) (norm_nonneg _)

lemma anchored_read (he : 0<θ) (h : Decay reachOf θ C A) (hC : 0≤C) (x y b : Dir G n) :
    ∑ p, receive A p ![x,y,b]=pair3 (anchored A) x y b := by
  let U p i := verse p i (![x,y,b]) • A i
  let V (p : Site n) (i : Batch G) := delivered p x y b i.1 i.2.1
    (dropPrice A i.1 i.2.1 i.2.2.1 i.2.2.2 • covector i.2.2.1)
  have hs (p : Site n) : Summable (U p) := (receive_norm he h ..).of_norm
  have hg (p : Site n) : Summable (V p) := batchable he h x y b p
  have ht (p i) : U p (released i) = V (wrap n i.2.2.2+p) i := by
    unfold U V; rw [batchList, map_smul]; simp only [smul_eq_mul]; rw [mul_comm]; rfl
  have hP : ∑ p, receive A p (![x,y,b])=∑ p,∑' i,V p i := by
    change ∑ p,∑' i,U p i= _
    rw [← Summable.tsum_finsetSum (fun p _ => hs p), ← Summable.tsum_finsetSum (fun p _ => hg p)]
    refine Eq.trans (tiesBatch.tsum_eq _).symm (tsum_congr fun i => ?_)
    change ∑ p,U p (released i)=_
    simp_rw [ht]; exact Equiv.sum_comp (Equiv.addLeft (wrap n i.2.2.2)) (fun p => V p i)
  rw [translation (anchored_price he h hC) (by positivity),hP]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [(hg p).tsum_prod,tsum_fintype,Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [((hg p).prod_factor _).tsum_prod]
  exact tsum_congr fun a => invoiceK he h hC x y b p _ a

/-- Reanchor before spending the cubic lift. -/
theorem TotalRep.relative {c : μ → Side} {F : ∀ p, Dir G (c p) → ℝ} (h : ∀ i, ContDiffAt ℝ 3 (F i) 0)
    (hp : TotalRep c 3 θ C (fun p x => term 3 (fun t : ℝ => F p (t • x)))) : ∃ K : Three (Shades G) 1 1 1,
      0<θ ∧ 0≤C ∧ Pace (θ/4) (exitFee G θ*C) K ∧ ∀ p (x y z : Dir G (c p)),pair3 K x y z=Tensor.coeff (F p) 3 0 ![x,y,z] := by
  obtain ⟨A,hθ,hC,hA,H⟩ := hp.symmetry h
  exact ⟨anchored A,hθ,hC,anchored_price hθ hA hC,fun p x y z => (anchored_read hθ hA hC x y z).symm.trans (H p _)⟩
end YM.CubicMatch
