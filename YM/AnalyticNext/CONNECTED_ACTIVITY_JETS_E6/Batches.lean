import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Combo
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Logs
import YM.Next.SCHEDULE.GridCost

/-!
# Price the local log diagonals by principal submatrices

Read on covering patches; no integration by parts needed. Keep exact i-block
trace invariant under block rotations of the same Window. In particular don't
charge separately color components touched by a choice of gauge before paying
the difference. All Prod associations on actual `frames` (minor of each block
shares same window), no inaccessible interpolation assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Pulse.Batch
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

section mat
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {W : Finset ι} {Y P : Matrix ι ι ℝ}

/-- factoring an exact principal patch. Safe if factor frozen along
color bundles. -/
def principal (W : Finset ι) (M : Matrix ι ι ℝ) := M.submatrix (Subtype.val : ↥W → ι) (Subtype.val : ↥W → ι)

omit [DecidableEq ι] in
lemma localize_left (h : ∀ i∈W, ∀ j : ι,j∉W → Y i j=0) (P : Matrix ι ι ℝ) :
    principal W (Y*P) = principal W Y*principal W P := by
  ext v w
  rw [Matrix.mul_apply]; change (Y*P) (v:ι) (w:ι) = _
  rw [Matrix.mul_apply]; symm
  have hp : (∑ i∈W,Y v i*P i w) = ∑ i,Y v i*P i w := Finset.sum_subset (Finset.subset_univ _)
    fun x _ hx => by rw [h _ v.property x hx,zero_mul]
  rw [← hp,← sum_attach W]; rfl
omit [DecidableEq ι] in
lemma localize_right (h : ∀ i : ι,i∉W→∀ j∈W, P i j=0) (Y : Matrix ι ι ℝ) :
    principal W (Y*P) = principal W Y*principal W P := by
  apply transpose_injective
  rw [show (principal W (Y*P)).transpose=principal W ((Y*P).transpose) from rfl,Matrix.transpose_mul,
    Matrix.transpose_mul]
  exact localize_left (Y:= P.transpose) (fun i hi j hj => h j hj i hi) _
omit [Fintype ι] in
lemma within_one (W : Finset ι) : principal W (1:Matrix ι ι ℝ)=1 := by
  ext i j; simp [principal, Matrix.one_apply]
end mat

variable {B : ℕ} (Y Z A : Itinerary.Mat f G) (D : Window (along (G:=G) S) B)
variable {η r Q : ℝ} {m : ℕ}
lemma perWindow (i : Tubular f G) (s : ℝ) {W : Finset (Tubular f G)} (he : D.take i=W)
    (hi : i∈W) :
    intensity D A s 0 i i =
      (Batch.principal W (A-1)*(Batch.principal W (glide A s))⁻¹) ⟨i,hi⟩ ⟨i,hi⟩ := by
  subst W
  unfold intensity; rw [pow_zero,mul_one,Matrix.mul_apply, Matrix.mul_apply]
  symm
  have hp : (∑ j∈D.take i, (A-1) i j* D.pad (glide A s) j i)= ∑ j, (A-1) i j* D.pad (glide A s) j i :=
    Finset.sum_subset (Finset.subset_univ _) fun j _ hj => by rw [D.outside _ _ _ hj,mul_zero]
  rw [← hp,← sum_attach (D.take i)]
  refine sum_congr rfl fun j _ => ?_
  rw [D.inside]; rfl

/-- Form block sum of the actual diagonal log letter. -/
def joint (A : Itinerary.Mat f G) (D : Window (along (G:=G) S) B) (p : Bond f) :=
    ∑ i : G.ColorIndex, localBase D A (p,i)

lemma inside_caps (h : Allow A (along S) m η r Q) (hp : Torch η r Q) :
    ContinuousOn (fun s=>intensity D A s 0) (Set.uIcc (0:ℝ) 1) := by
  simp only [intensity,pow_zero,mul_one]
  exact ContinuousOn.mul continuousOn_const (vibrate D A h hp)
lemma joint_coil (h : Allow A (along S) m η r Q) (hp : Torch η r Q) (v : Bond f) :
    joint A D v=∫ s in (0:ℝ)..1, (∑ j:G.ColorIndex,intensity D A s 0 (v,j) (v,j)) :=
  (intervalIntegral.integral_finsetSum (f:=fun j s=>intensity D A s 0 (v,j) (v,j))
    (fun i _ => (continuousOn_pi.mp (continuousOn_pi.mp (inside_caps A D h hp) (v,i)) (v,i)).intervalIntegrable)).symm

lemma rinse_at {Y Z A : Itinerary.Mat f G} (v : Bond f) (t : ℝ) (D : Window (along (G:=G) S) B)
    (hz : Y*A=A*Z) (hW : A.transpose*A=1)
    (hY : Allow (glide Z t) (along S) m η r Q) (h' : Allow (glide Y t) (along S) m η r Q)
    (he : ∀ i j : Tubular f G, i.1≠j.1 → A i j=0)
    (hq : D=Coat.frames G S B) :
    ∑ x : G.ColorIndex,Pulse.intensity D Y t 0 (v,x) (v,x)=∑ x : G.ColorIndex,Pulse.intensity D Z t 0 (v,x) (v,x) := by
  by_cases hu : Nonempty G.ColorIndex
  swap
  · have hn : IsEmpty G.ColorIndex := not_nonempty_iff.mp hu; simp
  obtain ⟨e⟩ := hu
  let p := (v,e)
  let W := D.take p
  have hD (i : G.ColorIndex) : D.take (v,i)=W := by unfold W; rw [hq]; ext; rfl
  have hm (x : G.ColorIndex) : (v,x)∈W := by rw [← hD]; exact D.here _
  let I (x : G.ColorIndex) : ↥W := ⟨(v,x),hm x⟩
  let C := Batch.principal W A
  let T (X : Itinerary.Mat f G) := Batch.principal W (glide X t)
  let g (X : Itinerary.Mat f G) := Batch.principal W (X-1)
  have hg (X : Itinerary.Mat f G) (h : X*A=A*Z) : glide X t*A=A*glide Z t := by
    simp_rw [glide, mul_add,add_mul,smul_mul_assoc,Matrix.mul_smul,one_mul,mul_one,sub_mul,mul_sub,h]
    rw [one_mul,mul_one]
  have hb i j (hi : i∈W) (hj : j∉W) : A i j=0 ∧ A j i=0 := by
    have ht : Prod.fst i≠j.1 := by
      intro h; apply hj; unfold W at hi ⊢; rw [hq,Coat.in_frame] at hi ⊢
      rw [← h]; exact hi
    exact ⟨he i j ht, he j i ht.symm⟩
  have left (X : Itinerary.Mat f G) := Batch.localize_left (fun i hi j hj => (hb i j hi hj).1) X
  have right (X : Itinerary.Mat f G) := Batch.localize_right (fun i hi j hj => (hb j i hj hi).2) X
  have h₀ : T Y*C=C*T Z := by unfold T C; rw [← right, hg _ hz, ← left]
  have h₁ : g Y*C=C*g Z := by unfold g C; rw [← right, sub_mul,hz,one_mul,← left,mul_sub,mul_one]
  have hI : C.transpose*C=1 := by
    rw [show C.transpose=Batch.principal W A.transpose from rfl]
    change _*Batch.principal W A=1; rw [← right A.transpose,hW,Batch.within_one]
  have hv : C*C.transpose=1 := mul_eq_one_comm.mp hI
  let o := g Y*(T Y)⁻¹
  let n := g Z*(T Z)⁻¹
  have hs : (T Y)⁻¹*T Y=1 := (h'.sub (Embedding.subtype (·∈W))).initial.2.1
  have hq' : T Z*(T Z)⁻¹=1 := (hY.sub (Embedding.subtype (·∈W))).initial.1
  have hn : o*C=C*n := by
    have ht : (T Y)⁻¹*C=C*(T Z)⁻¹ := by
      conv_lhs => rw [← mul_one C,← hq',← mul_assoc C,h₀.symm,← mul_assoc _ _ ((T Z)⁻¹), ← mul_assoc _ (T Y) C,hs,one_mul]
    unfold o n; rw [mul_assoc, ht, ← mul_assoc,h₁,mul_assoc]
  have hX (M : Itinerary.Mat f G) (x : G.ColorIndex) := perWindow M D (v,x) t (hD x) (hm x)
  simp_rw [hX]
  let U : Matrix (↥W) (↥W) ℝ := Matrix.diagonal fun i => if i.val.1=v then 1 else 0
  have hc : U*C=C*U := by
    ext i j; unfold U; rw [diagonal_mul, mul_diagonal]
    by_cases hi : i.val.1=j.val.1
    · rw [hi, mul_comm]
    have hx : C i j=0 := he _ _ hi
    rw [hx,zero_mul,mul_zero]
  have htrace (M : Matrix (↥W) (↥W) ℝ) : trace (U*M)=∑ x,M (I x) (I x) := by
    let W' := Finset.univ.image I
    have hx i (hi : i∉W') : (U*M) i i=0 := by
      unfold U; rw [diagonal_mul]; split
      next hh =>
        exact (hi (mem_image.mpr ⟨i.val.2, mem_univ _,Subtype.ext (Prod.ext hh.symm rfl)⟩)).elim
      next hn => rw [zero_mul]
    change (∑ i, (U*M) i i)=_
    rw [← Finset.sum_subset (f:=fun i => (U*M) i i) (Finset.subset_univ W') (fun i _ hi => hx i hi)]
    unfold W'; rw [Finset.sum_image (fun i _ j _ h => congr_arg (fun z : ↥W => z.val.2) h)]
    refine sum_congr rfl fun i _ => ?_
    unfold U; rw [diagonal_mul,if_pos (show _ from rfl),one_mul]
  change (∑ x, o (I x) (I x))=∑ x,n (I x) (I x)
  have hO : U*o=(C*(U*n))*C.transpose := by rw [← mul_assoc C, ← hc,mul_assoc U C n,← hn,mul_assoc U, mul_assoc o,hv,mul_one]
  rw [← htrace,← htrace,hO,Matrix.trace_mul_comm,← mul_assoc,hI,one_mul]
end YM.ConnectedActivityE6.Pulse.Batch
