import YM.Next.RANK.Along


/-! # Exact read of the linear curvature probe

Derived from Hol's path assignment and genuine weighted line sum at canonically
oriented square from the tree reference anchor. No hypothesis of exact rank. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function Set Filter Lattice Wilson RG Beamer Source Labels Source.Drops Configuration CellsInt MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} (H : Hol G) (d : ℕ)
variable {b : ℕ} {n : Side} {o : Site n}

def oneGlow (A : Snap G d) (r : Face ℤ) := Exterior.linkSum (access A) r.1 (square r.2.val.1 r.2.val.2)
def lamp (A : Snap G d) (v : Turn b) := oneGlow d A v.val

private def view (H : Hol G) (d : ℕ) (A : Snap G d) := H.links d (expand d A) 1
private lemma none : view H d 0=1 := funext fun i => (Work.G02.linkGerm H d i).2.1

@[simp] private lemma fires_zero (p : Turn b) : used (view H d 0) p=1 := by
  rw [none]; unfold used central; rw [Lattice.face_gauge,faceValue, Pressure.one]; group
lemma burnt (p : Turn b) (A : Snap G d) :
    HasDerivAt (fun t : ℝ => G.mat (used (view H d (t • A)) p)) (G.colorMat (lamp d A p)) 0 := by
  simp only [used,central,face_gauge,Gauge.mat_mul,Gauge.mat_inv]
  have hz : faceValue (view H d 0) p.val=1 := by rw [none,faceValue,Pressure.one]
  have ha : leaves (view H d 0) p.val.1=1 := by rw [none,leaves,Pressure.one]
  let f (t : ℝ) := leaves (view H d (t • A)) p.val.1
  let g (t : ℝ) := faceValue (view H d (t • A)) p.val
  have ht : HasDerivAt (fun t=> G.mat (f t)) _ 0 := (Work.G02.walkGerm H d (paths p.val.1) 0).2 A
  have hu : HasDerivAt (fun t=> G.mat (g t)) _ 0 := (Work.G02.walkGerm H d _ _).2 A
  apply ((ht.mul hu).mul ht.star).congr_deriv; simp only [f,g,zero_smul,hz,ha, G.mat_one,mul_one,one_mul, Gauge.colorMat_skew,star_one,Pi.mul_apply]
  unfold lamp oneGlow; abel
lemma coals (p : Word b) (A : Snap G d) :
    played (used (view H d 0)) p=1 ∧ HasDerivAt (fun t : ℝ => G.mat (played (used (view H d (t • A))) p)) (G.colorMat (stage p (lamp d A))) 0 := by
  induction p with
  | nil => simp only [played,stage,List.map_nil,List.prod_nil,List.sum_nil,map_zero]; exact ⟨trivial,hasDerivAt_const _ _⟩
  | cons j p IH =>
    let c:= p.length
    obtain ⟨a,i⟩ := j
    have ht := map_zero G.colorMat
    have hs := burnt H d a A
    let f (t : ℝ) := used (view H d (t • A)) a; let L:= lamp d A a; let X:=G.colorMat (stage p (lamp d A))
    have hv : f 0=1 := by simp [f]
    rcases IH with ⟨hg,hh⟩
    cases i with
    | false =>
      simp only [played,List.map_cons,List.prod_cons,Bool.false_eq_true,↓reduceIte,G.mat_mul,stage,List.sum_cons,map_add]
      refine ⟨by simp only [fires_zero, inv_one,one_mul]; simp, (hs.mul hh).congr_deriv ?_⟩
      simp only [zero_smul, hg, G.mat_one,mul_one,one_mul,fires_zero]
      change G.colorMat _+X= _+_; rfl
    | true =>
      simp only [played,List.map_cons,List.prod_cons,↓reduceIte,G.mat_mul,G.mat_inv,stage,List.sum_cons,map_add,map_neg]
      refine ⟨by simp only [fires_zero,inv_one,one_mul]; simp, (hs.star.mul hh).congr_deriv ?_⟩
      simp only [zero_smul, hg,G.mat_one,mul_one,one_mul,fires_zero,star_one, Gauge.colorMat_skew]; rfl

private lemma bend {f : ℝ → G.El} {a : G.Color} (hp : f 0=1) (h : HasDerivAt (fun t => G.mat (f t)) (G.colorMat a) 0) : HasDerivAt (fun t=> G.plog (G.mat (f t))) a 0 := by
  have he : DifferentiableAt ℝ G.plog 1 := G.plog_diff.differentiableAt (by simp)
  let v := fderiv ℝ G.plog 1
  have ht : HasFDerivAt G.plog v (G.mat (f 0)) := by rw [hp,G.mat_one]; exact he.hasFDerivAt
  refine (ht.comp_hasDerivAt 0 h).congr_deriv ?_
  have H : (v ∘L G.colorMat.toContinuousLinearMap)=ContinuousLinearMap.id ℝ G.Color := by
    apply HasFDerivAt.unique (f:=G.plog ∘ (fun a : G.Color => G.mat (G.lieExp a))) (x:=0)
    · apply HasFDerivAt.comp _ _ G.expDiff_zero; rw [G.mat_lieExp_zero,G.mat_one]; exact he.hasFDerivAt
    exact HasFDerivAt.congr_of_eventuallyEq (hasFDerivAt_id 0) G.plog_left
  exact DFunLike.congr_fun H a

lemma flowDir {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x : V) : HasDerivAt (fun t : ℝ=>t • x) x 0 := by simpa using (hasDerivAt_id' (0:ℝ)).smul_const x
lemma lumen (R : ℕ) (h : 2*(R+1)< n.val) (x : Dim o R) (A : Snap G d) :
    fderiv ℝ (bore H d R (register h x)) 0 A= stage (word G h x) (lamp d A) := by
  let p:= register h x; let a (t : ℝ) := view H d (t • A)
  have hu : (fun t : ℝ => bore H d R p (t • A)) = fun t => G.plog (G.mat (played (used (a t)) (word G h x))) := by
    ext1 t; apply congr_arg G.plog; apply congr_arg G.mat
    exact (Classical.choose_spec (rolled G _ _ p.property.1 p.property.2)).2 _
  obtain ⟨C,v,hC,Hc⟩ := shots H d 1
  have hs : DifferentiableAt ℝ (bore H d R p) 0 := ((Hc R p).1).differentiableAt (by simp)
  have hv := hs.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ)
    (flowDir A) (by simp)
  apply hv.unique; change HasDerivAt (fun t : ℝ => bore H d R p (t • A)) _ 0; rw [hu]
  refine bend (by unfold a; rw [zero_smul]; exact (coals H d _ A).1) (coals H d _ A).2

-- exact stencil coefficients in Key.In d
lemma revealed_cell (e : Edge Cover) (A : Snap G d) : access A e=∑ i∈Finset.range (d-1), trail (expand d A i) e.2 e.1 := by
  unfold access
  simp only [partConnection,potential,one_smul]
  rw [intervalIntegral.integral_finsetSum]; rfl
  intro i hi; refine Continuous.intervalIntegrable ?_ _ _
  exact (Tensor.diag_smooth _ 1).continuous.comp (by fun_prop)

lemma glows (A : Snap G d) (r : Face ℤ) : oneGlow d A r=∑ i∈Finset.range (d-1), CellsInt.test (expand d A i) r.2.val.1 r.2.val.2 r.1 := by
  obtain ⟨x,⟨i,j⟩,hr⟩ := r
  simp only [oneGlow,Exterior.linkSum,square,Step.used,posDir,negDir,Step.vec,↓reduceIte,Bool.false_eq_true,add_zero]; rw [show x+step i+step j-step i= x+step j by abel,show x+step i+step j+-step i=x+step j by abel,add_sub_cancel_right]
  simp_rw [revealed_cell]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]; simp only [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro m _; rw [cigar]; dsimp only [Pi.sub_apply,stepValue]; abel

-- read at KeyIn.d of actual Tester.In

def spanKey (x : KeyIn G d) : Fin (d-1) := ⟨x.val.1,by have he := x.property; unfold Labels.generation at he; omega⟩
def kp (A : Snap G d) := fun i : KeyIn G d => Labels.coord (expand d A) i.val
lemma traffic (A : Snap G d) (r : Face ℤ) (l : G.ColorIndex) :
    oneGlow d A r l=∑ i : KeyIn G d, ((kp d A) i).re * tester i.val (r.1,r.2,l) := by
  rw [glows]
  let a:= (r.1,r.2,l)
  let Y:= (i : Fin (d-1)) × Fin (Labels.dim G i.val)
  let hI : Y ≃ KeyIn G d := {
    toFun p:=⟨⟨p.1.val,p.2⟩, by change ↑p.1 + 2≤d; omega⟩
    invFun p:= ⟨spanKey d p,p.val.2⟩
    left_inv _:= rfl
    right_inv p:= rfl }
  have he (i) : i ∈ Finset.range (d-1) ↔ i< d-1 := Finset.mem_range
  conv_rhs => rw [← hI.sum_comp]
  rw [Fintype.sum_sigma]
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : Fin (d-1), sweep i.val (A i) a := by
      rw [show ∀ f : Fin (d-1) → G.Color,(∑ i,f i).ofLp l=∑ i,(f i).ofLp l from fun f => map_sum (EuclideanSpace.proj l : G.Color→L[ℝ] ℝ)  f _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [expand,dif_pos i.isLt]; rfl
    _ = _ := by
      apply Finset.sum_congr rfl; intro i _; conv_lhs => rw [← (axes G i.val).sum_repr (A i)]
      rw [map_sum, Finset.sum_apply]; apply Finset.sum_congr rfl; intro j _
      change (sweep i.val) _ a=Complex.re (Labels.coord _ ⟨i.val,j⟩) * tester _ _
      rw [map_smul]; simp only [Labels.coord,expand, dif_pos i.isLt, Complex.ofReal_re];rfl
end YM.Next.Rank.Spindle
