import YM.Ward.Genuine
import YM.Ward.Motion
import YM.Ward.PDE

/-!
# Transverse angular vector input implies polar PDE jets, at collinear positions
-/
set_option autoImplicit false
noncomputable section
namespace YM.Ward
open Function Set Filter Complex Analysis Table
open scoped Topology NNReal ENNReal BigOperators ContDiff
variable {G : Gauge} {L : Register G} {S : Table L}
variable (a b : Axis)

def lift (p : PDE.V) := p.1 • basis a+p.2 • basis b
def put (p : PDE.V) : Points 2 := points ![lift a b p,0]

def desc : PDE.V →L[ℝ] Points 2 := (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (Points.direction 0 a)+
  (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Points.direction 0 b)
@[simp] lemma floor (p) : desc a b p = put a b p := by
  ext k; fin_cases k <;> simp [desc,put,lift,Points.direction]

lemma ranges {x : PDE.V} (hv : x∈ PDE.side) (h : b≠a) : put a b x∈conf _ := by
  suffices he : lift a b x ≠ 0 by
    intro i j; fin_cases i <;> fin_cases j <;> simp [put,he,Ne.symm he]
  intro ht; have hh := congr_arg (fun x : E4 => x a) ht
  simp [lift,Ne.symm h] at hh
  exact (show 0<x.1 from hv).ne' hh

def F (p : S.Tag × S.Tag) (x : PDE.V) : ℂ := pair p.1 p.2 (lift a b x)
lemma Fu (H : S.Hierarchy) (p : S.Tag × S.Tag) (h : b≠a) : PDE.C (F a b p) := by
  rw [show F a b p=disc ![p.1,p.2] ∘ desc a b from funext (fun i => by simp; rfl)]
  intro x hi
  have hx : desc a b x∈conf _ := by rw [floor]; exact ranges _ _ hi h
  exact (cont_disc H _ hx).comp x (desc a b).contDiff.contDiffAt

def left (K : Ortho.Skew) (T : SpinRows S) (p : S.Tag × S.Tag) := (turns T K p.1,p.2)
def right (K : Ortho.Skew) (T : SpinRows S) (p : S.Tag × S.Tag) := (p.1,turns T K p.2)

lemma in_vector (H : S.Hierarchy) (p : S.Tag × S.Tag) (h : b≠a) {x : PDE.V} (ht : x∈PDE.side)
    (W : DiffPlan S) (g : W.Derivatives S) :
    PDE.tangent (F a b p) x=x.1 • pair (rise W b p.1) p.2 (lift a b x)-x.2 • pair (rise W a p.1) p.2 (lift a b x) := by
  have he (v : PDE.V) (c) (hw : desc a b v=Points.direction 0 c) :
      D v (F a b p) x=pair (rise W c p.1) p.2 (lift a b x) := by
    rw [show F a b p=disc ![p.1,p.2] ∘ desc a b from funext fun i => by simp;rfl]
    have hx := ranges a b ht h
    rw [D, fderiv_comp x (show DifferentiableAt ℝ (disc _) _ from
      (floor a b x) ▸ (cont_disc H _ hx).differentiableAt (by simp)) (desc a b).differentiableAt,
      (desc a b).fderiv, ContinuousLinearMap.comp_apply, hw, floor]
    change D _ (disc ![p.1,p.2]) _=_
    rw [fromD W H g hx]
    unfold pair
    congr 2; funext j; fin_cases j <;> simp
  unfold PDE.tangent
  rw [he PDE.e a (by simp [PDE.e,desc]
      ), he PDE.i b (by simp [PDE.i,desc])]

lemma planeVec (h : b ≠ a) (x : PDE.V) (i : Axis) : M4.move (Ortho.plane b a).val (lift a b x) i=
    if i=a then -x.2 else if i=b then x.1 else 0 := by
  have hh (k : Axis) := M4.move_basis (Ortho.plane b a).val i k
  unfold M4.move at *
  simp only [lift,map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,hh]
  simp only [Ortho.plane,
    Matrix.sub_apply,Matrix.single_apply]
  clear hh
  by_cases ht : i=a
  · subst i; simp [h,Ne.symm h]
  by_cases hw : i=b
  · subst i; simp [h,Ne.symm h]
  simp [h,Ne.symm h,ht,Ne.symm ht,hw,Ne.symm hw]

lemma sigma (h : b≠a) (W : DiffPlan S) (T : SpinRows S) (H : S.Hierarchy) (g : W.Derivatives S)
    (p : S.Tag × S.Tag) {x : PDE.V} (hx : x ∈ PDE.side) :
    let K := Ortho.plane b a
    PDE.law (left K T) (right K T) (F a b) p x=angular W T ![p.1,p.2] K (put a b x) := by
  intro K
  unfold PDE.law angular
  rw [in_vector a b H p h hx W g]; unfold left right
  rw [Fin.sum_univ_two]
  let q : Fin 2 → S.Tag := ![p.1,p.2]
  have he u : update q 0 u=![u,p.2] := by ext1 i;fin_cases i <;> simp [q]
  have ht u : update q 1 u=![p.1,u] := by ext1 i;fin_cases i <;> simp [q]
  dsimp only
  unfold F pair
  -- smul sums using basis
  have hs g (z : Points 2) : M4.move K.val (put a b x 1) g=0 := by simp [M4.move,put] -- no z
  change _= disc (update q 0 (turns T K (q 0))) (put a b x)+(∑ i, _)+ (disc (update q 1 (turns T K (q 1))) _+_)
  simp_rw [show ∀ i, M4.move K.val (put a b x 1) i=0 from fun i => hs i 0,zero_smul,Finset.sum_const_zero, add_zero]
  rw [ht,he]
  change _= disc ![turns T K p.1,p.2] _+(∑ i, (M4.move K.val (lift a b x) i) • disc (update q 0 (rise W i (q 0))) (put a b x)) + _
  simp_rw [show ∀ i, M4.move K.val (lift a b x) i = _ from planeVec a b h x,he]
  simp only [ite_smul,zero_smul,neg_smul]
  have hw (f g : Axis → ℂ) : (∑ i, if i=a then f i else if i=b then g i else 0)=f a+g b := by
    have he i : (if i=a then f i else if i=b then g i else 0)=(if i=a then f i else 0)+(if i=b then g i else 0) := by split_ifs <;> simp_all
    simp_rw [he,Finset.sum_add_distrib];simp
  rw [hw]; simp [q,put]; ring

theorem realized (h : b≠a) (W : DiffPlan S) (T : SpinRows S) (H : S.Hierarchy) (g : W.Derivatives S)
    (C : commutes W T) (Y : Collinear W T)
    (p : S.Tag × S.Tag) (n : ℕ) (t : ℝ) (ht : 0<t) :
    let K := Ortho.plane b a
    PDE.tower (PDE.law (left K T) (right K T) (F a b) p) n (t,0)=0 := by
  intro K
  rw [← PDE.actual (f := PDE.law _ _ _ p) (PDE.regular (left K T) (right K T) (fun i => Fu a b H i h) p)
    (x := (t,0)) (show _ from ht) n]; dsimp only
  let z := put a b (t,0)
  have hz y : put a b (t,y)=cast z 0 b y := by
    ext i; fin_cases i <;> simp [put,lift,z,cast,Points.direction]
  rw [show (fun y => PDE.law _ _ _ p (t,y))= angular W T ![p.1,p.2] K ∘ cast z 0 b from
      funext (fun y => (sigma a b h W T H g p (x := (t,y)) (show _ from ht)).trans (by rw [hz];rfl))]
  have hv : cast z 0 b 0 ∈ conf _ := by rw [start]; exact ranges a b ht h
  refine jet_line W T H g C K _ z 0 b 0 hv (fun w => Y a _ _ _ _ hv ?_) n
  rw [start]; intro i; fin_cases i
  · exact ⟨t,by simp [z,put,lift]⟩
  exact ⟨0,by simp [z,put,lift]⟩
end YM.Ward
