import YM.Next.BOUNDARY.Derivative
import YM.Next.BOUNDARY.Descends

/-!
# Real stress conventions and Lorentz covariance

Both sets of indices use `Axis`, time last (`timeAxis`). Thus hat is the
identity with our indexing; physical order is 1,2,3,then Minkowski 0
(Euclidean 4). Use the same finite labels, core, action and `Rotation` as in
reconstruction. No claims about selfadjointness as closed operators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter Table Boundary Mink Next.BOUNDARY Next.BOUNDARY.Descent Complex
open scoped Topology BigOperators LineDeriv Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} {P : DiffPlan S} {H : S.RealSpin} {R : Rotation S}

/-- Metric, for contravariant derivative. -/
def eta (a : Axis) : ℝ := if a=timeAxis then 1 else -1

def zeta (a : Axis) : ℂ := if a=timeAxis then -I else 1
lemma zeta_wick (a : Axis) : zeta a * wick a = 1 := by unfold zeta wick; split <;> simp
lemma zeta_square (a : Axis) : zeta a * zeta a = -(eta a : ℂ) := by unfold zeta eta; split <;> simp

/-- Minkowski-normalized stress label. -/
def M (T : S.Stress) (a b : Axis) := (-zeta a * zeta b) • T a b

lemma M_symmetric (T : S.Stress) (hT : Conserved P H T) (a b) : M T a b=M T b a := by
  unfold M; rw [hT.symmetric a b]; simp [mul_comm]

/-- Tensor column convention. (The stress field requested below is Φ of these labels.) -/
def column (T : S.Stress) (K : M4) (a b : Axis) := ∑ i : Axis, ∑ j : Axis, (((K i a * K j b : ℝ) : ℂ)) • T i j

lemma column_apply_one (T : S.Stress) (a b) : column T 1 a b = T a b := by
  simp [column,Matrix.one_apply,mul_ite,ite_smul]

lemma M_Herm (T : S.Stress) (hT : Conserved P H T) (hR : R.Laws P H) (h : Tensorial R T) (a b) :
    S.adj H 4 timeAxis (M T a b)=M T a b := by
  unfold M
  rw [map_smulₛₗ]
  have ht : S.adj H 4 timeAxis (T a b)=column T theta a b := by
    rw [Table.adj,LinearMap.comp_apply,hT.real,← hR.signed]; exact h _ a b
  have hh (i j) : theta i j = if i=j then -eta i else 0 := by
    rw [theta_entry]; by_cases e : i=j
    · subst j; unfold eta; split <;> simp [*]
    simp [basis_eq,e]
  rw [ht]; simp only [column, hh]; simp [ite_mul,mul_ite,ite_smul]
  unfold zeta eta
  by_cases ha : a=timeAxis <;> by_cases hb : b=timeAxis <;> simp [ha,hb]

lemma column_mult (T : S.Stress) (A B : M4) (a b) : column (column T A) B a b = column T (A*B) a b := by
  simp_rw [column, Matrix.mul_apply, ofReal_mul, ofReal_sum, Finset.mul_sum, Finset.sum_mul,
    Finset.smul_sum, Finset.sum_smul, smul_smul]
  let f (i j x y : Axis) := (((B i a:ℂ)*(B j b:ℂ))*((A x i:ℂ)*(A y j:ℂ))) • T x y
  have he : (∑ i, ∑ j, ∑ x, ∑ y, f i j x y)=(∑ x, ∑ y, ∑ j, ∑ i, f i j x y) := by
    have hm : (∑ p : Axis × Axis, ∑ q : Axis × Axis, f p.1 p.2 q.1 q.2) = ∑ q : Axis × Axis, ∑ p : Axis × Axis, f p.1 p.2 q.1 q.2 := Finset.sum_comm
    simp only [Fintype.sum_prod_type] at hm
    rw [hm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_comm
  refine he.trans (Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_)
  dsimp only [f]; simp only [ofReal_mul]; ring_nf

/-- The rank action appearing below really is the infinitesimal action of the
chosen label representation, along any differentiable Lorentz curve. -/
theorem rank_derivative (hR : R.Laws P H) (X : Spins S) (h : X.Descends R H) (d : ℕ)
    {V : M4} {c : ℝ → Lorentz} (hc : c 0=1) (hv : HasDerivAt (fun t => mat (c t)) V 0) (v : S.Field d) :
    tangent V ∧ HasDerivAt (fun t => X.shell d (c t) v) (rankAction R d V v) 0 := by
  have hr := rotation_port R hR
  obtain ⟨W, hW, hw, hy⟩ := (along_spins R d hr c hv.differentiableAt).2
  rw [hc,mat_one,one_mul] at hw
  obtain rfl := hw.unique hv
  refine ⟨hW, ?_⟩
  simp_rw [matches_shell R X h]
  simp only at hy
  rw [hc,spins_one R d hr,one_mul] at hy
  exact on_field hy _


lemma rank_boost_formula (R : Rotation S) (d : ℕ) (i : SpaceAxis) (v : S.Field d) :
    rankAction R d (B i) v = (-I) • R.lie d (Ortho.plane timeAxis i.castSucc) v := by rw [rank_B]; rfl

def speedTensor (T : S.Stress) (K : M4) (a b : Axis) :=
    (∑ i : Axis, (K i a : ℂ) • T i b) + ∑ j : Axis, (K j b : ℂ) • T a j

lemma column_speed (T : S.Stress) {K : ℝ → M4} (hk : K 0=1) {V : M4} (hv : HasDerivAt K V 0)
    (a b : Axis) : HasDerivAt (fun t => column T (K t) a b) (speedTensor T V a b) 0 := by
  have hp (i j : Axis) : HasDerivAt (fun t => K t i j) (V i j) 0 :=
    let Z : M4→L[ℝ] ℝ := LinearMap.toContinuousLinearMap {
      toFun m := m i j, map_add' _ _ := rfl, map_smul' _ _ := rfl }
    HasFDerivAt.comp_hasDerivAt (f := K) (f' := V) 0 Z.hasFDerivAt hv
  have hd (i j : Axis) := ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hp i a).fun_mul (hp j b))
  unfold column; refine (HasDerivAt.congr_deriv
    (HasDerivAt.fun_sum (fun i (_ : i∈(Finset.univ : Finset Axis)) => HasDerivAt.fun_sum fun j (_ : j∈(Finset.univ : Finset Axis)) =>
      (hd i j).smul_const (T i j))) ?_)
  rw [hk]
  simp [Matrix.one_apply, ite_mul, mul_ite, add_smul, ite_smul, Finset.sum_add_distrib,speedTensor]

lemma speedE (T : S.Stress) (hR : R.Laws P H) (h : Tensorial R T) (V : Ortho.Skew) (a b) :
    R.lie 4 V (T a b) = speedTensor T V.val a b := by
  have he := hR.infinitesimal 4 V (T a b)
  simp_rw [h _ a b] at he
  refine he.unique (column_speed T (K:=fun t => (Ortho.oneParameter V t).val) ?_ ?_ _ _)
  · change NormedSpace.exp ((0 : ℝ) • V.val)=1; simp
  change HasDerivAt (fun t : ℝ => NormedSpace.exp (t • V.val)) V.val 0
  simpa using! hasDerivAt_exp_smul_const V.val (0 : ℝ)

lemma boost_scale (a i : Axis) {X : M4} (h : boostLike X) :
    zeta a * (-I) * ((X * theta) i a:ℂ) = zeta i * (X i a:ℂ) := by
  have he := congr_fun (congr_fun h.2 i) a
  rw [theta_left,Matrix.neg_apply,theta_right] at he
  rw [theta_right]; unfold zeta
  by_cases ha : a=timeAxis <;> by_cases hi : i=timeAxis <;>
    simp only [ha,hi,↓reduceIte] at he ⊢
  · simp [show X timeAxis timeAxis=0 by linarith [he]]
  · simp
  · simp
  simp [show X i a=0 by linarith [he]]

lemma speedM (T : S.Stress) (hR : R.Laws P H) (h : Tensorial R T) (k : SpaceAxis) (a b) :
    rankAction R 4 (B k) (M T a b) = speedTensor (M T) (B k) a b := by
  rw [M,map_smul, rank_boost_formula, speedE T hR h]; unfold speedTensor
  rw [← BQ k]
  simp only [M, smul_add,Finset.smul_sum,smul_smul]
  have he (a i : Axis) := boost_scale a i (B_boostLike k)
  congr 1
  · refine Finset.sum_congr rfl fun i _ => congr_arg (· • T i b) ?_
    calc _ = -zeta b * (zeta a * -I * ((B k*theta) i a:ℂ)) := by ring
         _ = _ := by rw [he]; ring
  refine Finset.sum_congr rfl fun i _ => congr_arg (· • T a i) ?_
  calc _ = -zeta a * (zeta b * -I * ((B k*theta) i b:ℂ)) := by ring
       _ = _ := by rw [he]; ring

lemma column_var {T : ℝ → S.Stress} {U : S.Stress} (hp : ∀ a b,
    HasDerivAt (fun t => T t a b) (U a b) 0) (A : M4) (a b : Axis) :
    HasDerivAt (fun t => column (T t) A a b) (column U A a b) 0 := by
  unfold column; refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
  exact (hp i j).const_smul (((A i a * A j b:ℝ):ℂ))

variable {X : Spins S} {Q : Wightman S} {Y U : Table L} {F : Waves S} {W : Surface S}
  {D : ∀ n, Blanket n} {Z : W.Aurora D}

lemma boost_M (T : S.Stress) (hR : R.Laws P H) (h : Tensorial R T)
    (k : SpaceAxis) (hx : X.Descends R H) (s : ℝ) (a b : Axis) :
    X.shell 4 (boost k s) (M T a b) = column (M T) (mat (boost k s)) a b := by
  let N := rankAction R 4 (B k)
  let y (a b : Axis) := fun t => column (M T) (mat (boost k t)) a b
  have hd a b : HasDerivAt (y a b) (N (M T a b)) 0 := by
    dsimp only [N]; rw [speedM T hR h]
    exact column_speed _ (K:=fun t => mat (boost k t)) (by simp only [boost, Ray.boost_start, mat_one])
      (mat_boost k) _ _
  have hY (s : ℝ) : HasDerivAt (y a b) (N (y a b s)) s := by
    have he := (column_var (T:=fun t a b => column (M T) (mat (boost k t)) a b)
      (U := fun a b => N (M T a b)) hd (mat (boost k s)) a b).scomp_of_eq s
      ((hasDerivAt_id' s).sub_const s) (by simp)
    simp only [one_smul] at he
    simp_rw [Function.comp_def,column_mult,← mat_mul,boost,← Ray.boost_add,sub_add_cancel] at he
    refine he.congr_deriv ?_
    simp only [column,y, boost, map_sum,map_smul]
  let z := fun t => X.shell 4 (boost k t) (M T a b)
  have hz (s : ℝ) : HasDerivAt z (N (z s)) s := by
    dsimp only [z]; simp_rw [matches_shell R X hx,boost_spins R (rotation_port R hR)]
    exact on_field (eb_left R 4 k s) _
  have he : z 0=y a b 0 := by
    simp only [z,y,boost,Ray.boost_start,mat_one,column_apply_one]
    apply S.pin_inj; rw [← hx.ties,hx.identity]
  exact congr_fun (ODE_solution_unique_univ (s:=fun _ => univ) (fun (_ : ℝ) => N.lipschitz.lipschitzOnWith)
    (fun t => ⟨hz t,mem_univ _⟩) (fun t => ⟨hY t,mem_univ _⟩) he) s

lemma space_scale (a i : Axis) {X : M4} (h : theta*X=X*theta) :
    zeta a * (X i a:ℂ)=zeta i * (X i a:ℂ) := by
  have he := congr_fun (congr_fun h i) a
  rw [theta_left,theta_right] at he
  unfold zeta; split_ifs with ha hi hi
  · rfl
  · rw [if_pos ha,if_neg hi] at he
    simp [show X i a=0 by linarith [he]]
  · rw [if_neg ha,if_pos hi] at he
    simp [show X i a=0 by linarith [he]]
  rfl

lemma rotate_M (T : S.Stress) (h : Tensorial R T) (A : Ortho) (hp : Lorentz.spatialTurn A) (a b) :
    R.act 4 A (M T a b) = column (M T) A.val a b := by
  simp_rw [M,map_smul,h A a b,column, M,ofReal_mul, Finset.smul_sum,smul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => congr_arg (· • T i j) ?_
  calc _ = -(zeta a * (A.val i a:ℂ)) * (zeta b * (A.val j b:ℂ)) := by ring
       _ = _ := by rw [space_scale a i (space_parity A hp),space_scale b j (space_parity A hp)]; ring

lemma transform_M (T : S.Stress) (hR : R.Laws P H) (h : Tensorial R T)
    (hx : X.Descends R H) (g : Lorentz) (a b) : X.shell 4 g (M T a b) = column (M T) (mat g) a b := by
  let ok (g : Lorentz) := ∀ a b : Axis, X.shell 4 g (M T a b)=column (M T) (mat g) a b
  have hm (g k : Lorentz) (hg : ok g) (hk : ok k) : ok (g*k) := by
    intro a b
    have he (v : S.Field 4) : X.shell 4 (g*k) v = X.shell 4 g (X.shell 4 k v) := by
      apply S.pin_inj; rw [← hx.ties,← hx.ties,← hx.ties,hx.representation]
    rw [he,hk,mat_mul,← column_mult]
    unfold ok at hg; simp only [column,map_sum,map_smul]; simp_rw [hg]; rfl
  have he (a s) : ok (boost a s) := boost_M T hR h a hx s
  have ho : ok (.room (orientation g) (oriented g)) := by
    intro a b; rw [hx.spatial,mat_room]; exact rotate_M T h _ (oriented g) _ _
  have hu := hm _ _ (he 0 (b0 g)) (hm _ _ (he 1 (b1 g)) (hm _ _ (he 2 (b2 g)) ho))
  rw [factors g] at hu; exact hu a b

/-- The stress as a tested operator on the common domain. -/
def fieldM (Q : Wightman S) (T : S.Stress) (a b : Axis) := Q.operators.field (S.pin 4 (M T a b))
lemma TM (Q : Wightman S) (T : S.Stress) (a b) (f : Test4) : fieldM Q T a b f =
    (-zeta a * zeta b) • Q.operators.field (S.pin 4 (T a b)) f := by simp only [fieldM, M, map_smul, LinearMap.smul_apply]

theorem tensor_lorentz (hc : FieldCore W R H Q) (hR : R.Laws P H) (T : S.Stress) (h : Tensorial R T)
    (g : Poincare) (f : Test4) (a b : Axis) (x : Q.operators.domain) :
    Q.action.V g (fieldM Q T a b f x).val =
      ((∑ i : Axis, ∑ j : Axis, (((mat g.Λ i a * mat g.Λ j b : ℝ) : ℂ)) • fieldM Q T i j (Joint.push g f))
        ⟨Q.action.V g x.val,hc.covariance.domain g x.property⟩).val := by
  unfold fieldM; rw [hc.covariance.covariance,hc.letters.ties,transform_M T hR h hc.letters]; simp [column]

theorem tensor_herm (hc : FieldCore W R H Q) (hR : R.Laws P H) (T : S.Stress)
    (hT : Conserved P H T) (h : Tensorial R T) (f : Test4) (a b : Axis) (u v : Q.operators.domain) :
    inner ℂ (fieldM Q T a b f u).val v.val = inner ℂ u.val (fieldM Q T a b (Probe.bar f) v).val := by
  unfold fieldM; rw [hc.adj _ f u v, hc.induced _ _, M_Herm T hT hR h]

/-- Minus partial derivative on test. -/
def partialProbe (a : Axis) (f : Test4) := -(∂_{basis a} f)
lemma eucl_partial (a : Axis) (f : Test4) : probeAxis a f = wick a • partialProbe a f := by
  simp only [probeAxis,partialProbe,smul_neg,neg_smul]

theorem tensor_conserved (hc : FieldCore W R H Q)
    (hu : U.Hierarchy) (hs : S.Symmetric) (hp : P.Inclusions S) (hv : P.Derivatives U)
    (hF : F.Region U) (hZ : Z.FullBody F) (ht : Bid.cones W)
    (T : S.Stress) (hT : Conserved P H T) (b : Axis) (f : Test4) :
    (∑ a : Axis, (eta a : ℂ) • fieldM Q T a b (partialProbe a f)) = 0 := by
  have he (a : Axis) : (eta a : ℂ) • fieldM Q T a b (partialProbe a f) =
      zeta b • Q.operators.field (S.pin 5 (P.deriv 4 a (T a b))) f := by
    rw [TM,derivative_domain P hu hs hp hv hF hZ ht hc a 4 (T a b),eucl_partial,map_smul,
      smul_smul,smul_smul]
    congr 1; unfold eta zeta wick; by_cases ha : a=timeAxis <;> by_cases hb : b=timeAxis <;> simp [ha,hb]
  simp_rw [he]; rw [← Finset.smul_sum,← LinearMap.sum_apply,← map_sum,← map_sum,hT.divergence]; simp
end YM.EveryPhase.Stress
