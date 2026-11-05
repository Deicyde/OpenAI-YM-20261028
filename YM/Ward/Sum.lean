import YM.Ward.Plants


/-!
# Raw charge sums after normalization P=cD

Input line values for all quotient labels. Finite-dimensional λ over filtered levels;
no Lie reps assumed. Prove jets from comm D at all arities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Ward
open Set Function Filter Analysis Table
open scoped Topology ContDiff InnerProductSpace BigOperators
variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

abbrev SpinRows (S : Table L) := ∀ d : ℕ, Ortho.Skew →ₗ[ℝ] (S.Field d →ₗ[ℂ] S.Field d)

variable (W : DiffPlan S) (T : SpinRows S)

def turns (K : Ortho.Skew) (p : S.Tag) : S.Tag := ⟨p.1,T p.1 K p.2⟩

def disc (q : Fin n → S.Tag) (x : Points n) := S.useAt S x q

def angular (q : Fin n → S.Tag) (K : Ortho.Skew) (x : Points n) :=
    ∑ i, (disc (update q i (turns T K (q i))) x +
         ∑ b : Axis, M4.move K.val (x i) b • disc (update q i (rise W b (q i))) x)

def commutes := ∀ d (t : Ortho.Skew) b (p : S.Field d),
    W.deriv d b (T d t p)+ (∑ i : Axis, (t.val i b:ℂ) • W.deriv d i p)= T (d+1) t (W.deriv d b p)

def onLine (a : Axis) (x : Points n) := ∀ i : Fin n, ∃ t : ℝ, x i=t • basis a

def Collinear := ∀ (a : Axis) (n : ℕ) (K : Ortho.Skew) (q : Fin n → S.Tag) (x : Points n),
    x∈conf _ → onLine a x → angular W T q K x=0

lemma fromD (h : S.Hierarchy) (hp : W.Derivatives S) {x : Points n} (hx : x∈conf _) (i : Fin n) a (q : Fin n → S.Tag) :
    Analysis.D (Points.direction i a) (disc q) x=disc (update q i (rise W a (q i))) x := by
  rw [← show (fun y => S.useAt S y (update q i (⟨(q i).1,(q i).2⟩ : S.Tag))) = disc q from
    funext fun y => by rw [show update q i ⟨_,_⟩ = q from update_eq_self ..]; rfl]
  exact (W.derivative_slot hp h.laws.toSymmetric h.smooth hx i q (q i).2 a).symm

lemma cont_disc (h : S.Hierarchy) (q : Fin n → S.Tag) {x : Points n} (hx : x∈conf n) : ContDiffAt ℝ ∞ (disc q) x :=
    ((S.class_smooth S h.smooth q) _ hx).contDiffAt ((conf_open _).mem_nhds hx)

/-! Evaluate one tag at one slot, Heterogeneous, use arbitrary contexts. -/
private def dec {d k : ℕ} (h : d=k) : S.Field d→ₗ[ℂ] S.Field k := h ▸ LinearMap.id
private lemma dec_eq {d k : ℕ} (h : d=k) (p : S.Field d) : dec h p=cast (congr_arg (Field S) h) p := by subst k; rfl

def here (q : Fin n → S.Tag) (x : Points n) (i : Fin n) (d : ℕ) : S.Field d →ₗ[ℂ] ℂ := by
  classical
  let w (p : S.Field d) := update q i (⟨d,p⟩ : S.Tag)
  let t := w 0
  have hi : (t i).1=d := by simp [t,w]
  let f := (S.classMoment S (fun i => (t i).1) x).toLinearMap (fun i => (t i).2) i
  exact f.comp (dec hi.symm)

lemma takes (q : Fin n → S.Tag) (x) (i) (d : ℕ) (p : S.Field d) :
    here q x i d p = disc (update q i ⟨d,p⟩) x := by
  let t := update q i (⟨d,(0:S.Field d)⟩ : S.Tag)
  dsimp only [here]
  -- need classMoment heq congr, use d'= fixed
  have hi : d=(t i).1 := by simp [t]
  let V : S.Field (t i).1 := cast (congr_arg (Field S) hi) p
  have he : dec hi p = V := dec_eq ..
  let s := update (fun j => (t j).2) i V
  have hf : (fun j => (⟨(t j).1,s j⟩ : S.Tag))=update q i ⟨d,p⟩ := by
    funext j
    by_cases h : j=i
    · subst j; simp only [s,update_self]; exact Sigma.ext hi.symm (cast_heq _ p)
    simp [s,t,h]
  rw [← hf]; unfold disc useAt
  rw [LinearMap.comp_apply]; change ((S.classMoment S (fun i => (t i).1) x).toLinearMap _ i) (dec hi p)=_
  rw [he]; rfl

lemma born {i : Fin n} (q : Fin n → S.Tag) (k) : rise W k (q i) = ⟨(q i).1+1,W.deriv _ k (q i).2⟩ := rfl

def factor (i : Fin n) (b : Axis) (K : Ortho.Skew) : Points n →L[ℝ] ℝ := LinearMap.toContinuousLinearMap {
    toFun x := M4.move K.val (x i) b
    map_add' x y := congr_arg (fun p : E4 => p b) (map_add (Matrix.toEuclideanLin K.val) (x i) (y i))
    map_smul' c x := congr_arg (fun p : E4 => p b) (map_smul (Matrix.toEuclideanLin K.val) c (x i)) }
lemma fac (i : Fin n) (a j : Axis) k K : factor i a K (Points.direction k j)=if k=i then (K.val a j) else 0 := by
  change M4.move _ _ _=_
  by_cases h : k=i
  · subst k; simp [Points.direction]
  rw [if_neg h]; simp [Points.direction,Ne.symm h,M4.move]

lemma D_prod (c : Points n →L[ℝ] ℝ) (f : Points n → ℂ) (u x : Points n) (hf : DifferentiableAt ℝ f x) :
    D u (fun y => c y • f y) x=c u • f x + c x • D u f x := by
  unfold D; rw [fderiv_fun_smul c.differentiableAt hf,c.fderiv]; simp [add_comm]

theorem traverses (h : S.Hierarchy) (he : W.Derivatives S) (hc : commutes W T)
    {x : Points n} (hx : x∈conf _) (q : Fin n → S.Tag) (a : Axis) (k : Fin n) (K : Ortho.Skew) :
    let r := update q k (rise W a (q k))
    D (Points.direction k a) (angular W T q K) x= angular W T r K x := by
  intro r
  let t := Points.direction k a
  let comp (i) := disc (update q i (turns T K (q i)))
  let L (i) (b : Axis) := disc (update q i (rise W b (q i)))
  let y (i) (b) (z : Points n) := factor i b K z • L i b z
  let f (i) z := comp i z + ∑ b, y i b z
  have hu (i : Fin n) b : DifferentiableAt ℝ (L i b) x := (cont_disc h _ hx).differentiableAt (by simp)
  have hh i b : DifferentiableAt ℝ (y i b) x := (factor i b K).differentiableAt.smul (hu i b)
  have hz i : DifferentiableAt ℝ (comp i) x := (cont_disc h _ hx).differentiableAt (by simp)
  have hp i : DifferentiableAt ℝ (f i) x := (hz i).add (DifferentiableAt.fun_sum fun b hb => hh i b)
  have hm (i : Fin n) : D t (f i) x=D t (comp i) x+∑ b, D t (y i b) x := by
    simp only [f,D,fderiv_fun_add (hz i) (DifferentiableAt.fun_sum (fun b hb => hh i b)),
      fderiv_fun_sum (fun b hb => hh i b),_root_.sum_apply, _root_.add_apply]
  change fderiv ℝ (fun z => ∑ i, f i z) x t= _
  rw [fderiv_fun_sum (fun i hi => hp i),_root_.sum_apply]; unfold angular
  apply Finset.sum_congr rfl; intro i hi
  change D t (f i) x=_; rw [hm]
  by_cases hv : i=k
  · subst i; simp only [r,update_self,update_idem]
    -- derivative comm produces orbital cancel
    have hvb b : D t (y k b) x=(K.val b a) • disc (update q k (rise W b (q k))) x + factor k b K x • disc
        (update q k (rise W b (rise W a (q k)))) x := by
      unfold y
      rw [D_prod _ _ _ x (hu k b)]
      dsimp only [t,L]
      rw [fac,if_pos rfl,fromD W h he hx,update_self, update_idem]; unfold rise
      simp only
      rw [W.abelian h.laws.toSymmetric he h.smooth]
    simp_rw [hvb,Finset.sum_add_distrib,← add_assoc]
    congr 1
    unfold comp; rw [fromD W h he hx,update_self,update_idem]; unfold turns rise; simp only
    simp_rw [← takes,Complex.real_smul]
    rw [← hc _,map_add,map_sum]; simp
  have hu' : r i=q i := update_of_ne hv ..
  rw [hu']; congr 1
  · unfold comp; rw [fromD W h he hx,update_of_ne (Ne.symm hv),update_comm (show k≠i from (Ne.symm hv))] -- order check
  apply Finset.sum_congr rfl; intro b hb
  unfold y
  rw [D_prod _ _ _ x (hu i b)]
  dsimp only [L,t]; rw [fac,if_neg (Ne.symm hv),zero_smul,zero_add,fromD W h he hx,update_of_ne (Ne.symm hv),update_comm (show k≠i from (Ne.symm hv))]
  rfl

lemma ac (h : S.Hierarchy) {x : Points n} (hx : x∈conf _) (K : Ortho.Skew) (q : Fin n → S.Tag) :
    ContDiffAt ℝ ∞ (angular W T q K) x := by
  have hm := cont_disc h q hx
  apply ContDiffAt.sum
  intro i hi; apply ContDiffAt.add (cont_disc h _ hx); apply ContDiffAt.sum
  exact fun b _ => (factor i b K).contDiff.contDiffAt.smul (cont_disc h _ hx)
end YM.Ward
