import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import YM.Ward.Rows




/-!
# Single-angular formal comparison function

radial = strict OS interpolation. θ arctan. Check coefficient analytic along θ.
V rotation sign. No need oneParameter complexification yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Ward
open Function Set Filter Analysis Table OS
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators ContDiff

namespace Circle
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def θ (p : PDE.V) := Real.arctan (p.2/p.1)
def r (p : PDE.V) := √(p.1^2+p.2^2)
def u (p : PDE.V) := -p.2 • PDE.e+p.1 • PDE.i

lemma helpful {p} (h : p∈PDE.side) : 0<p.1^2+p.2^2 := add_pos_of_pos_of_nonneg (pow_pos (show 0<p.1 from h) _) (sq_nonneg _)
lemma pos {p} (h : p∈PDE.side) : 0<r p := Real.sqrt_pos_of_pos (helpful h)
lemma uniform {p} (h : p∈PDE.side) : AnalyticAt ℝ θ p ∧ AnalyticAt ℝ r p := by
  refine ⟨ContDiffAt.analyticAt ?_,ContDiffAt.analyticAt ?_⟩
  · exact Real.contDiff_arctan.contDiffAt.comp p
      (contDiffAt_snd.div contDiffAt_fst (show p.1 ≠ 0 from LT.lt.ne' h))
  exact ((contDiffAt_fst.pow 2).add (contDiffAt_snd.pow 2)).sqrt (helpful h).ne'

def shift (p : PDE.V) (t : ℝ) := p+t • u p
@[simp] lemma gone p : shift p 0=p := by simp [shift]
lemma has (p) : HasDerivAt (shift p) (u p) 0 := by
  unfold shift; simpa using (ContinuousLinearMap.toSpanSingleton ℝ (u p)).hasDerivAt (x := 0) |>.const_add p
lemma transport {f : PDE.V → X} {x : PDE.V} (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t => f (shift x t)) (D (u x) f x) 0 := by
  have he : DifferentiableAt ℝ f (shift x 0) := by rw [gone];exact hf
  rw [D]
  simpa [Function.comp_def] using he.hasFDerivAt.comp_hasDerivAt (x := 0) (has x)

private lemma compass (p : PDE.V) : HasDerivAt (fun t => (shift p t).1) (-p.2) 0 ∧ HasDerivAt (fun t => (shift p t).2) p.1 0 := by
  have h₁ := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt 0 (has p)
  have h₂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt 0 (has p)
  simpa [u,PDE.e,PDE.i,Function.comp_def] using And.intro h₁ h₂
lemma vector {p} (hp : p∈PDE.side) : HasDerivAt (θ ∘ shift p) 1 0 ∧ HasDerivAt (r ∘ shift p) 0 0 := by
  have pt := (show 0<p.1 from hp)
  obtain ⟨a,b⟩ := compass p
  constructor
  · let f := fun z : ℝ => (shift p z).2/(shift p z).1
    have he : HasDerivAt f _ (0:ℝ) := b.div a (by simp [pt.ne'])
    have hh := (Real.hasDerivAt_arctan (f 0)).comp 0 he
    change HasDerivAt (Real.arctan ∘ f) _ _
    convert hh using 1 <;> try rfl
    simp [f]
    field_simp
  have hz := ((a.pow 2).add (b.pow 2)).sqrt (by simpa [Pi.add_apply] using (helpful hp).ne')
  change HasDerivAt (fun t => √((shift p t).1^2+(shift p t).2^2)) _ _
  convert hz using 1
  · simp
  simp only [Nat.cast_ofNat, gone, Nat.add_one_sub_one,pow_one]
  ring
end Circle

variable {G : Gauge} {L : Register G} {S : Table L} {a b : Axis}
variable (V : Chamber S a) (h : S.Hierarchy)
variable (T : SpinRows S)

/-- via generic normed algebra to avoid instance synthesis glitch at Field. -/
def LieTick {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (U : E→L[ℂ] E) (t : ℝ) := NormedSpace.exp (t • U)
theorem ticking {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (v : E) (U : E →L[ℂ] E) (t : ℝ) : AnalyticAt ℝ (fun t => LieTick U t v) t ∧ HasDerivAt (fun t => LieTick U t v) (LieTick U t (U v)) t := by
  let A := (ContinuousLinearMap.apply ℂ E v).restrictScalars ℝ
  refine ⟨(A.analyticAt _).comp ((NormedSpace.exp_analytic (𝕂 := ℝ) (t • U)).comp (f := fun i : ℝ => i • U) (ContinuousLinearMap.toSpanSingleton ℝ U |>.analyticAt _)),?_⟩
  exact A.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const U t)
lemma stuck {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : E) (U : E →L[ℂ] E) : LieTick U 0 v=v := by simp [LieTick]
def spin (p : S.Tag) (K : Ortho.Skew) (t : ℝ) : S.Tag :=
  let W : S.Field p.1→L[ℂ] S.Field p.1 := LinearMap.toContinuousLinearMap (T _ K)
  ⟨p.1, LieTick W t p.2⟩

variable {d e : ℕ}
abbrev clock (v : S.Field d) (K : Ortho.Skew) (t : ℝ) : S.Field d := (spin T ⟨d,v⟩ K t).2
lemma atClock (v : S.Field d) K t : AnalyticAt ℝ (clock T v K) t := by
  apply (ticking v (LinearMap.toContinuousLinearMap (T _ K)) t).1
lemma moveClock (v : S.Field d) K t : HasDerivAt (clock T v K) (clock T (T d K v) K t) t := by
  apply (ticking v (LinearMap.toContinuousLinearMap (T _ K)) t).2

def Q (K : Ortho.Skew) (a : Axis) (p : S.Tag × S.Tag) (x : PDE.V) := pair
  (spin T p.1 K (-Circle.θ x)) (spin T p.2 K (-Circle.θ x)) (Circle.r x • basis a)

@[simp] lemma stationary (p : S.Tag) K : spin T p K 0=p := by unfold spin; dsimp only; rw [stuck]
lemma launch {a b} (K : Ortho.Skew) (p) {t : ℝ} (h : 0<t) : Q T K a p (t,0)=F a b p (t,0) := by simp [Q,F,Circle.θ,Circle.r,lift,h.le]

def E (v : S.Field d) (w : S.Field e) (x) := pair (S := S) ⟨d,v⟩ ⟨e,w⟩ x

private lemma stars (H : Module.Basis (Fin (Module.finrank ℂ (S.Field d))) ℂ (S.Field d))
    (J : Module.Basis (Fin (Module.finrank ℂ (S.Field e))) ℂ (S.Field e)) (v : S.Field d) (w : S.Field e) x :
    E v w x = ∑ i, ∑ j, H.coord i v * J.coord j w * E (H i) (J j) x := by
  have ha (s : S.Field d) (t : S.Field e) : E s t x=here (q := ![(⟨d,0⟩:S.Tag),⟨e,t⟩])
      (points ![x,0]) (0:Fin 2) d s := by
    rw [takes]; unfold E pair; congr 1; funext i;fin_cases i <;> simp
  have hb (s : S.Field d) (t : S.Field e) : E s t x=here (q := ![(⟨d,s⟩:S.Tag),⟨e,0⟩])
      (points ![x,0]) (1:Fin 2) e t := by
    rw [takes]; unfold E pair; congr 1; funext i;fin_cases i <;> simp
  conv_lhs => rw [ha, ← H.sum_repr v, map_sum]
  apply Finset.sum_congr rfl; intro i hi
  rw [map_smul,← ha,hb]
  conv_lhs => rw [← J.sum_repr w,map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl; intro j hj
  rw [map_smul,← hb,mul_assoc]; rfl

abbrev sector (d) := Module.finBasis ℂ (S.Field d)
include V h
lemma htQ (K) (p : S.Tag × S.Tag) : AnalyticOnNhd ℝ (Q T K a p) PDE.side := by
  obtain ⟨⟨d,u⟩,⟨e,v⟩⟩ := p
  intro x hx
  change AnalyticAt ℝ (fun x => E (clock T u K (-Circle.θ x)) (clock T v K (-Circle.θ x)) (Circle.r x • basis a)) x
  simp_rw [stars (sector d) (sector e) (clock T u K _) (clock T v K _)]
  -- need selectively
  apply ContDiffAt.analyticAt; refine ContDiffAt.sum (fun i hi => ?_)
  apply ContDiffAt.sum; intro j hj
  let A : S.Field d →L[ℝ] ℂ := (LinearMap.toContinuousLinearMap ((sector (S := S) d).coord i)).restrictScalars ℝ
  let B : S.Field e →L[ℝ] ℂ := (LinearMap.toContinuousLinearMap ((sector (S := S) e).coord j)).restrictScalars ℝ
  obtain ⟨hθ,hr⟩ := Circle.uniform hx
  exact ((((A.analyticAt _).comp ((atClock T u K _).comp hθ.neg)).mul
    ((B.analyticAt _).comp ((atClock T v K _).comp hθ.neg))).mul
    ((radial V h ⟨d,sector (S := S) d i⟩ ⟨e,sector (S := S) e j⟩ (Circle.r x) (Circle.pos hx)).comp hr)).contDiffAt

lemma solves (K) (p : S.Tag × S.Tag) (x : PDE.V) (hx : x∈PDE.side) : PDE.law (left K T) (right K T) (Q T K a) p x=0 := by
  let H := htQ V h T K p
  have hv := Circle.transport ((H x hx).differentiableAt)
  suffices he : HasDerivAt (fun t => Q T K a p (Circle.shift x t))
      (-Q T K a (left K T p) x+-Q T K a (right K T p) x) 0 by
    unfold PDE.law; rw [PDE.vector (show PDE.C (Q T K a p) from fun x hx => (H x hx).contDiffAt) hx, ← Circle.u, hv.unique he]; ring
  clear H hv
  obtain ⟨⟨d,v⟩,⟨e,u⟩⟩ := p
  obtain ⟨hθ,hρ⟩ := Circle.vector hx
  let f (t : ℝ) := Circle.θ (Circle.shift x t)
  let Z (t : ℝ) := -f t
  let r (t : ℝ) := Circle.r (Circle.shift x t)
  have hr : 0 < r 0 := by unfold r;rw [Circle.gone]; exact Circle.pos hx
  let V' := T d K v
  let U' := T e K u
  let X (i) : S.Field d →L[ℝ] ℂ := (LinearMap.toContinuousLinearMap ((sector (S := S) d).coord i)).restrictScalars ℝ
  let Y (i) : S.Field e →L[ℝ] ℂ := (LinearMap.toContinuousLinearMap ((sector (S := S) e).coord i)).restrictScalars ℝ
  have hy : Z 0= -Circle.θ x := by simp [Z,f]
  have hl : r 0= Circle.r x := by simp [r]
  change HasDerivAt (fun t => E (clock T v K (Z t)) (clock T u K (Z t)) (r t • basis a))
    (- E (clock T V' K (-Circle.θ x)) (clock T u K (-Circle.θ x)) (Circle.r x • basis a)+
       - E (clock T v K (-Circle.θ x)) (clock T U' K (-Circle.θ x)) (Circle.r x • basis a)) 0
  rw [← hy,← hl]
  simp_rw [stars (sector d) (sector e) (clock T _ K _)]
  simp_rw [← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  apply HasDerivAt.fun_sum; intro i hi; apply HasDerivAt.fun_sum; intro j hj
  have he : HasDerivAt Z (-1) 0 := hθ.neg
  have hw : HasDerivAt (fun t => r t) 0 0 := hρ
  have hh (c : ℕ) (v : S.Field c) : HasDerivAt (fun t => clock T v K (Z t)) (-clock T (T c K v) K (Z 0)) 0 := by
    have hh := (moveClock T v K (Z 0)).scomp 0 he
    simpa only [neg_smul,one_smul,Function.comp_def] using hh
  have hV : HasDerivAt (fun t => X i (clock T v K (Z t))) (- X i (clock T V' K (Z 0))) 0 := by
    have hv := (X i).hasFDerivAt.comp_hasDerivAt 0 (hh d v)
    simpa only [map_neg, Function.comp_def] using hv
  have hU : HasDerivAt (fun t => Y j (clock T u K (Z t))) (- Y j (clock T U' K (Z 0))) 0 := by
    have hv := (Y j).hasFDerivAt.comp_hasDerivAt 0 (hh e u)
    simpa only [map_neg,Function.comp_def] using hv
  let g (q : ℝ) := E (sector (S := S) d i) (sector (S := S) e j) (q • basis a)
  have hg : HasDerivAt (g ∘ r) 0 0 := by
    have hA : AnalyticAt ℝ g (r 0) := radial V h ⟨d,_⟩ ⟨e,_⟩ _ hr
    simpa only [zero_smul] using hA.differentiableAt.hasDerivAt.scomp 0 hw
  change HasDerivAt (fun t => (X i (clock T v K (Z t))*Y j (clock T u K (Z t)))*g (r t))
    (-(X i (clock T V' K (Z 0))*Y j (clock T u K (Z 0))*g (r 0))+ -(X i (clock T v K (Z 0))* Y j (clock T U' K (Z 0))*g (r 0))) 0
  convert (hV.mul hU).mul hg using 1 <;> try rfl
  dsimp only [Pi.mul_apply,Function.comp_apply];ring

/-- Full proposed shortcut (after Line & P=cD & Flux/D commutator) analytic
along transverse AXES for point ket. Doesn't prove E's intermediary point spectral cone,
not needed. -/
lemma pure (W : DiffPlan S) (K : commutes W T) (Y : Collinear W T) -- add binder W
    (P : W.Derivatives S) (p : S.Tag) (x : E4) (hx : 0<x a) (j : b≠a) (t : ℝ) :
    AnalyticAt ℝ (fun s => spot V p (inc b x s)) t := by
  let y := 2*x a
  have hy : 0<y := by unfold y; positivity
  let z : PDE.V := (y,0)
  let k := Ortho.plane b a
  let u : S.Tag × S.Tag := (p,refl p a)
  have hv := htQ V h T k u z (show _ from hy)
  apply fires V h W P p x hx j (fun t : ℝ => Q T k a u (y,t)) (by
    exact hv.comp (f := fun t => (y,t)) (ContDiffAt.analyticAt (contDiffAt_const.prodMk contDiffAt_id))) _ t
  let R (u) := Q T k a u
  have hR i : PDE.C (R i) := fun z hz => ((htQ V h T k i) z hz).contDiffAt
  let G (u : S.Tag × S.Tag) := F a b u
  have hG i : PDE.C (G i) := Fu a b h i j
  let L i x := G i x-R i x
  have he i : PDE.C (L i) := PDE.C.diff (hG i) (hR i)
  have ht : ∀ i n t, 0<t → PDE.tower (PDE.law (left k T) (right k T) L i) n (t,0)=0 := by
    intro i n t h'
    have hp : EqOn (PDE.law (left k T) (right k T) L i) (PDE.law (left k T) (right k T) G i) PDE.side := by
      intro x hx
      exact (PDE.linear (left k T) (right k T) hG hR i hx).symm.trans (by
        change _-PDE.law _ _ (Q T k a) i x=_
        rw [solves V h T k i x hx, sub_zero])
    exact (PDE.vanishing hp n (show (t,0) ∈ PDE.side from h')).trans (realized a b j W T h P K Y i n t h')
  intro n
  have hg := PDE.sure (left k T) (right k T) he ht (fun i t ht => sub_eq_zero.mpr (launch T k i ht).symm) n y hy u
  have hm := PDE.diffJet (hG u) (hR u) n (show z∈PDE.side from hy)
  change PDE.tower (L u) n z=0 at hg
  have hh := sub_eq_zero.mp (show PDE.tower (G u) n z-PDE.tower (R u) n z=0 from hm.symm.trans hg)
  exact (PDE.actual (hG u) (x := z) hy n).trans (hh.trans (PDE.actual (hR u) (x := z) hy n).symm)
end YM.Ward
