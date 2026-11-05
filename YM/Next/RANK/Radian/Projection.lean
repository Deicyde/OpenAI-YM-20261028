import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import YM.Next.RANK.Promises


/-!
# Through the low arc

Use derivative-movement stencil test (W), row absolute fine→coarse.
Pencils as operators on literal periodic cochains. Here the projection order
is charged pre-L against all funded heights. No Fourier tail assertions. Need
this on ANY data so that reading the cumulative whole kernel columns is bounded.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric Beamer Lattice Prayer VectorFourier Finset
open Atlas Normal Perch Wall CellsInt Function
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace

variable {H : Gauge} {P : Schedule} {n k p d L i' : ℕ}
variable (A : AtlasData H P p) {R S Z : ℝ}

def wall_chart (v : Chamber H P k p→ℝ) : Horizon H:= v ∘ body (k:=k) 0
def logic (v : Chamber H P k p →ℝ) (j : ℕ) (M : ℝ) := ∀ i : Degree H,i.degree=j→ ‖gesture i (wall_chart v)‖ ≤ M

private lemma jumps_move {V : Type*} [AddCommGroup V] (F : Cover→V) (u : Cover) (j : ℕ) (t : Fin j→ Axis) : jumps j t (fun p=>F (u+p))=(fun p=> jumps j t F (u+p)):= by
  induction j generalizing F with | zero=>rfl | succ n h=>
  rw [jumps,show stepValue (fun p=>F (u+p)) (t 0)= _ from (show _ = fun p=> stepValue F (t 0) (u+p) from funext fun x=> by simp [stepValue,add_assoc]),h];rfl
lemma summoned (v : Chamber H P k p→ℝ) (M : ℝ) (j : ℕ) (x : Cover) (hv : logic v j M) (i : Degree H) (hp : i.degree=j): ‖gesture i (fun p=>v (body x p))‖≤M:= by
  let f (z : Cover) := v (body 0 (z,i.a,i.paint))
  change ‖jumps _ i.layout _ i.point‖ ≤ M
  have hl z:v (body 0 (x+z,i.a,i.paint))=v (body x (z,i.a,i.paint)):=by simp [body]
  rw [show (fun z=>v (body x (z,i.a,i.paint)))=(fun z=>f (x+z)) from funext fun z=>(hl z).symm,jumps_move]
  exact hv {i with point:=x+i.point} hp
lemma shuttered (v : Chamber H P k p→ℝ) (h : shutter (wall_chart v)) (x : Cover) : shutter (fun p=> v (body x p)):= by
  let g:= fun (z : Address H)=> v (body x z)
  have hp (a b : Axis) y: polar g a b y=polar (wall_chart v) a b (x+y):= by
    unfold polar; split_ifs
    all_goals simp [Beamer.light,g,body,wall_chart]
  intro a b c; ext1 y; change _=0; specialize h a b c; have hh:=congr_fun h (x+y)
  simp only [Pi.add_apply,stepValue ]
  simp_rw [show (fun z=> v (body x z))=g from rfl,hp, ← add_assoc];exact hh

def hopP (i : ℕ) (f : Chamber H P i p →ℝ) (a : Chamber H P (i+1) p) := ∑ j,(A.path i a j).re * f j

structure Train (A : AtlasData H P p) (i d : ℕ) (R : ℝ) : Prop where
  pulses f v : ((A.path i f v).re:ℂ)=(A.path i f v)
  runs (f : Chamber H P i p→ℝ) : shutter (wall_chart f) → shutter (wall_chart (hopP A i f))
  optic j : j≤ d-1 → ∀ f v, 0 ≤ v → logic f j v → logic (hopP A i f) j (v*R/(P.a i/P.a (i+1))^(j+2))

lemma ends (T : Train A i' d R) {h : i'<k} (hh : ∀ f z, ((lines A _ (show i'+1≤k from h) f z).re:ℂ)=lines A _ h f z) (f z):
    lines A _ h.le f z=(∑ j, (lines A (i'+1) h f j).re*(A.path i' j z).re : ℝ):= by
  have he f : lines A i' h.le f = Finsupp.linearCombination ℂ (A.path i') (lines A (i'+1) h f):= by unfold lines;rw [Nat.decreasingInduction_succ_left]
  rw [he,Finsupp.linearCombination_apply_of_mem_supported ℂ (s:=univ) (by simp)]
  simp only [Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul, hh,T.pulses]
lemma lit_path (h : i'≤k) (V : ∀ i,i'≤ i → i<k → Train A i d R) f z : ((lines A i' h f z).re:ℂ)=lines A i' h f z:= by
  induction h using Nat.decreasingInduction generalizing f with
  | self=> unfold lines; rw [Nat.decreasingInduction_self]; by_cases f=z <;> simp [ *]
  | of_succ i h IH=>
    rw [ends A (V i le_rfl h) (h:=h) (fun f' p=> ?_) f z];simp
    exact IH (fun i hi=>V i ((Nat.le_succ _).trans hi)) f' p

lemma back (f : Chamber H P k p →ℝ) (x : Cover) (z : Address H): Wall.field A (le_refl k) x f z=f (body x z) := by
  unfold Wall.field Wall.liner lines; rw [Nat.decreasingInduction_self]; simp [Finsupp.single_apply, apply_ite]
lemma wheelPath (h : i'<k) (f : Chamber H P i' p →ℝ) (V : ∀ i,i' ≤ i → i< k → Train A i d R) x : Wall.field A h.le x f= Wall.field A (show i'+1≤k from h) x (hopP A i' f):= by
  unfold Wall.field; ext1 z; simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  let E i:= (A.path i)
  let T i:=lines A (i'+1) (show i'+1≤k from h) (body x z) i
  have hp j:liner A h.le x z j=∑ k,(T k).re*(A.path i' k j).re:= by rw [liner,ends A (V i' le_rfl h) (hh:=fun i j=>lit_path A h (fun k hk=> V k ((Nat.le_succ _).trans hk)) i j)];simp;rfl
  simp_rw [hp,hopP,mul_sum,Finset.sum_mul]; rw [Finset.sum_comm];apply sum_congr rfl; intro i _;apply sum_congr rfl;intro j _; change _=(_ * _)*(T i).re;ring
end YM.Next.Rank.Radian
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric Beamer Lattice Prayer VectorFourier Finset
open Atlas Normal Perch Wall CellsInt Function
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace

variable {H : Gauge} {P : Schedule} {n k i p d L : ℕ}
variable (A : AtlasData H P p) {R S Z : ℝ}

lemma tracking (h : i≤k) (V : ∀ j,i≤j→j<k→Train A j d R) (s : Chamber H P i p→ℝ) (he : shutter (wall_chart s)) (x : Cover) : shutter (Wall.field A h x s):= by
  induction h using Nat.decreasingInduction with
  | self=> rw [show Wall.field A _ x s=(fun p=>s (body x p)) from funext fun z=> back A s x z]; exact shuttered _ he x
  | of_succ i h ih=>rw [wheelPath A h s V]; exact ih (fun j hj=> V j ((Nat.le_succ i).trans hj)) _ ((V _ le_rfl h).runs s he)

lemma riveting (h : i≤k) (V : ∀ j,i≤ j → j< k→Train A j d R) (u : ℝ) (hu : 0≤u) (hv : 1≤R) (L : Degree H) (hp : L.degree ≤ d-1) (x : Cover)
    (F : Chamber H P i p →ℝ) (he : logic F L.degree u) :
    amount (P.a i / P.a k) L * ‖gesture L (Wall.field A h x F)‖ ≤ R^(k-i) * u := by
  induction h using Nat.decreasingInduction generalizing u with
  | self=> rw [div_self (P.a_pos _ |>.ne'),amount,one_pow,one_mul,Nat.sub_self,pow_zero,one_mul,show Wall.field A _ x F=(fun i=>F (body x i)) from funext fun z=> back A F x z]; exact summoned _ _ _ _ he _ rfl
  | of_succ i h ih=>
    rw [wheelPath A h F V]
    let r:= P.a i/P.a (i+1); have hr:0<r:= div_pos (P.a_pos _) (P.a_pos _); let D:=amount r L;have hh:0<D:=pow_pos hr _
    let t (k):= P.a k; let q:=u*R/D; have ht:0≤q:=div_nonneg (mul_nonneg hu (zero_le_one.trans hv)) hh.le
    have hz:= ih (fun j hj=> V j ((Nat.le_succ i).trans hj)) q ht _ ((V _ le_rfl h).optic _ hp F _ hu he)
    rw [show amount (P.a i / P.a k) L=D* amount (P.a (i+1)/P.a k) L from ?_,mul_assoc]; swap
    · unfold D amount r; rw [← mul_pow]; congr 1; field_simp [(P.a_pos (i+1)).ne', (P.a_pos k).ne']
    apply (mul_le_mul_of_nonneg_left hz hh.le).trans_eq; rw [show k-i=k-(i+1)+1 by omega,pow_succ]; unfold q;field_simp
private lemma remote (F : Chamber H P k p→ℝ) (g : ∀ i, ‖F i‖≤1) n : logic F n (2^n):= by
  intro a ha
  have ht (t : Cover →ℝ) (n : ℕ) (Q v) (C : ℝ) (h : ∀ i, ‖t i‖≤C) : ‖jumps n Q t v‖≤ 2^n*C:= by
    induction n generalizing t C with
    | zero=> simpa [jumps] using h v
    | succ n Ih=> rw [jumps];apply le_trans (b:= 2^n*(C+C)); exact Ih _ _ _ (fun v=> (norm_sub_le ..).trans (add_le_add (h _) (h _)));apply le_of_eq; rw [pow_succ];ring
  rw [← ha,←mul_one (2^a.degree : ℝ)]; exact ht _ _ _ _ _ (fun _=>g _)
lemma observatory (h : i≤k) (hk : 1≤R) (V : ∀ j,i≤j→j<k→Train A j d R) (L : Degree H) (hl : L.degree ≤ d-1) (x : Cover) :
    amount (P.a i/P.a k) L * (∑ j,‖gesture L (fun v=>liner A h x v j)‖) ≤ R^(k-i)*2^d := by
  let F j:= gesture L (fun v=>liner A h x v j)
  let u (i) := if 0≤F i then (1:ℝ) else -1
  have he : gesture L (Wall.field A h x u)= ∑ i,‖F i‖:= by
    rw [Wall.field,_root_.map_sum]; apply sum_congr rfl;intro i _; rw [map_smul]; change u i * F i= _
    unfold u; split
    · rename_i h; rw [Real.norm_of_nonneg h,one_mul]
    rename_i hu; rw [Real.norm_eq_abs, abs_of_nonpos (le_of_not_ge hu), neg_one_mul]
  have ht j: ‖u j‖≤1:=by unfold u;split <;>simp
  have hy:= riveting A h V _ (show 0 ≤ (2:ℝ)^L.degree by positivity) hk L hl x u (remote u ht _); rw [he,Real.norm_of_nonneg (Finset.sum_nonneg fun i _=> norm_nonneg _)] at hy; apply hy.trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (pow_nonneg (zero_le_one.trans hk) _)
-- give Fell receipt
lemma flown {P : RG.Levels H} (A : AtlasData H P.S p) (b : ℝ) (n K k : ℕ) (hr : 1≤R)
    (H : ∀ j,Station.middle P b k≤ j → j<k→Train A j d R)
    (he : R^(k-Station.middle P b k) * 2^d ≤ fraction n K (clim P k))
    (L : ∀ j T,((A.κ k|>.cov j T).re:ℂ)=(A.κ k).cov j T)
    (q : ∀ i j, (((A.κ (Station.middle P b k)).cov i j).re:ℂ)=(A.κ (Station.middle P b k)).cov i j)
    (C : ∀ i, shutter (wall_chart (fun j=>((A.κ (Station.middle P b k)).cov i j).re)))
    (hQ : ∀ i j, |((A.κ (Station.middle P b k)).cov i j).re| ≤ fraction n K (clim P k)) : Fell A (Station.before P b k) d (stretch P b k) (fraction n K (clim P k)):=
  ⟨L,q,lit_path A _ H,C,fun _ h=> tracking A _ H _ h,fun x y hp=> (observatory A _ hr H y hp x).trans he,hQ⟩
end YM.Next.Rank.Radian
