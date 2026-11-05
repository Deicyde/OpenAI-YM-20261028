import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import YM.Analysis.Symmetric
import YM.AnalyticNext.CUBIC_MATCH.Lift.Count
import YM.Bid.Station


set_option warningAsError false

/-!
# Weighted expression algebra on the actual link-space

A pointwise kernel on the cover with its distinct anchor. `LocalRep`
will allow only homogeneous polynomials COMPATIBLE across all used tori (no
periodization loss, windings, repeated labels can all contribute). Sum-product
estimates here, ahead of moving the anchor to the third argument. Insist
on joint width, and never spend path-length at a `card Site c` discount.
For most price estimates use diagonal germs first and purchase permutations
later. Fin k rather than symmetric indexes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter Lattice Laurent RG Wilson Precision Exterior Tree Bid
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {n : Side} {k m : ℕ}
  {E F Z R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedRing R] [NormedAlgebra ℝ R]
  {ι μ : Type*}

abbrev Tone (G : Gauge) := TypeFace 1 × G.ColorIndex
abbrev Tap (G : Gauge) := Cover × Tone G
abbrev TapSet (G : Gauge) (k : ℕ) := Fin k → Tap G

/-- Use pos displacement. -/
def toneOf (i : Tap G) (x : Site n) (a : Dir G n) := a (wrap n i.1+x,i.2.1) i.2.2

def verse (x : Site n) (u : TapSet G k) (a : Fin k → Dir G n) : ℝ := ∏ i,toneOf (u i) x (a i)

def receive (A : TapSet G k → E) (x : Site n) (a : Fin k → Dir G n) := ∑' i, verse x i a • A i

def reachOf (u : TapSet G k) := ∑ i,size (u i).1

variable {θ C B : ℝ} {A : TapSet G k → E}

lemma reach_appended (x : TapSet G k × TapSet G m) : reachOf (Fin.appendEquiv k m x) = reachOf x.1 + reachOf x.2 := by
  unfold reachOf; rw [Fin.sum_univ_add]
  change ∑ i,size (Fin.append x.1 x.2 (Fin.castAdd m i)).1 + ∑ i,size (Fin.append x.1 x.2 (Fin.natAdd k i)).1 = _
  simp
lemma verse_appended (x : TapSet G k × TapSet G m) (z : Site n) (a : Fin (k+m) → Dir G n) :
    verse z (Fin.appendEquiv k m x) a=verse z x.1 (a ∘ Fin.castAdd m)*verse z x.2 (a ∘ Fin.natAdd k) := by
  unfold verse; rw [Fin.prod_univ_add]; change (∏ i, toneOf (Fin.append x.1 x.2 (Fin.castAdd m i)) z (a (Fin.castAdd m i))) *
    ∏ i, toneOf (Fin.append x.1 x.2 (Fin.natAdd k i)) z (a (Fin.natAdd k i)) =_
  apply congr_arg₂ (·*·)
  · exact Finset.prod_congr rfl fun i _ => congr_arg (fun T => toneOf T z (a (Fin.castAdd m i))) (Fin.append_left ..)
  exact Finset.prod_congr rfl fun i _ => congr_arg (fun T => toneOf T z (a (Fin.natAdd k i))) (Fin.append_right ..)

lemma tone_bounded (i : Tap G) (x : Site n) (a : Dir G n) : |toneOf i x a| ≤ ‖a‖ := by
  let b (c : G.ColorIndex) := EuclideanSpace.basisFun G.ColorIndex ℝ c
  have hv (w : G.Color) (d : G.ColorIndex) : |w d| ≤ ‖w‖ := by
    simpa only [b,EuclideanSpace.basisFun_inner,OrthonormalBasis.norm_eq_one,one_mul] using (abs_real_inner_le_norm (b d) w)
  exact (hv ..).trans (norm_le_pi_norm ..)
lemma verse_bounded (x : Site n) (i : TapSet G k) (a : Fin k → Dir G n) :
    |verse x i a| ≤ ∏ i, ‖a i‖ := by
  unfold verse; rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => tone_bounded ..)

def tapEquivOne (G : Gauge) : Tap G ≃ TapSet G 1 where
  toFun i _ := i
  invFun u := u 0
  left_inv i := rfl
  right_inv v := funext fun i => by fin_cases i; rfl

lemma reaches_one (x : Tap G) : reachOf (tapEquivOne G x)=size x.1 := by unfold reachOf; simp; rfl

lemma taps_decay (k : ℕ) (he : 0 < θ) : Summable (fun i : TapSet G k => wanes θ (reachOf i)) := by
  have h : Summable (fun i : Tap G => wanes θ (size i.1)) := by
    let e := Equiv.prodComm (Tone G) Cover
    apply e.summable_iff.mp
    apply (summable_prod_of_nonneg (fun i => (wanes_pos ..).le)).mpr; exact ⟨fun _ => wanes_summable he,.of_finite⟩
  have H : Summable (fun i : TapSet G 1 => wanes θ (reachOf i)) := by
    apply (tapEquivOne G).summable_iff.mp; exact h.congr (fun i => congr_arg _ (reaches_one i).symm)
  induction k with
  | zero => exact Summable.of_finite
  | succ k ih =>
    apply (Fin.appendEquiv k 1).summable_iff.mp; refine (Summable.mul_of_nonneg ih H
      (fun i => (wanes_pos ..).le) (fun i => (wanes_pos ..).le)).congr fun i => ?_
    change _=wanes _ (reachOf (Fin.appendEquiv _ _ i)); rw [reach_appended,wanes_splits]

lemma receive_norm (he : 0<θ) (h : Decay reachOf θ C A) (x : Site n) (a : Fin k → Dir G n) :
    Summable (fun i => ‖verse x i a • A i‖) := by
  have ha := h.summable_norm (taps_decay _ he)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ (ha.mul_left (∏ i, ‖a i‖))
  intro i; rw [norm_smul, Real.norm_eq_abs]; gcongr; exact verse_bounded ..

/-- torus-indexed unmasked coefficient reading. Anchor at a site and test
one field. -/
abbrev SiteRead (G : Gauge) (c : μ → Side) (E : Type*) := ∀ i,Site (c i) → Dir G (c i) → E

def LocalRep (c : μ → Side) (k : ℕ) (θ C : ℝ) (f : SiteRead G c E) := 0<θ ∧ 0≤C ∧
    ∃ A : TapSet G k → E, Decay reachOf θ C A ∧ ∀ p x a,f p x a=receive A x (fun _ => a)

namespace LocalRep
variable {c : μ → Side} {f g : SiteRead G c E} (h : LocalRep c k θ C f)

lemma rate (h : LocalRep c k θ C f) : 0<θ := h.1
lemma cash (h : LocalRep c k θ C f) : 0≤C := h.2.1

lemma raisePrice (h : LocalRep c k θ C f) (he : C≤B) : LocalRep c k θ B f := by
  obtain ⟨hp,h₁,A,h₂,e⟩ := h; exact ⟨hp,h₁.trans he,A,h₂.enlarge he,e⟩
lemma fits (h : LocalRep c k θ C f) {g : SiteRead G c E} (e : ∀ p x a,f p x a=g p x a) : LocalRep c k θ C g :=
    Eq.mp (congr_arg (LocalRep c k θ C) (funext fun i => funext fun x => funext fun a => e i x a)) h

lemma none (he : 0<θ) : LocalRep c k θ 0 (fun p _ (_a : Dir G (c p)) => (0:E)) :=
  ⟨he,le_rfl,0,(fun i => by simp), fun p x a => by simp [receive]⟩
lemma scaled (h : LocalRep c k θ C f) (u : ℝ) : LocalRep c k θ (|u| *C) (fun p x a => u • f p x a) := by
  obtain ⟨he,hC,A,hA,H⟩ := h
  refine ⟨he,mul_nonneg (abs_nonneg _) hC,u • A, hA.scaled _,fun p x a => ?_⟩
  dsimp only; rw [H]; unfold receive; rw [← tsum_const_smul'']; exact tsum_congr fun i => smul_comm ..
lemma negative (h : LocalRep c k θ C f) : LocalRep c k θ C (fun p x a => -f p x a) := by
  simpa only [abs_neg,abs_one,one_mul, neg_smul,one_smul] using h.scaled (-1)

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace Z] [CompleteSpace R]
lemma plus (h : LocalRep c k θ C f) (h' : LocalRep c k θ B g) : LocalRep c k θ (C+B) (fun p x a => f p x a+g p x a) := by
  obtain ⟨he,hC,A,hA,H⟩ := h
  obtain ⟨-,hB,A',hA',H'⟩ := h'
  refine ⟨he,add_nonneg hC hB,A+A',hA.plus hA',fun p x a => ?_⟩
  dsimp only; rw [H,H']; unfold receive; simp only [Pi.add_apply,smul_add]
  exact ((receive_norm he hA ..).of_norm.tsum_add (receive_norm he hA' ..).of_norm).symm
lemma minus (h : LocalRep c k θ C f) (h' : LocalRep c k θ B g) : LocalRep c k θ (C+B) (fun p x a => f p x a-g p x a) := by
  simp_rw [sub_eq_add_neg]; exact h.plus h'.negative
lemma fin (s : Finset ι) {F : ι → SiteRead G c E} {v : ι → ℝ} (he : 0 < θ) (h : ∀ i∈s,LocalRep c k θ (v i) (F i)) :
    LocalRep c k θ (∑ i∈s,v i) (fun p x a => ∑ i∈s,F i p x a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact none he
  | @insert i s hx ih =>
    obtain ⟨ha,hb⟩ := (Finset.forall_mem_insert ..).mp h
    simp_rw [Finset.sum_insert hx]; exact ha.plus (ih hb)

omit [CompleteSpace F] in
lemma linear_bound (h : LocalRep c k θ C f) (L : E →L[ℝ] F) (hp : 0≤B) (hl : ∀ x : E, ‖L x‖ ≤ B*‖x‖) :
    LocalRep c k θ (B*C) (fun p x a => L (f p x a)) := by
  obtain ⟨he,hC,A,hA,H⟩ := h
  refine ⟨he,mul_nonneg hp hC, L ∘ A,fun i => (hl _).trans ((mul_le_mul_of_nonneg_left (hA i) hp).trans_eq ?_),fun p x a => ?_⟩
  · rw [mul_assoc]
  dsimp only; rw [H]; unfold receive; rw [L.map_tsum (receive_norm he hA ..).of_norm]; exact tsum_congr fun i => L.map_smul _ _
omit [CompleteSpace F] in
lemma linear (h : LocalRep c k θ C f) (L : E →L[ℝ] F) : LocalRep c k θ (‖L‖*C) (fun p x a => L (f p x a)) :=
    h.linear_bound L (norm_nonneg _) fun u => L.le_opNorm u

lemma bilinear_bound (h : LocalRep c k θ C f) {g : SiteRead G c F} (h' : LocalRep c m θ B g)
    (L : E →L[ℝ] F →L[ℝ] Z) {b : ℝ} (hp : 0≤b) (hl : ∀ x : E, ∀ y : F, ‖L x y‖ ≤ b*‖x‖*‖y‖) :
    LocalRep c (k+m) θ (b*C*B) (fun p x a => L (f p x a) (g p x a)) := by
  obtain ⟨he,hC,A,hA,H⟩ := h
  obtain ⟨-,hB,A',hA',H'⟩ := h'
  let e := Fin.appendEquiv (α:=Tap G) k m
  let K (u : TapSet G (k+m)) := L (A (e.symm u).1) (A' (e.symm u).2)
  have hK : Decay reachOf θ (b*C*B) K := by
    intro i; obtain ⟨z,rfl⟩ := e.surjective i; simp only [K,Equiv.symm_apply_apply]
    rw [show reachOf (e z)=_ from reach_appended z,wanes_splits]
    exact (hl _ _).trans ((mul_le_mul (mul_le_mul_of_nonneg_left (hA z.1) hp) (hA' z.2) (norm_nonneg _)
      (mul_nonneg hp (mul_nonneg hC (wanes_pos ..).le))).trans_eq (by ring))
  refine ⟨he,mul_nonneg (mul_nonneg hp hC) hB,K,hK,fun p x a => ?_⟩
  dsimp only; rw [H,H']; unfold receive
  let W i := verse x i (fun _ => a) • A i
  let T i := verse x i (fun _ => a) • A' i
  have hW : Summable W := (receive_norm he hA x _).of_norm
  have hT : Summable T := (receive_norm he hA' x _).of_norm
  let P i := verse x i (fun _ => a) • K i
  have ht : Summable P := (receive_norm he hK x _).of_norm
  change L (∑' i,W i) (∑' i,T i)=∑' i,P i
  have heq (i j) : L (W i) (T j)=P (e (i,j)) := by
    change L (W i) (T j)=verse x (e (i,j)) (fun _ => a) • L (A (e.symm (e (i,j))).1) (A' (e.symm (e (i,j))).2)
    simp only [Equiv.symm_apply_apply]
    rw [show verse x (e (i,j)) (fun _ => a)=_ from verse_appended (i,j) x (fun _ => a)]
    change L (verse x i _ • A i) (verse x j _ • A' j)=(verse x i (fun _ => a)*verse x j (fun _ => a)) • L (A i) (A' j)
    simp only [map_smul,smul_apply,smul_smul]; rw [mul_comm]
  calc
    L (∑' i,W i) (∑' i,T i) = ∑' i,L (W i) (∑' j,T j) := (L.flip _).map_tsum hW
    _ = ∑' i,∑' j,P (e (i,j)) := tsum_congr fun i => ((L (W i)).map_tsum hT).trans (tsum_congr (heq i))
    _ = ∑' i,P (e i) := (e.summable_iff.mpr ht).tsum_prod.symm
    _ = ∑' i,P i := e.tsum_eq P
lemma bilinear (h : LocalRep c k θ C f) {g : SiteRead G c F} (h' : LocalRep c m θ B g) (L : E →L[ℝ] F →L[ℝ] Z) :
    LocalRep c (k+m) θ (‖L‖*C*B) (fun p x a => L (f p x a) (g p x a)) :=
  h.bilinear_bound h' L (norm_nonneg L) fun x y => ((L x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (L.le_opNorm x) (norm_nonneg _))
lemma ring_mul {f g : SiteRead G c R} (h : LocalRep c k θ C f) (h' : LocalRep c m θ B g) :
    LocalRep c (k+m) θ (C*B) (fun p x a => f p x a * g p x a) := by
  simpa only [one_mul,ContinuousLinearMap.mul_apply'] using h.bilinear_bound h' (ContinuousLinearMap.mul ℝ R)
    zero_le_one (fun x y => by simpa only [one_mul,ContinuousLinearMap.mul_apply'] using norm_mul_le x y)


end LocalRep
end YM.CubicMatch
