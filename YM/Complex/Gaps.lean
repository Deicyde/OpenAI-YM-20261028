import Mathlib.Analysis.Complex.Liouville
import YM.Complex.Columns


/-!
# Integer finite trace difference inequality

Next mesh estimate checks the proposed shortcut has a chance to work: no rank
factor in the difference. Lattice units throughout. p_s=2p. Integer endpoints for
fidelity with remaining B kernels. In complex traces use the entire finite path,
zero on the spectral kernel at all complex times. (Agreement with powers at POSITIVE
integer arguments only.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Holder
open MeasureTheory Filter Function Set Complex Matrix WithLp
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.L2Operator ComplexOrder
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- Holomorphic kernel with positive integer powers. -/
def leap {X : M ι} (h : X.PosSemidef) (z : ℂ) :=
  let Y := h.1.eigenvectorUnitary.val
  Y * diagonal (fun i => specPow (h.1.eigenvalues i) z) * Yᴴ

lemma leap_at {A : M ι} (h : A.PosSemidef) {p : ℕ} (hp : 0<p) : leap h (p:ℂ)=A^p := by
  unfold leap
  simp only [spec_nat (h.eigenvalues_nonneg _) hp]
  generalize_proofs
  conv_rhs => lhs; rw [spectral_diag h.1]
  rw [spectral_power]
  rfl

lemma leap_smooth {X : M ι} (h : X.PosSemidef) : Differentiable ℂ (leap h) :=
  ((differentiable_const _).mul (diagonal_diff h.1.eigenvalues)).mul (differentiable_const _)

def Q (A : M ι) (N : ℕ) := ‖(A^N).trace‖

lemma flexPower {A : M ι} (h : A.PosSemidef) {N : ℕ} (hq : 0<N) :
    ∃ P : Flex ι, ∀ z, leap h z = specPow (Q A N) (z/N) • P.walk (z/N) := by
  let v := h.1.eigenvalues
  let Y := h.1.eigenvectorUnitary
  let s (i) := (v i)^N
  have hs (i) : 0 ≤ s i := pow_nonneg (h.eigenvalues_nonneg _) _
  let R := ∑ i, s i
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => hs i)
  have he : Q A N = R := by
    rw [Q,spectral_trace Y _ (spectral_diag h.1)]; exact Complex.norm_of_nonneg hR
  let f (i) := s i/R
  refine ⟨weighted _ _ _ (fun i => show 0 ≤ f i from div_nonneg (hs i) hR) (share hs) (unitary_safe Y) (unitary_safe' Y), fun z => ?_⟩
  rw [he]
  let w := z/(N:ℂ)
  have hw : (N:ℂ)*w=z := by dsimp only [w]; field_simp
  change Y.val * Matrix.diagonal _ * Y.valᴴ= specPow R w • (Y.val * Matrix.diagonal _ * Y.valᴴ)
  rw [← smul_mul_assoc, ← mul_smul_comm, ← diagonal_smul]; congr 2
  ext1 i j
  by_cases hh : i=j
  · subst j
    simp only [diagonal_apply_eq,Pi.smul_apply,smul_eq_mul]
    change specPow (v i) z=specPow R w * specPow (f i) w
    have hx (hb : s i≠0) : R≠0 := ne_of_gt ((lt_of_le_of_ne (hs i) hb.symm).trans_le (Finset.single_le_sum (fun j _ => hs j) (Finset.mem_univ _)))
    rw [← show specPow (s i) w = _ from pays (hs i) hR hx w, show s i = _ from (rfl : s i=v i^N),rolls (h.eigenvalues_nonneg i) w hq,hw]
  simp [Matrix.diagonal,hh]

variable {n : ℕ}

lemma onList (W : List (Flex ι × ℂ)) (h : ∀ p ∈ W, p.2.re ∈ Icc 0 1) (ht : (W.map (fun i => i.2.re)).sum=1) :
    ‖(family W).trace‖ ≤ 1 := by
  let V (i : Fin W.length) := (W.get i).1
  let v (i : Fin W.length) := (W.get i).2
  have hs : ∑ i, (v i).re=1 := by
    have H : List.ofFn (fun i => (v i).re)=W.map (fun i => i.2.re) := by
      change List.ofFn ((fun i : Flex ι × ℂ => i.2.re) ∘ W.get)=_; rw [← List.map_ofFn,List.ofFn_get]
    simpa only [List.sum_ofFn] using (congr_arg List.sum H).trans ht
  have hy := convexStrip V v (fun i => h (W.get i) (List.get_mem ..)) hs
  convert hy
  unfold family combine
  rw [show (fun i => (V i).walk (v i)) = (fun i : Flex ι × ℂ => i.1.walk i.2) ∘ W.get from rfl,
    ← List.map_ofFn,List.ofFn_get]

def alternating (a b : Fin n → Flex ι × ℂ) := (List.ofFn fun i => [a i,b i]).flatten
lemma paired (a b : Fin n → Flex ι × ℂ) :
    family (alternating a b) = combine (fun i => (a i).1.walk (a i).2 * (b i).1.walk (b i).2) := by
  induction n with
  | zero => simp [family,alternating,combine]
  | succ n ih =>
    rw [stem, show alternating a b = (a 0)::(b 0)::(alternating (Fin.tail a) (Fin.tail b)) from by
      simp [alternating,List.ofFn_succ];rfl]
    rw [show family _ = (a 0).1.walk (a 0).2 * ((b 0).1.walk (b 0).2 * family (alternating (Fin.tail a) (Fin.tail b))) by simp [family]]
    rw [ih,← _root_.mul_assoc]; rfl

lemma totalStrip (a b : Fin n → Flex ι × ℂ) :
    ((alternating a b).map fun i => i.2.re).sum = ∑ i, ((a i).2.re+(b i).2.re) := by
  induction n with
  | zero => simp [alternating]
  | succ n ih =>
    rw [show alternating a b = (a 0)::(b 0)::(alternating (Fin.tail a) (Fin.tail b)) from by
      simp [alternating,List.ofFn_succ];rfl]
    simp only [List.map_cons,List.sum_cons]; rw [ih,Fin.sum_univ_succ,← add_assoc]; rfl

lemma begin_of (a b : Fin n → Flex ι × ℂ) (p : Flex ι × ℂ) :
    p ∈ alternating a b ↔ ∃ i, a i=p ∨ b i=p := by
  simp [alternating,eq_comm]

def rate (p : ℕ) := (((p+p:ℕ):ℝ))⁻¹
def paysNorm (p : ℕ) (B : M ι) := ‖((Bᴴ*B)^p).trace‖^(rate p)

def total {X : M ι} (h : X.PosSemidef) (b : Fin n → M ι) (v : Fin n → ℂ) :=
  (combine fun i => b i*leap h (v i)).trace

def cost {n : ℕ} (X : M ι) (b : Fin n → M ι) (p N : ℕ) :=
  (∏ i, paysNorm p (b i))* (Q X N) ^ ((1:ℝ)-n*rate p)

lemma scalars (b : Fin n → M ι) (c : Fin n → ℂ) :
    combine (fun i => c i • b i) = (∏ i, c i) • combine b := by
  induction n with
  | zero => simp only [blank,Finset.univ_eq_empty,Finset.prod_empty,one_smul]
  | succ n ih =>
    rw [stem,stem b, Fin.prod_univ_succ]
    change c 0 • b 0 * combine (fun i : Fin n => c i.succ • b i.succ)=_
    rw [ih]; simp only [smul_mul_assoc,mul_smul_comm,mul_smul]
    rw [smul_comm]; rfl

theorem estimation {X : M ι} (h : X.PosSemidef) {b : Fin n → M ι} {p N : ℕ} (hp : 0 < p) (hN : 0 < N)
    {v : Fin n → ℂ} (hn : ∀ i, 0 ≤ (v i).re) (hx : n*rate p+ (∑ i, (v i).re)/N = (1:ℝ))
    (hz : 0 < Q X N) : ‖total h b v‖ ≤ cost X b p N := by
  have hd : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  let y := fun i => v i/N
  have he (i) : (y i).re=(v i).re/N := by
    unfold y; rw [show (N:ℂ)=↑(N:ℝ) by simp, Complex.div_ofReal_re]
  let s := rate p
  have hs : 0<s := inv_pos.mpr (Nat.cast_pos.mpr (by omega))
  choose P hP using fun i => even_cost (b i) p hp
  obtain ⟨R,hR⟩ := flexPower h hN
  let a (i : Fin n) := (P i, (s:ℂ))
  let d (i : Fin n) := (R,y i)
  let c (i : Fin n) := (P i).walk (s:ℂ) * R.walk (y i)
  let f (i : Fin n) := ↑(paysNorm p (b i)) * specPow (Q X N) (y i)
  have hW : ∑ i, (y i).re = 1-n*s := by
    simp only [he,← Finset.sum_div]; unfold s; linarith
  have hm : total h b v=(∏ i, f i) • (family (alternating a d)).trace := by
    rw [paired]
    have hu (i : Fin n) : b i*leap h (v i)=f i • c i := by
      conv_lhs => lhs; rw [hP i]
      rw [hR, smul_mul_assoc, mul_smul_comm, smul_smul]; rfl
    change (combine _).trace = _; simp_rw [hu]
    rw [scalars, Matrix.trace_smul]
  have hw (i) : (y i).re ∈ Icc 0 1 := by
    have hh j : 0≤(y j).re := by rw [he]; exact div_nonneg (hn _) hd.le
    refine ⟨hh _, (Finset.single_le_sum (fun j _ => hh j) (Finset.mem_univ _)).trans ?_⟩
    rw [hW]; nlinarith [show 0≤(n:ℝ) by positivity]
  rw [hm,norm_smul]
  apply le_trans (mul_le_of_le_one_right (norm_nonneg _) (onList _ (fun u hu => ?_) ?_))
  · unfold f
    simp only [norm_prod,norm_mul,Finset.prod_mul_distrib, spec_norm hz, ← Real.rpow_sum_of_pos hz,hW]
    have hh i : 0 ≤ paysNorm p (b i) := Real.rpow_nonneg (norm_nonneg _) _
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hh _)]
    exact le_rfl
  · rw [totalStrip, Finset.sum_add_distrib]; change ∑ _ : Fin n, ((s:ℂ).re) + ∑ i, (y i).re=1
    rw [hW]; simp
  obtain ⟨i,rfl|rfl⟩ := (begin_of a d u).1 hu
  · refine ⟨hs.le,?_⟩; change rate p ≤ _
    unfold rate; rw [← one_div, div_le_one (Nat.cast_pos.mpr (show 0<p+p by omega))]
    exact_mod_cast (show 1≤p+p by omega)
  exact hw i

/-- Move one step within two gaps (adjacent in actual application).
The radius parameter in native lattice steps, centers move nonnegative amount.
Gains R in denominator. -/
theorem finite_lip {X : M ι} (h : X.PosSemidef) (b : Fin n → M ι) {N width p m : ℕ}
    (he : N=(p+p)*width) (hp : 0 < p) (hw : 0 < width) (hz : 0 < Q X N)
    {Y Z : Fin n → ℕ} (hY : n*width+∑ i, Y i=N)
    (i j : Fin n) (hij : i≠j) (hu : Y i+m=Z i) (hv : Z j+m=Y j)
    (hm : ∀ a : Fin n, a≠i → a≠j → Y a=Z a)
    (r : ℝ) (hr : 0<r) (hO : ∀ i : Fin n, 2*r < Y i) (hs : (m:ℝ) ≤ r) :
    ‖(combine (fun i => b i*X^Z i)).trace-(combine (fun i => b i*X^Y i)).trace‖ ≤ cost X b p N / r * m := by
  have hN : 0<N := by rw [he]; positivity
  have hJ : 0<Y i := Nat.cast_pos.mp (lt_of_le_of_lt (show 0≤2*r by positivity) (hO i))
  let W (x : ℂ) (s : Fin n) := ↑(Y s) + ((if s=i then x else 0) - (if s=j then x else 0))
  let F (x : ℂ) := total h b (W x)
  have hF : Differentiable ℂ F := by
    unfold F total; apply (dtrace (ι := ι)).comp
      (dproduct (fun x i => b i*leap h (W x i)) ?_)
    intro a
    exact (differentiable_const _).mul ((leap_smooth h).comp (show Differentiable ℂ (fun x => W x a) from by
      unfold W; split_ifs <;> fun_prop))
  have hh (x : ℂ) (hx : ‖x‖ ≤ 2*r) : ‖F x‖ ≤ cost X b p N := by
    refine estimation h hp hN ?_ ?_ hz
    · intro a
      have hl := hO a
      have ha := (abs_le.mp (abs_re_le_norm x)).1
      have hb := (abs_le.mp (abs_re_le_norm x)).2
      change 0 ≤ (W x a).re; unfold W
      split_ifs <;> simp only [Complex.add_re,Complex.natCast_re,Complex.sub_re,Complex.zero_re] <;> linarith
    have hy : ∑ i, W x i = ∑ i, (Y i:ℂ) := by simp [W, Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have hg : ∑ i, (W x i).re = ∑ i, (Y i:ℝ) := by simp only [← Complex.re_sum, hy]; simp
    rw [hg,rate]
    have hN' : (N:ℝ)>0 := Nat.cast_pos.mpr hN
    have hf : (0:ℝ)<p+p := by exact_mod_cast (show 0<p+p by omega)
    have hj : (n:ℝ)*width+∑ i, (Y i:ℝ)=(N:ℝ) := by exact_mod_cast hY
    have hy' : (N:ℝ)=(↑p+↑p)*(width:ℝ) := by exact_mod_cast he
    rw [Nat.cast_add]
    calc
      _ = ((n:ℝ)*width+(∑ i, (Y i:ℝ)))/N := by field_simp; grind
      _ = _ := by rw [hj,div_self hN'.ne']
  have hD (x : ℂ) (hx : x ∈ Metric.closedBall 0 r) : ‖deriv F x‖ ≤ cost X b p N/r := by
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hF.diffContOnCl fun z he => hh z ?_
    rw [Metric.mem_sphere] at he
    have ht := dist_triangle z x 0
    rw [Metric.mem_closedBall] at hx; rw [he, dist_zero_right] at ht; linarith
  have hi (a : Fin n) : 0 < Z a := by
    apply (Nat.cast_pos (α := ℝ)).mp
    have hp := hO a; by_cases he : a=i
    · subst a; rw [← hu]; exact_mod_cast (show 0 < Y i + m by omega)
    rcases eq_or_ne a j with H|H
    · subst a; rw [← hv,Nat.cast_add] at hp; linarith
    rw [← hm a he H]; linarith
  have h0 : F 0=(combine (fun i => b i*X^Y i)).trace := by
    unfold F W; have hu (s : Fin n) : 0 < Y s := Nat.cast_pos.mp (lt_of_le_of_lt (show 0≤2*r by positivity) (hO s))
    simp [total,leap_at h (hu _)]
  have hs' : F (m:ℂ)=(combine (fun i => b i*X^Z i)).trace := by
    have hg (s : Fin n) : W (m:ℂ) s=(Z s:ℂ) := by
      by_cases H : s=i
      · subst s; simp [W,hij, ← hu]
      by_cases G : s=j
      · subst s; simp [W,Ne.symm hij,← hv]
      simp [W,H,G,hm s H G]
    unfold F total; simp only [hg,leap_at h (hi _)]
  rw [← hs',← h0]; simpa using ((convex_closedBall (0:ℂ) r).norm_image_sub_le_of_norm_deriv_le (fun x _ => hF x) hD (Metric.mem_closedBall_self hr.le) (show (m:ℂ)∈ Metric.closedBall 0 r from Metric.mem_closedBall.mpr (by simpa using hs)))
end YM.Holder
