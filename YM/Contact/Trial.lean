import YM.Euclid.Test
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! Contact-test and finite-jet conventions. Unlike `YM.Test`, the normal test here lives
on the *full* vector space (smooth, compactly supported, complex values; the readings are
complex-linear in the test, i.e. no conjugation at integration). -/
set_option autoImplicit false
noncomputable section
open Set Filter Function MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions BigOperators NNReal 
namespace YM.Contacts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable (E) in
abbrev Trial := TestFunction (⊤ : Opens E) ℂ (⊤ : ℕ∞)
variable (E) in
abbrev Reading := Trial E →L[ℂ] ℂ

def Major (j : ℕ) (φ : E → ℂ) (B : ℝ) := ∀ i ≤ j, ∀ x : E, ‖iteratedFDeriv ℝ i φ x‖ ≤ B

lemma Major.nonneg {j : ℕ} {φ : E → ℂ} {B : ℝ} (h : Major j φ B) : 0 ≤ B :=
  le_trans (norm_nonneg _) (h 0 (Nat.zero_le _) 0)
lemma Major.value {j : ℕ} {φ : E → ℂ} {B : ℝ} (h : Major j φ B) (x : E) : ‖φ x‖ ≤ B := by
  simpa only [norm_iteratedFDeriv_zero] using h 0 (Nat.zero_le _) x
lemma Major.weaken {j j' : ℕ} {φ : E → ℂ} {B B' : ℝ} (h : Major j φ B) (hj : j' ≤ j) (hB:B ≤ B') :
    Major j' φ B' := fun i hi x => h i (hi.trans hj) x |>.trans hB
lemma Trial.orders (φ : Trial E) (i : ℕ) : ContDiff ℝ i (φ : E→ℂ) :=
  φ.contDiff.of_le (WithTop.coe_le_coe.mpr (show ((i:ℕ∞) ≤ (⊤:ℕ∞)) from le_top))
lemma Trial.majorant (j : ℕ) (φ : Trial E) : ∃ B : ℝ, Major j φ B := by
  have he(i:ℕ) : ∃ B : ℝ, ∀ x : E, ‖iteratedFDeriv ℝ i φ x‖ ≤ B :=
    (Continuous.bounded_above_of_compact_support ((φ.orders i).continuous_iteratedFDeriv (m:=i) le_rfl)
      (φ.hasCompactSupport.iteratedFDeriv i))
  choose b H using he
  refine ⟨Finset.fold max 0 (fun x:ℕ=>b x) (Finset.Iic j),?_⟩; intro i hi x
  exact (H i x).trans ((Finset.le_fold_max _).2 (.inr ⟨i,Finset.mem_Iic.mpr hi,le_rfl⟩))

/-- Finite-order estimate on every test compact (here order independent of the compact). -/
def Controlled (A : Trial E → ℂ) (j : ℕ) (s : Set E := univ) :=
 ∀ R:ℝ,0<R → ∃ C:ℝ,0≤C ∧ ∀ φ:Trial E, (support ⇑φ) ⊆ s∩Metric.closedBall 0 R → ∀ {B},Major j φ B → ‖A φ‖ ≤ C*B

variable (A: Trial E→ₗ[ℂ] ℂ) {j:ℕ}
lemma controlled_continuous (h:Controlled A j) : Continuous A := by
  refine (TestFunction.continuous_iff_continuous_comp A).mpr ?_; intro K hK
  obtain ⟨R,hR,hR'⟩:= K.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨C,hC,hL⟩:= h R hR
  let B':= ContDiffMapSupportedIn.seminorm ℂ E ℂ (⊤:ℕ∞) K
  let f:ContDiffMapSupportedIn E ℂ ⊤ K →ₗ[ℂ] ℂ:= A.comp ((TestFunction.ofSupportedInCLM ℂ hK).toLinearMap)
  change Continuous f
  refine (ContDiffMapSupportedIn.withSeminorms ℂ E ℂ ⊤ K).continuous_of_isBounded
      (norm_withSeminorms _ _) _ (.of_real fun i ↦ ⟨Finset.range (j+1), C, fun φ ↦ ?_⟩)
  let b:= (Finset.range (j+1)).sup B'; let ψ:=TestFunction.ofSupportedIn hK φ
  change ‖A ψ‖ ≤ C*(b φ)
  exact hL ψ (fun x hx=> ⟨trivial,Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hR' x (φ.tsupport_subset (subset_closure hx)))⟩)
    (fun i hi x=> (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ).trans
       (show B' i φ ≤ b φ from (show B' i ≤ b from Finset.le_sup (Finset.mem_range_succ_iff.mpr hi)) φ))

def Controlled.view (h:Controlled A j) : Reading E where
  toLinearMap:= A
  cont:= controlled_continuous A h
@[simp] lemma Controlled.view_apply (h:Controlled A j) (φ) : Controlled.view A h φ=A φ:=rfl

/-- Homogeneous Taylor term with the ordinary factorial, using the diagonal
of the Fréchet derivative. -/
def jet (n:ℕ) (φ:E→ℂ) (x y : E) := ((n.factorial:ℝ)⁻¹ : ℝ) •
     iteratedFDeriv ℝ n φ x (fun _=> y - x)

def polynomial (m:ℕ) (φ:E→ℂ) (x y:E) := ∑ i∈Finset.range (m+1),jet i φ x y

lemma diag (φ : Trial E) (x v : E) (t : ℝ) (ht:t∈Icc (0:ℝ) 1) (i : ℕ) :
    iteratedDerivWithin i (fun t:ℝ=> φ (x+t • v)) (Icc (0:ℝ) 1) t =
      iteratedFDeriv ℝ i φ (x+t • v) (fun _=>v) := by
  let L: ℝ→L[ℝ] E:= ContinuousLinearMap.id ℝ ℝ |>.smulRight v
  let f(u:E):=φ (x+u)
  have hf:ContDiff ℝ i f:= (φ.orders _).comp (contDiff_const.add contDiff_id)
  change iteratedDerivWithin i (f∘(⇑L)) _ t=_
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (show (0:ℝ)<1 from zero_lt_one))
       (hf.comp L.contDiff|>.contDiffAt) ht, iteratedDeriv_eq_iteratedFDeriv]
  rw [L.iteratedFDeriv_comp_right hf t (le_refl _), show iteratedFDeriv ℝ i f (L t) = _ from iteratedFDeriv_comp_add_left ..]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply congr_arg (iteratedFDeriv ℝ i (φ:E→ℂ) (x+L t))
  funext j; change (1:ℝ) • v=v; exact one_smul ..
def jetLM (n:ℕ) (x:E) : Trial E →ₗ[ℂ] E → ℂ where
  toFun φ y:= jet n φ x y
  map_add' φ ψ:= by
    ext1 y; unfold jet
    rw [show ⇑(φ+ψ) = (φ:E→ℂ)+(ψ:E→ℂ) from rfl,iteratedFDeriv_add (φ.orders _) (ψ.orders _)]
    simp only [Pi.add_apply, add_apply, smul_add]
  map_smul' c φ:= by
    ext1 y; unfold jet; rw [show ⇑(c • φ) = c • (φ:E→ℂ) from rfl,iteratedFDeriv_const_smul_apply (φ.orders n|>.contDiffAt)]
    simp only [Pi.smul_apply, smul_apply, RingHom.id_apply]; apply smul_comm

lemma norm_jet {m i:ℕ} {φ:E→ℂ} {B:ℝ} (h:Major m φ B) (hi:i≤m) (x y:E) :
    ‖jet i φ x y‖ ≤ ‖y-x‖^i * B:=by
  rw [jet,norm_smul,Real.norm_of_nonneg (show (0:ℝ) ≤ ((i.factorial:ℕ):ℝ)⁻¹ by positivity)]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans ?_
  · apply (inv_le_one₀ (by positivity)).2; exact_mod_cast (Nat.factorial_pos i)
  refine ((iteratedFDeriv ℝ i φ x).le_opNorm (fun _=>y-x)).trans ?_
  simp; grw [h i hi];rw [mul_comm]

lemma taylor_est {m:ℕ} {φ:Trial E} {B:ℝ} (h:Major (m+1) φ B) (x y:E) :
    ‖φ y-polynomial m φ x y‖ ≤ ‖y-x‖^(m+1) * B:=by
  let L: ℝ→L[ℝ] E:= ContinuousLinearMap.id ℝ ℝ |>.smulRight (y-x)
  let f(t:ℝ):= φ (x+t • (y-x)); let P:= Icc (0:ℝ) 1
  have ht0: (0:ℝ)∈P := ⟨le_rfl,zero_le_one⟩
  have ht1: (1:ℝ)∈P:= ⟨zero_le_one,le_rfl⟩
  have hb:taylorWithinEval f m P 0 1=polynomial m φ x y:=by
    unfold polynomial; rw [taylor_within_apply]; unfold f; apply Finset.sum_congr rfl
    intro i _; rw [diag φ x _ _ ht0]; simp [jet]
  have hf:ContDiff ℝ (↑m+1 : ℕ∞ω) f:= (φ.orders (m+1)|>.of_le (mod_cast le_rfl)).comp (contDiff_const.add L.contDiff)
  have hz:= taylor_mean_remainder_bound (C:=B*‖y-x‖^(m+1)) (n:=m) zero_le_one hf.contDiffOn ht1 (fun t ht=> ?_)
  · rw [hb,show f 1=φ y by simp [f]] at hz
    simp only [sub_zero,one_pow,mul_one] at hz
    calc
      _ ≤ _ := hz
      _ ≤ B* ‖y-x‖^(m+1):=div_le_self (mul_nonneg h.nonneg (pow_nonneg (norm_nonneg _) _)) (Nat.one_le_cast.mpr (Nat.factorial_pos _))
      _ = _:= mul_comm ..
  · rw [show f=(fun t:ℝ=> φ (x+t • (y-x))) from rfl, diag φ x _ _ ht]
    refine ((iteratedFDeriv ℝ (m+1) (φ:E→ℂ) _).le_opNorm (fun _:Fin (m+1)=> y-x)).trans ?_
    simpa using (mul_le_mul_of_nonneg_right (h _ le_rfl _) (pow_nonneg (norm_nonneg (y-x)) (m+1)))

lemma jet_smooth (n:ℕ) (φ:E→ℂ) (x:E) : ContDiff ℝ ⊤ (jet n φ x) :=by
  exact (contDiff_const (c:=((n.factorial:ℝ)⁻¹))).smul (ContinuousMultilinearMap.contDiff (iteratedFDeriv ℝ n φ x) |>.comp (contDiff_pi.2 (fun _=>ContDiff.sub (contDiff_id (𝕜:=ℝ) (E:=E)) (contDiff_const (c:=x)))))

/-- The common cutoff is a fixed smooth real bump of the square of the Euclidean radius,
1 on the unit ball and vanishing outside the ball of radius 2. `s` is its subtraction length. -/
def lamp : ContDiffBump (0:ℝ):=⟨1,4,by norm_num,by norm_num⟩
def chi (s:ℝ) (y:E):= lamp (‖s⁻¹ • y‖ ^ 2)

lemma chi_one {s:ℝ} (hs:0<s) (y:E) (hy:‖y‖≤s) : chi s y=1:=by
  have hz : ‖s⁻¹ • y‖ ≤ 1:= by
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hs|>.le)]; exact inv_mul_le_one_of_le₀ hy hs.le
  refine lamp.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall,Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg _)]; change _ ≤ 1; nlinarith only [hz,norm_nonneg (s⁻¹ • y)]
@[simp] lemma chi_nonneg (s:ℝ) (y:E): 0 ≤ chi s y:=lamp.nonneg
@[simp] lemma chi_le_one (s:ℝ) (y:E): chi s y≤1:=lamp.le_one
lemma chi_zero (s:ℝ) (y:E) (hy:2 ≤ ‖s⁻¹ • y‖):chi s y=0:=by
  apply lamp.zero_of_le_dist; rw [Real.dist_eq,sub_zero,abs_of_nonneg (sq_nonneg _)]; change 4 ≤ _; nlinarith only [hy]
lemma chi_supported (s:ℝ) (hs:0<s) : tsupport (chi (E:=E) s) ⊆ Metric.closedBall (0:E) (2*s):= by
  refine closure_minimal (fun y hy=> ?_) Metric.isClosed_closedBall
  rw [Metric.mem_closedBall,dist_zero_right]; refine le_of_lt (not_le.mp (fun hn=> hy (?_)))
  exact chi_zero _ _ ((norm_smul s⁻¹ y).symm ▸ (Real.norm_of_nonneg (inv_pos.mpr hs).le).symm ▸ (le_inv_mul_iff₀ hs |>.2 (by rwa [mul_comm])))
lemma chi_len (s:ℝ) (y:E) : chi s y=chi 1 (s⁻¹ • y):=by simp [chi]
section
variable {V:Type*}[NormedAddCommGroup V][InnerProductSpace ℝ V]
lemma chi_smooth (s:ℝ) : ContDiff ℝ (⊤:ℕ∞) (chi (E:=V) s) :=
    lamp.contDiff.comp (contDiff_norm_sq ℝ |>.comp (contDiff_const.smul contDiff_id))
end
lemma chi_compact (s:ℝ)(hs:0<s)[FiniteDimensional ℝ E] : HasCompactSupport (chi (E:=E) s):=
  (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (chi_supported _ hs)

def taylorCut (s:ℝ) (m:ℤ) (φ:E→ℂ) (y:E) := if 0 ≤ m then chi s y • polynomial m.toNat φ 0 y else 0
def remainder (s:ℝ) (m:ℤ) (φ:E→ℂ) (y:E):=φ y-taylorCut s m φ y
lemma remainder_near (s:ℝ) (hs:0<s) {m:ℤ} {φ:Trial E} {B:ℝ}
    (h:Major (m+1).toNat φ B) (y:E) (hy:‖y‖≤s) : ‖remainder s m φ y‖ ≤ ‖y‖^(m+1).toNat*B:=by
  by_cases hp:m<0
  · rw [remainder,taylorCut,if_neg (not_le.mpr hp),Int.toNat_eq_zero.mpr (by omega : m+1≤0)]; simpa only [sub_zero,pow_zero,one_mul] using h.value y
  rw [remainder,taylorCut,if_pos (not_lt.mp hp), chi_one hs y hy,one_smul,show (m+1).toNat=m.toNat+1 by omega];
  simpa only [sub_zero] using taylor_est (show Major (m.toNat+1) φ B from (by omega:(m+1).toNat=m.toNat+1) ▸ h) 0 y
end YM.Contacts
