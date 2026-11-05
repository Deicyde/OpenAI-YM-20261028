import YM.Push.LOOP_COEFFICIENT.Line
import YM.Push.LOOP_COEFFICIENT.Signature
import YM.Push.LOOP_COEFFICIENT.Tubes

/-!
# Signature to momentum line calculus (prior to coefficient comparisons)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Complex Matrix Set Lattice Bloch Exterior
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {G : Gauge} {p : Momentum} {b : Bool}

lemma act_smul (s : Signed) (c : ℂ) (p : Momentum) : s.act (c • p) = c • s.act p := by ext1 i; simp [Signed.act]

lemma sign_diff (s : Signed) : ContDiff ℂ ω (s.act (R:=ℂ)) := contDiff_pi.mpr fun i => by unfold Signed.act; split <;> fun_prop
lemma corner_diff (s : Signed) (i : Axis) : ContDiff ℂ ω (fun p : Momentum => corner s p i) := by
  unfold corner; split
  · simp_rw [← Complex.exp_neg]; fun_prop
  fun_prop
lemma q_diff (i : Axis) : ContDiff ℂ ω (fun p => q p i) := by unfold q; fun_prop
lemma q_first (i : Axis) (p : Momentum) : lineD (fun z => q z i) p 1 = I * p i := by
  rw [lineD, iteratedDeriv_one]; unfold q; simp only [Pi.smul_apply,smul_eq_mul]
  convert! ((((hasDerivAt_id' (0:ℂ)).mul_const (p i)).const_mul I).cexp.sub_const (1:ℂ)).deriv using 1
  simp
lemma q_below (i : Axis) : Below (fun p => q p i) p 1 := below_one (by simp [q])

def unitAxis (i : Axis) : Momentum := Pi.single i 1
lemma unit_star (i : Axis) : star (unitAxis i) = unitAxis i := by ext1; simp [unitAxis,Pi.single_apply]
lemma unit_span (p : Momentum) : ∑ i, p i • unitAxis i = p := by ext1 j; simp [unitAxis, Pi.single_apply, mul_ite]
lemma unit_act (s : Signed) (i : Axis) : s.act (unitAxis i) = (if s.flip i then (-1:ℂ) else 1) • unitAxis (s.perm i) := by
  funext j; obtain ⟨j,rfl⟩ := s.perm.surjective j
  by_cases hi : i=j
  · simp [unitAxis, hi]
  simp [unitAxis, *]

variable {V W : Momentum → Matrix (Axes G) (Axes G) ℂ}

lemma ward_formula {J : Type*} {M : Matrix J (Axes G) ℂ} (hw : M * longitudinal G p = 0) (i : J) (a : G.ColorIndex) : ∑ j : Axis,M i (j,a) * q p j = 0 := by
  have he := congr_fun (congr_fun hw i) a
  simpa [Matrix.mul_apply,Fintype.sum_prod_type,longitudinal,mul_ite] using he

lemma orbit_congruence (s : Signed) (p : Momentum) (M : Matrix (Axes G) (Axes G) ℂ) (i j : Axes G) :
    ((orbitSymbol G s (-p)).transpose * M * orbitSymbol G s p) (s.perm i.1,i.2) (s.perm j.1,j.2) = corner s (-p) i.1 * M i j * corner s p j.1 := by
  simp [Matrix.mul_apply,orbitSymbol, Prod.mk.injEq, ← Prod.ext_iff, ite_mul,mul_ite]

def mark (V : Momentum → Matrix (Axes G) (Axes G) ℂ) (n : ℕ) (p : Momentum) : Matrix (Axes G) (Axes G) ℂ :=
    of fun i j => lineD (fun p => V p i j) p n

def Signature.Short (V : Momentum → Matrix (Axes G) (Axes G) ℂ) (n : ℕ) := ∀ p i j, Below (fun p => V p i j) p n

namespace Signature
lemma sub (h : Signature G b V) (h' : Signature G b W) : Signature G b (fun p => V p - W p) :=
  ⟨fun p hp => by simp [transpose_sub,h.symmetric p hp,h'.symmetric p hp],fun p hp => (h.hermitian p hp).sub (h'.hermitian p hp),
   fun p hp => by simp [Matrix.sub_mul,h.ward p hp,h'.ward p hp],fun s hs p hp => by simp only [Matrix.mul_sub,Matrix.sub_mul,h.spin s hs p hp,h'.spin s hs p hp],
   fun p hp u => by simp only [Matrix.mul_sub,Matrix.sub_mul,h.color p hp u,h'.color p hp u]⟩
lemma smul (h : Signature G b V) (c : ℝ) : Signature G b (fun p => (c:ℂ) • V p) :=
  ⟨fun p hp => by simp [h.symmetric p hp],fun p hp => (h.hermitian p hp).smul (by simp [IsSelfAdjoint]),
   fun p hp => by simp [h.ward p hp],fun s hs p hp => by simp [h.spin s hs p hp], fun p hp u => by simp [h.color p hp u]⟩

lemma short_zero (V : Momentum → Matrix (Axes G) (Axes G) ℂ) : Short V 0 := fun _ _ _ => below_zero
lemma Short.succ {n : ℕ} (h : Short V n) (h' : ∀ p,mark V n p = 0) : Short V (n+1) := fun p i j => below_succ.mpr ⟨h p i j, congr_fun (congr_fun (h' p) i) j⟩
end Signature

lemma mark_zero : mark V 0 p = V 0 := by ext; simp [mark]
lemma mark_neg (V : Momentum → Matrix (Axes G) (Axes G) ℂ) (n : ℕ) (p : Momentum) : mark V n (-p) = ((-1:ℂ)^n) • mark V n p := by
  ext i j; exact line_neg (fun z => V z i j) p n
lemma mark_smul (V : Momentum → Matrix (Axes G) (Axes G) ℂ) (n : ℕ) (c : ℂ) (p : Momentum) : mark (fun z => c • V z) n p = c • mark V n p := by
  ext i j; exact line_const_mul (f:=fun z => V z i j) c p n
lemma mark_sub (h : ContDiffAt ℂ ω V 0) (h' : ContDiffAt ℂ ω W 0) (n : ℕ) (p : Momentum) : mark (fun z => V z - W z) n p = mark V n p - mark W n p := by
  ext i j; exact line_sub (analyticComponent h i j) (analyticComponent h' i j) ..

lemma mark_ward {J : Type} {Y : Momentum → J → Axes G → ℂ}
    (h : ∀ p : Momentum,star p = p → (of (Y p)) * longitudinal G p = 0) (hd : ∀ i j, ContDiffAt ℂ ω (fun p => Y p i j) 0) {n : ℕ}
    (hs : ∀ p i j, Below (fun z => Y z i j) p n) (p : Momentum) (i : J) (b : G.ColorIndex) :
    ∑ j : Axis, lineD (fun z => Y z i (j,b)) p n * p j = 0 := by
  let f (j : Axis) (p : Momentum) := Y p i (j,b) * q p j
  have hf j : ContDiffAt ℂ ω (f j) 0 := (hd ..).mul (q_diff j).contDiffAt
  have he := germ_real (f:=fun p => ∑ j,f j p) (ContDiffAt.sum (fun j _ => hf j)).analyticAt analyticAt_const (Eventually.of_forall fun p hp => ward_formula (h p hp) i b)
  have hx (j : Axis) := Below.product (hd i (j,b)) (q_diff j).contDiffAt (hs p i (j,b)) (q_below j)
  have hy : (∑ j, lineD (f j) p (n+1)) = 0 := by rw [← line_sum _ _ (fun j _ => hf j),line_congr he,line_vac]
  unfold f at hy
  simp_rw [hx,q_first,Nat.choose_succ_self_right,show ∀ x y : ℂ,(↑(n+1:ℕ):ℂ) * x * (I*y) = ((n+1:ℕ):ℂ) * I * (x*y) from fun _ _ => by ring, ← Finset.mul_sum] at hy
  exact (mul_eq_zero.mp hy).resolve_left (mul_ne_zero (by exact_mod_cast n.succ_ne_zero) I_ne_zero)

lemma value_ward {J : Type} {Y : Momentum → J → Axes G → ℂ}
    (h : ∀ p : Momentum,star p = p → (of (Y p)) * longitudinal G p = 0) (hd : ∀ i j, ContDiffAt ℂ ω (fun p => Y p i j) 0) : Y 0 = 0 := by
  funext i ⟨j,b⟩; simpa [unitAxis,Pi.single_apply,mul_ite] using mark_ward h hd (fun _ _ _ => below_zero) (unitAxis j) i b

namespace Signature
variable (h : Signature G b V) (hd : ContDiffAt ℂ ω V 0) {n : ℕ}
include h hd
lemma transversal (hs : Short V n) (p : Momentum) (i : Axes G) (b : G.ColorIndex) :
    ∑ j : Axis, mark V n p i (j,b) * p j = 0 := mark_ward (Y:=fun p i j => V p i j) h.ward (analyticComponent hd) hs p i b

lemma short_one : Short V 1 := (short_zero _).succ fun _ => mark_zero.trans (value_ward (Y:=fun p i j => V p i j) h.ward (analyticComponent hd))

lemma mark_symmetry (p : Momentum) (n : ℕ) : (mark V n p).transpose = mark V n (-p) := by
  ext i j
  refine (line_congr (germ_real (analyticComponent hd j i).analyticAt
    (((show ContDiffAt ℂ ω (fun z => V z i j) (-0) by simpa using analyticComponent hd i j).comp (f:=(-·)) 0 (by fun_prop)).analyticAt) (Eventually.of_forall fun p hp => congr_fun (congr_fun (h.symmetric p hp) i) j)) p n).trans ?_
  simp only [lineD,mark,of_apply,smul_neg, Function.comp_apply]

lemma mark_color (hG : G.Simple) (a : G.ColorIndex) (n : ℕ) (p : Momentum) (i j : Axes G) :
    mark V n p i j = if i.2=j.2 then mark V n p (i.1,a) (j.1,a) else 0 := by
  split
  next he =>
    exact line_congr (germ_real (analyticComponent hd i j).analyticAt (analyticComponent hd (i.1,a) (j.1,a)).analyticAt (Eventually.of_forall fun p hp => by
      obtain ⟨c,hc⟩ := h.color_scalar hG hp i.1 j.1; simpa only using (hc i.2 j.2).trans ((show V p _ _ = (if i.2 = j.2 then c else 0) by simpa only [he,if_pos rfl] using hc a a).symm))) _ _
  next he =>
    exact (line_congr (germ_real (analyticComponent hd i j).analyticAt analyticAt_const (Eventually.of_forall fun p hp => by
      obtain ⟨c,hc⟩ := h.color_scalar hG hp i.1 j.1; simpa [he] using hc i.2 j.2)) _ _).trans (line_vac ..)

lemma mark_diagonal_star (p : Momentum) (hp : star p = p) (i : Axes G) (n : ℕ) : star (mark V n p i i) = mark V n p i i := by
  have he (t : ℝ) := congr_fun (congr_fun (h.hermitian ((t:ℂ) • p) (by simp [star_smul,hp])).eq i) i
  simpa [mark,lineD] using real_iterate (x:=0) (u:=fun t : ℂ => V (t • p) i i) (Eventually.of_forall he) (by simpa using line_smooth (analyticComponent hd i i) p ω) n

lemma mark_spin (hs : Short V n) (s : Signed) (hv : b=true ∨ (∀ i, s.flip i = false)) (p : Momentum) (i j : Axes G) :
    mark V n (s.act p) (s.perm i.1,i.2) (s.perm j.1,j.2) =
      (if s.flip i.1 then -1 else 1) * (if s.flip j.1 then -1 else 1) * mark V n p i j := by
  let u (p : Momentum) := V (s.act p) (s.perm i.1,i.2) (s.perm j.1,j.2)
  let c (p : Momentum) := corner s (-(s.act p)) i.1 * corner s (s.act p) j.1
  have hu : ContDiffAt ℂ ω u 0 := ContDiffAt.comp (g:=fun p => V p (s.perm i.1,i.2) (s.perm j.1,j.2)) 0 (by rw [s.act_zero]; exact analyticComponent hd _ _) (sign_diff s).contDiffAt
  have hc : ContDiffAt ℂ ω c 0 := (((corner_diff s i.1).comp (sign_diff s).neg).mul ((corner_diff s j.1).comp (sign_diff s))).contDiffAt
  have he : u =ᶠ[𝓝 0] (fun p => c p * V p i j) := germ_real hu.analyticAt (hc.mul (analyticComponent hd i j)).analyticAt (Eventually.of_forall fun p hp => by
    have h' := h.spin s hv (s.act p) (by simp only [star_signed,hp]); rw [Signed.inv_act] at h'
    unfold u; rw [← h',orbit_congruence]; dsimp [c]; ring)
  have hx := (line_congr he p n).trans (show lineD (fun z => c z * V z i j) p n = c 0 * lineD (fun z => V z i j) p n from by simpa using Below.product hc (analyticComponent hd i j) (below_zero (p:=p)) (hs p i j))
  simpa [lineD,u,mark,act_smul,c,corner] using hx
end Signature
end YM.Push.Loops
