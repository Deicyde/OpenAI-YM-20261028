import YM.Planned.PRIMARY_INTEGRAL_295.Bijets
import YM.Planned.PRIMARY_INTEGRAL_295.RuneTurn

/-!
# Orientation equivariance of the actual cover response S

Signed rows/unmodified cochain T0, every axis term acts on the convention
of THIS step. Costs and exact output uses still needed for interpreting
chart beta result on varying vacuum supports. No separate transformed
column estimate at a different offset implied.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Carrier
open Function Filter Set Lattice Laurent Bloch RG Precision Next.Free Exterior
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {L : Side} {j t : ℕ}

def bias (s : Signed) (a : Axis) : ℝ := if s.flip a then -1 else 1

def delay (s : Signed) (a : Axis) : Cover := if s.flip a then -step (s.perm a) else 0

def goingUp (s : Signed) (a : Axis) : Equiv.Perm Cover :=
    (s.actEquiv.toEquiv).trans (Equiv.addRight (delay s a))

lemma going_spec (s : Signed) (a : Axis) (x : Cover) : goingUp s a x = s.act x + delay s a := rfl
lemma spectral_move (s : Signed) (a : Axis) (p : Momentum) (x : Cover) :
    mode (s.act p) (goingUp s a x)=mode p x * mode (s.act p) (delay s a) := by rw [going_spec, mode_shift,prompt_flip]
lemma bias_spectral (s : Signed) (a : Axis) (p : Momentum) :
    (bias s a:ℂ) * mode (s.act p) (delay s a) = aspect s p a := by
  unfold delay bias aspect; split; swap; · simp
  rw [mode_opposite, factor,Signed.act_at,if_pos (by assumption)]
  unfold twirl; simp [Complex.exp_neg]

def addressed (K : Lines L) (x : Cover) (a b : Axis) (y : Cover) := member K x a b (y-cellar L x)

private lemma addressed_signal (K : Lines L) (x : Cover) (a b : Axis) (p : Momentum) :
    RRead (addressed K x a b) p=mode p (cellar L x)*RRead (member K x a b) p := market_move ..

variable (s : Signed) (P : Flight j t) (k : ℝ) (hk : 0 < k) (ht : 4≤t)
include hk ht
lemma address_flip (x y : Cover) (a b : Axis) :
    let K := linesOf P k
    bias s b * addressed K x a b y = bias s a * addressed K (goingUp s a x) (s.perm a) (s.perm b) (goingUp s b y) := by
  intro K
  let x' := goingUp s a x
  let Q0 := addressed K x a b
  let Q1 := addressed K x' (s.perm a) (s.perm b)
  let f z := bias s b * Q0 z; let g z:=bias s a * Q1 (goingUp s b z)
  have h z i a : Summable fun y => ‖addressed K z i a y‖ := by
    have hp : Summable fun y => ‖member K z i a y‖ := (stored P k hk ht).safe _ _
    exact shift_sound _ hp _
  suffices he : f=g from congr_fun he y
  have hm z i j (b : Axis) : Summable fun y => ‖bias s b * addressed K z i j y‖ := by
    simp_rw [norm_mul]; exact (h z i j).mul_left _
  apply RRead_injective (hm ..) ((goingUp s b).summable_iff.mpr (hm x' (s.perm a) (s.perm b) a))
  intro p hp; let q:=s.act p; let M := mode q (delay s b)
  apply mul_left_cancel₀ (mode_ne q (delay s b)) -- mode on left
  have h1 : M * RRead f p=aspect s p b * RRead Q0 p := by
    unfold RRead Laurent.read; rw [← tsum_mul_left,← tsum_mul_left]; refine tsum_congr fun i => ?_
    unfold M f q; simp only [Complex.ofReal_mul,smul_eq_mul,← bias_spectral]; ring
  have h2 : M * RRead g p=(bias s a:ℂ) * RRead Q1 q := by
    unfold RRead Laurent.read
    rw [← tsum_mul_left,← tsum_mul_left]
    -- reindex RHS
    rw [← (goingUp s b).tsum_eq (fun i => (bias s a:ℂ) * (mode q i • (Q1 i:ℂ)))]
    apply tsum_congr; intro i
    unfold M g q; simp only [spectral_move, Complex.ofReal_mul, smul_eq_mul]; ring
  change M*RRead f p=M*RRead g p
  rw [h1,h2]; unfold Q0 Q1 K; rw [addressed_signal,addressed_signal,status k hk P ht x a b p hp,status k hk P ht x' _ _ q (signed_base hp _)]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Equiv.sum_comp (s.actEquiv (R:=Per P.L)).toEquiv (fun l => (bias s a:ℂ)*(mode (aliasAt q l) x'*(((P.L.val:ℂ))⁻¹*Flight.pilot k P q l (coord (s.perm a)) (coord (s.perm b)))))]
  refine Finset.sum_congr rfl fun l _ => ?_
  change _ = (bias s a:ℂ) * (mode (aliasAt q (s.act l)) x'*_)
  unfold q; rw [alias_signed P.odd,show mode (s.act _) x'= _ from spectral_move s a (aliasAt p l) x]
  have hh:= perspective s p P k hk l hp a b
  rw [← bias_spectral] at hh
  calc
    _ = mode (aliasAt p l) x * (((P.L.val:ℂ))⁻¹ * (Flight.pilot k P p l (coord a) (coord b)*aspect s p b)) := by ring
    _ = _ := by rw [← hh]; ring_nf; rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def orient (s : Signed) (f : Window E) : Window E := fun x i => bias s i • f (goingUp s i x) (s.perm i)

omit hk ht in
lemma wide (A : Lines L) (f : Window E) (x : Cover) (i : Axis) :
    applyLine A f x i = ∑ j : Axis, ∑' y, addressed A x i j y • f y j := by
  unfold applyLine stream; apply Finset.sum_congr rfl; intro j _
  rw [← (Equiv.addRight (cellar L x)).tsum_eq (fun y => addressed A x i j y • f y j)]; simp [addressed,add_comm]

lemma origin_turn (f : Window E) : applyLine (linesOf P k) (orient s f) = orient s (applyLine (linesOf P k) f) := by
  let K := linesOf P k
  ext1 x; ext1 a
  unfold orient; rw [wide,wide]; rw [Finset.smul_sum,← Equiv.sum_comp s.perm (fun j => bias s a • ∑' y,addressed (linesOf P k) (goingUp s a x) (s.perm a) j y • f y j)]
  refine Finset.sum_congr rfl fun b _=> ?_
  rw [← tsum_const_smul'',← (goingUp s b).tsum_eq (fun n => bias s a • addressed K (goingUp s a x) (s.perm a) (s.perm b) n • f n (s.perm b))]
  exact tsum_congr fun y => by change addressed K x a b y • (bias s b • _) = _; rw [smul_smul, smul_smul, mul_comm, address_flip s P k hk ht]
end YM.Planned.PrimaryIntegral295.Carrier
