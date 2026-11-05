import YM.Next.FREE_KERNELS.Bend
import YM.Next.FREE_KERNELS.MatrixPay

/-!
# The unmodified H and its inverse

At the top the two-form precision is exactly Wilson. Identities valid on the
real enlarged cube. Width exports glue *these same symbols*, no assignment
of a separate value at harmonic momentum.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix
open scoped Topology BigOperators ComplexConjugate

variable {j : ℕ}

def vault (k : ℝ) (v : Train j) (p : Momentum) := v.bend k p • mask 2 (v.bulb k p)

def pulse (k : ℝ) (v : Train j) (p : Momentum) := (v.bend k p)⁻¹ • mask 2 (fun i => (v.bulb k p i)⁻¹)
-- `v.bend k p` elaborates bend k v

@[simp] lemma pulse_zero (k : ℝ) (v : Train j) : pulse k v 0=1 := by simp [pulse,mask_one]
@[simp] lemma vault_zero (k : ℝ) (v : Train j) : vault k v 0=1 := by simp [vault,show v.bulb k 0=(fun _ => 1) by ext; simp,mask_one]

lemma pulse_pays (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p ∈ realCube zone) :
    pulse k v p*vault k v p=1 ∧ vault k v p*pulse k v p=1 := by
  obtain ⟨ha,hb⟩ := mask_undo 2 (v.bulb k p) (Train.bulb_glows _ hk _ hp)
  have hx := Train.bend_live _ hk v hp
  unfold vault pulse
  rw [Matrix.smul_mul,Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,ha,hb]
  simp [smul_smul,hx]

lemma heart_budget {ι : Type*} (k : ℝ) (hk : 0<k) (hj : 4 ≤ j) (v : ι → Train j) :
    Pay (fun _ : ι => 1) (fun i => pulse k (v i)) ∧ Pay (fun _ : ι => 1) fun i => vault k (v i) := by
  have hc := Train.bend_budget _ hk hj v
  have hm (a : Axis) := Train.bulb_budget k hj v (fun _ => a)
  have hr := (Pay.expose_mask 2 hm).scale hc
  have hmn (a : Axis) := (hm a).inv (Train.bulb_firm _ hk v _) (fun _ => one_pos)
  have hb := (Pay.expose_mask 2 hmn).scale (hc.inv (Train.bend_firm _ hk hj v) (fun _ => one_pos))
  simp only [inv_one, one_pow, mul_one] at hb hr; exact ⟨hb,hr⟩

lemma vault_sources (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p ∈ realCube zone) (he : p≠0) :
    vault k v p=v.rho k p • mask 2 (fun i => v.levelD k i p) := by
  have hh (i) : v.levelD k i p=(divisor v.mass p)⁻¹*v.bulb k p i := by rw [Train.D_bulb k v hp he]; ring
  rw [Train.recover_rho _ hk _ hp he,vault]
  simp_rw [hh,mask_scale, smul_smul]
  have hz := divisor_ne v.mass hp he
  congr 1; field_simp

lemma pulse_sources (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p ∈ realCube zone) (he : p≠0) :
    pulse k v p=(v.rho k p)⁻¹ • mask 2 (fun i => (v.levelD k i p)⁻¹) := by
  have hh (i) : (v.levelD k i p)⁻¹=(divisor v.mass p)*(v.bulb k p i)⁻¹ := by rw [Train.D_bulb k v hp he, inv_div,div_eq_mul_inv];
  rw [Train.recover_rho _ hk _ hp he,pulse]
  simp_rw [hh,mask_scale, smul_smul]
  have hz := divisor_ne v.mass hp he
  congr 1; rw [_root_.mul_inv_rev,mul_assoc]; simp [hz]

lemma jewel_period (i : Axis) : Stable (fun p => jewel 1 p i) := by
  intro p x; change jewel 1 _ i=_; simp only [jewel_one];
  have hh (p : Momentum) (x : Cover) : chip ((p+reciprocal x) i) = chip (p i) := chip_repeat ..
  rw [hh, show -((p+reciprocal x) i) = ((-p)+reciprocal (-x)) i by rw [reciprocal_negate]; simp [Pi.neg_apply,add_comm],hh]
  rfl
lemma rho_period (k : ℝ) (v : Train j) : Stable (v.rho k) := by
  intro p x; unfold Train.rho; refine Finset.sum_congr rfl fun i _ => ?_
  rw [show jewel 1 (p+reciprocal x) i=jewel 1 p i from jewel_period i p x,Train.D_stable]
lemma rho_even (k : ℝ) (v : Train j) (p : Momentum) : v.rho k (-p)=v.rho k p := by
  unfold Train.rho; simp only [jewel, neg_neg, Train.D_even]; refine Finset.sum_congr rfl fun a _ => ?_; rw [mul_comm]

lemma overlap_regular {p : Momentum} {x : Cover} (hx : x≠0) (hp : p∈realCube zone) (hh : p+reciprocal x∈realCube zone) :
    p≠0 ∧ p+reciprocal x≠0 := by
  have hzero (x : Cover) (hx : x≠0) : reciprocal x∉realCube zone := by
    intro hh
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hx
    have h := hh.2 i
    change x i≠0 at hi
    have hk : 1≤ (x i).natAbs := by omega
    have hv : (1:ℝ)≤(x i).natAbs := by exact_mod_cast hk
    simp only [reciprocal,Complex.mul_re,Complex.re_ofNat,Complex.ofReal_re,Complex.im_ofNat,
      Complex.intCast_re,Complex.intCast_im,zero_mul,mul_zero,sub_zero] at h
    rw [abs_mul,abs_of_pos (by positivity),abs_nat] at h
    unfold zone at h; nlinarith [Real.pi_pos]
  constructor
  · intro hz; rw [hz,zero_add] at hh; exact hzero x hx hh
  intro hz
  rw [eq_neg_of_add_eq_zero_left hz,← reciprocal_negate] at hp; exact hzero (-x) (neg_ne_zero.mpr hx) hp

lemma overlap_heart (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p∈realCube zone)
    (x : Cover) (he : p+reciprocal x∈realCube zone) :
    pulse k v (p+reciprocal x)=pulse k v p ∧ vault k v (p+reciprocal x)=vault k v p := by
  by_cases h : x=0
  · rw [h,show reciprocal (0:Cover)=0 by ext; simp [reciprocal]]; simp
  obtain ⟨h₁,h₂⟩ := overlap_regular h hp he
  rw [pulse_sources _ hk _ he h₂,pulse_sources _ hk _ hp h₁,vault_sources _ hk _ hp h₁,vault_sources _ hk _ he h₂,rho_period]
  have hh (i : Axis) : v.levelD k i (p+reciprocal x)=v.levelD k i p := Train.D_stable k v i p x
  simp [hh]

lemma heart_even (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p ∈ realCube zone) :
    pulse k v (-p)=pulse k v p ∧ vault k v (-p)=vault k v p := by
  by_cases h : p=0
  · simp [h]
  have hn : -p≠0 := neg_ne_zero.mpr h
  rw [pulse_sources _ hk _ (realCube_neg hp) hn,pulse_sources _ hk _ hp h,vault_sources _ hk _ hp h,vault_sources _ hk _ (realCube_neg hp) hn,rho_even]
  simp [Train.D_even]

lemma pulse_diagonal (k : ℝ) (v : Train j) (p : Momentum) (i m) : pulse k v p i m=
    if i=m then (v.bend k p)⁻¹*inventory i (fun a => (v.bulb k p a)⁻¹) else 0 := by
  simp [pulse,mask,Matrix.diagonal_apply, mul_ite]
lemma vault_diagonal (k : ℝ) (v : Train j) (p : Momentum) (i m) : vault k v p i m=
    if i=m then v.bend k p * inventory i (v.bulb k p) else 0 := by
  simp [vault,mask,Matrix.diagonal_apply,mul_ite]

lemma heart_silver (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p∈realCube zone) (a b) :
    Silver (pulse k v p a b) ∧ Silver (vault k v p a b) := by
  rw [pulse_diagonal,vault_diagonal]; split_ifs with h
  · have hx := Train.bend_price _ hk v hp
    have he i := Train.bulb_cost _ hk v hp.1 i
    exact ⟨hx.inv.mul (inventory_pos a _ (fun i => (he i).inv)),hx.mul (inventory_pos a _ he)⟩
  exact ⟨Silver.zero,Silver.zero⟩
lemma heart_real (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p∈realCube zone) :
    (pulse k v (-p)).map star=pulse k v p ∧ (vault k v (-p)).map star=vault k v p := by
  obtain ⟨h,H⟩ := heart_even _ hk v hp
  rw [h,H]
  constructor <;> ext i b
  · exact (heart_silver _ hk v hp i b).1.fixed
  exact (heart_silver _ hk v hp i b).2.fixed
lemma heart_Herm (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p∈realCube zone) :
    (pulse k v p).IsHermitian ∧ (vault k v p).IsHermitian := by
  have he (r : ℕ) (z) : (mask r z).transpose=mask r z := mask_trans ..
  have hh (a b : TypeFace 2) : pulse k v p b a=pulse k v p a b ∧ vault k v p b a=vault k v p a b := by
    by_cases h : a=b
    · simp [h]
    simp only [pulse_diagonal,vault_diagonal,h,Ne.symm h,↓reduceIte,and_self]
  constructor <;> ext i b <;> rw [Matrix.conjTranspose_apply]
  · rw [(heart_silver _ hk v hp b i).1.fixed]; exact (hh i b).1
  rw [(heart_silver _ hk v hp b i).2.fixed]; exact (hh i b).2

lemma top_metric (k : ℝ) (hk : 0<k) (j : ℕ) {p : Momentum} (hp : p∈realCube zone) :
    vault k (.top j) p=1 ∧ pulse k (.top j) p=1 := by
  let v := Train.top j
  by_cases h : p=0
  · rw [h,vault_zero,pulse_zero]; exact ⟨rfl,rfl⟩
  have he i : v.levelD k i p=(divisor 1 p)⁻¹ := by
    unfold Train.levelD; rw [feed_top]; simp [v,Train.levelNoise,Train.stream,Train.nozzle]
  have ht : v.rho k p=divisor 1 p*divisor 1 p := by
    unfold Train.rho; simp_rw [he,div_inv_eq_mul]; rw [← Finset.sum_mul]; rfl
  have hz := divisor_ne 1 hp h
  have hb : vault k v p=1 := by
    rw [vault_sources k hk v hp h,ht]
    simp_rw [he]; rw [show mask 2 (fun _ : Axis => (divisor 1 p)⁻¹)=(divisor 1 p)⁻¹ ^ 2 • 1 by
      simpa only [mul_one,mask_one] using mask_scale 2 (fun _ => 1) (divisor 1 p)⁻¹, smul_smul]
    rw [show divisor 1 p*divisor 1 p*((divisor 1 p)⁻¹ ^ 2)=1 by field_simp,one_smul]
  refine ⟨hb,?_⟩; have hx := (pulse_pays k hk v hp).1; rw [hb,mul_one] at hx; exact hx
end YM.Next.Free
