import YM.Next.FREE_KERNELS.Heart

/-!
# Scaled puncture algebra

`S=1` gives coarse-output-side symbols for a step of dilation L. On the
input side use `S=L`. This makes currency in the alias proofs be on order
one (and will require restoring factors, including L⁴ from alias counting,
on installation in `Cross`). `mirage` and `flux` type stars with the
analytical convention (-p argument and **transpose** for a real stencil).
No projectors defined by removing frequency points on a physical grid.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix
open scoped Topology BigOperators ComplexConjugate

variable {j t : ℕ}

/-- One orientation of a hop, separating the two stage indices. -/
structure Flight (j t : ℕ) where
  L : Side
  odd : Odd L.val
  coarse : 3 ≤ L.val
  legal : 4 ≤ j
  mono : t ≤ j
  narrow : j ≤ t+1
  wing : Train j

namespace Flight

def patch (P : Flight j t) : RG.Patch := ⟨P.L,j,P.legal,P.coarse,P.odd⟩

def land (P : Flight j t) := Train.hop P.patch P.mono P.narrow P.wing
end Flight

def tripQ (S : Side) (p : Momentum) (i : Axis) := (S.val:ℂ)*chip (p i)
def signal (S : Side) (r : ℕ) (p : Momentum) := wedge r (tripQ S p)
def mirage (S : Side) (r : ℕ) (p : Momentum) := (signal S r (-p)).transpose

def hinges (P : Flight j t) (r : ℕ) (p : Momentum) := massFilter P.patch p • mask r (fun i => rail P.L (p i))
def flux (P : Flight j t) (r : ℕ) (p : Momentum) := (hinges P r (-p)).transpose

lemma signal_unit (r : ℕ) (p : Momentum) : signal 1 r p=symbol r p := by
  unfold signal tripQ chip symbol Exterior.q; simp
lemma scale_signal (S : Side) (r : ℕ) (p : Momentum) : signal S r p=(S.val:ℂ) • symbol r p := by
  unfold signal tripQ chip; rw [wedge_smul]; rfl
lemma signal_chain (S : Side) (r : ℕ) (p) : signal S (r+1) p*signal S r p=0 := Exterior.d_d ..
lemma mirage_chain (S : Side) (r : ℕ) (p) : mirage S r p*mirage S (r+1) p=0 := by unfold mirage; rw [← Matrix.transpose_mul, signal_chain,transpose_zero]

lemma hinges_nil (P : Flight j t) (p) : hinges P 0 p=massFilter P.patch p • 1 := by rw [hinges,mask_nil]
lemma hinges_rule (P : Flight j t) (l : Site P.L) (p : Momentum) (i : Axis) :
    rail P.L (aliasAt p l i)*tripQ P.L (aliasAt p l) i=tripQ 1 p i := by
  have hn := congr_arg (fun p : Momentum => p i) (alias_scale p l)
  change (P.L.val • aliasAt p l) i=_ at hn
  simp only [Pi.smul_apply,nsmul_eq_mul,Pi.add_apply,reciprocal] at hn
  have hh := rail_chip P.L (aliasAt p l i); rw [hn,chip_repeat] at hh
  unfold tripQ; rw [mul_left_comm,← mul_assoc,hh]; simp
lemma hinge_transport (P : Flight j t) (r : ℕ) (l : Site P.L) (p : Momentum) :
    hinges P (r+1) (aliasAt p l)*signal P.L r (aliasAt p l)=signal 1 r p*hinges P r (aliasAt p l) := by
  unfold hinges signal
  rw [Matrix.smul_mul,Matrix.mul_smul,mask_insert]; simp_rw [hinges_rule]
lemma flux_transport (P : Flight j t) (r : ℕ) (l : Site P.L) (p : Momentum) :
    mirage P.L r (aliasAt p l)*flux P (r+1) (aliasAt p l)=flux P r (aliasAt p l)*mirage 1 r p := by
  unfold mirage flux; rw [← transpose_mul,← transpose_mul, ← alias_reverse _ P.odd, hinge_transport]

lemma tripQ_stays (S : Side) (p : Momentum) (x : Cover) : tripQ S (p+reciprocal x)=tripQ S p := by
  funext i; simp only [tripQ,Pi.add_apply,reciprocal,chip_repeat]
lemma hinges_stays (P : Flight j t) (p : Momentum) (x : Cover) (r : ℕ) : hinges P r (p+reciprocal x)=hinges P r p := by
  unfold hinges massFilter; simp only [Train.area_period,Pi.add_apply,reciprocal,rail_repeat]
lemma mirage_herm (S : Side) (p : Momentum) (hp : physical p) (r) : mirage S r p=(signal S r p)ᴴ := by
  unfold mirage signal; rw [wedge_adj]
  have hh : tripQ S (-p)=star (tripQ S p) := by
    funext i; simp only [tripQ, Pi.star_apply, star_mul,flip_chip]; rw [show star (p i)=p i from congr_fun hp i]; simp [mul_comm]
  rw [hh]
lemma flux_herm (P : Flight j t) (p : Momentum) (hp : physical p) (r) : flux P r p=(hinges P r p)ᴴ := by
  have h₁ : massFilter P.patch (-p) = star (massFilter P.patch p) := by unfold massFilter; rw [star_pow,Train.area_conj,show star p=p from hp]
  have h₂ : (fun i => rail P.L ((-p) i))=star (fun i => rail P.L (p i)) := by funext i; simp only [Pi.star_apply,rail_bar]; rw [show star (p i)=p i from congr_fun hp i]; rfl
  unfold flux hinges; rw [Matrix.conjTranspose_smul,Matrix.transpose_smul,mask_trans,mask_adj,h₁,h₂]

def scaleD (S : Side) (k : ℝ) (v : Train j) (p : Momentum) (i : Axis) := ((S.val:ℂ)^2)⁻¹ * v.levelD k i p
def scaleR (S : Side) (k : ℝ) (v : Train j) (p : Momentum) := (S.val:ℂ)^4 * v.rho k p

def fieldD (S : Side) (k : ℝ) (v : Train j) (p : Momentum) := mask 1 (scaleD S k v p)
def fieldI (S : Side) (k : ℝ) (v : Train j) (p : Momentum) := mask 1 fun i => (scaleD S k v p i)⁻¹

def rotor (S : Side) (k : ℝ) (v : Train j) (p : Momentum) := mirage S 1 p*pulse k v p*signal S 1 p

def pipe (S : Side) (k : ℝ) (v : Train j) (p : Momentum) := (scaleR S k v p)⁻¹ • (mirage S 0 p*fieldI S k v p)
def creek (S : Side) (k : ℝ) (v : Train j) (p : Momentum) := (scaleR S k v p)⁻¹ • (fieldI S k v p*signal S 0 p)

section scaled
variable (S : Side) (k : ℝ) (hk : 0<k) (v : Train j) {p : Momentum} (hp : p∈realCube zone) (he : p≠0)
include hk hp he

lemma scaleD_live (i : Axis) : scaleD S k v p i ≠0 := mul_ne_zero (by exact inv_ne_zero (pow_ne_zero _ (side_ne S))) (Train.D_live k hk v hp he i)
lemma scaleR_live : scaleR S k v p ≠0 := by
  unfold scaleR; rw [Train.recover_rho _ hk v hp he]; exact mul_ne_zero (pow_ne_zero _ (side_ne S)) (mul_ne_zero (pow_ne_zero _ (divisor_ne _ hp he)) (Train.bend_live _ hk _ hp))
lemma field_counter : fieldI S k v p*fieldD S k v p=1 ∧ fieldD S k v p*fieldI S k v p=1 :=
    (mask_undo _ _ (scaleD_live S k hk v hp he)).symm

lemma rotor_law : rotor S k v p=fieldI S k v p -
    (scaleR S k v p)⁻¹ • (fieldI S k v p * signal S 0 p * mirage S 0 p * fieldI S k v p) := by
  let a := scaleR S k v p; have ha : a≠0 := scaleR_live S k hk v hp he
  let f i := (scaleD S k v p i)⁻¹
  let b := (S.val:ℂ)
  have hb : b≠0 := side_ne _
  have hh (i) : f i=b^2*(v.levelD k i p)⁻¹ := by unfold f b scaleD; rw [_root_.mul_inv_rev, inv_inv]; ring
  have hm : pulse k v p=a⁻¹ • mask 2 f := by
    rw [pulse_sources k hk v hp he]
    simp_rw [show f=(fun i => b^2*(v.levelD k i p)⁻¹) from funext hh,mask_scale,smul_smul]
    change _ = ((b^4 * _)⁻¹ * _) • _
    rw [_root_.mul_inv_rev, show (b^2)^2=b^4 by ring,mul_assoc]; simp [hb]
  have hx : ∑ i, tripQ S (-p) i*(f i*tripQ S p i)=a := by
    unfold a scaleR Train.rho tripQ; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [hh,jewel_one]; unfold b; rw [Pi.neg_apply]; ring
  unfold rotor; rw [hm,Matrix.mul_smul,Matrix.smul_mul]
  unfold mirage signal; rw [blade_price,hx,smul_sub,smul_smul,inv_mul_cancel₀ ha,one_smul]
  rfl
lemma rotor_split : rotor S k v p=fieldI S k v p-fieldI S k v p*signal S 0 p*pipe S k v p := by
  rw [rotor_law S k hk v hp he]; unfold pipe; rw [Matrix.mul_smul]; simp only [Matrix.mul_assoc]
lemma rotor_after : rotor S k v p * fieldD S k v p=1-creek S k v p*mirage S 0 p := by
  rw [rotor_law S k hk v hp he,sub_mul]; unfold creek; simp only [Matrix.smul_mul,Matrix.mul_assoc,(field_counter S k hk v hp he).1,Matrix.mul_one]
lemma rotor_before : fieldD S k v p*rotor S k v p=1-signal S 0 p*pipe S k v p := by
  rw [rotor_split S k hk v hp he,mul_sub]; simp only [← Matrix.mul_assoc,(field_counter S k hk v hp he).2,Matrix.one_mul]

omit hk hp he in
lemma rotor_immunity (p : Momentum) : rotor S k v p*signal S 0 p=0 ∧ mirage S 0 p*rotor S k v p=0 := by
  unfold rotor
  constructor
  · simp only [Matrix.mul_assoc,signal_chain,Matrix.mul_zero]
  simp only [← Matrix.mul_assoc,mirage_chain,Matrix.zero_mul]
end scaled
end YM.Next.Free
