import YM.Push.CORRECTED_COLUMNS.Array
import YM.Push.CORRECTED_COLUMNS.EndpointCaps
import YM.Push.CORRECTED_COLUMNS.Integrals
import YM.Push.CORRECTED_COLUMNS.Wire

/-!
# Paying the terminal bill, all slots together

Specialize to link tilings from the Calendar. `ticket` at any nonzero or
zero subset. No powers other than (copies)*(number of marks in that subset)
in the ticket's weight. One bill, including vacuum, for every replica array.
The same transfer, weights, signs and scalars even for the zero part. Can be
used before knowing any limiting kernels.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected
open MeasureTheory Lattice Cells Wilson RG Marker Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {C : Family G} {r k N p : ℕ}

variable {V : Type*} [DecidableEq V] [Fintype V]

-- Propagate unnormalized source F (already corrected) from the very same
-- fine configuration. Works for more general slot cardinalities too.
namespace Wire
variable (B : Wire C r k N p) (hr : r≤N)
variable (P : Config G (C.side N p) → Marks.Algebra V)

def term (i : Finset (Site (C.side r p) × V)) :=
    B.push (fun U => (bare (C.beta N p) U:ℂ)*Marks.part (Marks.replicate (center C.S p hr 0) P U) i) r hr

-- Requires actual replicated integrability (here: continuous).
lemma possible (h : ∀ i, Continuous fun U => Marks.part (P U) i) (z : Finset (Site (C.side r p) × V)) :
    Integrable (fun U => (bare (C.beta N p) U:ℂ)*Marks.part (Marks.replicate (center C.S p hr 0) P U) z)
      (prior G _) := (((Complex.continuous_ofReal.comp (bare_cont _)).mul
      (Marks.continuous_array (center C.S p hr 0) P h z))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma sight (h : ∀ i, Continuous fun U => Marks.part (P U) i) (z) : Integrable (B.term hr P z) (prior G _) :=
    B.integrable _ (possible hr P h z) _ _



lemma first_value (h : ∀ i, Continuous fun U => Marks.part (P U) i) (z) :
    (∫ U,B.term hr P z U ∂prior G _) = (partition G (C.side N p) (C.beta N p):ℂ)*
      moment (C.beta N p) (fun U => Marks.part (Marks.replicate (center C.S p hr 0) P U) z) := by
  rw [moment_formula _ _ (continuous_integrable _ (Marks.continuous_array _ P h _)),← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (partition_pos _).ne'),one_mul]; exact B.mass _ (possible hr P h z) _ _
lemma compare (h : ∀ i, Continuous fun U => Marks.part (P U) i) (u) :
    let T := center C.S p hr 0
    ‖(∫ U,B.term hr P (Marks.packed T u) U ∂prior G _)‖ = partition G (C.side N p) (C.beta N p)*
      (T.rootTest (C.beta N p) (fun U => Marks.part (P U) u))^(Fintype.card (Site (C.side r p))) := by
  dsimp only
  rw [first_value B hr P h,norm_mul,Complex.norm_real,Real.norm_of_nonneg (partition_pos _).le]
  let T := center C.S p hr (0 : Site (C.side N p))
  simp_rw [Marks.folded]
  rw [← show Fintype.card T.Cell= Fintype.card (Site (C.side r p)) from rfl,T.powering]; rfl
end Wire

namespace Endpoint

variable (B : Wire C r k N p) (hr : r≤N)
variable (F : Config G (C.side N p) → Marks.Algebra V)

/-- Exact restart, shared vacuum. We don't need the whole shape of the
weak calendar in this application: need attainment of the caps stated
here. Not assumed from `C.path`'s own caps. `hv` etc LIVE again AFTER
corrections/marker cancellations. Scalar relative to probability Haar on
this torus. -/
structure Resolved (R : Rep G (C.side r p)) (s l σ A Λ d w : ℝ) : Prop where
  identityV : R.eval=B.vacuum r hr
  lawful : R.Lawful σ A Λ d w
  budgetCoupling : R.beta=B.cost r
  -- for comparing vacuum
  small : s ≤ R.p.threshold
  positive : 0 < s
  linear : 4*l ≤ R.beta*R.clip.linear*s^2

section
variable {B hr} {R : Rep G (C.side r p)} {s l σ A Λ d w : ℝ}
lemma Resolved.positiveR (M : Resolved B hr R s l σ A Λ d w) : 0 < R.beta := M.budgetCoupling ▸ B.pays r le_rfl hr
abbrev underPrice (R : Rep G (C.side r p)) (s A Λ d : ℝ) := R.exCost A Λ d+R.beta*baseBudget R.clip A s

lemma Resolved.under (M : Resolved B hr R s l σ A Λ d w) :
    Real.exp (R.scalar - (Fintype.card (Site (C.side r p)):ℝ)*underPrice (C:=C) (r:=r) (p:=p) R s A Λ d) *
     G.probHaar.real (G.shell (s/4)) ^ (Torus.free (C.side r p)).card ≤ partition G (C.side N p) (C.beta N p) := by
  have hu (U : Config G (C.side r p)) (hU : U ∈ calm G (C.side r p) s) :
      Real.exp (R.scalar-(Fintype.card (Site (C.side r p)):ℝ)*(R.exCost A Λ d+R.beta*baseBudget R.clip A s)) ≤ B.vacuum r hr U := by
    have hh := R.exponent_lo M.lawful M.positiveR.le _ M.positive M.small hU
    rw [← M.identityV, Rep.eval, Activities.gas_one _ _ (voids hU M.small),mul_one]; exact Real.exp_monotone hh
  have he : 4≤ (C.side r p).val := Nat.le_of_dvd (C.side r p).property (C.S.side_four ..)
  exact (Torus.denominator (by omega : 2 ≤ (C.side r p).val) _ (B.vacuum_io _ hr) (B.vacuum_invariant r hr) (B.vacuum_pos r hr)
    s M.positive _ hu).trans_eq (B.vacuum_mass r hr)
end

-- scalars extensive in sites, probes pay volume-relative too
def outerPrice {n : Side} (R : Rep G n) (l A Λ d w u b c : ℝ) (m : ℕ) :=
    R.exCost A Λ d+Fintype.card PlaqAxes*(4*l)+w+(m:ℝ)*(u+b+c)

/-- Sufficient estimate **at the push**; still needs producers. Complete
polynomial identity as functions, uses corrected all-copy coefficients,
not just linearized actions. Value charges at restored radii. Last field
a numerical bound per site (that can depend e.g. on the chosen k and its
costs but not n). -/
structure Sources (R : Rep G (C.side r p)) (l s A Λ d w W Q : ℝ)
    (M : Bands (Marks.all (Site (C.side r p) × V)) R) (u b c : ℝ) : Prop where
  value : Value M (fun _ => W) u b c
  endAt v (U) : Marks.part (M.density U) v=B.term hr F v U
  ready : underPrice (C:=C) (r:=r) (p:=p) R s A Λ d+outerPrice R l A Λ d w u b c (Fintype.card V)+3*Real.log (multiplier G l) ≤ Q

section
variable {B F} (hF : ∀ i, Continuous fun U => Marks.part (F U) i)
variable {R : Rep G (C.side r p)} {s l σ A Λ d w : ℝ} {M : Bands (Marks.all (Site (C.side r p) × V)) R} {u b c W Q : ℝ} {hr}

-- terminal numerator
include hF in
lemma Sources.pays (hl : 0 < l) (H : Resolved B hr R s l σ A Λ d w) (Y : Sources B hr F R l s A Λ d w W Q M u b c)
    (z : Finset (Site (C.side r p) × V)) :
    W^z.card * ‖(∫ U,B.term hr F z U ∂prior G _)‖ ≤
      Real.exp (R.scalar+(Fintype.card (Site (C.side r p)):ℝ)*outerPrice R l A Λ d w u b c (Fintype.card V))*
        (multiplier G l * G.probHaar.real (G.shell (s/4)))^(Torus.paid (C.side r p)).card := by
  let n := C.side r p
  have he : (Fintype.card (Site (C.side r p)):ℝ)*(R.exCost A Λ d+Fintype.card PlaqAxes*(4*l)+w) +
      Fintype.card (Site (C.side r p) × V)*(u+b+c) =
      (Fintype.card (Site n):ℝ)*outerPrice R l A Λ d w u b c (Fintype.card V) := by
    rw [Fintype.card_prod,Nat.cast_mul]; unfold outerPrice n; ring
  let E := R.scalar+(Fintype.card (Site n):ℝ)*outerPrice R l A Λ d w u b c (Fintype.card V)
  let f := link G l (s/4)
  let g (U : Config G n) := ∏ p : Face (Per n),f (faceValue U p)
  have ht U : W^z.card * ‖B.term hr F z U‖ ≤ Real.exp E * g U := by
    rw [← Y.endAt, show W^z.card = _ from (show Poly.toll (fun _ : Site n × V => W) (Marks.mode z) = W^z.card by simp [Poly.toll]).symm]
    apply (Poly.member Y.value.pure _ _).trans -- bound the actual term
    have hh := Value.extent Y.value H.lawful hl H.positive H.positiveR H.small H.linear U
    rw [add_assoc R.scalar _ _,he] at hh; exact hh
  have hi : Continuous g := continuous_finsetProd _ fun i _ => (link_cont ..).comp (continuous_travel ..)
  have htoll : 0 ≤ W^z.card := by
    have h : 0 < Poly.toll (fun _ => W) (Marks.mode z) := Poly.worth Y.value.pure _
    simpa only [Poly.toll,Marks.mode,Finset.prod_const] using h.le
  have hx := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm (μ:=prior G _) (B.term hr F z)) htoll
  rw [← integral_const_mul] at hx
  apply hx.trans
  have hw := integral_mono (Integrable.const_mul (B.sight hr _ hF z|>.norm) (W^z.card))
    ((hi.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul (Real.exp E)) ht
  rw [integral_const_mul (Real.exp E)] at hw
  refine hw.trans ?_
  have hn : 4 ≤ n.val := Nat.le_of_dvd n.property (C.S.side_four ..)
  have hs := H.positive
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos E).le
  exact (Torus.numerator (by omega : 2 ≤ n.val) f (link_cont ..) (link_nonneg _ _ _) (link_le _ _ _ hl (by positivity))).trans
    (pow_le_pow_left₀ (integral_nonneg (link_nonneg _ _ _)) (link_est _ _ _ hl (by positivity)) _)

-- arithmetic phase
private lemma arithmetic {j n m : ℕ} {Q D E S s K Z W H : ℝ} (ho : 0≤W) (ht : 0≤H) (hK : 1≤K) (hs : 0<s)
    (hp : j+4=m) (hw : j≤ 3*n)
    (he : Real.exp (S-(n:ℝ)*D)*s^m≤Z) (hi : W^n*(Z*H^n)≤Real.exp (S+(n:ℝ)*E)*(K*s)^j)
    (hQ : D+E+3*Real.log K ≤ Q) :
    (W*H)^n*s^4 ≤ Real.exp ((n:ℝ)*Q) := by
  have hk := lt_of_lt_of_le zero_lt_one hK
  rw [← hp,pow_add] at he
  rw [mul_pow] at hi
  have hj : Real.exp (S-(n:ℝ)*D)*((W*H)^n*s^4) ≤ Real.exp (S+(n:ℝ)*E)*K^j := by
    refine le_of_mul_le_mul_right (a:=s^j) ?_ (by positivity)
    calc
      _ = W^n*(Real.exp (S-(n:ℝ)*D)*(s^j*s^4)*H^n) := by rw [mul_pow]; ring
      _ ≤ W^n*(Z*H^n) := by gcongr
      _ ≤ _ := hi.trans_eq (by rw [mul_assoc])
  apply le_of_mul_le_mul_left (a:=Real.exp (S-(n:ℝ)*D)) ?_ (by positivity)
  have hh : K^j ≤ K^(3*n) := pow_le_pow_right₀ hK hw
  apply hj.trans ((mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le).trans ?_)
  rw [show K^(3*n) = Real.exp (↑(3*n)*Real.log K) by rw [Real.exp_nat_mul,Real.exp_log hk],← Real.exp_add,← Real.exp_add]
  apply Real.exp_monotone
  push_cast; nlinarith only [mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg (α:=ℝ) n)]

private lemma root_le {n : ℕ} {s Q W H : ℝ} (hp : 0<n) (hs : 0<s) (ho : 0<W)
    (hi : (W*H)^n*s^4 ≤ Real.exp ((n:ℝ)*Q)) :
    H ≤ (s^4:ℝ)⁻¹ ^ ((n:ℝ)⁻¹) * Real.exp Q / W := by
  rw [le_div_iff₀ ho,mul_comm H]
  have hx : (0:ℝ)<n := by exact_mod_cast hp
  apply le_of_pow_le_pow_left₀ (ne_of_gt hp) (a:=W*H) (by positivity) ?_
  rw [mul_pow _ (Real.exp Q),← Real.rpow_mul_natCast (by positivity), inv_mul_cancel₀ hx.ne',Real.rpow_one, ← Real.exp_nat_mul, mul_comm _ (Real.exp _), ← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity)).2 hi

include hF in
/-- The very same Wilson-tiling exponent and normalization for ANY subset
of the slots. Arbitrarily many copies. Price from the genuine corrected
term including translations and conjugations prescribed by `replicate`.
`cheap` only calls this on nonempty subsets. Loss s-shell at just FOUR links
under the full replication root; even crude lower bounds on that same s
shell can now be used for the limit. -/
theorem ticket {w₀ : ℝ} (hh : 0<w₀) (h' : w₀ ≤ G.probHaar.real (G.shell (s/4))) (hl : 0 < l)
    (H : Resolved B hr R s l σ A Λ d w) (hW : 0<W) (Y : Sources B hr F R l s A Λ d w W Q M u b c) (z : Finset V) :
    (center C.S p hr 0).rootTest (C.beta N p) (fun U => Marks.part (F U) z) ≤
      (w₀^4:ℝ)⁻¹ ^ ((Fintype.card (Site (C.side r p)):ℝ)⁻¹) * Real.exp Q / W^z.card := by
  let n := C.side r p
  let T := center C.S p hr (0 : Site (C.side N p))
  let m := Fintype.card (Site n)
  let a := G.probHaar.real (G.shell (s/4))
  let X := T.rootTest (C.beta N p) (fun U => Marks.part (F U) z)
  have ht : 0 ≤ X := T.root_nonneg ..
  have hs := lt_of_lt_of_le hh h'
  have hn : 4 ≤ n.val := Nat.le_of_dvd n.property (C.S.side_four ..)
  have hj := Torus.howmany (by omega : 2≤ n.val)
  have hp := Torus.rim_count (by omega : 2≤ n.val)
  have hJ : (Torus.paid n).card ≤ 3*m := by unfold m; omega
  have hi := Y.pays hF hl H (Marks.packed T z)
  rw [Wire.compare B hr F hF z] at hi
  change W^(Marks.packed T z).card * (_ * X^m) ≤ _ at hi
  rw [show (Marks.packed T z).card = z.card*m by
    rw [Marks.packed,Finset.card_product,Nat.mul_comm,Finset.card_univ]; rfl, pow_mul] at hi
  apply root_le (n:=m) Fintype.card_pos hh (by positivity)
  exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh.le h' _) (show 0 ≤ (W^z.card*X)^m by positivity))
    (arithmetic (pow_nonneg hW.le _) ht (mult_ge G l) hs hp hJ H.under hi Y.ready)
end
end Endpoint
end YM.Push.Corrected
