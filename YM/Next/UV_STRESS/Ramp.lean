import YM.Next.UV_STRESS.Stack



/-!
# Product comparison lanes after signed birth at k

Additional route to price the physical *input* estimates. Need real producers
of these finite representation costs, for instance along histories with suitable
`Duet`s. Below only the propagation & payoff from an ACTUAL density join already
attaining rooted budgets in the mask/flag/regular representation. No assumption
of any implication of some quantitative multi-source theorem not in the tree.

Stair operates *on the interval* ℓ,..,k≤N of this same trajectory N,p, no
fictitious Lane from k replacing N and asserting marginal laws are same. In the
next files use OLD real lanes for induction from N on ALL corresponding subsets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Lattice Wilson Overlay Marker Cells RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Census ι} {N p ℓ k h m : ℕ}

/-- Note that `(C.path.rep N p m).beta=C.path.β N p m`. Use this actual β at every step. -/
structure Stair (R : Census ι) (N p : ℕ) where
  representation (m : ℕ) : Bands R (C.path.rep N p m)
variable (X : Stair C R N p)
namespace Stair
variable (k ℓ : ℕ)

def echo (m : ℕ) (s : R.Mode) (U : Config G (C.side m p)) : ℂ := ((X.representation m).density U).part s

structure Limit (load : ι → ℕ) : Prop where
  active : ℓ ≤ k ∧ k ≤ N
  steps m : ℓ ≤ m → m < k → ∀ s,X.echo C m s= Ride.bump (C.S.block m).val s load •
    (operation C p m).push (C.path.β N p (m+1)) (X.echo C (m+1) s)
  paid m : ℓ ≤ m → m ≤ k → (X.representation m).Active ∧ ∃ w u c d b,(X.representation m).Radial w u c d b
  ancestors m : ℓ ≤ m → m < k → ∀ i,(X.representation m).origins i= (operation C p m).ratio.parent ((X.representation (m+1)).origins i)

variable {k ℓ}
end Stair

omit [Fintype ι] in
lemma bump_steps (m : ℕ) (s : R.Mode) (g : ι→ℕ) : Ride.bump (C.S.a m) s g =
    Ride.bump (C.S.block m).val s g * Ride.bump (C.S.a (m+1)) s g := by
  unfold Ride.bump
  rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro i _
  rw [← mul_pow, ← Complex.ofReal_mul,show (((C.S.block m).val:ℝ)*C.S.a (m+1))=C.S.a m from ?_]
  rw [C.S.a_step,mul_div_cancel₀ _ (by exact_mod_cast (C.S.block m).property.ne')]

variable (hp : C.Makes)

namespace Stair

/-- At the birth k we will prove actual moment matches from lower-level
representation estimates plus genuine integral identities. -/
def Lit (k : ℕ) (g : ι→ℕ) (values : R.Mode → ℂ) : Prop :=
    ∀ s,(∫ U, X.echo C k s U ∂prior G (C.side k p))= Ride.bump (C.S.a k) s g *
      (partition G (C.side N p) (C.beta N p):ℂ) * values s

include hp
private lemma inductive_eq {g : ι → ℕ} (h : X.Limit C k ℓ g) {m} (hl : ℓ≤m) (hm : m < k) (s : R.Mode) :
    (∫ U, X.echo C m s U ∂prior G (C.side m p))=
      Ride.bump (C.S.block m).val s g * (∫ U, X.echo C (m+1) s U ∂prior G (C.side (m+1) p)) := by
  simp_rw [h.steps m hl hm s, Pi.smul_apply,smul_eq_mul, integral_const_mul]
  congr 1
  obtain ⟨hh,w,u,c,d,b,hv⟩ := h.paid _ (hl.trans (Nat.le_succ _)) hm
  have ht := Nat.le_trans hm h.active.2
  have he : Integrable (X.echo C (m+1) s) (prior G _) := ((X.representation _).material hh hv
    (hp.wilson.represents N p _ ht).good (beta_positive hp.wilson ht).le s).1
  exact StepData.push_integral (C.path.levels.transition_mass ..) _ he

lemma echoes {g : ι→ℕ} {values : R.Mode → ℂ} (h : X.Limit C k ℓ g) (ht : X.Lit C k g values) (hm : m ≤ k) (hl : ℓ≤m) :
    X.Lit C m g values := by
  intro s
  induction hm using Nat.decreasingInduction with
  | self => exact ht s
  | of_succ m hm IH =>
    rw [inductive_eq C X hp h hl hm s, IH (hl.trans (Nat.le_succ _)),bump_steps C m s g]; ring

lemma attendant {g : ι→ℕ} {values : R.Mode → ℂ} {w : ι → ℝ} {u c d b : ℝ} (h : X.Limit C k ℓ g) (he : X.Lit C k g values)
    (hh : (X.representation ℓ).Radial w u c d b) (s : R.Mode) :
    ‖Ride.bump (C.S.a ℓ) s g‖ * ‖values s‖ * Poly.toll w s ≤ Real.exp ((Fintype.card (Site (C.side ℓ p)):ℝ) *
      Vac.treasury C.path.levels ℓ + Fintype.card ι*(u+c+d*b)) := by
  have hn : ℓ≤N := h.active.1.trans h.active.2
  have hx := hp.wilson.represents N p ℓ hn
  let F := C.path.levels.clock
  have hm := C.path.partition_eq hp.wilson N p ℓ hn
  have hC : 0 < F.hatCoupling ℓ := inv_pos.mpr (Real.sqrt_pos.2 (lt_trans zero_lt_one (C.path.levels.fits.delayed _)))
  have hg : F.hatCoupling ℓ ≤ (C.path.rep N p ℓ).p.threshold := by
    rw [hx.vac]; change _ ≤ F.hatCoupling ℓ * Real.exp _; exact le_mul_of_one_le_right hC.le (Real.one_le_exp (sq_nonneg _))
  have ht := (X.representation ℓ).total ((h.paid ℓ le_rfl h.active.1).1) hh hx.good
    (beta_positive hp.wilson hn).le _ hC hg (C.path.nonnegative hp.wilson N p ℓ hn) s
  rw [hm, show (∫ x, ((X.representation ℓ).density x).part s ∂prior G _)= _ from X.echoes C hp h he
      h.active.1 le_rfl s, norm_mul,norm_mul, mul_right_comm _ _ ‖values s‖,Complex.norm_real,
      Real.norm_of_nonneg (partition_pos _).le,mul_div_cancel_right₀ _ (partition_pos (C.beta N p)).ne'] at ht
  exact ht.trans (Real.exp_monotone (Vac.suffices_bill hp.wilson hn ..))
end Stair

include hp
lemma lifted_spine {X : Stair C (Stock.census (Site (C.side h p))) N p} {d : ℕ} {s : (Stock.census (Site (C.side h p))).Mode → ℂ}
    {W u c b a : ℝ} (H : X.Limit C k ℓ (fun _ => d)) (ht : X.Lit C k (fun _ => d) s)
    (he : (X.representation ℓ).Radial (fun _ => W) u c b a) (hW : 0 < W) :
    ‖s (Stock.final (Site (C.side h p)))‖ ^ ((Fintype.card (Site (C.side h p)) : ℝ)⁻¹) ≤
      Real.exp (Stock.expPrice C h ℓ d W u c b a) := by
  let T := Site (C.side h p)
  let V := Stock.final T
  let n := Fintype.card T
  have h1 : ‖Ride.bump (C.S.a ℓ) V (fun _ => d)‖ = ((C.S.a ℓ)^d)^n := by
    simp only [Ride.bump,V,Stock.final, norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le,
      Finset.prod_const, Finset.card_univ]; rfl
  have h2 : Poly.toll (fun _ => W) V=W^n := by simp only [Poly.toll,V, Stock.final,Finset.prod_const, Finset.card_univ]; rfl
  let s' := C.S.a ℓ ^ d * W
  have hs : 0 < s' := mul_pos (pow_pos (C.S.a_pos _) _) hW
  let q := ((C.S.a h/C.S.a ℓ)^4)*YM.Vac.treasury C.path.levels ℓ + u+c+b*a
  have hz : ‖s V‖ * s'^n ≤ Real.exp ((n:ℝ)*q) := by
    have hw := X.attendant C hp H ht he V
    rw [h1,h2,mul_comm _ ‖s V‖,mul_assoc,← mul_pow] at hw
    apply hw.trans_eq; congr 1; unfold q
    rw [show (C.side ℓ p)=C.S.side ℓ p from rfl, Stock.tallies C.S h ℓ p]; dsimp only [n,T]; ring
  apply (Stock.spacer _ _ _ n (norm_nonneg (s V)) hs Fintype.card_pos hz).trans_eq
  unfold s' Stock.expPrice q
  rw [Stock.a_log C.S ℓ,← Real.exp_nat_mul,show W=Real.exp (Real.log W) from (Real.exp_log hW).symm,
    Real.log_exp, ← Real.exp_add, ← Real.exp_sub]; congr 1; ring
end YM.Next.UVStress
