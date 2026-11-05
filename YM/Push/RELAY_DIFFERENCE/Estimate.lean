import YM.Next.FOUNDATIONS.SU2
import YM.Push.RELAY_DIFFERENCE.Stencils

/-!
# Rooted cost of a discrepancy array, with stopping levels

The input to the finite bound `density_price`
is polynomial representation data on the *actual* family (not a bound
on moments). Needs the simultaneous density, not a list of singleton
representations. Later we will use it on *signed difference markers*,
with their growing marker radius.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson RG Lattice Cells Marker Overlay Stock Bid
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {C : Family G} {N p m r e : ℕ} {f : Extraction.Order} {F : Trial C}

abbrev GridLane (C : Family G) (m N p : ℕ) :=
  Lane C.path (census (Site (C.side m p))) N p

/-- Centered copies at side a_m. Entirely arbitrary F, our main use is
`F = P(A) - A` at the cutoff. Unnormalized *multiplicative* push through
`L.Works`, divide once by the Wilson denominator, positive finite by construction.
No assertion that `L` exists! Adapted from the primary estimate Stock.est.
Every volume/site cost enters before rooting. Bill includes `e` every
copy's physical weight. u c d b: `Radial`'s real costs (incl b positive,
and nonnegativity of budgets implied as needed there).
-/
theorem density_price (hn : m ≤ N) (h : C.Makes) (F : Config G (C.side N p) → ℂ)
    (L : GridLane C m N p) (hl : L.Works r) {W u c d b : ℝ}
    (he : (L.sites r).Radial (fun _ => W) u c d b) (hW : 0 < W) (hf : ∀ i, L.load i=e)
    (hq : ∀ i,L.uses i=(center C.S p hn 0).copy i F) :
    (center C.S p hn 0).rootTest (C.beta N p) F ≤
      Real.exp (((C.S.a m/C.S.a r)^4)*Vac.treasury C.path.levels r + (u+c+d*b)) / ((C.S.a r ^ e)*W) := by
  let T := Site (C.side m p)
  let V := Stock.final T
  let n := Fintype.card T
  have h1 : ‖Ride.bump (C.path.S.a r) V L.load‖=((C.S.a r)^e)^n := by
    unfold Ride.bump V final
    simp_rw [hf,norm_prod,norm_pow,Complex.norm_real, Real.norm_of_nonneg (C.path.S.a_pos r).le,
      Finset.prod_const,Finset.card_univ]; rfl
  have h2 : Poly.toll (fun _ => W) V=W^n := by simp [Poly.toll,n,V,final]
  let a := C.S.a r
  let X := a^e*W
  let M := moment (C.path.β N p N) (Ride.Product L.uses V)
  let Y := ((C.S.a m/C.S.a r)^4)*Vac.treasury C.path.levels r + (u+c+d*b)
  have H := L.pays h.wilson hl he V
  have H' := H.trans (Real.exp_monotone (Vac.suffices_bill h.wilson hl.admits n ..))
  have he' : ‖M‖*X^n ≤ Real.exp ((n:ℝ)*Y) := by
    rw [h1] at H'
    have hx₁ : _ ≤ Real.exp (↑(Fintype.card (Site (C.path.levels.clock.schedule.side r p))) * Vac.treasury C.path.levels r +
         ↑n*(u+c+d*b)) := H'
    change (a^e)^n*‖M‖*Poly.toll (R:=(census _)) (fun _ => W) V ≤ _ at hx₁
    rw [show Fintype.card (Site (C.path.levels.clock.schedule.side r p)) = Fintype.card (Site (C.S.side r p)) from rfl,
        tallies C.S m r p] at hx₁
    change (a^e)^n*‖M‖*Poly.toll (R:=(census _)) (fun _ => W) V ≤ Real.exp ((n:ℝ)*_*_ + n*(u+c+d*b)) at hx₁
    rw [h2,mul_comm _ ‖M‖,mul_assoc, ← mul_pow] at hx₁
    apply hx₁.trans_eq; congr 1; unfold Y; ring
  have hv : (center C.S p hn (0:Site (C.side N p))).rootTest (C.beta N p) F=‖M‖^(n:ℝ)⁻¹ := by
    unfold M Ride.Product
    simp_rw [hq]; rfl
  exact hv.le.trans (Stock.spacer _ _ X n (norm_nonneg _) (mul_pos (pow_pos (C.S.a_pos _) _) hW) Fintype.card_pos he')

/-- Comparison rate from G09. Quote in two currencies, birth budget
E `≥...` and scale-r envelope paid by that. -/
def gamma : ℝ := 1/8

def escrow (C : Family G) (N i : ℕ) (E : ℝ) := E / gainChart C.path N i

lemma escrow_pos {E : ℝ} (h : 0 < E) : 0 < escrow C N r E := div_pos h (Real.exp_pos _)

lemma escrow_eq (E : ℝ) : escrow C N r E = Real.exp (gamma*C.S.scale r) * E * flight C (-gamma) (N,p) := by
  rw [escrow,gainChart, flight, div_eq_mul_inv, ←Real.exp_neg]
  rw [show ((1:ℝ)/8)=gamma from rfl,mul_comm (Real.exp _ ) E, mul_assoc,← Real.exp_add]
  rw [show C.path.S = C.S from rfl]; ring_nf

def fee (C : Family G) (m r e : ℕ) (a : ℝ) : ℝ :=
  Real.exp (((C.S.a m/C.S.a r)^4)*Vac.treasury C.path.levels r + (5:ℝ)) / ((C.S.a r ^ e)*a) * Real.exp (gamma*C.S.scale r)



/-- Discrepancy finite bound when the radius expands. These fixed
 per-marker bills are enough (match `I02`); do not forget their per-site
 vacuum bill. The whole prefactor `fee` independent of N and p once m r
 and stop budget fixed. Includes e powers; no d-vs-d+1 passage in rooting. -/
theorem repelled (h : m ≤ N) (hc : C.Makes) (F : Config G (C.side N p) → ℂ)
    (L : GridLane C m N p) (hh : L.Works r) {E a : ℝ} (he : 0 < E) (ha : 0 < a)
    (hR : (L.sites r).Radial (fun _ => a / escrow C N r E) 1 2 2 1)
    (hf : ∀ i,L.load i=e) (hw : ∀ i,L.uses i=(center C.S p h 0).copy i F) :
    (center C.S p h 0).rootTest (C.beta N p) F ≤ fee C m r e a * E * flight C (-gamma) (N,p) := by
  apply (density_price h hc F L hh hR (div_pos ha (escrow_pos he)) hf hw).trans_eq
  rw [fee, escrow_eq (p:=p)]; norm_num
  have hp := C.S.a_pos r
  unfold flight; field_simp

/-- Intermediate interface (will supply this from singleton and mixed
estimates). `e` the weight used through every scale of these arrays. -/
structure Centers (C : Family G) (f : Extraction.Order) (F : Trial C) (e : ℕ) (E : Cutoffs → ℝ) : Prop where
  holds : ∀ j : ℕ, ∃ m ≥ j, ∃ r ≥ m, ∃ a : ℝ, 0 < a ∧ f.late fun N p =>
    ∃ h : m ≤ N, 0 < E (N,p) ∧ ∃ L : GridLane C m N p, L.Works r ∧
      (L.sites r).Radial (fun _ => a / escrow C N r (E (N,p))) 1 2 2 1 ∧
      (∀ i,L.load i=e) ∧ (∀ i,L.uses i=(center C.S p h 0).copy i (F N p 0))

/-- licenses an actual rate for the centered arrays. For stencils
we can convert this directly to `close`. Use each m,r once fixed, no
assumption that all k have same cost C across cell sides. -/
theorem Centers.earn {E : Cutoffs → ℝ} (h : Centers C f F e E) (H : C.Makes) (hs : Slow C f E)
    (hF : Stencilled f F) {γ : ℝ} (hγ : γ < gamma) : CenterRents F (flight C (-γ)) f := by
  refine ⟨hF.literal, fun j => ?_⟩
  obtain ⟨m,hm,r,hr,a,ha,hh⟩ := h.holds j
  have he := (Order.fused f _).mp (hF.fits m)
  have hd : Slow C f fun i => fee C m r e a * E i := (Slow.const _).mul hs
  have hv := (Order.fused f _).mp (hd.sink hγ)
  refine ⟨m,hm,?_⟩
  unfold Order.late at hh he hv ⊢
  filter_upwards [he,hh,hv] with q hi hi' ho
  filter_upwards [hi,hi',ho] with k hx hR hu
  obtain ⟨ht,hf,L,hw,hW,hc,hq⟩ := hR
  exact ⟨ht,hx.choose_spec 0, (repelled ht H _ L hw hf ha hW hc hq).trans hu⟩

theorem CenterRents.closes {γ : ℝ} (h : CenterRents F (flight C (-γ)) f) (H : C.Makes) (hq : 0 < γ) :
    Bid.close C f F := by
  refine ⟨Function.curry (flight C (-γ)), ?_, h.rents H⟩
  rw [Function.uncurry_curry]
  exact flight_lands hq


end YM.Push.RelayDifference
