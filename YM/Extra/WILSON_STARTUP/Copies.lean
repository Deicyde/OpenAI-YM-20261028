import YM.Extra.WILSON_STARTUP.MixRoom
import YM.Work.D01

/-!
# A top `Bands` for actual normalized C.O with all the centered copy orientations

One physical family.

No separate retunings at offsets.

Coefficients compensate
each hand and signed action at the terminal level *then* use the actual
terminal.symm in the chosen family (terminal values are not assumed bounded
uniformly in N).

`terminal_ready` below is just for the cutoff end of `Story`
(incidence, calibration, widths, and income for this particular layout), on the
explicit assumptions; `first_edition` prices its extra waits pre-schedule.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Mixture
open Function Filter RG Lattice Wilson Finset Overlay Source Mix Labels Cells Marker Start
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {d : ℕ} {n : Side} {F : Frame G d} (S : SectionData F)

def reoriented (U : Tiling n) (z : F.Coeff) (j : U.Cell) : F.Coeff :=
    let x := F.act (U.omega j).ortho z
    if U.hand j then star x else x

lemma coeff_norm (v : F.Coeff) : F.coeffSize v ≤ Fintype.card F.Index * ‖v‖ := by
  simpa [Frame.coeffSize] using sum_le_sum (s:=univ) (fun i _ => norm_le_pi_norm v i)

lemma cost_turn (F : Frame G d) : ∃ c : ℝ, 1 ≤ c ∧ ∀ {n : Side} (U : Tiling n) (z : F.Coeff) j,
    F.coeffSize (reoriented U z j) ≤ c * ‖z‖ := by
  let L := fun i : Signed => (F.act i.ortho).toContinuousLinearMap
  let w := Fintype.card F.Index
  refine ⟨1+w*∑ i, ‖L i‖, le_add_of_nonneg_right (by positivity),fun {n} U z j => ?_⟩
  have he : ‖reoriented U z j‖ ≤ (∑ i, ‖L i‖)*‖z‖ := by
    have hh := ((L (U.omega j)).le_opNorm z).trans (mul_le_mul_of_nonneg_right (single_le_sum (fun i _ => norm_nonneg (L i))
      (mem_univ (U.omega j))) (norm_nonneg z))
    unfold reoriented; split <;> simpa only [norm_star,L, LinearMap.coe_toContinuousLinearMap'] using hh
  exact (coeff_norm _).trans ((mul_le_mul_of_nonneg_left he (Nat.cast_nonneg w)).trans (by nlinarith only [norm_nonneg z]))

def quote (S : SectionData F) (r : ℝ) := (cost_turn F).choose * (1+|r|)* Mark.price S

theorem quote_pos (r : ℝ) : 0<quote S r := by unfold quote; have := Mark.price_ge_one S; have := (cost_turn F).choose_spec.1; positivity

variable {S}
variable (C : Family G) {N p : ℕ} (U : Tiling (C.side N p))

def turn (v : C.label d) : U.Cell → (C.labels.level d).Coeff := fun i => (C.factory d N p).terminal.symm (reoriented U v i)

def books (o : U.Cell → Site (C.side N p)) (v : C.label d) (R : Census U.Cell) :=
  overlay R (C.localSection d) o (C.path.rep N p N) (turn C U v)

def tide (r : ℝ) (d N : ℕ) := Mix.width C (quote (C.localSection d) r) (order (C.labels.level d)) N

lemma cost_back (hc : C.Makes) (d N p : ℕ) (hv : C.ref d ≤ N) (x : C.label d) :
    let F := C.labels.level d
    let L := ∏ j∈ range N, (C.path.levels.params (j+1)).columns
    F.coeffSize ((C.factory d N p).terminal.symm x) ≤ L*F.coeffSize x := by
  have hh := Work.D01.back_budget (p:=p) C hc x hv (N:=N) le_rfl
  dsimp only at hh ⊢; rw [(hc.calibrated d N p hv).bare_coord, Work.D01.columnLogs,Real.exp_sum] at hh
  simpa only [Real.exp_log (lt_of_lt_of_le one_pos (Stage.columns_ge ..))] using hh

lemma turned_fit (h : C.Makes) {v : C.label d} (hr : C.ref d ≤ N) {r : ℝ} (hb : ‖v‖ ≤ r) :
    let a := C.path.levels
    0 < tide C r d N ∧ ∀ i, Cap (turn C U v i) (C.localSection d) (a.params N).columns (a.clock.hatCoupling N) (tide C r d N) := by
  intro a
  let F := C.labels.level d
  let w := quote (C.localSection d) r
  let L := ∏ j∈ range N, (C.path.levels.params (j+1)).columns
  let s := (a.params N).columns
  have hs j : 0 < (a.params j).columns := one_pos.trans_le (Stage.columns_ge ..)
  have hs' : 0<s := hs N
  have hw : 0<w := quote_pos _ _
  have hL : 0<L := prod_pos fun j _ => hs _
  have hg : 0 < a.clock.hatCoupling N := inv_pos.mpr (Real.sqrt_pos.mpr (one_pos.trans (a.fits.delayed N)))
  refine ⟨div_pos (pow_pos hg _) (by change 0<w*s*L; positivity),fun i => ?_⟩
  have hK := Mark.price_ge_one (C.localSection d)
  have h' := (cost_turn F).choose_spec
  have hx : F.coeffSize (turn C U v i)* Mark.price (C.localSection d) ≤ w*L := by
    apply le_trans (mul_le_mul_of_nonneg_right (cost_back C h d N p hr _) (zero_le_one.trans hK))
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h'.2 U v i) hL.le) (zero_le_one.trans hK)).trans
    change L*_*_ ≤ w*L; unfold w quote; rw [mul_comm _ L, ← mul_assoc,← mul_assoc, ← mul_assoc]
    have h₁ : (cost_turn (C.labels.level d)).choose ≥ 1 := h'.1
    gcongr
    linarith [(le_abs_self r).trans_eq (rfl)]
  unfold Cap
  change _/(w*s*L)* _*(_*s) ≤ _
  let g := a.clock.hatCoupling N ^ order F
  have hp := mul_le_mul_of_nonneg_left hx (pow_pos hg (order F)).le
  change g / (w*s*L) * _ * _ ≤ g
  field_simp
  linarith

lemma copies_eq (h : C.Makes) {v : C.label d} (hr : C.ref d ≤ N) (i : U.Cell) (o : Site (C.side N p))
    (Q : Config G (C.side N p)) : U.copy i (C.O N p (d:=d) v o) Q = C.O N p (reoriented U v i) (U.copyMap i o) Q := by
  simp only [Tiling.copy,Tiling.copyMap,reoriented,← C.rotated h hr]; split
  · rw [C.reality h hr]
  rfl

theorem signal (h : C.Makes) {v : C.label d} (hr : C.ref d ≤ N) {o : U.Cell → Site (C.side N p)} {x : Site (C.side N p)}
    (ho : ∀ i,U.copyMap i x = o i) (hd : Mark.diameter (C.localSection d) ≤ (C.path.levels.budget N).B) (hw : Wide (C.path.rep N p N))
    (R : Census U.Cell) (s : R.Mode) (V) : ((books C U o v R).density V).part s =
      Ride.bump (C.S.a N) s (fun _ => d) * (bare (C.beta N p) V : ℂ) * ∏ i∈s.val,U.copy i (C.O N p v x) V := by
  obtain ⟨hP,hq,hv,heb⟩ := h.wilson.represents N p N le_rfl
  have hs := h.sections d
  have ht := fun i => Mark.stencil (C.localSection d) (C.path.levels.budget N) (C.side N p) hd (o i)
  rw [books,density hw (hP.symm ▸ ht) hs hv.labels, Poly.part_smul,LinearMarkers.across,(h.wilson.starts N p).2]
  have he : ((C.S.a N : ℂ)^d) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos N).ne')
  rw [Ride.bump, mul_comm (∏ i∈_,_) (↑(bare (C.beta N p) V):ℂ),mul_assoc,← Finset.prod_mul_distrib]
  simp_rw [copies_eq C U h hr, Family.O,TransferData.cylinder,ho, initial, Pi.smul_apply,smul_eq_mul]
  congr 1; apply Finset.prod_congr rfl; intro i _
  change _ = (C.S.a N : ℂ)^d * (((C.S.a N:ℂ)^d)⁻¹ * _)
  rw [mul_inv_cancel_left₀ he]
  unfold entire Mark.realMaskFree; rw [hP]; rfl

def issued (m N p : ℕ) (h : m≤N) (v : C.label d) :
    Bands (Stock.census (Site (C.side m p))) (C.path.rep N p N) := books C (center C.S p h 0) (camp C p m N) v _

structure Terminal (C : Family G) (m N p : ℕ) (h : m≤N) (v : C.label d) (w : ℝ) : Prop where
  meaningful : Stubs.Holds (issued C m N p h v) w
  reads (s : (Stock.census (Site (C.side m p))).Mode) : MeasureTheory.Integrable
    (Ride.Product (H:=C.path) (N:=N) (p:=p) (fun j => (center C.S p h 0).copy j (C.O N p (d:=d) v 0)) s)
      (law G (C.side N p) (C.beta N p))
  signals (s : (Stock.census (Site (C.side m p))).Mode) (U) : ((issued C m N p h v).density U).part s =
    Ride.bump (C.S.a N) s (fun _ => d) * (bare (C.beta N p) U : ℂ) * Ride.Product (H:=C.path) (N:=N) (p:=p)
      (fun j => (center C.S p h 0).copy j (C.O N p (d:=d) v 0)) s U


end YM.WilsonStartup.Mixture
