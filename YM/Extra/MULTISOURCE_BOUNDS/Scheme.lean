import YM.Extra.MULTISOURCE_BOUNDS.SystemPrices

/-!
# A more elementary offer towards `Unbilled.raw`

One *sufficient* procedure based on actual product, component, numbered
log, merger, and canonical-read terms. It is NOT claimed that the physical
RG map has data obeying this model! In particular global singleton units are
not admitted as arbitrarily large interacting vertices. Need component and
vacuum integrals/derivative estimates with `Forward`'s individual product
bounds (including κ on the *output* forced species) and with enough actual
support and derivative reserves. Need common production labels whose
multiplicities can be accounted for by the exact maps (not just equality of
a polynomial on a different alphabet), or justify more merger passes or other
altered inputs. In particular *one* overlap pass here for exclusions plus base
reset, which requires transparent supports/multiplicities through that whole
operation. A second pass for the combined section corrections. These are
price tests with hypotheses on the true arrays, not new constraints on the
spec of CLOSED; can instead prove `Raw` directly.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi.System
open Function Filter Lattice RG Source Wilson Overlay Marker Labels MeasureTheory Finset LogTerms Germs Merger Repeated
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff

variable {G : Gauge} {C : Family G} {V : Type} [DecidableEq V] {R : Census V} {N p m : ℕ}
    {D : V → ℕ}

def paint (C : Family G) (D : V→ℕ) (m) := duty (fun i => (C.S.block m).val ^ D i : V → ℝ)

def outlet (C : Family G) (D : V→ℕ) (A : Bands R (C.path.rep N p m)) : Layer G V (C.side m p) where
  Id := ℕ × ℕ
  supp i := Multi.forced (C.path.rep N p m) i
  names i := (tags A i).val
  value i := if mixed (tags A i) then (↑(paint C D m (tags A i).val):ℂ)⁻¹ • A.entries i.1 i.2 else 0

/-- Structural comparisons and pointwise merger-product tests on the actual
values. Anchor locations here and below are those of A (the desired output),
and reference prices/labels are from exactly C. Individual receipt hypotheses
for producing integrals in these arrays are in Forward. Sup-norm bounds of
forced mergers are instead DERIVED from `restore` and `finish`. -/
structure Scheme (C : Family G) (D : V → ℕ) (A : Bands R (C.path.rep N p m)) where
  marks : Layer G V (C.side m p) -- support/naming only needed for input vertices
  vac : Layer G V (C.side m p)   -- same
  reg : Layer G V (C.side m p)   -- integrated first-system unforced terms PRE log, PRE L^D
  hard : Layer G V (C.side m p)  -- integrated first-system d_X
  reset : Layer G V (C.side m p) -- base/reset/indicator partners (only unmarked)
  interim : Layer G V (C.side m p) -- forced AFTER exclusions/reset
  anchors : reg.Id → Site (C.side m p)
  no_marks i : vac.names i=∅
  no_renew i : reset.names i=∅
  cut : Slit C D A.origins reg.log
  matchLog : ∃ map : {j // mixed (A.rays j) ∧ A.H j ≠ 0} → reg.log.Id, Injective map ∧
    ∀ i, (A.rays i.val).val = reg.log.names (map i) ∧ A.support i.val = reg.joint (map i) ∧
      A.H i.val = (↑(paint C D m (A.rays i.val).val):ℂ) • reg.log.value (map i)
  restore : hard.Merge ((reg.negative (point C m)).combine reset) interim
  finish : interim.Merge cut.layer (outlet C D A)

/-- Unmarked prices, individual first-system kernel and inventory estimates.
These are needed only on an actual representation with structural receipt above;
they refer to `A'` = true input and `F` used to price the true output A. Values
of `Scheme.marks/.vac` aren't used, only their alphabets with support and the
absolute multiplicity and vertex prices.

Not assuming either the full mixed output mass estimate of the step or a
compatible mixed budget already attained along the run. Numeric hypotheses
before estimating tree series/resets. Use larger output exponent/pre-L flags
if hprice (=7 extra in Scope.inflate on the FINE side, shrinking geometry)
is not enough to attain these individual estimates without losing orders.
-/
structure Forward {A : Bands R (C.path.rep N p m)} (F : Scheme C D A)
    (A' : Bands R (C.path.rep N p (m+1))) (s : Scope) (loss : Tariff) (d : ℕ → ℕ) (ζ : ℕ → ℝ) : Prop where
  costs (e : Pieces → ℝ) : Inbox A' (divisor C (m+1)) e →
    let P := point C m; let Q := point C (m+1); let j := year C (m+1); let η := hat C m ^ (-ζ j)
    ∃ a : F.marks.Id→ℝ, ∃ b : F.vac.Id → ℝ, ∃ t : F.reset.Id → ℝ, ∃ g : F.reg.Id → ℝ, ∃ k : F.hard.Id → ℝ,
      (∀ i,0 ≤ a i) ∧ (∀ i,0 ≤ b i) ∧ F.reset.Covers t 1 ∧ F.hard.Covers k (divisor C m) ∧
      Fork (bids A') (blocks A') F.marks.names F.marks.supp A.origins (C.path.levels.clock.op m p).ratio
        (s.expand j) P.B Q.B (d j) e a (quote C m loss) ∧
      Ac.Hit F.vac.supp P.B b (P.supportExponent+6) η ∧ Ac.Hit F.reset.supp P.B t (P.supportExponent+3) η ∧
      (∀ i, F.anchors i∈F.reg.supp i ∧ P.Regular (F.reg.supp i) (F.reg.value i) ∧
        P.supBounds (F.anchors i) (F.reg.supp i) (F.reg.value i) (g i)) ∧
      Display (F.marks.combine F.vac).names (F.marks.combine F.vac).supp F.reg.names F.reg.supp (Sum.elim a b) g 1 ∧
      Display (F.marks.combine F.vac).names (F.marks.combine F.vac).supp F.hard.names F.hard.supp (Sum.elim a b) k 1

omit [DecidableEq V] in
lemma paint_pos (C : Family G) (m : ℕ) (names : Finset V) : 0 < paint C D m names := prod_pos fun i _ =>
    pow_pos (by exact_mod_cast (C.S.block m).property) _

omit [DecidableEq V] in
lemma earns (C : Family G) (m : ℕ) (names : Finset V) (w : V → ℝ) (τ : Tariff) :
    duty (fun v => w v / scaleFee C m τ (D v)) names * paint C D m names = duty (fun v => w v / quote C m τ) names := by
  rw [duty,paint,duty,← prod_mul_distrib]; exact prod_congr rfl fun i _ => by have := scaleFee_pos C m τ (D i); unfold scaleFee at *; field_simp

/-- Turning the intermediate receipts into `Spent mixed` after shipping the
actual normalized arrays with L^D per name. No cost depending on number of
placements. -/
theorem Scheme.raw_cost {A : Bands R (C.path.rep N p m)} (F : Scheme C D A) (H : C.Makes) (hm : m ≤ N) (hA : A.Active)
    (w : V → ℝ) {t : Tariff} (hw : ∀ v, 0 ≤ w v) (g : Tuple F.reg.Id → ℝ) (k : ℕ × ℕ → ℝ)
    (hg : ∀ i, 0 ≤ g i ∧ ∀ p∈F.reg.joint i, (point C m).supBounds p (F.reg.joint i) (F.reg.log.value i) (g i))
    (hk : (outlet C D A).Covers k (divisor C m))
    (hG : Rooted F.reg.log.names F.reg.joint (point C m).B ((point C m).supportExponent+1)
      (F.reg.log.weighted (fun v => w v / quote C m t) g) (quote C m t))
    (hK : let X := outlet C D A
      Rooted X.names X.supp (point C m).B ((point C m).supportExponent+1) (X.weighted (fun v => w v / quote C m t) k) (quote C m t)) :
      Spent mixed A (fun v => w v / scaleFee C m t (D v)) 1 (divisor C m) (quote C m t) := by
  obtain ⟨f,hi,hf⟩ := F.matchLog
  let Z := point C m
  have hZ := (H.wilson.represents N p m hm).vac
  let u v := w v / scaleFee C m t (D v)
  have hu v : 0 ≤ u v := div_nonneg (hw v) (scaleFee_pos ..).le
  let δ := Z.supportExponent+1
  let price := paint C D m
  let a i := if hi : mixed (A.rays i) ∧ A.H i ≠ 0 then price (A.rays i).val * g (f ⟨i,hi⟩) else 0
  let b i := if mixed (tags A i) then price (tags A i).val * (divisor C m * k i) else 0
  have ha i : 0≤a i := by dsimp only [a]; split; exact mul_nonneg (paint_pos ..).le (hg _).1; rfl
  have hb i : 0≤b i := by dsimp only [b]; split; exact mul_nonneg (paint_pos ..).le (mul_nonneg (divisor_pos ..).le (hk _).1); rfl
  refine ⟨⟨a,ha,fun i hi v hv => ?_,?_⟩,⟨b,hb,fun j hj U => ?_,?_⟩⟩
  · unfold a; split <;> rename_i h
    · obtain ⟨h₁,h₂,h₃⟩ := hf ⟨i,h⟩
      dsimp only at h₁ h₂ h₃
      have ht := hA.pins i v hv; rw [h₂] at ht
      rw [hZ,h₂,h₃]
      simpa only [Complex.norm_real,Real.norm_of_nonneg (paint_pos C m (A.rays i).val).le] using!
        Next.Foundations.bound_smul (paint C D m (A.rays i).val : ℂ) ((hg _).2 (A.origins v) ht)
    rw [show A.H i=0 by tauto]; exact supBounds_zero ..
  · intro v
    refine Budget.certify (fun i => ?_) fun s => ?_
    · split
      next => exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (prod_nonneg fun i _ => hu i) (ha i))
      exact le_rfl
    let s' := s.filter (fun i => v∈(A.rays i).val ∧ mixed (A.rays i) ∧ A.H i ≠ 0)
    let send : s' → F.reg.log.Id := fun i => f ⟨i.val,(mem_filter.mp i.property).2.2⟩
    let charge i := Real.exp (δ*coverNumber Z.B (A.support i))*(Poly.toll u (A.rays i)*a i)
    rw [hZ]
    calc
      _ = ∑ i∈s',charge i := Eq.symm ((sum_filter ..).trans (sum_congr rfl (fun i _ => by
        dsimp [a,charge,u,δ,Z]; split_ifs <;> first | rfl | tauto | simp)))
      _ = ∑ i:s',charge i := Finset.sum_coe_sort .. |>.symm
      _ ≤ _ := (le_of_eq ?_).trans (Budget.cap (hG v) (univ.image send))
    · have hs' : Injective send := fun i j hh => Subtype.ext (congr_arg (fun i : {j // mixed (A.rays j) ∧ A.H j ≠ 0} => i.val) (hi hh))
      rw [sum_image hs'.injOn]; refine sum_congr rfl fun i _ => ?_
      obtain ⟨hx,hy,hz⟩ := (mem_filter.mp i.property).2
      obtain ⟨h₁,h₂,h₃⟩ := hf ⟨i.val,hy,hz⟩; dsimp only at h₁ h₂
      have he : (F.reg.log.names (send i))=(A.rays i.val).val := h₁.symm
      dsimp only [a,charge]; rw [dif_pos (And.intro hy hz),h₂,he,if_pos hx,← mul_assoc (Poly.toll ..), Layer.weighted,he]
      change _*((duty u (A.rays i.val).val * price _)*g (send i)) = _; unfold u price; rw [earns]
  · have h := (hk j).2 U
    simp only [outlet, if_pos hj, Pi.smul_apply,norm_smul,norm_inv,Complex.norm_real, Real.norm_of_nonneg (paint_pos C m (tags A j).val).le] at h
    rw [show b j = _ from if_pos hj,mul_comm]; rw [inv_mul_eq_div] at h; exact (div_le_iff₀ (paint_pos ..)).mp h
  · intro v; refine Budget.mono (Budget.scale (hK v) (divisor_pos ..).le) (fun i => ?_) (fun i => ?_) le_rfl
    · split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (prod_nonneg fun v _ => hu v) (hb _)); rfl
    dsimp only [Layer.weighted,outlet]; rw [hZ]; split_ifs
    · unfold b; split
      next hm =>
        change _*(duty u (tags A i).val * (paint C D m _ * _)) ≤ _
        unfold u; rw [← mul_assoc (duty _ _),earns]; apply le_of_eq; ring
      next => rw [mul_zero,mul_zero]; exact mul_nonneg (divisor_pos ..).le (mul_nonneg (Real.exp_pos _).le
          (mul_nonneg (prod_nonneg fun i _ => div_nonneg (hw _) (zero_le_one.trans (quote_ge ..))) (hk i).1))
    exact (mul_zero _).symm.le
end YM.Extra.Multi.System
