import YM.Bid.Corners
import YM.Next.EXTRACTION.Tails
import YM.Push.CORRECTED_COLUMNS.FinalBill
import YM.Push.CORRECTED_COLUMNS.Placement
import YM.Work.B04
import YM.Work.B06
import YM.Work.E01


/-!
# The fixed Wilson input

Producer gate for one d. No parameter from a phase. `Tests` and
`Offer` here do NOT include RankWidths, or a bound on root z,
or an estimate of physical moments. They request terminal-scale RG estimates
with true marked density identities and local value bounds with uniform
costs, also at the restored radii. Separate witness for lift budgets,
so one does not infer anything at all periods for the estimates from later
fused convergence. Mark `i` below is a *row*, the other index a column
of the full free matrix. Every slot, including pair spectators in every
column, uses the same finite weights/c caps.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected
open Filter Function Set Lattice Wilson RG MeasureTheory Cells Marker
open Overlay Extraction
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {S T : Table C.book} {d : ℕ}
abbrev Row (X : Columns C S d) := Fin X.amount
abbrev Mark (X : Columns C S d) (r : Row X) := Fin ((X.row r).extra+1)
abbrev AxisX (X : Columns C S d) := Fin (X.dim+1)
abbrev label (X : Columns C S d) (i c s) := X.basis (Columns.Trials.names (X:=X) i c s)

/-- Actual cutoff normalized columns of d. Strong padding for Basis inputs
outside eventual grids. For all `k`, `at (N,p)` below refers to the very same
`C` actual fields. No convergence assumption. Rows fixed independently of
both cutoffs, even when using a proper subsequence below. -/
structure Tests (X : Columns C S d) where
  B : Series C
  room : Placed X B
  tune (k N p : ℕ) : AxisX X → C.label d
  real (k N p i) : star (tune k N p i)=tune k N p i
  unit (k N p) : tune k N p 0=C.refUnit d

namespace Tests
variable {X : Columns C S d} (Y : Tests X)

def place (k : ℕ) (i : Row X) : Points ((X.row i).extra+1) := Y.B.site k (X.row i).expected
def location (k N p : ℕ) (i : Row X) (s : Mark X i) := Cells.location C.S (Y.B.depth k) N p (Y.B.address k (X.row i).expected s)
def letter (k N p : ℕ) (i : Row X) (c : AxisX X) (s : Mark X i) :=
    C.O N p (d:=d) (Y.tune k N p (Columns.Trials.names (X:=X) i c s)) (Y.location k N p i s)

def reads (k : ℕ) (i : Row X) := Y.B.rescaled k (X.row i).expected

-- Components c_U (in the code `(Columns.Trials).singleton`, `.cumulant`).
def one (k : ℕ) (i : Row X) (c : AxisX X) (s : Mark X i) := (standard C).useAt (standard C)
  (points (fun _ : Fin 1 => Y.reads k i s)) (fun _ => ⟨d,label X i c s⟩)
def pair (k : ℕ) (i : Row X) (c : AxisX X) (s t : Mark X i) := (standard C).useAt (standard C)
  (points ![Y.reads k i s, Y.reads k i t]) ![⟨d,label X i c s⟩,⟨d,label X i c t⟩] - Y.one k i c s * Y.one k i c t

def cumulant (k : ℕ) (i : Row X) (c : AxisX X) : Marks.Algebra (Mark X i) :=
  Poly.inject fun v => (∑ s : Mark X i, if v.val={s} then Y.one k i c s else 0) +
    ∑ s : Mark X i, ∑ t : Mark X i, if s<t ∧ v.val={s,t} then Y.pair k i c s t else 0

-- no constant part
lemma none (k i c) : Marks.part (Y.cumulant k i c) ∅=0 := by
  change (∑ s : Mark X i, if (∅:Finset _)={s} then _ else 0)+(∑ s : Mark X i, ∑ t : Mark X i,if s<t∧(∅:Finset _)={s,t} then _ else 0)=_
  simp
  exact Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun j _ => if_neg (fun h =>
    Finset.nonempty_iff_ne_empty.mp (Finset.insert_nonempty s {j}) h.2.symm)
lemma alone (k i c s) : Marks.part (Y.cumulant k i c) {s}=Y.one k i c s := by
  have he (t j : Mark X i) : ¬(t<j ∧ ({s}:Finset _)={t,j}) := by
    rintro ⟨h,e⟩; exact absurd (congr_arg Finset.card e) (by simp [Finset.card_pair h.ne])
  change (∑ j : Mark X i, if {s}=({j}:Finset _) then _ else 0)+(∑ t : Mark X i, ∑ j : Mark X i,if t<j∧({s}:Finset _)={t,j} then _ else 0)=_
  simp only [if_neg (he _ _), Finset.sum_const_zero,add_zero, Finset.singleton_inj]
  simp
lemma both (k i c s t) (h : s<t) : Marks.part (Y.cumulant k i c) {s,t}=Y.pair k i c s t := by
  have he (v : Mark X i) : ({s,t}:Finset _)≠{v} := by intro e; exact absurd (congr_arg Finset.card e) (by simp [Finset.card_pair h.ne])
  have hv (j v : Mark X i) : (j<v ∧ ({s,t}:Finset _)={j,v}) ↔ s=j ∧ t=v := by
    constructor
    · rintro ⟨hx,hv⟩
      have hA : s∈({j,v}:Finset _) := hv ▸ Finset.mem_insert_self ..
      have hB : t∈({j,v}:Finset _) := hv ▸ Finset.mem_insert_of_mem (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at *
      rcases hA with e|e <;> rcases hB with f|f
      · exact (h.ne (e.trans f.symm)).elim
      · exact ⟨e,f⟩
      · exact (hx.not_gt (show v<j from e ▸ f ▸ h)).elim
      exact (h.ne (e.trans f.symm)).elim
    rintro ⟨rfl,rfl⟩; exact ⟨h,rfl⟩
  change (∑ j : Mark X i, if {s,t}=({j}:Finset _) then _ else 0)+(∑ j : Mark X i, ∑ v : Mark X i,if j<v∧({s,t}:Finset _)={j,v} then _ else 0)=_
  simp only [if_neg (he _), Finset.sum_const_zero,zero_add,hv]
  rw [Finset.sum_eq_single s]
  · simp
  · intro b hb h; simp [Ne.symm h]
  simp

def pattern (k N p : ℕ) (i : Row X) (c : AxisX X) (U : Config G (C.side N p)) :=
    Marks.adjusted (Y.cumulant k i c) fun s => Y.letter k N p i c s U

lemma single (k N p i c s U) : Marks.part (Y.pattern k N p i c U) {s}=Y.letter k N p i c s U-Y.one k i c s := by
  rw [pattern,Marks.corrected_single _ (none Y ..), Y.alone]
lemma pairs (k N p i c s t U) (h : s<t) : Marks.part (Y.pattern k N p i c U) {s,t}=
    (Y.letter k N p i c s U-Y.one k i c s)*(Y.letter k N p i c t U-Y.one k i c t)-Y.pair k i c s t := by
  rw [pattern,Marks.corrected_pair _ (none Y ..) _ s t h.ne, Y.alone,Y.alone,Y.both _ _ _ _ _ h]
lemma meaningful (k N p i c u) : Continuous fun U => Marks.part (Y.pattern k N p i c U) u := by
  have he s : Continuous (Y.letter k N p i c s) := C.continuousO ..
  let XU (U : Config G (C.side N p)) := Marks.ordinary fun s => Y.letter k N p i c s U
  have hh : Continuous XU := continuous_finsetProd _ fun j _ => continuous_const.add ((Bands.sends _).comp (he j))
  exact (Poly.part_cont (Marks.mode u)).comp (continuous_const.mul hh)


lemma anchor (k N p i s) (h : Y.B.depth k≤N) :
    let hr := (Y.B.side_le k).trans h
    let T := center C.S p hr 0
    ∀ j : Site (C.side (Y.B.side k) p), (C.S.toDepth hr p).parent (T.copyMap j (Y.location k N p i s))=j := by
  exact Positions.parentCopy C.S (Y.B.side_le k) h _ ((Y.room k i).2 s)

end Tests

/-- Uniform terminal per-site expense Q (includes Haar multiplier). `runs`
is numerical, requires comparing all costs after restoration of W, even
when J,L increase. Typically buy Q <= (γ-η)*log(monitor at k) with W =
monitor^γ and η>0. `since` is a small-field LENGTH in terminal variables,
can shrink with k, used only at fixed k. Uniform at fixed k in p. -/
structure Prices where
  since : ℕ → ℝ
  rate : ℕ → ℝ
  Q : ℕ → ℝ
  W : ℕ → ℝ
  tiny (k) : 0 < since k
  little k : since k ≤ 1
  weight k : 1 ≤ W k
  margin (k) : 0 < rate k
  runs : Tendsto (fun k => Real.exp (Q k)/ W k) atTop (𝓝 0)

namespace Tests
variable {X : Columns C S d} (Y : Tests X)

/-- Producer inputs at the final push of these actual marks. Lens can
restart only on the authorized stretch. Not assuming small moments,
instead need VALUE caps with actual restored W and enough per-site bills.

`known` separately: one D per k,d basis for all periods; N tail at EACH p,
not necessarily uniform in p. `solves` needs existence along `late`.
One output Rep, `l` rate and path used in all rows, even if each mark's
gas line retains different forced coefficients on that dictionary. -/
structure Offer (P : Prices) (f : Extraction.Order) : Prop where
  known (k : ℕ) : ∃ D : ℝ, 0≤D ∧ ∀ p, ∀ᶠ i : ℕ in atTop, ∀ c, ‖Y.tune k (f.mesh i) p c‖ ≤ D
  solves (k : ℕ) : f.late fun N p =>
    ∃ (h : Y.B.depth k ≤ N) (B : Wire C (Y.B.side k) (Y.B.depth k) N p) (R : Rep G (C.side (Y.B.side k) p))
      (s σ A Λ d' w : ℝ), P.since k≤s ∧ Endpoint.Resolved B ((Y.B.side_le k).trans h) R s (P.rate k) σ A Λ d' w ∧
      ∀ i c, ∃ M u b C', Endpoint.Sources B ((Y.B.side_le k).trans h) (Y.pattern k N p i c) R (P.rate k) s A Λ d' w (P.W k) (P.Q k) M u b C' ∧
        ∀ j, M.origins j=j.1

namespace Offer
variable {P : Prices} {f g : Extraction.Order}
lemma tails (h : Next.Extract.Tails g f) (H : Y.Offer P f) : Y.Offer P g where
  solves k := h.late (H.solves k)
  known k := by obtain ⟨D,hD,hP⟩ := H.known k; exact ⟨D,hD,fun p => h.mesh.holds (fun N => ∀ c, ‖Y.tune k N p c‖ ≤ D) (hP p)⟩

/-! No interchange of limits, spend the four-global-links factor at fixed k. -/
private lemma frequency (k : ℕ) : Tendsto (fun i : ℕ => Fintype.card (Site (C.side k (f.per i)))) atTop atTop := by
  simp_rw [site_card]
  have he : Tendsto (fun i : ℕ => (C.side k (f.per i)).val) atTop atTop :=
    tendsto_atTop_mono (fun i : ℕ => (Nat.le_mul_of_pos_right ((C.S.period (f.per i)).val) (C.S.denominator k).property))
      (C.S.period_strict.tendsto_atTop.comp f.per.cofinal)
  apply tendsto_atTop_mono (f:=fun i => (C.side k (f.per i)).val) ?_ he
  intro i
  let x := C.side k (f.per i)
  exact show x.val ≤ x.val^4 from (pow_one x.val).symm.le.trans (pow_le_pow_right₀ (show 1 ≤ x.val from x.property) (by norm_num))

/-- Every subset estimate of the exact determinant-corrected test, at the
regulator. In iterated epsilon-slack sense, not claiming per-period norms
on every period. Sign/radii independent of how many copies. -/
theorem stamp (H : Offer Y P f) (k : ℕ) (ε : ℝ) (hε : 0 < ε) : f.late fun N p =>
    ∃ h : Y.B.depth k ≤ N,
      let T := center C.S p ((Y.B.side_le k).trans h) (0 : Site (C.side N p))
      ∀ i c (s : Finset (Mark X i)), s.Nonempty →
        T.rootTest (C.beta N p) (fun U => Marks.part (Y.pattern k N p i c U) s) ≤ Real.exp (P.Q k)/P.W k+ ε := by
  let w := G.probHaar.real (G.shell (P.since k/4))
  let m i := Fintype.card (Site (C.side (Y.B.side k) (f.per i)))
  have hx := frequency (C:=C) (f:=f) (Y.B.side k)
  have hh : 0 < w := by
    have hP := P.tiny k; have hq := P.little k
    exact lt_of_lt_of_le (pow_pos (by positivity) _) (G.shell_ge (P.since k/4) (by positivity) (by linarith))
  have he := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hx : Tendsto (fun i => (m i:ℝ)) atTop atTop)
  let q := P.W k
  have hg : 0 < q := zero_lt_one.trans_le (P.weight k)
  let A := Real.exp (P.Q k)
  have ht : Tendsto (fun i => (w^4:ℝ)⁻¹ ^ (((m i):ℝ)⁻¹) * A / q) atTop (𝓝 (A/q)) := by
    have hp := ((tendsto_const_nhds (x := (w^4:ℝ)⁻¹)).rpow he (Or.inl (by positivity))).mul_const A
    simpa using hp.div_const q
  have h := H.solves k
  unfold Order.late at *
  filter_upwards [h, ht.eventually (ge_mem_nhds (show A/q < A/q+ε by linarith))] with j hj hq
  refine hj.mono ?_
  rintro n ⟨hN,B,R,a,σ,D,l,d',b,ha,H',hi⟩
  have hb : w≤ G.probHaar.real (G.shell (a/4)) := measureReal_mono
    (s₁ := G.shell (P.since k / 4)) (fun x hx => le_trans (show G.chord x ≤ P.since k/4 from hx) (show P.since k/4 ≤ a/4 by linarith)) (measure_ne_top _ _)
  refine ⟨hN,fun i c s hs => ?_⟩
  obtain ⟨W',u,U',c',e,hj⟩ := hi i c
  refine (Endpoint.ticket (Y.meaningful k _ _ i c) hh hb (P.margin _) H' hg e s).trans ((_root_.le_trans ?_ (show (w^4:ℝ)⁻¹ ^ (((m j):ℝ)⁻¹)*A/q ≤ _ from hq)))
  refine div_le_div_of_nonneg_left (by positivity) hg ?_
  conv_lhs => rw [← pow_one q]
  exact pow_le_pow_right₀ (P.weight k) (show 1 ≤ s.card from Finset.card_pos.mpr hs)
end Offer
end Tests
end YM.Push.Corrected
