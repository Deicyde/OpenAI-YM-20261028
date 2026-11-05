import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Procession

/-! # Early bounds on curve-labelled path terms
 Not yet after cancellations. Keep mass measured at exponent +3 already here.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Song
open Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Geo
open Extra.Iteration  WilsonStartup
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {ι : Type} (R : PathData G) (c : Clip) (p : BudgetPoint)
variable {l : ℕ} (A : ℕ→Atom G l) {σ C Λ : ℝ}

def headline (p : BudgetPoint) : BudgetPoint := {p with supportExponent := preExponent p, exponent_pos := by unfold preExponent; linarith [p.exponent_pos] }

theorem enhanced (A : ι→RegularAddress n) (f : ι→ℝ) (c : ℝ) (h : Quotes.anchored (headline p) A f c) : Quotes.early p A f c := by
  intro i; convert h i using 2 with x; dsimp only; split_ifs; exact mul_comm ..; rfl

def sine (β : ℝ) (i : ℕ) := |factor*β| *(turnFee p * Next.Scheduling.Wages.price p (A i))
lemma sine_pos (β : ℝ) (i : ℕ) : 0≤ sine p A β i := mul_nonneg (abs_nonneg _) (mul_nonneg (turnFee_pos p).le (Wages.fin p (A i) (0:Site ⟨1,by omega⟩)).nonneg) -- n issue

def tenor (G : Gauge) (l : ℕ) (p : BudgetPoint) (σ t β : ℝ) := |factor*β| * (turnFee p * (Geo.highFee G l p σ*p.threshold^l*t))
lemma act_lp (β : ℝ) (he : 0<σ) (h : SumBudget (fun i=> (A i).budget σ) C) : SumBudget
    (fun i=> sine p A β i*Real.exp ((σ/2)*(A i).length)) (tenor G l p σ C β) := by
  let S:= turnFee p; let D:= highFee G l p σ
  have hs : 0 ≤ S := (turnFee_pos p).le
  have heD : 0 ≤ D := (Geo.highFee_pos G p l he).le
  let d:= p.threshold^l; have hd : 0 ≤ d := pow_nonneg p.threshold_pos.le l
  refine budget_mono (Cost.scale (Cost.scale (Cost.scale h (D*d) (by positivity)) _ hs) |factor*β| (abs_nonneg _)) ?_ fun j=>?_
  · intro i; exact mul_nonneg (sine_pos p A β i) (Real.exp_pos _).le
  unfold sine; rw [mul_assoc, mul_assoc _ _ (Real.exp _)]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); apply mul_le_mul_of_nonneg_left _ hs
  rw [Wages.scan, Atom.budget]; let t:ℝ := (A j).length; have hz : 0≤t := Nat.cast_nonneg _
  let g:= Wages.grade l p.power p.order; let b:= Wages.startup G l p.power p.order; let w:= (A j).magnitude
  change b*d*w*(t+1)^g*Real.exp ((σ/2)*t)≤ D*d*(w*Real.exp (σ*t))
  have hw : 0 ≤ b*d*w := mul_nonneg (mul_nonneg (show 0≤b by have hh := Wages.slot_ge G p.power p.order 0; unfold b Wages.startup; positivity) hd) (by unfold w Atom.magnitude; positivity)
  rw [add_comm t]
  apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (spendMoment g (half_pos he) hz) hw) (Real.exp_pos _).le) ?_
  rw [show σ*t=σ/2*t+σ/2*t by ring,Real.exp_add]; change _ ≤ b*momentPrice g _*_*_; apply le_of_eq; ring

def octave (l : ℕ) := 2*l+4
lemma singBook (β : ℝ) (h : SumBudget (fun i=> (A i).budget σ) C) (hs : 0<σ) (he : preExponent p / p.B ≤ σ/2) : Quotes.early p (pitch (n:=n) A) (fun i => sine p A β i.2)
    (anchoredFee (headline p) (octave l)*tenor G l p σ C β) := by
  apply enhanced; refine Quotes.channel_mass (p:=headline p) (fun i=> (A i).length) (fun i=> (A i).footprint 0) _ (sine_pos p A β) (act_lp p A β hs h) (octave l) he ?_
  intro i; have ht:= Wages.traversed (A i) (0:Site n) p.B p.B_pos; change p.B* _ ≤ p.B*octave l+_; refine ht.trans ?_; unfold octave; nlinarith

def mezzo (γ : ℝ) (i : Low) := |factor*γ| * (turnFee p*(|i.mark R c| * lowCost G p (i.length R)*p.threshold^2))
def host (G : Gauge) (c : Clip) (p : BudgetPoint) (σ C γ : ℝ) := |factor*γ| * (turnFee p*p.threshold^2 * (lowFee G p σ * lowerSize c C))
lemma mezzo_pos (γ : ℝ) (i : Low) : 0 ≤ mezzo R c p γ i := by unfold mezzo; have := turnFee_pos p; have := low_nonneg G p (i.length R); positivity
lemma mezzoBook (γ : ℝ) (h : R.Bounds c σ C Λ) (he : preExponent p / p.B ≤ σ/2) : Quotes.early p (fun i:Tally n=>strings R p (.inl i)) (fun i => mezzo R c p γ i.2)
    (anchoredFee (headline p) lowCount*host G c p σ C γ) := by
  apply enhanced; apply Quotes.channel_mass (p:=headline p) (Low.length R) (fun i=> i.home R p (0:Site n)) _ (mezzo_pos R c p γ) _ lowCount he fun i=> low_geometry p R i _
  convert (Cost.scale (Cost.scale (low_budget G p R h) (turnFee p*p.threshold^2) (mul_nonneg (turnFee_pos _).le (sq_nonneg _))) |factor*γ| (abs_nonneg _)) using 2 with i
  unfold mezzo; ring
  rfl

def octaveNeed (G : Gauge) (p : BudgetPoint) (c : Clip) (σ C Λ β γ : ℝ) := anchoredFee (headline p) lowCount*host G c p σ C (-γ) +
    (anchoredFee (headline p) (octave 3)*tenor G 3 p σ C (-β) +(anchoredFee (headline p) (octave 4)*tenor G 4 p σ C (-β) + anchoredFee (headline p) (octave 2)*tenor G 2 p σ Λ (-1)))
lemma stanzaReady (β γ : ℝ) (hs : R.Bounds c σ C Λ) (hp : Decent c p) (he : preExponent p / p.B ≤ σ/2) : ∃ f : Songbook n →ℝ, Quotes.early p (strings R p) f (octaveNeed G p c σ C Λ β γ) ∧
    ∀ i,p.Regular (strings R p i).support (sounding R c β γ i) ∧ p.supBounds (strings R p i).site (strings R p i).support (sounding R c β γ i) (f i) := by
  let f : Songbook n→ℝ := Sum.elim (fun i=> mezzo R c p (-γ) i.2) (Sum.elim (fun i=> sine p R.cubic (-β) i.2) (Sum.elim (fun i=> sine p R.quartic (-β) i.2) (fun i=> sine p R.loop (-1) i.2)))
  refine ⟨f,fun i=> ?_,fun i=>?_⟩
  · exact Cost.sum (mezzoBook R c p (-γ) hs he i) (Cost.sum (singBook p R.cubic (-β) hs.three hs.width he i) (Cost.sum (singBook p R.quartic (-β) hs.four hs.width he i) (singBook p R.loop (-1) hs.two hs.width he i)))
  rcases i with i|i|i|i
  · exact tally_charge R c p i (-γ) hp
  · exact pitch_charge p _ i (-β) fun i => (hs.invariant i).2.1
  · exact pitch_charge p _ i (-β) fun i => (hs.invariant i).2.2
  exact pitch_charge p _ i (-1) fun i => (hs.invariant i).1
end YM.PhysicalNext.Repeat.Song
