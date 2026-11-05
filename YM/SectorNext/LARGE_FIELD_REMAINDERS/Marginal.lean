import YM.Bid.Craft
import YM.Push.SECTOR_MEASURE.Payment
import YM.Push.SECTOR_MEASURE.Presented
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Joint
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Weights


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Joint-sector L1 charges (still no Gaussian substitution)

Resource independent of the seed list except THROUGH the retained probabilities:
a column can cost more (the shield option estimates even with the coarse sieve
factored *in*, so can cost less in bulk); an external volume bill for defect
free integration & projector work; and per-seed post-L costs. Total resources
of these various choices/allocations **sum** to at most the same volume bill (for
common parameters, direction V, forest), no seed count needed for that assertion.
Still before extensive RG/vacuum or extracting the full interacting coarse base. Use
this also for testing summability of still-function multipliers which are only
controlled on their own intact sectors. Norms, fixed V, all genuine integrals.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector Scales Oriented Presented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure

variable {G : Gauge} {c f n : Side} {S : StepData c f} {x W γ : ℝ} (d : Allocation G S x W)
  (m : Mode) (F : Forest S.ratio) (V : Config G c)

def nt {g : Ratio c f} (F : Forest g) := Fintype.card F.Free

def pilot (F : Forest S.ratio) (V : Config G c) (i : F.Free) : G.El := replica S.ratio V i

/-- k-section of the common resource. -/
def room (A : Stores S) (C γ s : ℝ) (k : S.Choices) : ℝ :=
  ∫ a, d.bill A k (F.drape a) V * (S.likelihood (F.drape a) k * m.lamp (pilot F V) C γ s a) ∂F.order G

def seats (A : Stores S) (C γ s : ℝ) : ℝ := ∑ k : S.Choices, room d m F V A C γ s k

lemma room_nonneg (A : Stores S) (C γ s : ℝ) (hs : 0≤s) (k : S.Choices) : 0≤room d m F V A C γ s k := by
  apply integral_nonneg; intro a
  exact mul_nonneg (d.nonneg ..) (mul_nonneg (S.likelihood_pos _ _) (m.lamp_nonneg _ _ _ _ hs _))

lemma seats_nonneg (A : Stores S) (C γ s : ℝ) (hs : 0≤s) : 0≤seats d m F V A C γ s :=
  Finset.sum_nonneg fun i _ => room_nonneg d m F V A _ _ s hs i

lemma room_int (A : Stores S) (C γ s : ℝ) (k : S.Choices) (hB : S.patch.Branches S.kernel G) :
    Integrable (fun a => d.bill A k (F.drape a) V * (S.likelihood (F.drape a) k * m.lamp (pilot F V) C γ s a))
      (F.order G) := by
  exact ((d.envelope hB (V:=fun _ => V) F.continuous_drape.measurable measurable_const A k).mul
    ((env_likelihood k hB F.continuous_drape.measurable).mul (m.lamp_env _ ..))).integrable _

/-- Includes all A on the common probability space. -/
lemma seats_price (m : Mode) (G : Gauge) (C γ : ℝ) (hC : 0<C) (hγ : 0<γ) : ∃ H : ℝ, 1≤H ∧
    ∀ (c f : Side) (S : StepData c f) (x W : ℝ) (d : Allocation G S x W)
    (F : Forest S.ratio) (V : Config G c), S.patch.Branches S.kernel G → ∀ s : ℝ, 0<s →
    ∑ A, seats d m F V A C γ s ≤ (H*s^dim G)^nt F := by
  obtain ⟨H,hH,h⟩ := Mode.lamp_price (G:=G) m C γ hC hγ
  refine ⟨H,hH,fun c f S x W d F V hB s hs => ?_⟩
  let N := fun (k : S.Choices) a => S.likelihood (F.drape a) k * m.lamp (pilot F V) C γ s a
  have hi (k : S.Choices) : Integrable (N k) (F.order G) :=
    ((env_likelihood k hB F.continuous_drape.measurable).mul (m.lamp_env _ ..)).integrable _
  apply le_trans ?_ (h F.Free (pilot F V) s hs)
  refine le_of_eq ?_
  change ∑ A, d.column A F V N = ∫ a, _ ∂(F.order G)
  rw [d.partitions hB F V _ hi]; unfold tagTotal
  rw [← integral_finsetSum _ fun i _ => hi i]
  apply integral_congr_ae; filter_upwards with a; unfold N
  rw [← Finset.sum_mul,S.chosen hB _,one_mul]

/-- Bool o = true uses whole `meanRest` in the exact push expression, otherwise the
canonical `unassigned`. `Mode` controls whether spending the *cut* V factor. -/
def rest (o : Bool) (T : Tube G S) (A : Stores S) (x : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :=
  if o then meanRest A T x U k V else unassigned A T x U k V

def Mode.cleared (m : Mode) (α : ℝ) := match m with
  | .clipped => 0
  | .shielded => α

def outputCut (o : Bool) (T : Tube G S) (x : ℝ) (V : Config G c) := if o then meanCut T x V else cutOutput T x V

def outputReserve (o : Bool) (T : Tube G S) (x β : ℝ) (V : Config G c) :=
  Real.exp (-β*(m.cleared (reserve T.low/2*(if o then visionMean T x V else visionTotal T x V))))



/-- Acted-on outgoing remainder, likelihood convention counting sum; this exact function
in each mode agrees with the library one or its shield/sieve version. -/
def kernel (o : Bool) (T : Tube G S) (A : Stores S) (x β : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :=
  S.likelihood U k * Real.exp (-β*(rest o T A x U k V + m.cleared (outputCut o T x V)))

@[simp] lemma clip_single (T : Tube G S) (A : Stores S) (x β : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :
    kernel .clipped false T A x β U k V = outgoing A T β x k V U := by simp [kernel,rest,Mode.cleared,outgoing]
@[simp] lemma clip_mean (T : Tube G S) (A : Stores S) (x β : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :
    kernel .clipped true T A x β U k V = leaves A T β x k V U := by simp [kernel,rest,Mode.cleared,leaves]
@[simp] lemma shield_single (T : Tube G S) (A : Stores S) (x β : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :
    kernel .shielded false T A x β U k V = shield T β x V * outgoing A T β x k V U := by
  unfold kernel shield outgoing; rw [mul_add,Real.exp_add]; unfold rest Mode.cleared outputCut cutOutput; simp; ring
@[simp] lemma shield_mean (T : Tube G S) (A : Stores S) (x β : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :
    kernel .shielded true T A x β U k V = sieve T β x V * leaves A T β x k V U := by
  unfold kernel sieve leaves; rw [mul_add,Real.exp_add]; unfold rest Mode.cleared outputCut meanCut cutOutput; simp; ring

lemma kernel_nonnegative (o : Bool) (T : Tube G S) (A : Stores S) (x β : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :
    0 ≤ kernel m o T A x β U k V := by unfold kernel; exact mul_nonneg (S.likelihood_pos ..) (Real.exp_pos _).le

/-- This is the cost of inserting the common lamp even over all the
inactive degrees of freedom. -/
def hole (F : Forest S.ratio) (A : Stores S) (G : Gauge) (x s : ℝ) :=
  (s⁻¹ ^ dim G)^(frozen A (radiusB x) F).card

lemma hole_nonneg (F : Forest S.ratio) (A : Stores S) (x s : ℝ) (hs : 0≤s) : 0 ≤ hole F A G x s := by
  unfold hole; positivity

section val
variable (o : Bool) {T : Tube G S} {A : Stores S} {β C e : ℝ} {k : S.Choices} {a : F.Slice G}

lemma joint_light_bound (hβ : y G S.patch.L x/2 ≤ β) (hx : 0 < y G S.patch.L x) (hγ : 0 < γ)
    (h : Joint T A (F.drape a) k V x C γ e) :
    let s := m.size G S.patch.L x
    Real.exp (-β*(rest o T A x (F.drape a) k V + m.cleared (outputCut o T x V))) ≤
      Real.exp (β*e*Fintype.card (Site c)) * outputReserve m o T x β V *
        ∏ i ∈ regular A (radiusB x) F, m.light C (γ/2) s (a i*(pilot F V i)⁻¹) := by
  intro s
  let M := (Fintype.card (Site c):ℝ)
  let b := rest o T A x (F.drape a) k V
  let w := if o then visionMean T x V else visionTotal T x V
  let R := reserve T.low/2*w
  let B := regular A (radiusB x) F
  let f (i : F.Free) := a i*(pilot F V i)⁻¹
  have hb : 0 ≤ β := by linarith
  cases m with
  | clipped =>
    have hh : -(e*M) ≤ b := by cases o; exact h.single; exact h.mean
    have hF (i : F.Free) (hi : i∈B) : Mode.light Mode.clipped C (γ/2) s (f i)=1 := Set.indicator_of_mem
      (show f i ∈ G.shell (C*s) from
        by simpa only [s,Mode.size,pilot,f,Gauge.shell,Set.mem_setOf_eq,linking, Forest.off_tree] using!
          h.charts _ (Finset.mem_filter.mp hi).2) (fun _ => (1:ℝ))
    change Real.exp (-β*(b+0)) ≤ Real.exp (β*e*M)*Real.exp (-β*0) * ∏ i∈B, Mode.clipped.light C (γ/2) s (f i)
    rw [Finset.prod_eq_one hF, mul_one,mul_zero,Real.exp_zero,mul_one,add_zero]
    apply Real.exp_monotone; nlinarith only [hh,hb]
  | shielded =>
    let L := S.patch.L
    have hs : 0 < s := Scales.gauge G L hx
    have hh : γ * linkCost A x V (F.drape a) + R - e*M ≤ b + outputCut o T x V := by
      cases o <;> first | exact h.use_single | exact h.use_mean
    have hh' : -β*(b+outputCut o T x V) ≤ β*e*M - β*R - β*γ*linkCost A x V (F.drape a) := by
      nlinarith only [hb,hh]
    change Real.exp (-β*(b+outputCut o T x V)) ≤ Real.exp (β*e*M)*Real.exp (-β*R) * ∏ i∈B, candle (γ/2) s (G.chord (f i))
    unfold candle; rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]; apply Real.exp_monotone; apply hh'.trans
    obtain ht := Scales.yg2 G L hx
    have hy i : -(γ/2)*(G.chord (f i)/s)^2 = -(y G L x/2)*γ*G.chord (f i)^2 := by
      rw [div_pow]; apply mul_right_cancel₀ (b:=s^2) (pow_ne_zero _ hs.ne')
      change _* (g G L x)^2 = _*(g G L x)^2
      calc
        _ = -(γ/2)*G.chord (f i)^2 := by change -(γ/2)*(G.chord (f i)^2/s^2)*s^2 = _; field_simp
        _ = -(γ/2)*G.chord (f i)^2 * (y G L x*(g G L x)^2) := by rw [ht,mul_one]
        _ = _ := by ring
    simp_rw [hy,← Finset.mul_sum]
    have hk := draped_link A x F a V
    change ∑ i ∈ B, G.chord (f i)^2 ≤ _ at hk
    have hz : 0≤linkCost A x V (F.drape a) := linkCost_nn ..
    have hv := mul_le_mul_of_nonneg_left hk (show 0≤y G L x/2*γ by unfold L; positivity)
    nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβ hγ.le) hz,hv]
end val
end YM.SectorNext.Remainder
