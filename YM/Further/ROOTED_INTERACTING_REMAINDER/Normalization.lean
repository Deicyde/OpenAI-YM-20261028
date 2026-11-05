import YM.Further.ROOTED_INTERACTING_REMAINDER.Custom
import YM.SectorNext.VACUUM_NORMALIZATION.Ledger

/-!
# Recover the four-link balance before any activity regrouping

Exact APIs use localRatio of the same gauge, Chart as well for first gas; all
remaining dependence on Λ,N expressed as app inputs. Ratio estimates here
retain growth in P (the small-field monitor, p in E), not done with
post-L pressure work for large-field *post component* coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder
open Lattice RG RG.Supply Wilson Filter Function Set Tree Finset MeasureTheory Precision
open SectorNext.Vacuum Pressure Pressure.Stores Push.SectorMeasure
open Next.Fluctuations.Sector Oriented Presented
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
  {F : Forest S.ratio} {T : Tube G S} {P : Teller G} {R : Rep G f} {x W : ℝ} {D : Allocation G S x W}
local notation "Δ" => Module.finrank ℝ G.Color
local notation "t" => fiery G x S.patch.L

-- b = log link window of normalized Haar in chosen chart
lemma zed (P : Teller G) : ∃ b : ℝ, 0<b ∧ ∀ᶠ τ : ℝ in atTop, ∀ (c f : Side) (S : StepData c f), S.kernel=P.bind →
    prefactor S G (τ^2) ≤ Real.exp (wires c*b)*(τ^Δ)^(Fintype.card (Bond c)) := by
  let A := Next.Foundations.chart G
  have hA := Next.Foundations.chart_ok G
  let d := narrow A P.bind.penalty
  have he : 0<d := narrow_pos A hA _ P.bind.penalty_pos
  let b := 1+|Real.log (d/2)|
  have hb : 0 < b := add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg _)
  refine ⟨b,hb,?_⟩
  filter_upwards [(first_asymptotic A hA _ P.bind.penalty_pos).eventually (le_mem_nhds (show d/2< d by linarith)),eventually_gt_atTop (0:ℝ)] with τ h ht
  intro c f S hk
  let z := S.penaltyZ (τ^2) G
  have hz : 0 < z := S.penaltyZ_pos _
  have hf : z=linkZ G (P.bind.penalty*τ^2) := by
    unfold z StepData.penaltyZ StepData.penaltyWeight linkZ mouth; rw [hk]; congr 1; ext u; ring_nf
  have hv : Real.exp (-b) ≤ d/2 := by
    rw [← Real.exp_log (show 0<d/2 by positivity)] -- second? occurrence count
    exact Real.exp_le_exp.mpr (by unfold b; linarith [neg_abs_le (Real.log (d/2))])
  have hr : z⁻¹ ≤ Real.exp b*τ^Δ := by
    rw [inv_eq_one_div,div_le_iff₀ hz,mul_assoc,hf]
    apply le_trans (b:=Real.exp b * Real.exp (-b))
    · rw [← Real.exp_add,add_neg_cancel, Real.exp_zero]
    exact mul_le_mul_of_nonneg_left (hv.trans h) (Real.exp_pos _).le
  rw [wires,Real.exp_nat_mul,←mul_pow]
  exact pow_le_pow_left₀ (inv_pos.mpr hz).le hr _

lemma gaussian_basis (A : ChartRatio G) (hA : LocalRatio A) :
    ∃ b : ℝ,0<b ∧ ∀ τ : ℝ,0 < τ → (Real.exp (-b))*τ⁻¹^Δ ≤ gaussLink A (τ^2) := by
  let M : ℝ := (2*Real.pi)^((Δ:ℝ)/2)*A.scale
  have hM : 0 < M := by unfold M; have := Real.pi_pos; have := hA.scale; positivity
  let b := 1+|Real.log M|
  have hb : 0 < b := by unfold b; positivity
  refine ⟨b,hb,fun τ ht => ?_⟩
  have he : Real.exp (-b) ≤ M := by
    calc
      _ ≤ Real.exp (Real.log M) := Real.exp_le_exp.mpr (by unfold b; linarith [neg_abs_le (Real.log M)])
      _ = _ := Real.exp_log hM
  have hx : gaussLink A (τ^2) = M*τ⁻¹^Δ := by
    unfold gaussLink
    let k : ℝ := 2*Real.pi
    change (k/τ^(2:ℕ))^((Δ:ℝ)/2)*A.scale=k^((Δ:ℝ)/2)*A.scale*τ⁻¹^Δ
    have hk : 0≤k := by unfold k; have := Real.pi_pos; positivity
    rw [div_eq_mul_inv,Real.mul_rpow hk (by positivity),← inv_pow,← Real.rpow_natCast τ⁻¹,← Real.rpow_mul (by positivity),Nat.cast_ofNat,show (2:ℝ)*((Δ:ℝ)/2)=(Δ:ℝ) by ring,Real.rpow_natCast]; ring
  rw [hx]; exact mul_le_mul_of_nonneg_right he (by positivity)

private lemma exponential_basis (A : ChartRatio G) (b τ a : ℝ) (B : Round.Wall (Key F G))
    (he : Real.exp (-b)*τ⁻¹^Δ ≤ gaussLink A (τ^2)) (ht : 0<τ) (ha : 0<B.det)
    (hA : Real.log B.det ≤ 2*a) :
    Real.exp (-b*nt F-a)*(τ⁻¹^Δ)^nt F ≤ flatLine F A (τ^2) B := by
  have hh : Real.exp (-a) ≤ (Real.sqrt B.det)⁻¹ := by
    rw [Real.exp_neg]; apply inv_anti₀ (Real.sqrt_pos.mpr ha)
    have hm := Real.log_sqrt ha.le
    rw [← Real.exp_log (Real.sqrt_pos.mpr ha)]
    exact Real.exp_le_exp.mpr (by linarith)
  have hp := pow_le_pow_left₀ (by positivity) he (nt F)
  calc
    _ = (Real.exp (-b)*τ⁻¹^Δ)^nt F*Real.exp (-a) := by rw [mul_pow,← Real.exp_nat_mul, sub_eq_add_neg, Real.exp_add]; rw [mul_comm (-b)]; ring
    _ ≤ _ := mul_le_mul hp hh (Real.exp_pos _).le ((pow_nonneg (by positivity) _).trans hp)

lemma four_slot (F : Forest S.ratio) : nt F= (rich f+(Fintype.card (Site c)-1))+4 := by
  rw [bonds_nt]; unfold rich; have he := Fintype.card_pos (α:=Site f); have hf := Fintype.card_pos (α:=Site c); omega

-- Issued Counter is still major red assumption. Deduct at the actual
-- scalar using it (positivity automatically here; adding comparison to
-- kinetic or even existence of output history would require much more).
-- `pb` must estimate the very flat Gram; can use genuine free kernel
-- prerequisites before applying. --
lemma counted_floor {a : ChartRatio G} {B : Round.Wall (Key F G)} {G0 : Config G c→ℝ} {X : ℕ→Support c} {v : BudgetPoint}
    {E : ℕ→ Config G c→ℝ} {d : Activities G c}
    (H : Counter D F a B G0 R X v E d) (hk : S.patch.Branches S.kernel G)
    {r σ C Λ θ : ℝ} (hr : R.Lawful σ C Λ θ r)
    (hf : LocalRatio a) {τ b pb : ℝ} (hβ : R.beta=τ^2)
    (hbox : Real.exp (-b)*τ⁻¹^Δ ≤ gaussLink a (τ^2)) (ht : 0<τ)
    (ha : 0<B.det) (hx : Real.log B.det ≤ 2*pb)
    (h0 : G0 1=0) {z : ℕ→ℝ} (hE : ReLog.Tags X v E z) (M : ℕ)
    {l e δ : ℝ} (hF : ReLog.Fund X M l e δ z) :
    Real.exp (-b*nt F-pb-sites c*e)*(τ⁻¹^Δ)^nt F*prefactor S G R.beta ≤ S.push R.beta (stripped R) 1 := by
  let J := ∑ i : Support c,ReLog.raw X E i 1
  have hp := issues H hk hr (1:Config G c)
  rw [h0,neg_zero,Real.exp_zero,mul_one,ReLog.first_flat X v E d hE M hF] at hp
  have he : Real.exp R.scalar*S.push R.beta (stripped R) 1 = S.push R.beta R.eval 1 := by
    unfold StepData.push; simp only [smul_eq_mul]
    rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards with U
    rw [mul_left_comm,restore]
  have hh := office H hk hr hf (show 0<R.beta by rw [hβ]; positivity) ha h0 hE M hF |>.1
  change |J| ≤ _ at hh
  have hl : Real.exp (-(sites c*e)) ≤ Real.exp (-J) := Real.exp_monotone (by linarith [le_abs_self J])
  let y := Real.exp (-b*nt F-pb)*(τ⁻¹^Δ)^nt F
  have hP : 0<y := by unfold y; positivity
  have hY := exponential_basis (F:=F) a b τ pb B hbox ht ha hx
  have hK : S.push R.beta (stripped R) 1=prefactor S G R.beta*flatLine F a R.beta B*Real.exp (-J) := by
    apply mul_left_cancel₀ (Real.exp_pos R.scalar).ne'; rw [he]; simpa only [mul_assoc] using hp
  rw [hK,hβ]
  calc
    _ = prefactor S G _ * (y*Real.exp (-(sites c*e))) := by unfold y; simp_rw [sub_eq_add_neg,Real.exp_add]; ring
    _ ≤ _ := by rw [mul_assoc (prefactor S G _) (flatLine F a _ B)]; exact mul_le_mul_of_nonneg_left (mul_le_mul hY hl (Real.exp_pos _).le (hP.le.trans hY)) (prefactor_pos _).le

-- ratio arithmetic, same in both uses. do not force Δ>0.
lemma splits {x y E C D U p K τ : ℝ} {d N : ℕ}
    (hp : 0<p) (ht : 0<τ)
    (hX : x ≤ p*Real.exp E*(K*U^d)^N*C) (hn : 0≤C) (hK : 0<K) (hU : 0<U)
    (hY : p*Real.exp (-D)*(τ⁻¹^d)^(N+4) ≤ y) :
    x/y ≤ Real.exp (E+D)*(K*(τ*U)^d)^N*τ^(4*d)*C := by
  have he : 0<y := lt_of_lt_of_le (by positivity) hY
  rw [div_le_iff₀ he]
  calc
    _ ≤ _ := hX
    _ = Real.exp (E+D)*(K*(τ*U)^d)^N*τ^(4*d)*C*(p*Real.exp (-D)*(τ⁻¹^d)^(N+4)) := by
      rw [Real.exp_add,Real.exp_neg,pow_add,mul_pow τ,inv_pow,show 4*d=d*4 by omega,pow_mul]
      have h0 := ht.ne'
      have hx := (Real.exp_pos D).ne'
      simp only [mul_pow, inv_pow]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hY (by positivity)

/-- Queries on each F and D can use this common map (independent of
volume except `sites`s in named cost). `Pb` pays the issued Gaussian Gram
bill, with convention per-step log of **sqrt determinant** (often linear
in #keys). Here's the exact κ margin condition and pre-L seal version
(without `affine`), also used late in `Service`. -/
structure Survey (P : Teller G) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
    (R : Rep G f) (x W ε Λ δ y K τ κ m q : ℝ) : Prop where
  input : R.Lawful P.top.width P.top.paths Λ δ y
  supports : P.Funds S T
  cut : R.clip=P.top.clip
  halt : y≤1
  hot : 0 < fiery G x S.patch.L
  boil : fiery G x S.patch.L ≤ 1
  width : 0 ≤ W
  lift : 1 ≤ τ
  rate : R.beta=τ^2
  room : τ⁻¹ ≤ R.p.threshold
  /-- Unassigned cost, proven across periods on protocol; no unestimated
  LF/integral assumption in this field. -/
  far : ∀ A U k V,SliceSet S F U → Alive S U k → Seeded A U k V x W →
    -R.beta * meanRest A T x U k V ≤ ε*sites c
  money : 1 ≤ K
  gear : (∫ i,draught (fiery G x S.patch.L)⁻¹ i ∂G.probHaar) ≤ K*(fiery G x S.patch.L)^Δ
  active : 0≤m
  spare : Real.exp ((q-κ+m)*(R.beta*(fiery G x S.patch.L)^2))* (fiery G x S.patch.L)⁻¹^Δ ≤ 1

variable {Y : Finset (Stores S)} {n : ℕ}
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
    {g : GaugeProbe G S F X} {ε b₀ q δ y Λ κ m K τ : ℝ}

def rental (n : Side) (R : Rep G f) (P : Stage) (ε x W b Λ δ : ℝ) := rooms R P ε x W b Λ δ n + supplicant n f

lemma norm_parts (s : Survey P S T F R x W ε Λ δ y K τ κ m q) (he : ∀ A i,Envelope (g A i))
    (hp : PointCharge T x W κ) (hh : Fits T R x) (V : Config G c) :
    Envelope (itinerary F T R D g κ Y) ∧ Envelope (repaid F R D g Y) ∧
      repaid F R D g Y V ≤ itinerary F T R D g κ Y V :=
  ⟨itinerary_portable F R D g s.supports s.input _ _ he,repaid_portable F R D g s.supports s.input _ he,
    authorized F R D g s.supports s.input _ he hp hh (s.rate.symm ▸ sq_nonneg _) V⟩

set_option linter.unusedSectionVars false in
/-- Pointwise normalized `leftOver`. Reserve share still present for
large/stress probes even on allgood and complements. X(1) is the
actual scalar jump (at the very issued step); no R' or Program assumed;
Counter is required (for the pointwise version; not for partition
version below). In particular use `literal_cargo` for actual leftOver
without growth. No growth credit consumed in assessing the left column;
then can use `authorized` or even direct calls for pastry/other readouts.
Cases with zero toll parameters/smaller period need their own procurement;
not licensed by this theorem. -/
theorem pointwise_price (s : Survey P S T F R x W ε Λ δ y K τ κ m q)
    (h : CargoBill R D F g b₀ q) (he : ∀ A i,Envelope (g A i)) (hc : 2≤c.val) (hY : ∀ A∈Y,n≤A.shares)
    {a : ChartRatio G} {B : Round.Wall (Key F G)} {G0 : Config G c→ℝ} {D0 : ℕ→Support c} {v : BudgetPoint}
    {E : ℕ→ Config G c→ℝ} {d : Activities G c}
    (H : Counter D F a B G0 R D0 v E d) (hh : LocalRatio a)
    (h0 : G0 (1:Config G c)=0) (ha : 0<B.det)
    (V : Config G c) {z : ℕ→ℝ} (hZ : ReLog.Tags D0 v E z) {M : ℕ} {l budget δ' b pb : ℝ} (hF : ReLog.Fund D0 M l budget δ' z)
    (hdet : Real.log B.det ≤ 2*pb) (hLink : Real.exp (-b)*τ⁻¹^Δ ≤ gaussLink a (τ^2)) :
    let deltaC := Real.exp (-m * (R.beta * (fiery G x S.patch.L)^2 * max n (RG.flags (temp x) V).card)) -- coerce max real vs Nat? MAX coerces nat
    let Z := S.push R.beta (stripped R) 1
    let e := rental c R P.top ε x W b₀ Λ δ
    0<Z ∧ itinerary F T R D g κ Y V / Z ≤
      Real.exp (e+(b*(nt F:ℝ)+pb+sites c*budget)) * (K*(τ*(fiery G x S.patch.L))^Δ)^(rich f+(Fintype.card (Site c)-1)) *
        τ^(4*Δ)*deltaC*sieve T R.beta x V := by
  intro deltaC Z e
  have hβ : 0 ≤ R.beta := s.rate.symm ▸ sq_nonneg _
  have ht : 0<τ := zero_lt_one.trans_le s.lift
  have hSc := funds_branch s.supports
  let A := b*(nt F:ℝ)+pb+sites c*budget
  let N := rich f+(Fintype.card (Site c)-1)
  have hU : prefactor S G R.beta* Real.exp (-A)*(τ⁻¹^Δ)^(N+4) ≤ Z := by
    rw [show N+4=_ from (four_slot F).symm]
    apply le_trans _ (counted_floor H hSc s.input hh s.rate hLink ht ha hdet h0 hZ M hF)
    apply le_of_eq; rw [show -A=-b*nt F-pb-sites c*budget by unfold A; ring]; ring
  have hg : 0<Z := by have hP := prefactor_pos (S:=S) (G:=G) R.beta; exact lt_of_lt_of_le (by positivity) hU
  let U := fiery G x S.patch.L
  have hI := (engaged h s.input s.supports s.cut s.halt s.hot s.boil s.width hβ s.far s.money s.gear hc s.active s.spare he Y n hY).1 V
  have hd : 0 < deltaC*sieve T R.beta x V := mul_pos (Real.exp_pos _) (Real.exp_pos _)
  refine ⟨hg,?_⟩
  change _ ≤ Real.exp _ * (K*(τ*U)^Δ)^N * τ^(4*Δ)*deltaC*sieve T R.beta x V
  rw [mul_assoc (_*τ^_) deltaC _]
  refine splits (p:=prefactor S G R.beta) (prefactor_pos _) ht (by simpa [e,rental,N,U,deltaC,mul_assoc] using hI) hd.le
    (zero_lt_one.trans_le s.money) s.hot hU

-- before restoring: marginal tree housing in Stripped/Haar. Four powers
-- from fine torus only, no fake coarse or extra link cancellations. -/
def divide (R : Rep G f) (s : ℝ) (P : Stage) (Λ δ : ℝ) := sites f * (R.exCost P.paths Λ δ+baseBudget P.clip P.paths s)

set_option linter.unusedSectionVars false in
/-- Normalizing **actual** growth probe by true partition. A pure Teller/Funds,
profile & rate calculation. HERE no Counter/charged/determinant (call
PortionCost or norm_parts in addition for the true push probes, and
pointwise_price above for normalization at flat). Nonnegative R required to
use the earlier Haar denominator; doesn't assume transfer certificate or
Counter. -/
theorem marginal_given (s : Survey P S T F R x W ε Λ δ y K τ κ m q)
    (h : CargoBill R D F g b₀ q) (he : ∀ A i,Envelope (g A i)) (hc : 2≤c.val) (hN : ∀ U,0≤R.eval U)
    (hY : ∀ A∈Y,n≤A.shares)
    (p0 : ℝ) (hP : prefactor S G R.beta ≤ Real.exp (wires c*p0)*(τ^Δ)^(Fintype.card (Bond c)))
    {d z : ℝ} (_hd : 0<d) (_hD : d≤1) (hZ : 0<z) (_hz : z≤1)
    (hw : Real.exp (-(divide R d P.top Λ δ))*((z*τ⁻¹^Δ)^spare f) ≤ strippedZ R) :
      let deltaC := Real.exp (-m * (R.beta * t^2 * n))
      let Z := strippedZ R
      let e := rental c R P.top ε x W b₀ Λ δ + wires c*p0
      0<Z ∧ (∫ V,itinerary F T R D g κ Y V ∂prior G c) / Z ≤
        Real.exp (e+ (divide R d P.top Λ δ - spare f * Real.log z)) *
          (K*(τ*t)^Δ)^(rich f+Fintype.card (Bond c)) * τ^(4*Δ)*deltaC := by
  intro deltaC Z e
  have hβ : 0 ≤ R.beta := s.rate.symm ▸ sq_nonneg _
  have ht : 0<τ := zero_lt_one.trans_le s.lift
  have hI := (engaged h s.input s.supports s.cut s.halt s.hot s.boil s.width hβ s.far s.money s.gear hc s.active s.spare he Y n hY).2
  have hf : 2 ≤ f.val := hc.trans (by rw [S.sizes]; exact Nat.le_mul_of_pos_right _ S.patch.L.property)
  let A := divide R d P.top Λ δ-spare f*Real.log z
  let p := (τ^Δ)^(Fintype.card (Bond c))
  let N := rich f+Fintype.card (Bond c)
  let u := K*t^Δ
  have hU : p*Real.exp (-A)*(τ⁻¹^Δ)^(N+4) ≤ Z := by

    apply le_trans (le_of_eq _) hw
    unfold A p
    rw [show N+4=(Fintype.card (Bond c))+spare f by rw [spare_four]; unfold N; omega]
    rw [pow_add,mul_pow,neg_sub, sub_eq_add_neg, Real.exp_add,Real.exp_nat_mul,Real.exp_log hZ]
    simp only [inv_pow, neg_mul]
    field_simp
  have hg : 0<Z := lt_of_lt_of_le (by unfold p; positivity) hU
  refine ⟨hg,splits (p:=p) (by unfold p; positivity) ht ?_ (Real.exp_pos _).le (zero_lt_one.trans_le s.money) s.hot hU⟩
  let b := rental c R P.top ε x W b₀ Λ δ
  have hp := mul_le_mul_of_nonneg_right hP (show 0≤Real.exp b*u^N*deltaC by unfold u; have := s.hot; have := s.money; have h : 0 ≤ deltaC := (Real.exp_pos _).le; positivity)
  apply hI.trans
  unfold e
  change prefactor S G R.beta*Real.exp b*u^N*deltaC ≤ p*Real.exp (b+_)*u^N*deltaC
  rw [Real.exp_add]
  calc
    _ = prefactor S G R.beta * (Real.exp b*u^N*deltaC) := by ring
    _ ≤ _ := hp
    _ = _ := by unfold p; ring

end YM.Further.RootedInteractingRemainder
