import YM.Further.ROOTED_INTERACTING_REMAINDER.Circulation
import YM.Further.ROOTED_INTERACTING_REMAINDER.Exposure
import YM.Further.ROOTED_INTERACTING_REMAINDER.Probe
/-!
# No denominator argument yet: absolute survey of the intact profiles

We conserve some of the share suppression explicitly through the integral.
Always by coupling R.beta of the given query; `x` is the *other* variable (hat).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder
open Lattice RG Wilson Filter Function Set Tree Finset MeasureTheory Precision
open SectorNext.Vacuum Pressure Pressure.Stores Push.SectorMeasure
open Next.Fluctuations.Sector Oriented Presented
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}
  {F : Forest S.ratio} {T : Tube G S} {P : Teller G} {R : Rep G f} {x W : ℝ} {D : Allocation G S x W}
  {X : Type*} [NormedAddCommGroup X]
local notation "Δ" => Module.finrank ℝ G.Color
local notation "t" => fiery G x S.patch.L  -- local can't capture?

-- envelope for a probe system; growth rate allowed on *any subset*
-- of Stores. Charge per-shares includes tags and LF chords, not an assertion
-- on the ratio to output V density. UR is still the supplied map; hypothesis
-- only where a particular guard & Alive holds. etc context.
structure CargoBill (R : Rep G f) (D : Allocation G S x W) (F : Forest S.ratio)
    (g : GaugeProbe G S F X) (b q : ℝ) : Prop where
  issues (A : Stores S) i (a : F.Slice G) V : D.bill A i (F.drape a) V ≠ 0 → Alive S (F.drape a) i →
    ‖g A i (a,V)‖ ≤ Real.exp (b * sites c + q*(R.beta*(fiery G x S.patch.L)^2*A.shares))

private lemma gates (A : Stores S) (U : Config G f) (i : S.Choices) (V : Config G c)
    (h : Seeded A U i V x W) (ht : 0<t) (hW : 0≤W) :
    let Q := S.prediction U i
    let Gt := Fintype.card (Cell f) + (Fintype.card (Bond c):ℝ)*(2*W)
    1 ≤ Real.exp Gt * (ration A.costs t U * gapper A.aisles t V Q) := by
  intro Q Gt
  let K := G.chord
  let e := fun u : G.El=>draught t⁻¹ u
  have hi (s : ℝ) (hs : 0≤s) (u : G.El) (h : K u ≤ s*t) : 1 ≤ Real.exp s * e u := by
    unfold e draught; rw [← Real.exp_add]; apply Real.one_le_exp
    have he : t⁻¹*t=1 := inv_mul_cancel₀ ht.ne'
    unfold K at h; nlinarith only [mul_le_mul_of_nonneg_left h (inv_pos.mpr ht).le,
      show s*(t⁻¹*t)=s by rw [he,mul_one]]
  have hb {ι : Type} [Fintype ι] (s : Finset ι) (q : ι → ℝ) (v : ℝ) (hv : 0≤v)
      (hh : ∀ i∈s,1≤Real.exp v*q i) :
      1 ≤ Real.exp ((Fintype.card ι:ℝ)*v)*∏ i∈s,q i := by
    have hp : ∀ i∈s,0 ≤ q i := by
      intro i hi; exact nonneg_of_mul_nonneg_right (zero_le_one.trans (hh i hi)) (Real.exp_pos _)
    calc
      1 = ∏ i∈s,(1:ℝ) := by simp
      _ ≤ ∏ i∈s, (Real.exp v*q i) := prod_le_prod (fun i _ => zero_le_one) hh
      _ ≤ _ := by
        rw [prod_mul_distrib,prod_const,←Real.exp_nat_mul]
        exact mul_le_mul_of_nonneg_right (Real.exp_monotone
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_univ _)) hv)) (prod_nonneg hp)
  have hc : 1 ≤ Real.exp ((Fintype.card (Cell f):ℝ)*1)*ration A.costs t U := hb A.costsᶜ (fun j => e (faceValue U j)) 1 zero_le_one fun p hp => hi 1 zero_le_one (faceValue U p)
    (by rw [one_mul]; change toll U p ≤ _; exact ((h.fine p).2 (mem_compl.mp hp)).trans (by linarith only [ht]))
  have hw : 1 ≤ Real.exp ((Fintype.card (Bond c):ℝ)*(2*W))*gapper A.aisles t V Q :=
    hb A.aislesᶜ (fun i=>e (V i*(Q i)⁻¹)) (2*W) (by positivity) fun p hp =>
      hi (2*W) (by positivity) (V p*(Q p)⁻¹) ((h.coarse p).2 (mem_compl.mp hp))
  unfold Gt; rw [Real.exp_add]
  rw [mul_one] at hc
  exact le_trans (b:=Real.exp (↑(Fintype.card (Cell f)))*ration A.costs t U *
    (Real.exp (Fintype.card (Bond c)*(2*W))*gapper A.aisles t V Q)) (one_le_mul_of_one_le_of_one_le hc hw)
    (le_of_eq (by ring))

/-- Quantitative. No small output-field assumptions. `far` is the exact
far-zone receipt produced on ALL instances by `settled_exterior` at chosen
x tail. -/
theorem sample {g : GaugeProbe G S F X} {b q δ y Λ ε : ℝ}
    (h : CargoBill R D F g b q)
    (hR : R.Lawful P.top.width P.top.paths Λ δ y) (hc : R.clip=P.top.clip)
    (hy : y≤1) (ht : 0<t) (hW : 0≤W) (hβ : 0≤R.beta)
    (far : ∀ A U k V, SliceSet S F U → Alive S U k → Seeded A U k V x W →
      -R.beta * meanRest A T x U k V ≤ ε*sites c)
    (A : Stores S) (i : S.Choices) (a : F.Slice G) (V : Config G c) :
    let p := sites f*(R.exCost P.top.paths Λ δ + R.beta*(Fintype.card PlaqAxes*(wound P.top.width P.top.paths R.p.threshold (till x) 1)))
    let Gt := Fintype.card (Cell f) + (Fintype.card (Bond c):ℝ)*(2*W)
    D.bill A i (F.drape a) V * carrier (x:=x) F T R g A i V a ≤
      Real.exp (p + b*sites c + q*(R.beta*t^2*A.shares) + ε*sites c + Gt) * flight A t i V (F.drape a) := by
  intro p Gt
  let U := F.drape a
  let d := D.bill A i U V
  have h1 : 0≤Real.exp (p+b*sites c+q*(R.beta*t^2*A.shares)+ε*sites c+Gt)*flight A t i V U :=
    mul_nonneg (Real.exp_pos _).le (flight_nonneg ..)
  by_cases he : d=0
  · change d*_ ≤ _; rw [he,zero_mul]; exact h1
  by_cases ha : Alive S U i
  swap
  · change d*(_*_*(S.likelihood U i*_)) ≤ _; simp_rw [dead ha]; simpa only [zero_mul,mul_zero] using h1
  have hp := launched P.top hR hc hβ hy (till x) U
  have hQ := h.issues A i a V he ha
  let L := b*sites c + q*(R.beta*t^2*A.shares)
  have hP := D.actual _ _ _ _ he
  have hX := far A U i V (fun j hj => F.on_tree _ ⟨j,hj⟩) ha hP
  let Y := S.prediction U i
  let w := S.likelihood U i
  have hw : 0≤w := ha.le
  have hm : leaves A T R.beta x i V U ≤ w*Real.exp (ε*sites c) :=
    mul_le_mul_of_nonneg_left (Real.exp_monotone hX) hw
  have hx : 1≤Real.exp Gt * (ration A.costs t U*gapper A.aisles t V Y) := gates _ _ _ _ hP ht hW
  calc
    _ ≤ ‖Real.exp (-R.scalar)*exposed R (till x) U‖ * ‖g A i (a,V)‖ * leaves A T R.beta x i V U :=
      mul_le_of_le_one_left (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hw (Real.exp_pos _).le)) (D.range ..)
    _ ≤ Real.exp p * Real.exp L * (w*Real.exp (ε*sites c)) :=
      mul_le_mul (mul_le_mul hp hQ (norm_nonneg _) (Real.exp_pos _).le) hm (mul_nonneg hw (Real.exp_pos _).le) (by positivity)
    _ ≤ Real.exp p * Real.exp L * (w*Real.exp (ε*sites c))*(Real.exp Gt*(ration A.costs t U*gapper A.aisles t V Y)) :=
      le_mul_of_one_le_right (by positivity) hx
    _ = _ := by dsimp only [L,w,Y,U,flight]; simp_rw [Real.exp_add]; ring

/-- Nonnegative rates before dividing in the normalized probe. `rooms`
has no power of β from a bare integration, only a β *tail* correction
from cutting the genuine paths, the inherited prices, and a constant
factor per oriented plaquette/bond. These latter per-level constants can
grow with blocks (DON'T claim pre-block pricing of the *density step*). -/
def rooms {G : Gauge} {f : Side} (R : Rep G f) (P : Stage) (ε x W b Λ δ : ℝ) (_n : Side) : ℝ :=
    sites f*(R.exCost P.paths Λ δ + R.beta*(Fintype.card PlaqAxes*wound P.width P.paths R.p.threshold (till x) 1)) + (b+ε)*sites _n +
      Fintype.card (Cell f) + (Fintype.card (Bond _n):ℝ)*(2*W)

variable [NormedSpace ℝ X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
/-- Estimate with the V-testing right side (still needs a rotation trick even
here). -/
lemma gauge_tally {g : GaugeProbe G S F X} {b q δ y Λ ε : ℝ}
    (h : CargoBill R D F g b q)
    (hR : R.Lawful P.top.width P.top.paths Λ δ y) (hT : P.Funds S T) (hc : R.clip=P.top.clip)
    (hy : y≤1) (ht : 0<t) (hW : 0≤W) (hβ : 0≤R.beta)
    (far : ∀ A U k V,SliceSet S F U → Alive S U k → Seeded A U k V x W →
      -R.beta * meanRest A T x U k V ≤ ε*sites c)
    (A : Stores S) (V : Config G c) (he : ∀ i,Envelope (g A i)) :
    cargo F T R D g A V ≤
      sieve T R.beta x V * Real.exp (rooms R P.top ε x W b Λ δ c + q*(R.beta*t^2*A.shares)) *
        ∑ i : S.Choices,∫ a,flight A t i V (F.drape a) ∂F.order G := by
  let ν := F.Slice G
  let ρ := F.order G
  let v : ℝ := rooms R P.top ε x W b Λ δ c + q*(R.beta*t^2*A.shares)
  unfold cargo Allocation.column tagTotal
  rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [Finset.mul_sum]; apply sum_le_sum; intro i _
  rw [←integral_const_mul]
  change (∫ a,D.bill A i (F.drape a) V * carrier (x:=x) F T R g A i V a ∂ρ) ≤ _
  let m (p : F.Slice G × Config G c) := D.bill A i (F.drape p.1) p.2 * carrier (x:=x) F T R g A i p.2 p.1
  haveI : IsProbabilityMeasure ρ := by unfold ρ; infer_instance
  have hm : Envelope m := (actual F R D g hT hR A i (he i)).1
  have h₁ : Integrable (fun a : ν => m (a,V)) ρ := Env.integrableX (Env.along hm (g:=fun a:ν => (a,V)) (measurable_id.prodMk measurable_const)) _
  apply integral_mono h₁
  · exact ((Envelope.const _).mul (wing (funds_branch hT) A t i (V:=fun (_ : F.Slice G) => V) measurable_const F.continuous_drape.measurable)).integrable _
  intro a; exact (sample h hR hc hy ht hW hβ far A i a V).trans_eq (by dsimp only [rooms]; congr 2; ring)

local notation "sV" => Fintype.card (Site c)-1
local notation "eV" => Fintype.card (Bond c)
local notation "ΔV" => rich f+sV -- beware notation precedence
local notation "ΔI" => rich f+eV

set_option linter.unusedSectionVars false
lemma landed_issue {g : GaugeProbe G S F X} {b q δ y Λ ε : ℝ}
    (h : CargoBill R D F g b q) (hr : R.Lawful P.top.width P.top.paths Λ δ y)
    (hT : P.Funds S T) (hc : R.clip=P.top.clip) (hy : y≤1) (ht : 0<t) (hs : t≤1)
    (hW : 0≤W) (hβ : 0≤R.beta)
    (far : ∀ A U k V,SliceSet S F U → Alive S U k → Seeded A U k V x W →
      -R.beta * meanRest A T x U k V ≤ ε*sites c)
    (A : Stores S) (he : ∀ i,Envelope (g A i))
    {K : ℝ} (hK : 1≤K) (hZ : (∫ i,draught t⁻¹ i ∂G.probHaar) ≤ K*t^Δ) (hn : 2≤c.val)
    {κ m : ℝ} (hp : 0≤m) (hu : Real.exp ((q-κ+m)*(R.beta*t^2))*t⁻¹^Δ ≤ 1) :
    let L := Real.exp (rooms R P.top ε x W b Λ δ c)
    let C := Real.exp (-m*(R.beta*t^2*A.shares))
    (∀ V,earn S G x κ R.beta A.shares * cargo F T R D g A V ≤
      prefactor S G R.beta * L * (K*t^Δ)^ΔV * C * sieve T R.beta x V) ∧
      (∫ V,(earn S G x κ R.beta A.shares * cargo F T R D g A V) ∂prior G c) ≤
        prefactor S G R.beta * L * (K*t^Δ)^ΔI * C := by
  intro L C
  let Dn : ℕ := A.costs.card + A.aisles.card
  let a : ℝ := A.shares
  let v := R.beta*t^2
  have hK' : 0<K := zero_lt_one.trans_le hK
  have hh : 0 ≤ v := by unfold v; positivity
  let h₁ (j : ℕ) := (K*t^Δ)^j*(t⁻¹^Δ)^Dn
  have hl : 1≤t⁻¹^Δ := one_le_pow₀ (by simpa using inv_anti₀ ht hs)
  have h2 : Real.exp ((q-κ+m)*(v*a))*(t⁻¹^Δ)^Dn ≤ 1 := by
    calc
      _ ≤ Real.exp ((q-κ+m)*(v*a))*(t⁻¹^Δ)^A.shares := by
        gcongr _ * ?_; exact pow_le_pow_right₀ hl (by dsimp only [Stores.shares,Dn]; omega)
      _ = (Real.exp ((q-κ+m)*v)*t⁻¹^Δ)^A.shares := by
        unfold a; rw [show _*((v:ℝ)*(A.shares:ℝ))=(A.shares:ℝ)*((q-κ+m)*v) by ring,Real.exp_nat_mul,mul_pow]
      _ ≤ _ := pow_le_one₀ (by unfold v; positivity) hu
  let M := rooms R P.top ε x W b Λ δ c + q*(v*a)
  have hf (j : ℕ) : earn S G x κ R.beta A.shares*Real.exp M*h₁ j ≤ prefactor S G R.beta * L * (K*t^Δ)^j * C := by
    have he : Real.exp (-R.beta * (κ*t^2*a))*Real.exp M = L*C*Real.exp ((q-κ+m)*(v*a)) := by rw [← Real.exp_add]; unfold L C M; rw [←Real.exp_add,←Real.exp_add]; congr 1; unfold v; ring
    change (prefactor S G _ * Real.exp _)*_*_ ≤ _
    calc
      _ = (prefactor S G R.beta*L*(K*t^Δ)^j*C)*(Real.exp ((q-κ+m)*(v*a))*(t⁻¹^Δ)^Dn) := by
        unfold h₁; rw [mul_assoc (prefactor S G _) _ (Real.exp M), show (A.shares:ℝ) = a by rfl,he]; ring
      _ ≤ _ := mul_le_of_le_one_right (by
        apply mul_nonneg _ (Real.exp_pos _).le
        exact mul_nonneg (mul_nonneg (prefactor_pos _).le (Real.exp_pos _).le) (by positivity)) h2
  let z := fun V => ∑ i : S.Choices,∫ a : F.Slice G,flight A t i V (F.drape a) ∂F.order G
  have hcV V : cargo F T R D g A V ≤ sieve T R.beta x V*(Real.exp M*z V) := by
    rw [←mul_assoc]; exact gauge_tally h hr hT hc hy ht hW hβ far A V he
  constructor
  · intro V
    have hs' : 0 ≤ sieve T R.beta x V := (Real.exp_pos _).le
    calc
      _ ≤ earn S G x κ R.beta A.shares*(sieve T R.beta x V*(Real.exp M*h₁ ΔV)) := by
        apply mul_le_mul_of_nonneg_left _ (earn_pos ..).le; apply (hcV V).trans
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (circuit F A t K V hn (funds_branch hT) ht hs hK hZ) (Real.exp_pos _).le) hs'
      _ = earn S G x κ R.beta A.shares*Real.exp M*h₁ ΔV * sieve T R.beta x V := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hf _) hs'
  let ν := prior G c
  have hg : Integrable (cargo F T R D g A) ν := (cargo_portable F R D g hT hr A he).integrable _
  have hi : Envelope z := by
    unfold z; apply Envelope.sum
    intro i
    let Y := F.Slice G × Config G c
    exact Env.marginal (g:=fun p:Y=>flight A t i p.2 (F.drape p.1))
      (wing (funds_branch hT) A t i (V:=Prod.snd) measurable_snd (F.continuous_drape.measurable.comp measurable_fst)) _
  haveI : IsProbabilityMeasure ν := by unfold ν; infer_instance
  calc
    _ ≤ ∫ V,earn S G x κ R.beta A.shares*(Real.exp M*z V) ∂ν := by
      refine integral_mono (hg.const_mul _) (((hi.integrable ν).const_mul (Real.exp M)).const_mul _) fun V => ?_
      apply mul_le_mul_of_nonneg_left _ (earn_pos ..).le
      exact (hcV V).trans (mul_le_of_le_one_left (mul_nonneg (Real.exp_pos _).le
        (sum_nonneg fun i _=>integral_nonneg fun j => flight_nonneg ..)) (sieve_nonpositive S T R.beta x hβ V)) -- hβ needed
    _ ≤ earn S G x κ R.beta A.shares*Real.exp M*h₁ ΔI := by
      rw [integral_const_mul,integral_const_mul,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (earn_pos ..).le; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact circulation F A t K (hn.trans (by rw [S.sizes]; exact Nat.le_mul_of_pos_right _ S.patch.L.property)) (funds_branch hT) ht hs hK hZ
    _ ≤ _ := hf _

/-- Bill for counting the true allocation records before reorganizing into LF
components. No entropy spent on k or F. -/
def supplicant (c f : Side) := (Real.log 2)*((Fintype.card (Cell f):ℝ)+ Fintype.card (Bond c)+sites c)

lemma plural : (Fintype.card (Stores S):ℝ) = Real.exp (supplicant c f) := by
  rw [Fintype.card_congr (inventory S)]
  unfold supplicant sites
  simp only [Support,Fintype.card_prod,Fintype.card_finset]
  push_cast
  simp_rw [mul_add,Real.exp_add]
  simp only [mul_comm (Real.log 2),Real.exp_nat_mul,Real.exp_log (show 0<(2:ℝ) by norm_num),mul_assoc, ← pow_mul]
  simp [mul_comm]

/-- Pre-normalization survey. Both arbitrary V (including retained flag
suppression; arbitrary further subcollection of Stores) and partition
version with tail/siting specified BEFORE integration (use with e.g. event
on compulsory mergers; strengthening with V-dependent masks restricted by
Y ok, add it to g). No cost supplied for organizing by fcrec. -/
theorem engaged {g : GaugeProbe G S F X} {b q δ y Λ ε : ℝ}
    (h : CargoBill R D F g b q) (hr : R.Lawful P.top.width P.top.paths Λ δ y)
    (hT : P.Funds S T) (hc : R.clip=P.top.clip) (hy : y≤1) (ht : 0<t) (hs : t≤1)
    (hW : 0≤W) (hβ : 0≤R.beta)
    (far : ∀ A U k V,SliceSet S F U → Alive S U k → Seeded A U k V x W →
      -R.beta * meanRest A T x U k V ≤ ε*sites c)
    {K : ℝ} (hK : 1≤K) (hZ : (∫ i,draught t⁻¹ i ∂G.probHaar) ≤ K*t^Δ) (hn : 2≤c.val)
    {κ m : ℝ} (hp : 0≤m) (hu : Real.exp ((q-κ+m)*(R.beta*t^2))*t⁻¹^Δ ≤ 1)
    (he : ∀ A i,Envelope (g A i)) (Y : Finset (Stores S)) (n : ℕ) (hY : ∀ A∈Y,n≤A.shares) :
    let L := Real.exp (rooms R P.top ε x W b Λ δ c + supplicant c f)
    let C := fun j : ℕ => Real.exp (-m*(R.beta*t^2*j))
    (∀ V,itinerary F T R D g κ Y V ≤
      prefactor S G R.beta * L * (K*t^Δ)^ΔV * C (max n (RG.flags (temp x) V).card) * sieve T R.beta x V) ∧
      (∫ V,itinerary F T R D g κ Y V ∂prior G c) ≤
        prefactor S G R.beta * L * (K*t^Δ)^ΔI * C n := by
  intro L C
  let E := fun j : ℕ => prefactor S G R.beta * Real.exp (rooms R P.top ε x W b Λ δ c) * (K*t^Δ)^j
  have hE j : 0≤E j := mul_nonneg (mul_nonneg (prefactor_pos _).le (Real.exp_pos _).le) (by have := hK; positivity)
  have h := fun A => landed_issue h hr hT hc hy ht hs hW hβ far A (he A) hK hZ hn hp hu
  have hm : Antitone C := by
    intro i j hij
    apply Real.exp_monotone
    exact mul_le_mul_of_nonpos_left (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hij) (mul_nonneg hβ (sq_nonneg _))) (by linarith)
  have hX (u : ℝ) (j : ℕ) (hU : 0≤u) : (∑ i∈Y,E j*u) ≤ prefactor S G R.beta*L*(K*t^Δ)^j*u := by
    rw [sum_const,nsmul_eq_mul]
    apply le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_univ _)) (mul_nonneg (hE _) hU))
    refine le_of_eq ?_
    unfold L E; rw [plural,Real.exp_add]; ring
  constructor
  · intro V
    let l := max n (RG.flags (temp x) V).card
    let w := sieve T R.beta x V
    have hw : 0≤w := (Real.exp_pos _).le
    rw [mul_assoc (_ * _ * _) _ (sieve T _ _ _)] -- C*w
    refine le_trans ?_ (hX _ _ (show 0≤ C l*w from mul_nonneg (Real.exp_pos _).le hw))
    unfold itinerary; refine sum_le_sum fun i hi => ?_
    by_cases hh : RG.flags (temp x) V=i.flags
    · have he : l ≤ i.shares := by
        unfold l; rw [hh]; exact max_le (hY i hi) (by unfold Stores.shares; omega)
      rw [←mul_assoc]
      exact ((h i).1 V).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hm he) (hE _)) hw)
    rw [sees_flags (T:=T) (F:=F) (D:=D) (g:=g) (R:=R) hh,mul_zero]
    apply mul_nonneg (hE _) (mul_nonneg (Real.exp_pos _).le hw)
  refine le_trans ?_ (hX _ _ (show 0≤ C n from (Real.exp_pos _).le))
  unfold itinerary
  rw [integral_finsetSum]
  · exact sum_le_sum fun i hi=> ((h i).2).trans
      (mul_le_mul_of_nonneg_left (hm (hY i hi)) (hE _))
  exact fun i _ => ((cargo_portable F R D g hT hr i (he i)).integrable _).const_mul _

end YM.Further.RootedInteractingRemainder
