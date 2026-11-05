import YM.Further.ROOTED_INTERACTING_REMAINDER.Protocol
import YM.Further.ROOTED_INTERACTING_REMAINDER.Station
/-!
# Post station constant pressure bound

Intact normalized growth through arbitrary volume even with **constant**
per-volume credit besides at most four □ powers, even without LF integration
assumptions. Not persistence of the estimate on separated component tables.
Post Counter use meets same data at `girder` with retained HALF kinetic
suppression, no competition among shares. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder.Levy
open Filter Function Lattice RG RG.Supply Axial Wilson Finset Precision Tree MeasureTheory
open Pressure Pressure.Stores Pressure.Teller Pressure.Tube Bid Next.Fluctuations
open Next.Fluctuations.Sector Push.SectorMeasure Oriented Presented SectorNext.Vacuum
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x W : ℝ}
    {F : Forest S.ratio} {T : Tube G S} {P : Teller G} {R : Rep G f} {D : Allocation G S x W}
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] {g : GaugeProbe G S F X}
local notation "t" => fiery G x S.patch.L
local notation "Δ" => Module.finrank ℝ G.Color
local notation "eV" => Fintype.card (Bond c)
local notation "nP" => Fintype.card PlaqAxes
local notation "ΔI" => rich f+eV
local notation "ΔV" => rich f+(Fintype.card (Site c)-1)

-- Useful cost form at fixed heights before schedule delays.
lemma pressure_marginal (ρ : Teller G) {κ b Λ δ y τ K K' η : ℝ} (h : CargoBill R D F g b (κ/4))
    (he : ∀ A i,Envelope (g A i))
    (s : Survey ρ S T F R x W 1 Λ δ y K τ κ (κ/4) (κ/4))
    (a : Ample T x W R.beta κ η F)
    (hk : 1≤K') (hc : 2≤c.val) (hS : (∫ i,draught (τ⁻¹)⁻¹ i ∂G.probHaar) ≤ K'*(τ⁻¹)^Δ)
    (Y : Finset (Stores S)) (n : ℕ) (hY : ∀ A∈Y,n≤A.shares)
    (p : ℝ) (hp : prefactor S G R.beta ≤ Real.exp (wires c*p)*(τ^Δ)^eV)
    {d z : ℝ} (hz : 0<z) (hw : Real.exp (-(divide R d ρ.top Λ δ))*((z*τ⁻¹^Δ)^spare f) ≤ strippedZ R) :
    let c₁ := duty R ρ.top b Λ δ η x c
    let C := Real.exp (c₁+wires c*p+(divide R d ρ.top Λ δ-spare f*Real.log z) + ((ΔI : ℕ):ℝ)*Real.log K')
    let y₀ := Real.exp (-(κ/4)*(R.beta*t^2*n))
    let Z := strippedZ R
    0<Z ∧ (∫ V,itinerary F T R D g κ Y V/Z ∂prior G c) ≤ C*τ^(4*Δ)*y₀ := by
  intro c₁ C y₀ Z
  let A := divide R d ρ.top Λ δ-spare f*Real.log z
  let N := ΔI
  have ht : 0<τ := zero_lt_one.trans_le s.lift
  have hk₀ : 0<K' := zero_lt_one.trans_le hk
  let E := c₁+wires c*p
  have H := (relay ρ h he s a hk hc hS Y n hY).2
  let L := (τ^Δ)^eV
  have hU : L*Real.exp (-A)*(τ⁻¹^Δ)^(N+4) ≤ Z := by
    apply le_trans (le_of_eq _) hw
    unfold A L
    rw [show N+4=eV+spare f by rw [spare_four]; unfold N; omega]
    rw [pow_add,mul_pow,neg_sub, sub_eq_add_neg, Real.exp_add,Real.exp_nat_mul,Real.exp_log hz]
    simp only [inv_pow]; field_simp
  have hx : 0<L := by unfold L; positivity
  have h₀ : 0<Z := lt_of_lt_of_le (by positivity) hU
  refine ⟨h₀,?_⟩
  rw [integral_div]
  have he : (∫ V,itinerary F T R D g κ Y V ∂prior G c) ≤ L*Real.exp E*(K'*τ⁻¹^Δ)^N*y₀ := by
    apply H.trans
    unfold E; rw [Real.exp_add]
    calc
      _ ≤ Real.exp (wires c*p)*L*Real.exp c₁*(K'*τ⁻¹^Δ)^N*y₀ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) (by positivity)) (Real.exp_pos _).le
      _ = _ := by ring
  apply (splits hx ht he (Real.exp_pos _).le hk₀ (inv_pos.mpr ht) hU).trans_eq
  unfold C E A N; rw [mul_inv_cancel₀ ht.ne',one_pow,mul_one, Real.exp_add _ (((ΔI : ℕ):ℝ)*Real.log K'), Real.exp_nat_mul,Real.exp_log hk₀]

lemma pressure_pointwise (ρ : Teller G) {κ b Λ δ y τ K K' η : ℝ} (h : CargoBill R D F g b (κ/4))
    (he : ∀ A i,Envelope (g A i))
    (s : Survey ρ S T F R x W 1 Λ δ y K τ κ (κ/4) (κ/4))
    (am : Ample T x W R.beta κ η F)
    (hk : 1≤K') (hc : 2≤c.val) (hS : (∫ i,draught (τ⁻¹)⁻¹ i ∂G.probHaar) ≤ K'*(τ⁻¹)^Δ)
    (Y : Finset (Stores S)) (n : ℕ) (hY : ∀ A∈Y,n≤A.shares)
    {a : ChartRatio G} {B : Round.Wall (Key F G)} {D0 : ℕ→Support c} {v : BudgetPoint}
    {E : ℕ→ Config G c→ℝ} {d : Activities G c} {G0 : Config G c→ℝ}
    (H : Counter D F a B G0 R D0 v E d) (hh : LocalRatio a)
    (h0 : G0 (1:Config G c)=0) (ha : 0<B.det)
    (V : Config G c) {z : ℕ→ℝ} (hZ : ReLog.Tags D0 v E z)
    {M : ℕ} {l budget δ' b0 pb : ℝ} (hF : ReLog.Fund D0 M l budget δ' z)
    (hdet : Real.log B.det ≤ 2*pb) (hLink : Real.exp (-b0)*τ⁻¹^Δ ≤ gaussLink a (τ^2)) :
    let c₁ := duty R ρ.top b Λ δ η x c
    let y₀ := Real.exp (-(κ/4)*(R.beta*t^2*max n (RG.flags (temp x) V).card))
    let C := Real.exp (c₁+(b0*nt F+pb+sites c*budget)+((ΔV : ℕ):ℝ)*Real.log K')
    let Z := S.push R.beta (stripped R) 1
    0<Z ∧ itinerary F T R D g κ Y V/Z ≤ C*τ^(4*Δ)*y₀*halfprice T x R.beta V := by
  intro c₁ y₀ C Z
  let L:=prefactor S G R.beta
  let A := b0*nt F+pb+sites c*budget
  let N:=ΔV
  have ht : 0<τ := zero_lt_one.trans_le s.lift
  have hL : 0<L := prefactor_pos _
  have hK := zero_lt_one.trans_le hk
  have hV := halfprice_pos T x R.beta V
  have hfloor := counted_floor H (funds_branch s.supports) s.input hh s.rate hLink ht ha hdet h0 hZ M hF
  have hU : L*Real.exp (-A)*(τ⁻¹^Δ)^(N+4) ≤ Z := by
    rw [show N+4=_ from (four_slot F).symm]
    apply le_trans (le_of_eq _) hfloor
    rw [show -A=-b0*nt F-pb-sites c*budget by unfold A; ring]; unfold L; ring
  have h₀ : 0<Z := lt_of_lt_of_le (by positivity) hU
  refine ⟨h₀,?_⟩
  have hi : itinerary F T R D g κ Y V ≤ L*Real.exp c₁*(K'*τ⁻¹^Δ)^N*(y₀*halfprice T x R.beta V) := by
    rw [←mul_assoc]
    exact (relay ρ h he s am hk hc hS Y n hY).1 V
  apply (splits hL ht hi (mul_nonneg (Real.exp_pos _).le hV.le) hK (inv_pos.mpr ht) hU).trans_eq
  unfold C A N; rw [mul_inv_cancel₀ ht.ne',one_pow,mul_one,Real.exp_add _ (((ΔV : ℕ):ℝ)*Real.log K'),Real.exp_nat_mul,Real.exp_log hK,←mul_assoc]

-- seal combined uniform. Half sacrifice in sieve; cross with earlier Desk
-- variation when singular large field portions are queried. Consumers below
-- for determinant and integrated bounds need no unverified LF work. -/
structure License.{u} (G : Gauge) (c f : Side) (S : StepData c f) (F : Forest S.ratio) (T : Tube G S)
    (R : Rep G f) (x W M κ r : ℝ) (O : ChartRatio G) (e l l' : ℝ) : Prop where
  funds (D : Allocation G S x W) (Z : Type u) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [SecondCountableTopology Z]
      [MeasurableSpace Z] [BorelSpace Z] [CompleteSpace Z] (g : GaugeProbe G S F Z)
      (he : ∀ A i, Envelope (g A i)) (h : CargoBill R D F g M (κ/4)) (Y : Finset (Stores S)) (n : ℕ) (hY : ∀ A∈Y,n≤A.shares) :
    let w := fiery G x S.patch.L; let τ := Real.sqrt R.beta
    let price (j : ℕ) := Real.exp (-(κ/4)*(R.beta*w^2*j))
    let L := Real.exp (sites f*r) * τ^(4*Module.finrank ℝ G.Color)
    Envelope (itinerary F T R D g κ Y) ∧ Envelope (repaid F R D g Y) ∧
      (∀ V : Config G c, repaid F R D g Y V ≤ itinerary F T R D g κ Y V) ∧
      ((∀ U,0≤R.eval U) → let z := strippedZ R
        0 < z ∧ (∫ V,itinerary F T R D g κ Y V/z ∂prior G c) ≤ L*price n) ∧
      ∀ (B : Round.Wall (Key F G)) (X : ℕ→Support c) (b : BudgetPoint) (E : ℕ→Config G c→ℝ) (d : Activities G c),
        Counter D F O B (fun V=>R.beta*girder T.down T.low b V) R X b E d → b.threshold=temp x →
        ∀ v : ℕ→ℝ, ReLog.Tags X b E v → ∀ A e' δ', e'≤e → ReLog.Fund X b.B A e' δ' v →
        B.IsHermitian → Numeric B l l' → 0<l →
    let z := S.push R.beta (stripped R) 1
    0<z ∧ ∀ V, let s := z*Real.exp (-(R.beta/2)*girder T.down T.low b V)
      0<s ∧ itinerary F T R D g κ Y V / s ≤ L * price (max n (RG.flags (temp x) V).card)

private lemma halfway (ρ : Teller G) (T : Tube G S) (h : ρ.Funds S T) (b : BudgetPoint) (ht : b.threshold=temp x)
    (β : ℝ) (hb : 0≤β) (hW : β*wound ρ.below.width ρ.below.paths (temp x) (till x) S.patch.L.val ≤ 1)
    (V : Config G c) : halfprice T x β V ≤ Real.exp (sites c*nP/2)*Real.exp (-(β/2)*girder T.down T.low b V) := by
  have hg := ceiling_sieve h b ht hb hW V
  change Real.exp (-β*averaged (fun j=>coarse T x (pull j 0 V)))≤_ at hg
  rw [← Real.exp_add,Real.exp_le_exp] at hg
  unfold halfprice; rw [←Real.exp_add]; exact Real.exp_monotone (by linarith)

set_option maxHeartbeats 500000 in
/-- Primary station. Bounds simultaneous *constant* per-site cost, and at
flat jumps with half kinetic retained. These buy especially `leftOver` under
the whole normalized representation, beyond mere re-integration of Gram
measures at a fixed volume, and even prior to certified Counter for the
partition version. Not approval on peeled gas components (see post module).
When a full kinetic comparison is desired use `ticket` (might still need job
costs *not* growing with p; see caveats in report). Only terminal replicated
network costing asks for the four-link residual in E; LF calculations use
whole component hit sums, not the consequence per torus e.g. from this file;
see follow-on work.
-/
theorem every_issue.{u} (ρ : Teller G) (O : ChartRatio G) (hO : LocalRatio O)
    (M e l l' : ℝ) (hM : 0 ≤ M) (hc : 0≤e) :
    ∀ L : Side, ∀ W κ : ℝ, 0<W → 0<κ → ∃ r : ℝ, 0<r ∧ ∀ᶠ x : ℝ in atTop,
      let v := betaF G x L
      ∀ (c f : Side) (S : StepData c f), S.patch.L=L → 100*(1+radiusB x) ≤ c.val →
        ∀ (T : Tube G S), ρ.Funds S T → PointCharge T x W κ →
        ∀ (F : Tree.Forest S.ratio) (R : Rep G f),∀ Λ δ y : ℝ,
          R.Lawful ρ.top.width ρ.top.paths Λ δ y → v/2 ≤ R.beta → R.beta ≤ 2*v →
          Presented.Fits T R x → y≤1 → δ≤1 → Λ ≤ 2*Vac.Numbers.P v →
            License.{u} G c f S F T R x W M κ r O e l l' := by
  obtain ⟨η,hη,HP⟩ := branch ρ 1 zero_lt_one

  obtain ⟨a,z,ha,ha',hz,hz',HY⟩ := housing (G:=G)
  obtain ⟨D,hD,HD⟩ := gaussian_basis O hO
  obtain ⟨s,hs,He⟩ := sip G
  intro L W κ hW hκ
  obtain ⟨A,B,p,K,hA,hB,hp,hK,HS⟩ := surveyed ρ L W κ M hW hκ hM
  -- K' here always s not Survey.K
  let d := (Δ:ℝ)
  let y := 7*Real.log s
  let δ := A+(nP+4)*η⁻¹
  let sumPro := δ+4*p+(B+baseBudget ρ.top.clip ρ.top.paths a) + 4*(-Real.log z) + y
  let J := Panel.amount l l'
  let box := δ + (4*D+4*d*J/2 + e) + y
  let price := box + (nP:ℝ)/2
  let r := max (max price sumPro) 1
  refine ⟨r,zero_lt_one.trans_le (le_max_right ..),?_⟩
  filter_upwards [HS,(Work.E09.betaF_growth G L).eventually_ge_atTop 2,HP L W hW,cash_holes G L κ hκ] with x hS hg hη' hcash
  intro v c f S hL' hN T hT hP F R Λ θ u hR hm he hC hy hθ hΛ
  obtain ⟨S₁,hPr,hRa,hV,hQ,h₂⟩ := hS c f S hL' hN T hT F R Λ θ u hR hm he hC hy hθ hΛ
  let τ := Real.sqrt R.beta
  let Y (i : ℕ) := Real.exp (-(κ/4)*(R.beta*(fiery G x S.patch.L)^2*i))
  have hβ : 0<R.beta := lt_of_lt_of_le (by change (0:ℝ)< betaF G x L/2; linarith) hm
  have hh : 1 ≤ τ := S₁.lift
  have ht₁ : 0<τ := zero_lt_one.trans_le S₁.lift
  have hf := site_compare S
  have hn : 1 ≤ sites f := by unfold sites; exact_mod_cast Fintype.card_pos (α:=Site f)
  have hr := (site_pos f).le
  have hN' : 2≤c.val := by omega
  have hN'' : 2≤f.val := hN'.trans (by rw [S.sizes]; exact Nat.le_mul_of_pos_right _ S.patch.L.property)
  have hηA := hη' c f S hL' hN T hT F
  have hcash := hcash _ hm he
  have ham : Ample T x W R.beta κ η F := ⟨hη,fun A U k V h₁ hk h₃ => by
    simpa only [one_mul,sites] using hηA A U k V h₁ hk h₃ R.beta hβ.le he,by simpa only [hL'] using hcash⟩
  have hτs := He τ⁻¹ (by positivity) (show τ⁻¹≤1 by simpa only [inv_one] using inv_anti₀ zero_lt_one hh)
  have hlogs : 0 ≤ Real.log s := Real.log_nonneg hs
  constructor
  intro D0 Z _ _ _ _ _ _ g hE hI i j hIJ w τ₀ p₁ X0
  let Pp := τ^(4*Δ)
  have hτ' : (0:ℝ) ≤ Pp := by unfold Pp; positivity
  have hm := norm_parts (Y:=i) (D:=D0) S₁ hE hP hC (1:Config G c)
  let eX := duty R ρ.top M Λ θ η x c
  have htC : eX ≤ sites f*δ := by
    apply (duty_rental R _ M Λ θ W η x hW.le hη.le).trans; unfold δ
    linarith only [hRa,mul_le_mul_of_nonneg_right hf (show 0 ≤ 4*η⁻¹ by positivity)]
  refine ⟨hm.1,hm.2.1,fun V=>(norm_parts (Y:=i) (D:=D0) S₁ hE hP hC V).2.2,fun H=>?_,?_⟩
  · intro z'
    have hF := HY f hN'' R hR H τ hh S₁.rate S₁.room
    rw [S₁.cut,neg_mul] at hF
    obtain ⟨hz0,hC'⟩ := pressure_marginal ρ hI hE S₁ ham hs hN' hτs i j hIJ p hQ hz hF
    have hspare : (spare f:ℝ) ≤ 4*sites f := by unfold spare sites; push_cast; unfold sites at hn; linarith
    have hw : Real.log z ≤ 0 := Real.log_nonpos hz.le hz'
    have hN0 := (seven_sites S)
    have hNF : ((rich f+Fintype.card (Bond c):ℕ):ℝ) ≤ 7*sites f := by unfold sites; exact_mod_cast hN0
    have hpS : sumPro≤r := (le_max_right ..).trans (le_max_left ..)
    refine ⟨hz0,hC'.trans ?_⟩
    change _ ≤ Real.exp (sites f*r)*Pp*Y j
    apply mul_le_mul_of_nonneg_right _ (show (0:ℝ)≤Y j from (Real.exp_pos _).le)
    refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) hτ'
    rw [wires_sites]; unfold divide; unfold eX at htC; unfold sumPro y at hpS
    linarith only [mul_le_mul_of_nonneg_left hpS hr,htC,mul_le_mul_of_nonneg_right hf (show 0 ≤ 4*p by positivity),
      mul_le_mul_of_nonpos_right hspare hw,mul_le_mul_of_nonneg_left hV hr,mul_le_mul_of_nonneg_right hNF hlogs]
  intro C X v E d' hL hb v₁ hv₁ d₀ eX' a₀ hyp hF hv' hBoard hl z0
  obtain ⟨hD0,hD',hPB⟩ := Panel.determinant hv' hBoard hl
  let pb := sites f * (4*d*J/2)
  have hx : ((nt F):ℝ) ≤ sites f*4 := by rw [bonds_nt]; push_cast; unfold sites at *; linarith only [hf]
  have hdθ : Real.log C.det ≤ 2*pb := by
    apply (le_abs_self _).trans
    apply hPB.trans
    rw [card_meter]; push_cast
    unfold pb; have he := mul_le_mul_of_nonneg_right hx (mul_nonneg (show 0≤ d by unfold d; positivity) (Panel.amount_nonneg l l'))
    unfold J; unfold d at he ⊢; linarith only [he]
  have H₁ (V:Config G c):=pressure_pointwise ρ hI hE S₁ ham hs hN' hτs i j hIJ hL hO
    (by rw [girder_flat,mul_zero]) hD0 V hv₁ hF hdθ (HD τ ht₁)
  refine ⟨(H₁ 1).1,fun V=>?_⟩
  intro q; let Yj:= Y (max j (RG.flags (temp x) V).card)
  let zV:= girder T.down T.low v V; let Wz:=Real.exp (-(R.beta/2)*zV)
  refine ⟨mul_pos (H₁ V).1 (Real.exp_pos _),?_⟩
  unfold q; rw [← div_div,div_le_iff₀ (Real.exp_pos _)]
  apply (H₁ V).2.trans
  have hhalf := halfway ρ T hT v hb R.beta hβ.le h₂ V
  let n0 := (nP:ℝ)
  let bV := Real.exp (sites c*n0/2)
  have hNS : ((rich f+(Fintype.card (Site c)-1):ℕ):ℝ) ≤ 7*sites f := by
    unfold sites
    exact_mod_cast (le_trans (four_sites S) (show 4*Fintype.card (Site f)≤7*Fintype.card (Site f) by omega))
  have hh : price≤r := (le_max_left price sumPro).trans (le_max_left ..)
  let y₁ := eX+(D*nt F+pb+sites c*eX')+((rich f+(Fintype.card (Site c)-1):ℕ):ℝ)*Real.log s
  have hpz : Real.exp y₁*bV ≤ Real.exp (sites f*r) := by
    unfold bV; rw [← Real.exp_add]; apply Real.exp_monotone
    unfold price box at hh; unfold y₁ pb; change δ + (4*D+4*d*J/2+e)+ y + n0/2 ≤ _ at hh
    unfold y at hh
    linarith only [mul_le_mul_of_nonneg_left hh hr,htC,mul_le_mul_of_nonneg_right hx hD.le,
      mul_le_mul_of_nonneg_left hyp (site_pos c).le,mul_le_mul_of_nonneg_right hf hc,mul_le_mul_of_nonneg_right hNS hlogs,mul_le_mul_of_nonneg_right hf (show 0 ≤ n0 by unfold n0; positivity)]
  change Real.exp y₁ * Pp*Yj * halfprice T x R.beta V ≤ Real.exp (sites f*r)*Pp*Yj*Wz
  have hyJ : 0 ≤ Yj := (Real.exp_pos _).le
  calc
    _ ≤ Real.exp y₁ * Pp * Yj * (bV*Wz) := mul_le_mul_of_nonneg_left hhalf (by positivity)
    _ = (Pp*Yj*Wz)*(Real.exp y₁*bV) := by ring
    _ ≤ (Pp*Yj*Wz)*Real.exp (sites f*r) := mul_le_mul_of_nonneg_left hpz (mul_nonneg (mul_nonneg hτ' hyJ) (Real.exp_pos _).le)
    _ = _ := by ring

/-- Reapply with existential grant. Stamp versions can instead apply
`every_issue` on the *actual* Ringing using only the extra x height
threshold here. -/
theorem license.{u} (ρ : Teller G) (O : ChartRatio G) (hO : LocalRatio O)
    (M e l l' : ℝ) (hM : 0 ≤ M) (hc : 0≤e) :
    ∃ n₀ : ℕ, ∀ L : Side, n₀≤L.val → ∀ᶠ W : ℝ in atTop, ∃ κ r : ℝ, 0<κ ∧ 0<r ∧ ∀ᶠ x : ℝ in atTop,
      let v := betaF G x L
      ∀ (c f : Side) (S : StepData c f), S.patch.L=L → 100*(1+radiusB x) ≤ c.val →
        ∀ (T : Tube G S), ρ.Funds S T →
        ∀ (F : Tree.Forest S.ratio) (R : Rep G f),∀ Λ δ y : ℝ,
          R.Lawful ρ.top.width ρ.top.paths Λ δ y → v/2 ≤ R.beta → R.beta ≤ 2*v →
          Presented.Fits T R x → y≤1 → δ≤1 → Λ ≤ 2*Vac.Numbers.P v →
            License.{u} G c f S F T R x W M κ r O e l l' := by
  obtain ⟨n₀,h₀⟩ := points_grant ρ
  refine ⟨n₀,fun L hL => ?_⟩
  filter_upwards [h₀ L hL] with W ⟨hW,κ,hκ,H⟩
  obtain ⟨r,hr,he⟩ := every_issue.{u} ρ O hO M e l l' hM hc L W κ hW hκ
  refine ⟨κ,r,hκ,hr,?_⟩
  filter_upwards [he,H] with x he ⟨_,_,ht⟩
  intro v c f S hL hR T h; exact he c f S hL hR T h (ht c f S T hL hR h)
end YM.Further.RootedInteractingRemainder.Levy
