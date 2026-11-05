import YM.Further.ROOTED_INTERACTING_REMAINDER.Credit
/-!
# Simultaneous intact leftOver station

Combine with Counter on THAT authorization, and exponent is in
log p (=o(log β)), without further per-volume log β losses.
Use another method/prove sharper hypothesis than intact masks for steps
where even this per-site log p would exhaust the rooted budget; in particular
not offering it as payment of K endpoint! Includes nonabelian clean choice
and retained probes on arbitrary volume. No positivity of R from Lawful
assumed. Charge licenses comparisons with the actual entered queries (no
extra denominators etc). -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder
open Lattice RG Wilson Function Filter MeasureTheory Precision
open SectorNext.Vacuum Pressure Pressure.Stores Push.SectorMeasure Tree Next.Fluctuations
open Next.Fluctuations.Sector Oriented Presented
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}

local notation "Δ" => Module.finrank ℝ G.Color

def lprice (G : Gauge) (E x : ℝ) := E + (7:ℝ)*Module.finrank ℝ G.Color*Real.log (Vac.Numbers.P x)

lemma surveil {H H' K τ b t p : ℝ} {n : Side} {N M : ℕ} (hK : 1≤K) (hp : 1 ≤ p)
    (ht : 0 ≤ τ*t) (hs : τ*t ≤ 2*p) (h : N ≤ 7*Fintype.card (Site n))
    (hA : H ≤ sites n*b) (hB : b+ (7:ℝ)*(Real.log K+M*Real.log 2) ≤ H') :
    Real.exp H *(K*(τ*t)^M)^N ≤ Real.exp (sites n*(H'+7*M*Real.log p)) := by
  have hk := zero_lt_one.trans_le hK
  have hh := zero_lt_one.trans_le hp
  have hX : K*(τ*t)^M ≤ Real.exp (Real.log K + M*Real.log 2 + M*Real.log p) := by
    simp only [Real.exp_add,Real.exp_nat_mul,Real.exp_log hh,Real.exp_log hk,Real.exp_log (show 0<(2:ℝ) by norm_num),mul_assoc]
    rw [←mul_pow]; gcongr
  let x := Real.log K+M*Real.log 2+M*Real.log p
  have hx : 0 ≤ x := by
    have := Real.log_nonneg hK; have := Real.log_nonneg hp; have := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num); unfold x; positivity
  calc
    _ ≤ Real.exp H * (Real.exp x)^N := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg hk.le (pow_nonneg ht _)) hX _) (Real.exp_pos _).le
    _ = Real.exp (H+N*x) := by rw [Real.exp_add H,Real.exp_nat_mul x N]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hz : (N:ℝ) ≤ 7*sites n := by unfold sites; exact_mod_cast h
      have hZ := mul_le_mul_of_nonneg_right hz hx; unfold x at hZ; have hr := (site_pos n).le
      linarith only [hZ,hA,mul_le_mul_of_nonneg_left hB hr])

/-- An exact authorization. `X` arbitrary level in `admit`, use ℝ for
unmarked. Growth charge at κ/4. Reserve at κ/4. Additional inequalities
supplied later for the case that post-L funding of the answers must be
stronger. No ControlField cooling/conditioning ambiguity at flagged
points even for signed input costs (for integrated /Z still demands actual
nonnegative trajectory/vacuum as indicated). -/
structure Appointment (G : Gauge) (c f : Side) (S : StepData c f) (F : Forest S.ratio) (T : Tube G S)
    (R : Rep G f) (x W M κ r : ℝ) : Prop where
  positive : 0<κ
  rate : 0<R.beta
  admit (D : Allocation G S x W)
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
    (g : GaugeProbe G S F X) (he : ∀ A i,Envelope (g A i)) (h : CargoBill R D F g M (κ/4))
    (Y : Finset (Stores S)) (n : ℕ) (hY : ∀ A∈Y,n≤A.shares) :
    let b := betaF G x S.patch.L; let w := fiery G x S.patch.L
    let τ := Real.sqrt R.beta; let a (j : ℕ) := Real.exp (-(κ/4)*(R.beta*w^2*j))
    let L := Real.exp (sites f*lprice G r b)
    Envelope (itinerary F T R D g κ Y) ∧ Envelope (repaid F R D g Y) ∧
    (∀ V : Config G c, repaid F R D g Y V ≤ itinerary F T R D g κ Y V) ∧
    ((∀ U,0≤R.eval U) → let Z := strippedZ R
        0<Z ∧ (∫ V,itinerary F T R D g κ Y V / Z ∂prior G c) ≤ L*τ^(4*Module.finrank ℝ G.Color)*a n)

/-- Conditions for scalar upgrade of all those probes on intact Counter.
Keep numerical rates (user can e.g. procure R before Survey and check
these extra rates funded at L). Reusing an Appointment with different
receipts than here? insist on this **explicit** port on the same step. -/
structure Desk.{u} (G : Gauge) (c f : Side) (S : StepData c f) (F : Forest S.ratio) (T : Tube G S)
    (R : Rep G f) (x W M κ r : ℝ) (a : ChartRatio G) (e l l' : ℝ) : Prop where
  issue (D : Allocation G S x W) (Z : Type u) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [SecondCountableTopology Z]
      [MeasurableSpace Z] [BorelSpace Z] [CompleteSpace Z] (g : GaugeProbe G S F Z)
      (he : ∀ A i, Envelope (g A i)) (h : CargoBill R D F g M (κ/4)) (Y : Finset (Stores S)) (n : ℕ) (hY : ∀ A∈Y,n≤A.shares)
      (B : Round.Wall (Key F G)) (X : ℕ→Support c) (b : BudgetPoint) (E : ℕ→Config G c→ℝ) (d : Activities G c)
      (Hx : LocalRatio a) (h : Counter D F a B (fun V=>R.beta*girder T.down T.low b V) R X b E d) (hb : b.threshold=temp x)
      (v : ℕ → ℝ) (hE : ReLog.Tags X b E v) (A e' δ : ℝ) (_hr : e'≤e) (hF : ReLog.Fund X b.B A e' δ v)
      (hB : B.IsHermitian) (hP : Numeric B l l') (hl : 0<l) :
    let v := betaF G x S.patch.L; let w := fiery G x S.patch.L
    let τ := Real.sqrt R.beta; let price (j : ℕ) := Real.exp (-(κ/4)*(R.beta*w^2*j))
    let L := Real.exp (sites f*lprice G r v); let z := S.push R.beta (stripped R) 1
    0<z ∧ ∀ V, let s := z*Real.exp (-R.beta*girder T.down T.low b V)
      0<s ∧ itinerary F T R D g κ Y V / s ≤ L*τ^(4*Module.finrank ℝ G.Color)*price (max n (RG.flags (temp x) V).card)

lemma girder_flat {G : Gauge} {n : Side} (T : PathData G) (a : Clip) (b : BudgetPoint) :
    girder T a b (1:Config G n)=0 := by
  have h0 i : T.baseTerm a b (1:Config G n) i=0 := by
    have hf (j : Face (Per n)) : faceValue (1:Config G n) j=1 := by simp [faceValue,square,travel]
    have hs (k : ℕ) : T.ellTerms i k (1:Config G n)=0 := by
      unfold PathData.ellTerms Slot.atSite Slot.eval; let p := (T.row i.2 k).2
      have he : faceValue (expandAt i.1 (1:Config G n)) (p.offset,p.plaq)=
          faceValue (1:Config G n) (wrap n p.offset+i.1,p.plaq) := travel_at ..
      have hg : G.curvature 1=0 := norm_le_zero_iff.mp ((G.curvature_norm 1).trans G.chord_one.le)
      rw [he,hf,hg,map_zero,smul_zero]
    unfold PathData.baseTerm PathData.ell; simp_rw [hf,G.chord_one,hs,tsum_zero]; rw [PathData.clipped,if_pos b.threshold_pos.le]; split <;> ring_nf
    simp
  have ht i : pull i 0 (1:Config G n)=1 := by funext k; unfold pull Step.read; split <;> simp
  simp only [girder,ht,h0,Finset.sum_const_zero,Branch.avg_const]

lemma ceiling_sieve {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {x β : ℝ} (hT : P.Funds S T)
    (b : BudgetPoint) (ht : b.threshold=temp x) (hh : 0≤β)
    (h : β*wound P.below.width P.below.paths (temp x) (till x) S.patch.L.val ≤ 1) (V : Config G c) :
    sieve T β x V ≤ Real.exp (sites c*Fintype.card PlaqAxes)*Real.exp (-β*girder T.down T.low b V) := by
  obtain ⟨α,Λ,he,hk⟩ := hT.feeds
  have hx := (abs_le.mp (aligned T P.below hT.low hk β x hh b ht V)).2
  rw [← Real.exp_add,←Real.exp_log (show 0<sieve T β x V from Real.exp_pos _)]
  apply Real.exp_monotone
  let n := sites c
  let u := (Fintype.card PlaqAxes:ℝ)
  have ho : 0≤n*u := mul_nonneg (site_pos _).le (Nat.cast_nonneg _)
  have hp := mul_le_mul_of_nonneg_left h ho
  -- only in girder expression rw; h unchanged by ht?
  change _ ≤ _ at hx
  rw [←hT.low,ht] at hx -- dependent issue in V? hx occurrences? P.below paths and clip only
  unfold u n at *; linarith only [hx,hp]

-- Makes no promise on later entries at a Ringing without buying these
-- delays on the *same* alloy. All inputs and works specialized together here.
set_option maxHeartbeats 500000 in
theorem ticket.{u} (ρ : Teller G) (O : ChartRatio G)
    -- no hypothesis needed on O for the Appointment, but the pointwise
    -- Desk in both directions will only be queried with a legal chart; to
    -- fix constants require here
    (hO : LocalRatio O) (M e l l' : ℝ) (hM : 0≤M) (hc : 0≤e) :
    ∃ n₀ : ℕ, ∀ L : Side, n₀≤L.val → ∀ᶠ W : ℝ in atTop, ∃ κ r : ℝ, 0<κ ∧ 0<r ∧ ∀ᶠ x : ℝ in atTop,
      let v := betaF G x L
      ∀ (c f : Side) (S : StepData c f), S.patch.L=L → 100*(1+radiusB x) ≤ c.val →
        ∀ (T : Tube G S), ρ.Funds S T →
        ∀ (F : Tree.Forest S.ratio) (R : Rep G f),∀ Λ δ y : ℝ,
          R.Lawful ρ.top.width ρ.top.paths Λ δ y → v/2 ≤ R.beta → R.beta ≤ 2*v →
          Presented.Fits T R x → y≤1 → δ≤1 → Λ ≤ 2*Vac.Numbers.P v →
            Appointment G c f S F T R x W M κ r ∧ Desk.{u} G c f S F T R x W M κ r O e l l' := by
  obtain ⟨n₀,h₀⟩ := points_grant ρ
  refine ⟨n₀,fun L hL => ?_⟩
  filter_upwards [h₀ L hL] with W ⟨hW,κ,hκ,H⟩
  obtain ⟨A,B,p,K,hA,hB,hp,hK,HS⟩ := surveyed ρ L W κ M hW hκ hM
  obtain ⟨a,z,ha,ha',hz,hz',HY⟩ := housing (G:=G)
  obtain ⟨D,hD,HD⟩ := gaussian_basis O hO
  let d := (Δ:ℝ)
  let y := 7*(Real.log K+d*Real.log 2)
  let sumPro := A+4*p+(B+baseBudget ρ.top.clip ρ.top.paths a) + 4*(-Real.log z) + y
  let J := Panel.amount l l'
  let box := A + (4*D+4*d*J/2 + e) + y
  let price := box + (Fintype.card PlaqAxes:ℝ)
  let r := max (max price sumPro) 1
  refine ⟨κ,r,hκ,zero_lt_one.trans_le (le_max_right ..),?_⟩
  filter_upwards [HS,H,(Work.E09.betaF_growth G L).eventually_ge_atTop 2] with x hS ⟨hx,ht,hP⟩ hg
  intro v c f S hL' hN T hT F R Λ δ u hR hm he hC hy hδ hΛ
  obtain ⟨S₁,hPr,hRa,hV,hQ,h₂⟩ := hS c f S hL' hN T hT F R Λ δ u hR hm he hC hy hδ hΛ
  let τ := Real.sqrt R.beta
  let t := fiery G x S.patch.L
  have hβ : 0<R.beta := lt_of_lt_of_le (by change (0:ℝ)< betaF G x L/2; linarith) hm
  have ht₁ : 0<τ := zero_lt_one.trans_le S₁.lift
  let Y (i : ℕ) := Real.exp (-(κ/4)*(R.beta*t^2*i))
  let X := Vac.Numbers.P v
  have hM : 1≤X := Real.one_le_exp (sq_nonneg _)
  have hf : sites c ≤ sites f := site_compare S
  have hn : 1 ≤ sites f := by unfold sites; exact_mod_cast Fintype.card_pos (α:=Site f)
  have ho (a b : ℝ) : 7*(Real.log K+d*Real.log 2)=y := rfl
  have hN' : 2≤c.val := by omega
  have hN'' : 2≤f.val := hN'.trans (by rw [S.sizes]; exact Nat.le_mul_of_pos_right _ S.patch.L.property)
  let E := rental c R ρ.top 1 x W M Λ δ
  constructor
  · constructor
    · exact hκ
    · exact hβ
    intro Z _ _ _ _ _ _ gD g hBills hReach i j hIJ -- fix order D BEFORE Z
    intro X0 wt τ1 funds Q
    have hA := norm_parts (Y:=i) (D:=Z) S₁ hBills (hP _ _ _ _ hL' hN hT) hC (1:Config G c)
    refine ⟨hA.1,hA.2.1,fun V=>(norm_parts (Y:=i) (D:=Z) S₁ hBills (hP _ _ _ _ hL' hN hT) hC V).2.2,fun hh=>?_⟩
    intro ζ
    have hsh := HY _ hN'' R hR hh _ S₁.lift S₁.rate S₁.room
    rw [S₁.cut,neg_mul] at hsh
    obtain ⟨hz0,hC'⟩ := marginal_given S₁ hReach hBills hN' hh hIJ p hQ ha ha' hz hz' hsh
    refine ⟨hz0,?_⟩
    rw [integral_div]
    let X1 := A+4*p+(B+baseBudget ρ.top.clip ρ.top.paths a)+4*(-Real.log z)
    let m := divide R a ρ.top Λ δ
    have h0 : 0≤sites f := (site_pos _).le
    have h3 : (spare f:ℝ) ≤ sites f * 4 := by unfold spare sites; push_cast; unfold sites at hn; linarith only [hn]
    have hw : Real.log z ≤ 0 := Real.log_nonpos hz.le hz'
    have hE : E+wires c*p+(m-spare f*Real.log z) ≤ sites f*X1 := by
      unfold X1 m E divide; rw [wires_sites];
      linarith only [hRa,mul_le_mul_of_nonneg_right hf (show 0 ≤ 4*p by positivity),mul_le_mul_of_nonneg_left hV h0,
        mul_le_mul_of_nonpos_right h3 hw]
    have hi := seven_sites S
    let dG := Module.finrank ℝ G.Color
    have hu : 0 ≤ τ*t := mul_nonneg ht₁.le S₁.hot.le
    have hc' := surveil (M:=dG) hK hM hu hPr hi hE (le_of_eq (show X1+7*((Real.log K)+dG*Real.log 2)=sumPro from rfl))
    apply hC'.trans
    gcongr ?_ * _ * _
    apply hc'.trans
    change Real.exp _ ≤ Real.exp (sites f*_)
    have hsr : sumPro ≤ r := (le_max_right ..).trans (le_max_left ..)
    apply Real.exp_monotone
    unfold lprice X X0 v; rw [hL']; linarith only [mul_le_mul_of_nonneg_left hsr h0]
  constructor
  intro D0 Z _ _ _ _ _ _ g hE hReach i j hIJ T' X' b' E' d' hZ Hx hF v' hz'' A' e' B' hslim hF' ha'' hN hl w q a0 aV YS z0 -- binder count
  obtain ⟨hD0,hD',hPB⟩ := Panel.determinant ha'' hN hl
  let NT := nt F
  have hj : 0≤J := Panel.amount_nonneg ..
  let DT := Module.finrank ℝ G.Color
  let d0 : ℝ := DT
  have hd : 0 ≤ d0 := by unfold d0 DT; positivity
  have hr : (0:ℝ) ≤ sites f := (site_pos f).le
  let pb := sites f * (4*d0*J/2)
  have hx : (NT:ℝ) ≤ sites f*4 := by unfold NT; rw [bonds_nt]; push_cast; unfold sites at *; linarith only [hf]
  have hc' : Real.log T'.det ≤ 2*pb := by
    apply (le_abs_self _).trans
    apply hPB.trans
    rw [card_meter]; push_cast
    unfold pb; linarith only [mul_le_mul_of_nonneg_right hx (mul_nonneg hd hj)]
  let f0 := fun (V : Config G c) => Real.exp (-R.beta*girder T.down T.low b' V)
  have H (V : Config G c) := pointwise_price S₁ hReach hE hN' hIJ Hx hZ
    (show R.beta*girder T.down T.low b' (1:Config G c)=0 by rw [girder_flat,mul_zero]) hD0 V hz'' hF' hc' (HD τ ht₁)
  refine ⟨(H 1).1,fun V=>?_⟩
  intro cP
  refine ⟨mul_pos (H V).1 (Real.exp_pos _),?_⟩
  let Yj := aV (max j (RG.flags (temp x) V).card)
  have hY : 0≤Yj := (Real.exp_pos _).le
  have hE' : rental c R ρ.top 1 x W M Λ δ + (D * nt F + pb + sites c * e') ≤ sites f * (box-y) := by
    unfold pb box; change _ ≤ sites f*(A+(4*D+4*d0*J/2+e)+y-y)
    linarith only [hRa,mul_le_mul_of_nonneg_right hx hD.le,mul_le_mul_of_nonneg_left hslim (site_pos c).le,mul_le_mul_of_nonneg_right hf hc]
  have hP' := surveil (M:=DT) hK hM (mul_nonneg ht₁.le S₁.hot.le) hPr
    (le_trans (four_sites S) (show 4*Fintype.card (Site f) ≤ 7*Fintype.card (Site f) by omega)) hE' (le_of_eq (b:=box) (by dsimp only [y,d,d0,DT]; ring))
  let nP := (Fintype.card PlaqAxes:ℝ)
  let yP := Real.exp (sites c*nP)
  have hgP := ceiling_sieve hT b' hF hβ.le h₂ V
  have hnP : 0 ≤ nP := by unfold nP; positivity
  have hhP : price ≤ r := (le_max_left price sumPro).trans (le_max_left ..)
  have hq : Real.exp (sites f*(box+7*d0*Real.log X))*yP ≤ YS := by
    dsimp only [YS,w,yP,d0,DT,X,v]
    rw [←Real.exp_add,hL']
    unfold lprice; apply Real.exp_monotone
    unfold price at hhP; change box+nP ≤ _ at hhP
    linarith only [mul_le_mul_of_nonneg_left hhP hr,mul_le_mul_of_nonneg_right hf hnP]
  unfold cP
  rw [← div_div,div_le_iff₀ (Real.exp_pos _)]
  apply (H V).2.trans
  change _ ≤ _
  let eP := rental c R ρ.top 1 x W M Λ δ + (D*NT+pb+sites c*e')
  let UP := rich f+(Fintype.card (Site c)-1)
  change Real.exp eP * (K*(τ*t)^DT)^UP * τ^(4*DT) * Yj * sieve T R.beta x V ≤ YS*τ^(4*DT)*Yj*f0 V
  have hR : 0 ≤ τ^(4*DT) := by positivity
  calc
    _ ≤ Real.exp (sites f*(box+7*d0*Real.log X)) * τ^(4*DT) * Yj * (yP * f0 V) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP' hR) hY) hgP (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg (Real.exp_pos _).le hR) hY)
    _ = (Real.exp (sites f*(box+7*d0*Real.log X)) * yP)*(τ^(4*DT)*Yj*f0 V) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right hq (mul_nonneg (mul_nonneg hR hY) (Real.exp_pos _).le)).trans_eq (by ring)

end YM.Further.RootedInteractingRemainder
