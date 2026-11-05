import YM.RG08.Arc.Puff
/-!
# full weight proof, path through flat representative
Laplace receipt of the *formal finite tori kernels* after exponential-chart
choice, tag collapse, denominator (rank-zero not dropped), auxiliary genuine
integral. Does not assert MASK independence or thermodynamic equality.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f m : Side} (S : StepData c f) (G : Gauge) (T : Forest S.ratio)
variable (U : Matrix (Body 1 f) (Body 1 c) ℝ) (v : ℝ→ Link G c)
local notation "A" => FreeResolvent.Active G T →ℝ
local notation "L" => T.Free → G.Color
local notation "Z" => (T.Free → G.Color) × ℝ
variable (κ : S.Choices) (n : ℕ) (V : ℕ → Config G f → ℝ) (F F' : Air G) (K M : FreeResolvent.FaceRow) (i : G.ColorIndex)
variable (D : ChartRatio G) (hD : LocalRatio D)
local notation "Q" => YM.RG08.quad G (YM.RG08.hessian M)
local notation "W" => regal S G T U v κ n V Q
local notation "Δ" => treeMatrix G S T K
local notation "☼" => nibble S G T U v D
local notation "RΦ" => fun t : ℝ=>Real.exp (-(1-stanza Q c (v t)))
local notation "Ξ" => awakening i S.patch D S.kernel.penalty F
local notation "X'" => heated S G T U v
local notation "P" => scout S G T U v n F i D

lemma surge_spice (h : ContDiffAt ℝ ω v 0) (j : ℕ) : Meadow (fun t x=> expEra (surge S G F i D) j (X' t x)) := by
  refine meadowCompose (priorigrass (F:=surge S G F i D) (fun i=> Grass.list (fun r _=> Grass.base (Hemi.pos (recital _ _)))) j) ?_
  intro a
  let m t := (X' t 0) a; let b (x:A):=(chargeS S T G *ᵥ x) a
  have he : Grass b := Grass.base (k:=1) (start_hemi ((ContinuousLinearMap.proj (R:=ℝ) a).comp (chargeS S T G).mulVecLin.toContinuousLinearMap|>.analyticAt _) (fun x t=> by simp [b,Matrix.mulVec_smul])) -- phi infer
  have hp : ContDiffAt ℝ ∞ m 0 := ((contDiffAt_pi.mp (heat_lamp S G T U v h 0)) a).of_le le_top
  rw [show (fun (t:ℝ) (x:A)=> X' t x a)=(fun _=>b)+ (fun t:ℝ=> fun _ : A=> m t) from funext fun t=>funext fun x=> by simp [b,m,heated,settler, Matrix.mulVec_zero]; rfl]
  exact (Meadow.single he).more (Meadow.work _ hp)
lemma scout_sun (h : ContDiffAt ℝ ω v 0) : Meadow P :=
  Meadow.sums (F:=fun j t x=> t^j * expEra (surge S G F i D) j (X' t x)) (s:=range (n+1)) (fun j _=> (Meadow.work (fun t:ℝ=>t^j) (contDiffAt_id.pow j)).times (surge_spice S G T U v F i D h j))

local notation "H" => hatsScale S T D * Real.exp (-1)
lemma sun_scout (hΔ : (Δ).PosDef) (h : ContDiffAt ℝ ω v 0) (hyp : ∀ w : Link G c, Aura (fun j=> leaned hΔ (snow G T) (chargeS S T G) (lodgeP G S.ratio (riseM S G T U *ᵥ w) w) (expEra (surge S G F i D) j)) (fun j=> -grand (j+2) (F' j) c w)) :
    Fit (n+1) (fun t=> Real.exp (-year (fun j t=> grand (j+2) (F' j) c (v t)) n t)) (fun t=> (crownM hΔ).average (snow G T) (P t)) := by
  let p e t:= -grand (e+2) (F' e) c (v t); let m := fun e t=> leaned hΔ (snow G T) (chargeS S T G) (lodgeP G S.ratio (riseM S G T U *ᵥ v t) (v t)) (expEra (surge S G F i D) e)
  have ha t : (crownM hΔ).average (snow G T) (P t)=year m n t := by
    let f j (x : A):=expEra (surge S G F i D) j (X' t x)
    have hv e : Grass (f e) := (surge_spice S G T U v F i D h e).sets _
    rw [show P t=∑ j∈range (n+1), t^j • f j from funext fun x=> by simp [Finset.sum_apply,scout,year,f], sun_list hΔ (snow G T) (fun i _=> (hv i).scale _)]; unfold year; simp_rw [sun_stem]; rfl
  have he (e) : Grass (grand (e+2) (F' e) c) := Grass.list (fun i _=> Grass.base (Hemi.pos (recital _ _)))
  rw [show (fun t=> Real.exp (-year (fun j t=> grand (j+2) (F' j) c (v t)) n t))=Real.exp ∘ year p n from funext fun t=> by simp [p,year,Finset.sum_neg_distrib]]; simp_rw [ha]
  exact year_aura (p:=m) (fun t=> hyp _) (fun e=>life_price (((he e).smooth.continuous.continuousAt.comp h.continuousAt|>.neg).mono_left nhdsWithin_le_nhds)) n

-- actual group coordinate proof

def discPay (t : ℝ)(u : T.Slice G) := Real.exp (- laboratory S κ n V t (input G c (t • v t)) (T.drape u)/t^2)
local notation "Θ" => discPay S G T v κ n V
lemma formulate (t) (ht : 0<t) (x : T.Free→G.Color) :
    PertExtension.Series.Radial.projection ☼ W t (plates G T.Free x)= (RΦ) t*(jacobian D (t • x + shifting S G T U v t)* Θ t (expLinks G _ (t•x+shifting S G T U v t))) := by
  rw [projection_eq]; unfold regal nibble; simp only [plates, Prod.smul_mk, smul_eq_mul,mul_one,chic,lodge_f,lodge_c]; unfold discPay
  have hv:= @drape_sprig c f S G T ((maplit G T).symm (t • x + shifting S G T U v t)) -- arg order?
  rw [← hv];
  set Z' := t•x+shifting S G T U v t
  have hp : profile T ((maplit G T).symm Z')=Z' := rfl; rw [hp, mul_left_comm (Real.exp ..),← Real.exp_add]; congr 2; field_simp; ring

include hD
-- The normalization pulls through exponential exp(-coarse Taylor chosen action) for every fixed small window.
-- coefficient factors in pulled-through normalization order, no prior scalar history here.
-- input history K frozen at one finite step. Multiple heights via wedges.
set_option maxHeartbeats 600000 in
lemma unbless (h : ContDiffAt ℝ ω v 0) (hV : Measurable v) (hp : S.patch.Branches S.kernel G) (he : ∀ i,Caper (quad G (YM.RG08.hessian K)) F n i (V i))
    (hF : Gets F) (hA : Halt F) (hX : Whole K) (hR : Whole M) (hK : ∀ m,(K.acts m).IsSymm) (hM : ∀ m,(M.acts m).IsSymm)
    (hU : Inputs S U (K.acts f) (M.acts c)) (hΔ : (Δ).PosDef)
    (hyp : ∀ w : Link G c, Aura (fun j=> leaned hΔ (snow G T) (chargeS S T G) (lodgeP G S.ratio (riseM S G T U *ᵥ w) w) (expEra (surge S G F i D) j)) (fun j=> -grand (j+2) (F' j) c w)) :
    let C:=∫ x,(crownM hΔ).kern x ∂snow G T
    ∃ s ∈ 𝓝 (1:T.Slice G), ∀ a : ℝ→Set (T.Slice G), (∀ᶠ t in 𝓝[>]0, MeasurableSet (a t) ∧ a t ⊆ s)→ (∃ y∈𝓝 1,∀ᶠ t in 𝓝[>]0, y ⊆ a t) →
      Fit (n+1) (fun t=> (t^Module.finrank ℝ (L))⁻¹ * (∫ x in a t, Θ t x ∂T.order G))
          (fun t=> C*hatsScale S T D * Real.exp (-oblige Q F' n t (v t))) := by
  intro C
  let B:=H
  obtain ⟨hi,ht⟩:= day_station S G T U v κ n V F K M i h hp he hF.1 hA hX hR hK hM hU hΔ
  have hm (t : ℝ) : Measurable (Θ t) := Real.continuous_exp.measurable.comp ((labs_meas S (fun i=> (he i).stamp) κ hp _ (w:=fun _=> input G c (t•v t)) measurable_const (T.continuous_drape.measurable) measurable_const n).neg.div_const _)
  have hw : ContinuousAt (RΦ) 0 := Real.continuous_exp.continuousAt.comp ((continuousAt_const.sub ((stanza_smooth Q c).continuous.continuousAt.comp h.continuousAt)).neg)
  obtain ⟨s,hS,h⟩:=shift_hall G T.Free hD (shifting S G T U v) (shift_zero S G T U v ▸ ((living_mean S G T U v h).continuousAt.mono_left nhdsWithin_le_nhds)) Θ (RΦ)
    (Eventually.of_forall hm) W ☼ (regal_meas S G T U v κ n V Q hV hp (fun i=> (he i).stamp)) (nibble_meas S G T U v D hD hV) hi ((nibble_fit S G T U v D hD h).of_le le_top) ht ⟨1,one_pos,eventually_pos.mono fun t hv x _=> formulate S G T U v κ n V M D t hv x⟩ n -- h shadow
  refine ⟨s,hS,fun a hb hd=>?_⟩
  let Y t:= (t^Module.finrank ℝ (L))⁻¹ * (∫ x in a t, Θ t x ∂T.order G)
  have hC : Fit (n+1) (fun t=> (RΦ) t*Y t) (fun t=> C*(B*Real.exp (-year (fun e z=>grand (e+2) (F' e) c (v z)) n t))) := by
    have hS:= apertures S G T U v κ n V F K M i D hD ‹ContDiffAt ℝ ω v 0› hp he hF hA hX hR hK hM hU
    let S' t:= B • (P t)
    have hu := moment_reels G T hΔ W ☼ hi ((nibble_fit S G T U v D hD ‹_›).of_le le_top) S' (Meadow.times (Meadow.single (Grass.const B)) (scout_sun S G T U v n F i D ‹_›)) n (fun x=>hS x hΔ)
    have hx:= (Fit.join (h a hb hd) hu.turn)
    let D' := sun_scout S G T U v n F F' K i D hΔ ‹_› hyp
    simp_rw [S',sun_stem] at hx
    apply hx.join (Fit.join (Fit.supply ?_ _) ((D'.turn.scale B).scale C))
    apply Eventually.of_forall; intro t; exact mul_comm ..
  let w':=(RΦ)
  have hl := hC.left (life_price ((hw.inv₀ ((Real.exp_pos _).ne')).mono_left nhdsWithin_le_nhds))
  refine (Fit.supply ?_ _).join (Fit.join hl (Fit.supply ?_ _))
  · exact Eventually.of_forall (p:=fun t=> Y t= (w' t * Y t)*(w' t)⁻¹) (fun t=> by rw [mul_comm (w' t),mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero _),mul_one])
  filter_upwards [] with t
  let u:=year (fun e z=> grand (e+2) (F' e) c (v z)) n t
  change (C*((_ * Real.exp (-1))* Real.exp (-u)))* _ = _
  rw [show oblige Q F' n t _=stanza Q c (v t)+u from rfl]; change _ * (Real.exp (-(1- stanza Q c (v t))))⁻¹ = _
  rw [← Real.exp_neg, mul_assoc, mul_assoc, mul_assoc,← Real.exp_add, ← Real.exp_add, ← mul_assoc]; congr 2; ring
end YM.RG08.Reflect
