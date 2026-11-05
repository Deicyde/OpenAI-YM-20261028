import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Sum
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Port
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lapis.Misty

/-!
# Central exact μ integral with Gram and price

All for same F,k (any t at near vector uses same analytic φ,ψ). β
 physical. No reflag when drawing from r. Will verify stay permission next.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Fare
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange
open ConnectedActivityE6 Blaze Brush Poll Coat
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (F : Forest S.ratio) (T : Tube G S) (O : ChartRatio G) (k : S.Choices)
local notation "X" => Positions (Uniform.Primary c G)
local notation "K" => Precision.Key F G
local notation "Y" => Poll.Body K
variable (ρ : Bid.Dir G c→AxisChart G F) (B : BudgetPoint) (β D : ℝ) {p a s u v : ℝ} {j : ℕ}

def coverLog (x : X) := β*Lapis.table F k T.up T.high (x,Lapis.orbit F ρ x)+mist F O T.up (x,Lapis.orbit F ρ x)+Lantern.shade (Lapis.gram F T.up T.high ρ k) x
def solar := (prefactor S G β)*(Real.sqrt (2*Real.pi)*gStep β)^ Fintype.card K*O.scale^Fintype.card F.Free
lemma sun (he : 0<β) (hO : LocalRatio O) : 0 < solar F O β := by
  have ht:0<gStep β:= inv_pos.mpr (Real.sqrt_pos.mpr he); have hs:= hO.scale
  have H : 0 < prefactor S G β := pow_pos (inv_pos.mpr (S.penaltyZ_pos _)) _
  unfold solar; positivity
local notation "M" => Lapis.gram F T.up T.high ρ k
local notation "A" => Lapis.table F k T.up T.high
local notation "μ" => Poll.sweep (M 0)⁻¹
local notation "H₀" => mist F O T.up
local notation "G₀" => Lapis.orbit F ρ
local notation "V" => (fun x : X=> represent (tint G _ x))
local notation "d" => gStep β
variable (h' : Golf (Lapis.table F k T.up T.high) (mist F O T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ k) j D u v p) (he : 0<β) (hv : gStep β < v) (hS : S.patch.Branches S.kernel G)
    {x : Positions (Uniform.Primary c G)} (hx : ‖x‖<u)
lemma gS (h : 0<β) : 0 < d ∧ (d)^2*β=1 := by
  have he : 0<d:=inv_pos.mpr (Real.sqrt_pos.mpr h); refine ⟨he,?_⟩
  unfold gStep; rw [inv_pow,Real.sq_sqrt h.le]; field_simp
-- momentum payment not erasing anything
variable (Z : ∀ z:Poll.Body (Precision.Key F G), ‖z‖≤D → ∀ l:S.Choices, Lapis.table F l T.up T.high (x,Lapis.orbit F ρ x+gStep β • z)=Lapis.table F k T.up T.high (x,Lapis.orbit F ρ x+gStep β • z))
    (hO : LocalRatio O) (hlight : ∀ z:Poll.Body (Precision.Key F G), ‖z‖≤D → windmill F (Lapis.orbit F ρ x+gStep β • z) ∈ mouth O) (hQ : ∀ z:Poll.Body (Precision.Key F G), ‖z‖≤D → flags B.threshold (F.drape (draw F (represent (Uniform.tint G _ x)) (Lapis.orbit F ρ x+gStep β • z)))=∅)
include h' hx he hv Z hO hlight hQ hS
lemma reserves (z:Y) (hz : z∈closedBall 0 D) : let W:= G₀ x+d • z; let U := V x
    d^Fintype.card K * (pay O (windmill F W)*overall F T B β U (draw F U W))=
      solar F O β * Real.exp (-coverLog F T O k ρ β x) * (Blaze.Shield.lens₀ ((M 0)⁻¹) z * Real.exp (grace A H₀ G₀ M z (d,x))) := by
  intro W U; let u':= F.drape (draw F U W)
  obtain ⟨hh,hE⟩:=gS β he; have hv': ‖d‖ < v :=by rw [Real.norm_of_nonneg hh.le]; exact hv
  have ht:0<u:=h'.pos
  have h₀ := h'.station 0 (show ‖(0:X)‖<u from by simpa)
  let D' := vote A G₀ z (0,0); let K' := vote A G₀ z (d,x)
  have hj : Blaze.Shield.lens₀ ((M 0)⁻¹) z= (((Real.sqrt (2*Real.pi))^Fintype.card K)⁻¹ * Real.exp (Lantern.shade M 0-D')):= by
    rw [Blaze.Shield.lens₀, nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (h'.gram 0 (show ‖(0:X)‖<u from by simpa)).1.det_pos.ne'),det_nonsing_inv,Ring.inverse_eq_inv,Real.log_inv]
    unfold D' Lantern.shade; rw [Lantern.roll, ← (h₀ z).2]; ring_nf
  have ha := mem_closedBall_zero_iff.mp hz
  have hf : ∀ t∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ 2 A (visit G₀ z t (d,x)) := fun t ht=> (h'.color z t _ ha ht hv' hx).1.smooth.of_le (by exact_mod_cast show 2 ≤ j+2 from Nat.le_add_left ..)
  have hF := Lantern.funds A G₀ z d x (h'.station x hx z).1 hf
  have hL : ∀ l:S.Choices, mainTerm T.high T.up u'+noiseTaylor S U u' l=A (x,W):= Z z ha
  let y:= pay O (windmill F W); let q':= Real.exp (-β*A (x,W)-Precision.loop T.up u')
  have hx l : actU F T l B β U (draw F U W)=prefactor S G β*S.likelihood u' l * q':= by rw [acts F T l B β U _ (hQ z ha), show mainTerm T.high T.up _+noiseTaylor _ _ _ _= _ from hL l]
  have hp : overall F T B β U (draw F U W)=prefactor S G β*q':= by unfold overall; simp_rw [hx,← sum_mul,← mul_sum,S.chosen hS,mul_one]
  have hg i : 0 < O.J (windmill F W i):= hO.pos _ (hlight z ha i (Set.mem_univ _))
  have hy : y= O.scale^Fintype.card F.Free * Real.exp (sumAt F O W) := by
    unfold y pay sumAt; rw [Real.exp_sum,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]; apply congr_arg; apply Finset.prod_congr rfl; intro i _; exact (Real.exp_log (hg i)).symm
  have hb : β*A (x,W)-β*A (x,G₀ x)=K':= by change A (x,W)-_=d^2*K' at hF; rw [← mul_sub,hF,← mul_assoc,mul_comm β,hE,one_mul]
  have hk : -coverLog F T O k ρ β x + (Lantern.shade M 0 -D' + grace A H₀ G₀ M z (d,x)) = -(β*A (x,W) + H₀ (x,W)) := by
    unfold coverLog grace
    rw [show Lantern.visit G₀ z 0 (d,x)=(x,G₀ x) by simp [Lantern.visit],show Lantern.visit G₀ z 1 (d,x)=(x,W) by simp [Lantern.visit,W]]
    change -(_+_+_)+(_- D'+(_-_+(D'-K')+_))=_; linarith only [hb]
  have hpow : q' =Real.exp (-(β*A (x,W)+H₀ (x,W))-sumAt F O W) := by
    unfold q'; apply congr_arg Real.exp; rw [Lapis.plume]; change -β*A _-Precision.loop _ u'= -(_+ (Precision.loop T.up u'-_))-_; ring
  let m:=Fintype.card K; let R:=Real.sqrt (2*Real.pi)^m
  let r:=Fintype.card F.Free
  rw [hp,hj, show pay O (windmill F W)=_ from hy,hpow, solar, mul_pow]
  change d^m*(O.scale^r*_ *(_ * _)) = _* (R * _)* O.scale^r*_ * (R⁻¹*Real.exp _*Real.exp _)
  rw [mul_assoc R⁻¹, ← Real.exp_add, show Lantern.shade M 0 - D'+_ = (-(β*A (x,W)+H₀ (x,W)))+coverLog F T O k ρ β x from (by linarith only [hk]),Real.exp_sub,Real.exp_add,Real.exp_neg (coverLog F T O k ρ β x)] -- edit
  have hR:0<R:=by unfold R; positivity
  field_simp; unfold m; ring
lemma pricing (hg : StronglyMeasurable (overall F T B β (V x))) :
    ∫ y in staying F (G₀ x) d D (V x), overall F T B β (V x) y ∂F.order G =
      solar F O β * Real.exp (-coverLog F T O k ρ β x) * ratify A H₀ G₀ M D (d,x) := by
  rw [cubits F O _ _ _ _ _ (gS _ he).1 hO hlight hg,← integral_const_mul,ratify,Blaze.Shield.recommends _ (h'.gram 0 (by simp [h'.pos])).1.inv]
  rw [← integral_const_mul, ← integral_indicator (measurableSet_closedBall)]; apply integral_congr_ae; filter_upwards with z
  by_cases hp:z∈ closedBall (0:Y) D
  · unfold ballots; rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; exact reserves F T O k ρ B β D h' he hv hS hx Z hO hlight hQ z hp
  unfold ballots; rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp,mul_zero,mul_zero]
end YM.PhysicalNext.Repeat.Fare
