import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Armada
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Rising

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March
namespace Charity
variable (M:Leaf R) (H:Cash W x μ L Q o C T R)
    {s Y A b B C' v d q u r:ℝ}{j n:ℕ}{χ:Chi} (N: Captain H j q d v Y A b r B C' n χ)
local notation "d0" => jewelDebt M Q L x
local notation "za'" => za M H (n:=n)
variable {t Y₁ g z c₁ v₁ b₁ κ' e:ℝ}
variable (h: Herd H N.conduit A B n)
open Next.Foundations
variable (U : BudgetPoint) {y:Site c} (hy:y∈M.crest.image S.ratio.parent) (hu:U.threshold=Pressure.temp x)(hf:U.order≤j)
local notation "K" => flareC (x:=x) (j:=j) U.power
include H h hu hf hy
lemma scops (p:H.fragrances): U.Regular (locus M H y p) (matin M H p χ):=by
  have he:=seatY M H y hy p; unfold locus at *; split at he
  next hx => rw [if_pos hx]; exact ((adapted M H N h U hu hf y p he)).1
  next hx=> rw [if_neg hx,quiet M H χ p hx]; exact AnalyticBridge.VerifiedReset.reg_const (p:=U) 0
-- at m&gt; cardinal
lemma aliveY (p:H.fragrances) : U.supBounds y (locus M H y p) (matin M H p χ) (if speaks M H p then d0*oval M H N p*K (H.bookFoot (.inr p)) else 0):=by
  have he := seatY M H y hy p; unfold locus at *; split_ifs with hx
  · exact (adapted M H N h U hu hf y p (show y∈ H.bookFoot (.inr p) from (by rwa [if_pos hx] at he))).2
  rw [quiet M H χ p hx]; simpa using! (AnalyticBridge.VerifiedReset.sup_const (p:=U) (G:=G) (X:={y}) (o:=y) 0)
-- when σ Packed.Low, actual Crown not money.upper label by card ≥2
omit h hu hf hy in
private lemma ordinal (p : H.ThinP) : speaks M H (chip H p) ↔ M.turn.badge S∈p.val ∧ troupe T R Q.halo (radiusB x) p.val := ⟨fun ⟨_i,hi⟩=>hi,fun h=>⟨none,h⟩⟩
omit h hu hf hy
omit H in
lemma worthN (X : Support c) : 0≤K X:=by apply pow_nonneg; unfold March.shiftG; positivity
-- force provide if any query on no-chip.Red.
variable (D:Plating (b₁:=b₁) M H N a t g c₁ u κ' e)
include D
lemma roughS (z : ℕ)(i : ℕ)(y : Site c)(hy:y∈M.crest.image S.ratio.parent):
    let p i:= locus M H y i
    SumBudget (fun q:H.fragrances=> if speaks M H q ∧ z≤q.fst then (oval M H N q * (flareC (x:=x) (j:=j) i (p q)))*Real.exp (a*coverNumber (radiusB x) (p q)) else 0) (collars G e x j i*(t*g^z*(1-g)⁻¹)):=by
  intro p; have ht:= ticks M H N D z y
  have hp:0≤ collars G e x j i:= by unfold collars Reserves.polyPrice shiftG; have h:= D.post; positivity
  refine budget_mono (budget_scale hp ht) (fun k=>?_) (fun k=>?_)
  · split; · apply mul_nonneg; exact mul_nonneg (oval_pos M H N _) (by unfold flareC shiftG; positivity); exact (Real.exp_pos _).le
    exact le_rfl
  have hh:=seatY M H y hy k; have hq:0 ≤ oval M H N k:=oval_pos ..; unfold locus at hh; dsimp only; split
  next hs =>
    rw [if_pos hs.1] at hh
    rw [if_pos hh,if_pos hs.2]; unfold p locus; rw [if_pos hs.1]
    unfold flareC collars; let z:ℝ:=coverNumber (radiusB x) (H.bookFoot (.inr k)); rw [mul_pow]; apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (polynomial_cost D.post (show 0 ≤ z from Nat.cast_nonneg _) _) (pow_nonneg (show 0≤ shiftG x by unfold shiftG; positivity) _)) hq) (Real.exp_pos _).le).trans_eq
    unfold Reserves.polyPrice z; rw [add_mul,Real.exp_add]; ring
  exact (budget_scale hp ht).1 _
omit D
-- collapsed budget α reserved.Back
abbrev potY (θ : Site c)(L:ℕ)(i : H.fragrances):=(flareC (x:=x) (j:=j) L (locus M H θ i))
-- separate PCS high bill. regular no-chip.
def pine (θ : Site c)(L:ℕ)(m': ℕ)(i : H.fragrances):=
    if speaks M H i then potY M H θ L (j:=j) i*d0*(if i.1=0 then B*persona M H q N.conduit.flair m' n 0 (i.2 none).val else oval M H N i) else 0
lemma baron (p : H.ThinP) (hp:¬prince M H (chip H p)) (hv:speaks M H (chip H p)): 1≤ p.val.card-1:=by
  obtain ⟨hK,hX⟩:= (ordinal M H p).1 hv; contrapose! hp
  have hh:p.val.card=1:= by have hx':0<p.val.card:=Finset.card_pos.mpr ⟨_,hK⟩; omega
  obtain ⟨i,hV⟩:= Finset.card_eq_one.mp hh; have hz:i=M.turn.badge S:= (mem_singleton.mp (hV ▸ hK)).symm
  exact ⟨rfl,hz ▸ hV,hX⟩
lemma quench (θ : Site c)(P m':ℕ)(i : H.fragrances):0 ≤ pine M H N θ P m' i:=by
  unfold pine; split; next=>
    apply mul_nonneg (mul_nonneg (by unfold potY flareC shiftG; positivity) (dew M H|>.2.1))
    split; exact mul_nonneg N.balance (earned M H q _ N.conduit.fares ..); exact oval_pos M H N _
  exact le_rfl

include h hy hu hf
lemma stockB (p:H.fragrances)(hp : ¬prince M H p): U.supBounds y (locus M H y p) (matin M H p χ) (pine M H N y U.power 1 p):=by
  unfold pine; by_cases hs : speaks M H p
  swap; · have he':=aliveY M H N h U hy hu hf p; rwa [if_neg hs] at he' ⊢
  rw [if_pos hs]; split
  next he =>
    obtain ⟨s,hq⟩:∃ s,p=chip H s:=⟨_,single H p he⟩; subst p; let K':= locus M H y (chip H s)
    have hx:=seatY M H y hy (chip H s)
    rw [chip_m]; unfold potY locus; rw [if_pos hs, Charity.clipS]
    let t:= escort M χ Q.table s.val Q.halo T W x o.K o.a
    let Z : ℝ:= B*persona M H q N.conduit.flair 1 n 0 s.val; let Y':=U.power
    have hk : (persona M H q N.conduit.flair 1 n 0 s.val)= persona M H q N.conduit.flair 0 n 0 s.val:=by
      have ht : 1≤ s.val.card-1:=baron M H s hp hs
      have hh : H.ticketsP 1 0 0 s.val ↔ H.ticketsP 0 0 0 s.val := by
        unfold Cash.ticketsP Mixed.Allowed; simp only [ht,Nat.zero_le,true_and]
      unfold persona; simp_rw [hh]
    let z:ℝ:=coverNumber (radiusB x) (H.unionP s.val); let f:=March.shiftG x*(1+z)
    have ht:1≤f:= one_le_mul_of_one_le_of_one_le (by unfold March.shiftG; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]) (le_add_of_nonneg_right (Nat.cast_nonneg _))
    change U.supBounds y _ t (K _*d0*Z); have hb:0≤ Z:=mul_nonneg N.balance (earned M H q _ (N.conduit.fares) ..)
    have hh:=debtor M H (p:=s.val) h s.2.2; unfold locus at hx;rw [if_pos hs, Charity.clipS] at hx
    have ha : Sailor G U.threshold C' j:= ⟨fun c _ h=> N.weigh.stroke c _ (h.trans (hu.trans_le N.talent))⟩
    refine ⟨mul_nonneg (mul_nonneg (worthN ..) (dew M H|>.2.1)) hb, fun V hv l hl h=>?_⟩
    have hK' : Ore V t v (d0*Z) j:= by unfold Z; rw [hk]; exact hh.2.2.2.2 V (hu ▸ hv)
    refine (costsD hh.1 ha N.income y (d0*Z) N.near hK' (Y:=f) ?_ ht l (hl.trans hf) h).trans_eq ?_
    · intro i hi; have hf : (separation i y:ℝ) ≤ z*(4*(radiusB x:ℝ)+2)+2*(radiusB x:ℝ):=by unfold z; exact_mod_cast Corona.extent _ _ hi hx
      unfold f shiftG; nlinarith [Nat.cast_nonneg (α:=ℝ) (radiusB x),show 0≤z from Nat.cast_nonneg _]
    change (K _)*_= _; ring
  have hh:=aliveY M H N h U hy hu hf p
  rw [if_pos hs] at hh; unfold potY; rw [locus,if_pos hs]; rw [locus,if_pos hs] at hh; rw [mul_right_comm, mul_comm _ d0,mul_comm (flareC ..), ←mul_assoc]  
  exact hh
end Charity
end YM.PhysicalNext.Repeat.Daisy
