import YM.FullVolume.Sector.Twice
/-! Force strip. Not probing masked comparator on V jets. This is also lift of first unforced masked labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R} -- implicit v
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
namespace Tune
variable (U:Tune H v δ)
-- continuation of raw labels. Reimburse Sales optional once.
local notation "Λ" => U.pole
local notation "t'"=> U.notes
local notation "B₀" => radiusB x₀
local notation "Q'" => stella Q
local notation "A'" => topStorm S.patch
variable {p:Lyre.Signal 0} {ν:ℝ}
local notation "g"=> Q.goal L x₀
local notation "g₀"=> plainP U p ν
local notation "g₁"=> totalP U p ν
set_option quotPrecheck false
local notation "p₀" => (Q').costs L μ R.beta x₀ ν
open Greenbelt Gas Ursell Trees
variable {ε:ℝ} (hc:Clear Q L μ ν x₀ v p)(hr:Lyre.Clarity H 0 C δ ν) (hM:Margin G L x₀ ε δ) (ht:2≤v)
-- sticker under dictionary
abbrev feeI (l : ℕ) (α ν : ℝ) (p:Lyre.Signal 0) (i:Molecule S):= if H.ticketsP 0 l 0 i then 2*U.incomeK α ν p i else 0
local notation "t₀"=> U.feeI
lemma paidI {i n α ν p}:0 ≤ t₀ n α ν p i:=by unfold feeI; split; exact mul_nonneg (by norm_num) (U.income_pos ..); exact le_rfl
include hc U
lemma marque (a : ℕ) : Ac.Hit H.unionP B₀ (t₀ a ε ν p) (Q.exp-ε) (2*((Q').quantum L μ x₀ 0 0 a 0)):=by
  let AX:= p₀ -- collision
  have hp := H.laws.data.funds.length_eq; have hv:= H.laws.intake.window.1; rw [hp] at hv
  let V:= U.receipt p (H.alarms* topStorm S.patch); have h:= (U.furnace p).raise hc.shill
  have he : Mixed.Accounts S Q.halo B₀ AX H.birth V (ConnectedActivityE6.lengths T R) (steamP S AX):= ⟨fun i _=> ⟨mul_nonneg (show (0:ℝ)≤1 from zero_le_one) (Real.exp_pos _).le,le_rfl⟩, h.nonneg,fun _=> Nat.cast_nonneg _,h.hit⟩
  have hz:= Mixed.mixed_hit S Q.halo B₀ AX H.birth V _ _ (show AX.Buy S.patch.L Q.halo B₀ from by rw [hp]; exact hc.forcer _ hv) he 0 0 a 0
  intro i; have hP:= budget_scale (by norm_num : (0:ℝ)≤2) (hz i)
  refine budget_mono hP (fun j=> ?_) (fun j=> ?_)
  · split; next=> exact mul_nonneg (paidI U) (Real.exp_nonneg _)
    rfl
  split
  next ht =>
    dsimp only; rw [if_pos (show i ∈ Finset.biUnion j (Mixed.foot S Q.halo B₀ H.birth) from ht)]
    unfold feeI; split
    next ha =>
      rw [show Mixed.selected _ _ _ AX H.birth V _ _ 0 0 a 0 j= _ from if_pos (show Mixed.Allowed S Q.halo B₀ AX H.birth (ConnectedActivityE6.lengths T R) 0 a 0 j from ha)]; unfold incomeK
      let z:ℝ:= coverNumber B₀ (H.unionP j)
      change 2 * (Real.exp (ε*z)*_)*Real.exp _ ≤ 2*( ( (∏ r∈j,g₁ r) * _^0 ) * Real.exp (Q.exp*z))
      rw [show Q.exp*z=ε*z+(Q.exp-ε)*z from by ring,Real.exp_add,pow_zero,mul_one]
      unfold weightK; exact le_of_eq (by ring)
    rw [zero_mul]; have hf:= hP.1 j; dsimp only at hf; rw [if_pos (show i∈ Finset.biUnion j (Mixed.foot S Q.halo B₀ H.birth) from ht)] at hf; exact hf -- ht split
  exact hP.1 _
include hr ht hM
lemma likely_scout {A:Type} [Fintype A] [Nonempty A] {a:ℝ} (F:A→ℝ→ℝ) (h:∀ i, Scout (v/2) (F i) a) : Scout (v/2) (fun t=> likely (fun i=>F i t)) a:= by
  have hp := (Scout.pieces univ F (fun _=>a) (by linarith : 1≤v/2) (fun i _=>h i)).scale ((Fintype.card A:ℝ)⁻¹)
  rw [norm_inv,Real.norm_natCast,sum_const,nsmul_eq_mul,card_univ,inv_mul_cancel_left₀ _ _] at hp; exact hp
  exact_mod_cast Fintype.card_ne_zero
lemma amounted (X:Coat T F) (hx:X.x=x₀) (he:X.width=o.K) (i:Molecule S) (a:ℕ) (hT: a≤Cash.numP i) :
    Scout (v/2) (fun t=>proceedsA (U.notes t) X W o.a Q.halo Q.table i) (t₀ a ε ν p i):= by
  have hp: X.B=radiusB x₀:=congr_arg _ hx
  have hv t (ht:t∈sun): standsIn X R Q.halo i=standsIn X (U.notes t) Q.halo i:=by
    have he:= U.seats _ (U.lay ht); unfold standsIn claimed; apply propext
    rw [hp]; refine and_congr ?_ (and_congr (U.troupe_hold t (U.lay ht) i) ?_)
    · rw [show areas R T Q.halo B₀=areas (U.notes t) T Q.halo B₀ from U.arena t (U.lay ht)]
    change _= _ ↔ _= _; have hp:= congr_fun (U.stage t (U.lay ht)) i;
    change _ ∩ H.unionP i=_ ↔ _ ∩ _=_; rw [hp]; exact Iff.rfl
  set x:= 2*U.incomeK ε ν p i; let y:= fun k:S.Choices=> (planted X i).taggedL k; let f k t:= Coat.attains (y k) (U.notes t) Q.table W o.a (own i) Q.halo i
  have hb:1≤v/2:= by linarith
  by_cases h: standsIn X R Q.halo i; swap
  · refine ((Scout.still hb (0:ℝ)).enlarged (by simpa only [norm_zero] using U.paidI)).replace (fun t ht=> Eq.symm (if_neg (fun H=> h ((hv t ht).symm ▸ H))))
  have h':Ac.Spark H.supportP i:= (show Ac.Spark (areas R T Q.halo (radiusB x₀)) i from hp ▸ h.1)
  have hz: t₀ a ε ν p i=x:= if_pos (show H.ticketsP 0 a 0 i from ⟨h',Nat.zero_le _,hT,H.positive_volume _⟩)
  rw [hz]; have hg k:= U.hier hc hr hM (y k) hx he (planted_valid X i) (own i) i
  have hh:=half_lt_self (U.pole.full.1); refine (likely_scout U hc hr hM ht f (fun k=> ?_)).replace (fun t ht=>Eq.symm (if_pos (show standsIn X (U.notes t) Q.halo i from hv t ht ▸ h)))
  convert (hg _).recovery hb hh using 1
  unfold x; rw [show (1-(v/2)/v)⁻¹=2 from (by have h:=U.pole.full.1; field_simp; ring)]

def beverage (χ:Chi) (V:Config G c) (z:Molecule S) (t:ℝ) := poolA T x₀ χ o.K Q.table V (U.notes t) W o.a Q.halo z
lemma sweetly (χ:Chi) (V:Config G c) (z:Molecule S) (a:ℕ)(h:a ≤ Cash.numP z) : Scout (v/2) (U.beverage χ V z) (t₀ a ε ν p z):=by
  letI:Nonempty (Tree.Forest S.ratio):= Tree.select S.ratio S.patch.odd_side
  exact likely_scout U hc hr hM ht _ (fun (p:Reserve S)=> U.amounted hc hr hM ht (Greenbelt.prism T x₀ χ o.K V (Greenbelt.allot p)) rfl rfl z a h)
end Tune
end YM.ConnectedActivityE6.Empire
