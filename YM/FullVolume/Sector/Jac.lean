import YM.FullVolume.Sector.Frail
/-! Include Omiss.Spark & orbit-control at all complex apertures. -/
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
open Gas Ursell Trees Multiple Letter OmitClusters
variable {χ:Chi}
private lemma multiples {Y:Type*} (X:Finset Y) (f:Y→ℝ→ℝ) (a:Y→ℝ) (p : 1≤u) (he : ∀ i∈X,Scout u (f i) (a i)): Scout u (fun t=> ∏ i∈X,f i t) (∏ i∈X,a i):=by
  classical induction X using Finset.induction_on with
  | empty =>simpa using! Scout.still p (1:ℝ)
  | insert i s hi hx=> simp_rw [prod_insert hi]; exact (he i (mem_insert_self ..)).multiplies (hx fun j hj=> he j (mem_insert_of_mem hj))

section knot
variable {L':Side} (χ:Chi)
def bottle (V : Config G c) (p:H.Chapter) (t:ℝ):= p.elim (fun p=> Tune.beverage U χ V p.val t)
   fun z=> -Gas.term H.seam (fun i=>Tune.beverage U χ V i.val t) z
def fellows (V:Config G c) (s:H.Chainbook) (t:ℝ):= if H.Fresh s∧ Ac.Spark H.bookFoot s.1 ∧ H.statesPool V s then manyW (fun i=> bottle U χ V i t) s else 0

lemma picks {i:H.ThinP} (V:Config G c) {t:ℝ} (A:Cash W x₀ μ L Q o C T (U.notes t)) (P:Match.Alliance H A 1 0) (hp:P.units=Equiv.refl _): Tune.beverage U χ V i.val t=A.entriesPool χ V (P.bearing i):=by
  change Greenbelt.poolA _ _ _ _ _ _ _ _ _ _ i.val=_
  -- reducing inside .Aim too hard
  exact (congr_arg (fun x=> Greenbelt.poolA T x₀ χ o.K Q.table V (U.notes t) W o.a Q.halo x) (show i.val=(P.bearing i).val from (show i.val=P.units i.val from hp ▸ rfl)))
lemma bottles (V:Config G c) {t:ℝ} (A:Cash W x₀ μ L Q o C T (U.notes t))(P:Match.Alliance H A 1 0)(hp:P.units=Equiv.refl _): ∀ i:H.Chapter, U.bottle χ V i t=A.colognePool χ V (P.editor i):=by
  rintro (p|p)
  · exact congr_arg (fun x=> Greenbelt.poolA T x₀ χ o.K Q.table V (U.notes t) W o.a Q.halo x) (show p.val=P.units p.val from hp ▸ rfl)
  exact congr_arg Neg.neg (Match.sale P.bearing (fun i=>U.beverage χ V i.val t) (A.entriesPool χ V) P.sec (fun _=>U.picks χ V A P hp) p)
lemma purse (V:Config G c) {t:ℝ} (A:Cash W x₀ μ L Q o C T (U.notes t))(P:Match.Alliance H A 1 0)(hp:P.units=Equiv.refl _) (i:H.Chainbook): U.fellows χ V i t=A.smilesPool χ V (P.tongs i):=by
  unfold fellows Cash.smilesPool
  refine if_congr (and_congr (P.sap _) (and_congr (P.splint _) ?_)) (Match.cashes _ _ _ (U.bottles χ V A P hp) _) rfl
  have he:pull (1:Signed) (0:Site c) V=V:= pull_id V; have hx:= P.festoon V i; rwa [he] at hx
variable {e:ℝ} (hc:Clear Q L μ ν x₀ v p)(hr:Lyre.Clarity H 0 C δ ν) (hM:Margin G L x₀ e δ) (ht:2≤v)
abbrev currencyL (e ν:ℝ) (p:Lyre.Signal 0):= grade H.seam (fun i=> feeI U 0 e ν p i.val) (fun i : H.ThickP=> feeI U 1 e ν p i.val)
abbrev paysL (e ν : ℝ) (p: Lyre.Signal 0) (Z:H.Chainbook):= if H.Fresh Z∧Ac.Spark H.bookFoot Z.1 then manyW (U.currencyL e ν p) Z else 0
local notation "σ"=> U.currencyL e ν p
local notation "ρ"=> U.paysL e ν p
include hc hr hM ht
lemma midair (V:Config G c) (t:H.Chapter): Scout (v/2) (U.bottle χ V t) (σ t):=by
  have hv:1≤v/2:=by linarith
  rcases t with p|t; · exact U.sweetly hc hr hM ht χ V _ _ (Cash.forced_cost p.val p.2.2) -- edit order
  let q i := feeI U 0 e ν p (t.2 i).val; let D:ℝ:= coefficient H.seam t.2 / (t.1+1).factorial
  let f i:= Tune.beverage U χ V (t.2 i).val
  refine (((multiples univ f q hv (fun i _=> U.sweetly hc hr hM ht χ V _ _ (Nat.zero_le _))).scale (-D)).enlarged ?_).replace (fun t ht=>?_)
  · apply le_of_eq; unfold currencyL OmitClusters.grade; dsimp only [Sum.elim]; unfold clusters; unfold D; rw [norm_neg,norm_div,Real.norm_natCast]; change |coefficient _ _| / _*_= _; unfold q; ring
  change - D*(∏ i,f i t)= _; unfold bottle D Gas.term; dsimp only [Sum.elim]; unfold f; ring
lemma stays (V:Config G c) (i:H.Chainbook): Scout (v/2) (U.fellows χ V i) (ρ i):= by
  have h := midair U χ hc hr hM ht V
  have hz:1≤v/2:= by linarith
  unfold paysL fellows
  by_cases hh:H.Fresh i ∧ Ac.Spark H.bookFoot i.1; swap
  · rw [if_neg hh]; simp_rw [if_neg (show ¬(H.Fresh i ∧ Ac.Spark H.bookFoot i.1∧ H.statesPool V i) from fun hx=> hh ⟨hx.1,hx.2.1⟩)]
    exact (Scout.still hz (0:ℝ)).enlarged (by simp)
  rw [if_pos hh]; by_cases hp : H.statesPool V i; swap
  · simp_rw [if_neg (show ¬(H.Fresh i ∧ Ac.Spark H.bookFoot i.1∧ H.statesPool V i) from fun h=>hp h.2.2)]
    exact (Scout.still hz (0:ℝ)).enlarged (by rw [norm_zero]; exact Finset.prod_nonneg fun _ _=>div_nonneg (pow_nonneg ((h _).nonneg) _) (by positivity)) -- note field subst impossible placeholders
  simp_rw [if_pos (show H.Fresh i ∧ Ac.Spark H.bookFoot i.1∧ H.statesPool V i from ⟨hh.1,hh.2,hp⟩)]
  unfold manyW
  apply multiples _ _ _ hz; intro j _; let A:ℕ:= i.snd j+1; let B:ℝ:=(A.factorial:ℝ)⁻¹
  refine (((h j.val).power A).scale B).enlarged ?_ |>.replace (fun t ht=>?_)
  · rw [Real.norm_of_nonneg (show 0≤B from by unfold B; positivity)]; change _ ≤ (currencyL U e ν p j.val)^A/A.factorial; exact le_of_eq (by unfold B; ring)
  change B*_ = (U.bottle χ V j.val _)^A/A.factorial; unfold B; ring
end knot
end Tune
end YM.ConnectedActivityE6.Empire
