import YM.FullVolume.Sector.Burn
/-! Stamped integral in old world for all marked columns.
    Clock comparisons on *same point*. -/
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
local notation "g₁"=> U.totalP p ν
lemma swell (i:Molecule S):
    (∏ k∈i,g₀ k)*H.alarms^(blaze i).card=∏ k∈i,g₁ k:=by
  let f:=g₁; let u:=g₀; let U':=i.toRight; rw [cumulate i (g₀),cumulate i (g₁)]; change ((∏ k∈_, _)*(∏ k∈U',_))*_= _*_
  have h(k): u (Sum.inl k)=f (Sum.inl k):=rfl
  rw [show (∏ k∈_,g₀ (Sum.inl k))= _ from Finset.prod_congr rfl (fun k (_:k∈i.toLeft)=>h k),mul_assoc]; apply congr_arg; rw [cumulate U',cumulate U']
  have he(k): u (.inr (.inl k))=f (.inr (.inl k)):=rfl; let Z:=U'.toRight
  rw [show (∏ k∈_,g₀ (Sum.inr (Sum.inl k)))= _ from Finset.prod_congr rfl (fun k (_:k∈U'.toLeft)=>he k),mul_assoc]; apply congr_arg
  change (∏ k∈Z,_)*_=∏ k∈Z,_; rw [cumulate Z,cumulate Z]; apply le_antisymm -- hack after factor
  all_goals -- fix
    have eqp : (∏ x∈Z.toRight,A') * H.alarms^(blaze i).card = ∏ x∈Z.toRight,(H.alarms * topStorm S.patch):=by rw [prod_const,prod_const,mul_pow]; exact mul_comm ..
    simp only [mul_assoc]; -- rr
    first| exact (congr_arg (fun z=> (∏ k∈Z.toLeft,u (Sum.inr (.inr (.inl k)))) * z) eqp).le | exact (congr_arg (fun z=> (∏ k∈Z.toLeft,u (Sum.inr (.inr (.inl k)))) * z) eqp).ge
lemma propense i: 0 ≤ g₀ i:=by
  rcases i with p|i|i|i
  · unfold plainP sheet Mixed.costs; dsimp only [Sum.elim]; split; next h=> change 0 ≤ 1*Real.exp _; positivity
    rfl
  · exact (U.furnace p).nonneg (.inl i)
  · exact (U.furnace p).nonneg (.inr (.inl i))
  exact zero_le_one.trans (topStorm_one _)
variable (X : Coat T F)
abbrev weightK (i:Molecule S):= ∏ k∈i,g₁ k
abbrev incomeK (α ν:ℝ) (p:Lyre.Signal 0) (i:Molecule S) := Real.exp (α*coverNumber (radiusB x₀) (H.unionP i)) * weightK U (p:=p) (ν:=ν) i

lemma glass_w (I: Finset (Bond f)) (z:Air f G) (h:X.relating.PosDef) : Scout v (fun t=>Lyre.markL X z I ((Λ).flow t)) ((1+δ)^(lensS I G).card):=by
  let H:= swim (lensS I G) z; let D:=circuit (lensS I G) X.relating; have hd : D.PosDef:=h.submatrix Subtype.val_injective
  let A:= H.ofLp; let q:= dotProduct A (D⁻¹ *ᵥ A)/2; let T:=U.pole; let n:= (lensS I G).card
  have hp : 0 ≤ q:= div_nonneg (show 0≤ dotProduct A (D⁻¹ *ᵥ A) from hd.posSemidef.inv.dotProduct_mulVec_nonneg A) (by norm_num)
  have ht : Real.exp (T.scaleT q) ≤ 1:=by
    let t:=v*T.seat q (0:Fin 1); have hg:= (T.moves t (U.away q (k:=0) 0)).1
    apply Real.exp_le_one_iff.mpr; apply (T.landing q (k:=0) 0).trans (mul_nonpos_of_nonpos_of_nonneg (show T.sqcost t ≤0 from (by unfold Fold.sqcost; nlinarith)) hp)
  refine (((T.pulse.power n).multiplies (T.unveils q)).enlarged (mul_le_of_le_one_right (pow_nonneg (by have hp:=T.full.2.2; linarith) _) ht)).replace (fun t h=>?_)
  exact (Lyre.present X z I _).symm

-- value mountain for all Crew even forced
variable (k:Finset ℕ) (i:Molecule S)
def content (t:ℝ) (y:F.Slice G × Air f G):= X.body (U.notes t) Q.table W o.a k Q.halo i (y.1,(Λ).flow t • y.2)
variable (hC:Clear Q L μ ν x₀ v p) (hr:Lyre.Clarity H 0 C δ ν) (hX:X.x=x₀)(he:X.width=o.K) (hy:X.manifest)
include hC hr hX he hy
lemma gains (y:F.Slice G × Air f G): Scout v (fun t=> U.content X k i t y) ((X.catastrophe o.ξ R.beta (blaze i)).indicator (fun _=> ∏ j∈i,g₀ j) y.2):=by
  let F t:= U.content X k i t y; let Y:= X.wrapY y.1; let z:=y.2
  by_cases hg:z∈ X.catastrophe o.ξ R.beta (blaze i)
  · rw [Set.indicator_of_mem hg]; change Scout v (fun t=> ∏ j∈i,snaps U Y j z k t) _
    let p' i' t := snaps U Y i' z k t
    suffices hv : ∀ J: Molecule S, Scout v (fun t=> ∏ x∈J,p' x t) (∏ x∈J,g₀ x) from hv i
    intro J; induction J using Finset.induction_on with
    | empty=> simpa using! Scout.still U.normed (1:ℝ)
    | insert x j' hx h=> simp_rw [prod_insert hx]; exact (sprawl U Y hC hr z k hX he hy x).multiplies h
  rw [Set.indicator_of_notMem hg]; apply ((Scout.still U.normed (0:ℝ)).enlarged (by simp)).replace
  intro t ht; have h:= U.lay ht; symm; by_contra hp; apply hg; exact (Lyre.bells (U:=U) X h i z o.ξ).1 ((U.beams t h).lease X hX he hy k i y.1 ((Λ).flow t • z) hp)
end Tune
end YM.ConnectedActivityE6.Empire
