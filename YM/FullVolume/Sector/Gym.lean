import YM.FullVolume.Sector.Reign
/-! Product revenue. Keep Wake — move criterion exactly to base price. -/
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
namespace Lyre
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
local notation "ψ" => U.pole
variable (X : Coat T F)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U₀:E→ Config G c} {s:E} (hx:X.x=x₀)(he:X.width=o.K)(hv:X.χ=χ)(hm:X.manifest)(hy:U₀ s=X.V)(hU:Mode U₀ s j u)
variable (z:Air f G)
local notation "Λ" => U.pole
local notation "β"=> R.beta
local notation "w₀"=> radiusB x₀
local notation "I₀" => X.input (worldZ X β z)
local notation "f₀" => fun i=> steer X A (worldZ X β z) (U₀ i)
local notation "z₀" => fun i=> course X A β z (U₀ i)
local notation "Yd"=> fun i=> vary X (U₀ i)
variable {p:Signal j} {ν:ℝ}
abbrev paysT := (stella Q).costs L μ R.beta x₀ ν
-- Keep clearance:
local notation "σ" => paysT (ν:=ν) (Q:=Q) (L:=L) (μ:=μ) (x₀:=x₀) (R:=R)
set_option quotPrecheck false
abbrev markP (ν:ℝ) (p:Signal j) (x:ℝ):= stout S Q.halo (radiusB x₀) (paysT (ν:=ν) (Q:=Q) (L:=L) (μ:=μ) (x₀:=x₀) (R:=R)) (M.billK) (M.billE p) x
abbrev meadow (ν:ℝ) (p:Signal j):= M.markP ν p (M.pole.stencil.M)
abbrev mouth (ν:ℝ) (p:Signal j):= M.markP ν p M.weft
local notation "f₁"=> M.mouth ν p
local notation "f₂"=> M.meadow ν p
variable (hC:Clear Q L μ ν x₀ v p)
structure Clarity (H : Cash W x₀ μ L Q o C T R) (j:ℕ) (A' δ ν:ℝ) : Prop where
  pays : ∀ (F:Tree.Forest S.ratio)(X:Coat T F) (i:Stores S), X.x=x₀ → 1≤ i.shares → FullVolume.Ray.Fold.charge j*(1+δ)^(Tune.count X i)*steamP S (Q.costs L μ R.beta x₀ A') i≤ steamP S ((stella Q).costs L μ R.beta x₀ ν) i
variable (hr:Clarity H j A' δ ν)
lemma bells {i:ℝ} (hi:|i|≤6*v) (p : Molecule S) (w:Air f G) (ξ:ℝ) :
    U.pole.flow i • w ∈ X.catastrophe ξ (U.notes i).beta (blaze p) ↔ w∈X.catastrophe ξ R.beta (blaze p):=by
  obtain ⟨ha,hb,hc,hK,h⟩:= uplift (U.seats i hi); rw [U.pitch i hi] at h hc; unfold catastrophe Poll.Crash; simp only [Set.mem_setOf]; simp_rw [← h, PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc]
  simp_rw [show ξ*X.t * (U.pole.flow i*(gStep R.beta)⁻¹) = U.pole.flow i * (ξ*X.t*(gStep R.beta)⁻¹) from (by ring),mul_le_mul_iff_right₀ hc]

lemma value_nn (i:Head S):0≤ f₂ i:= by
  rcases i with i|i|i|i
  · unfold meadow markP stout Mixed.costs; dsimp only [Sum.elim]; split; · unfold steamP Packets.income; change 0≤1*_; positivity
    rfl
  · exact (M.fortify p).nonneg (.inl i)
  · exact (M.fortify p).nonneg (.inr (.inl i))
  exact M.pole.stencil.positive
lemma coal_norm (i:Molecule S): (∏ x∈i,f₂ x)*M.pole.stencil.rad^(blaze i).card=∏ x∈i,f₁ x:=by
  let U:=i.toRight; rw [cumulate i,cumulate i]
  have hp x: f₂ (Sum.inl x)=f₁ (Sum.inl x):=rfl
  simp_rw [hp,mul_assoc]; apply congr_arg
  change (∏ x∈U, _)*_=∏ x∈U,_; rw [cumulate U,cumulate U]; have ht x: f₂ (.inr (.inl x))=f₁ (.inr (.inl x)):= rfl
  simp_rw [ht,mul_assoc]; apply congr_arg
  let D:=U.toRight; change (∏ x∈D, _)*_=∏ x∈D,_; rw [cumulate D,cumulate D]; have hh x: f₂ (.inr (.inr (.inl x)))=f₁ (.inr (.inr (.inl x))):=rfl
  simp_rw [hh,mul_assoc]; apply congr_arg
  change (∏ _x∈blaze i,M.pole.stencil.M)*_=∏ _x∈blaze i,(M.pole.stencil.M*M.pole.stencil.rad); rw [prod_const,prod_const]; exact (mul_pow ..).symm
include hC M
lemma acclaim: Mixed.Accounts S Q.halo w₀ σ H.birth (M.ledger p M.weft) (ConnectedActivityE6.lengths T R) (steamP S σ):=
   ⟨fun i _=> ⟨mul_nonneg (show (0:ℝ)≤1 from zero_le_one) (Real.exp_pos _).le,le_rfl⟩,(M.fortify p).nonneg,fun _=>Nat.cast_nonneg _,((M.fortify p).raise hC.shill).hit⟩
include hr hx he hv hm hy hU
lemma tided (k:Finset ℕ) (i:Head S) (h:Healthy (Pressure.temp X.x) (H.supportP i) X.V): Weigh j s v (f₂ i) (shape (R:=R) (T:=T) (Q:=Q) (x₀:=x₀) (r:=r) i) (fun t x=> M.vertex X U₀ z k i t x):=by
  rcases i with i|i|i|i
  · by_cases ht:Packets.connected S Q.halo w₀ i
    · have he := actors (E:=E) M X hx he hv hm hy hU z k i ht h
      have ha:= hr.pays F X i hx (Packets.shares_nonzero S _ _ ht)
      have hk : M.meadow ν p (.inl i)=steamP S σ i:= if_pos ht
      exact he.loses (ha.trans_eq hk.symm) (by change r≤r*1; simp)
    have hh : ¬Packets.connected S Q.halo X.B i:= by rw [show X.B=w₀ from congr_arg _ hx]; exact ht
    have hp : Weigh j s v 0 (r*1) (fun _ _=> (0:ℝ)):= FullVolume.Ray.Weigh.zero U.normed (by rw [mul_one]; exact zero_le_one.trans M.pole.stencil.active)
    refine (hp.loses (M.value_nn (ν:=ν) (p:=p) (.inl i)) le_rfl).cong ?_
    intro t ht; filter_upwards with y; exact (if_neg hh : ite (Packets.connected S Q.halo X.B i) (stock (vary X (U₀ y)) o.a (U.notes t) W Q.table (f₀ y) I₀ k i) 0=0)
  · exact hatched M X hx he hv hm hy hU z k i h
  · exact loglift M X hx he hv hm hy hU z p hC.low hC.promise k i h
  exact alerts M X hx he hv hm hy hU z k i h
-- revenue WHILE preserving alarm deposits
abbrev pulseJ (x:E)(t:ℝ):= course X A (U.notes t).beta (U.pole.flow t • z) (U₀ x)
set_option maxHeartbeats 300000 in
lemma ventures (l:Finset ℕ)(i:Molecule S) (hp : troupe T R Q.halo w₀ i) (hZ : Healthy (Pressure.temp X.x) (H.unionP i) X.V) :
    let F x t:= course X A (U.notes t).beta (U.pole.flow t • z) (U₀ x)
    Weigh j s v (Set.indicator (X.catastrophe (o.ξ/2) R.beta (blaze i)) (fun _=> ∏ k∈i,f₂ k) z) (r*(2*H.shapeW i))
      (fun t x=> Polar.floating (vary X (U₀ x)) o.a (U.notes t) W Q.table (F x t) l Q.halo i):=by
  intro f
  let S' := fun t x=> Polar.floating (vary X (U₀ x)) o.a (U.notes t) W Q.table (f x t) l Q.halo i
  have hf t (ht:t∈sun): S' t=ᶠ[𝓝 s] fun x=>∏ k∈i, M.vertex X U₀ z l k t x:=by
    have h0:= U.lay ht; let K:= M.plot t h0; let Y:=U.beams t h0; let D:=U.notes t; let z':= U.pole.flow t • z
    have hy := (K.rays F X hx he hv hm E U₀ s hy hU).2 z'|>.1
    have hf:worldZ X D.beta z'=worldZ X R.beta z:=by unfold z'; rw [← U.pitch t h0]; exact moving (U.seats t h0) ..
    have ht y:f y t= U.pole.flow t • course X A R.beta z (U₀ y) := by unfold f; rw [← U.pitch t h0]; exact coursing (U.seats _ h0) ..
    filter_upwards [hy.patch] with y hy'; unfold S' Polar.floating
    rw [hy.moving]; apply prod_congr rfl; intro j _
    let V:=vary X (U₀ y)
    have hr: Room P S T V.x := hx.symm ▸ H.laws.data.room
    have hp': Intake P T V.x D:= hx.symm ▸ Y.laws.intake
    refine ((plastic hy' hy.pulse).reeled hr W Q.table l Q.halo hp' j _).trans ?_
    unfold vertex; change Polar.ember V o.a _ _ _ (steer X A (worldZ X D.beta z') (U₀ y)) _ (f y t) l Q.halo j= _
    rw [ht y,hf]
  let V k:= M.vertex X U₀ z l k
  have ht : Weigh j s v (∏ k∈i,f₂ k) (r*(2*H.shapeW i)) S':= (FullVolume.Ray.Weigh.cong ((FullVolume.Ray.Weigh.prod i V f₂ _ U.normed (fun x hz=> tided M X hx he hv hm hy hU z hC hr _ _ (Finset.disjoint_of_subset_left (Finset.subset_biUnion_of_mem H.supportP hz) hZ))).loses le_rfl ?_) hf)
  swap
  · change ∑ k∈i,r*_≤_; rw [← mul_sum]; apply mul_le_mul_of_nonneg_left (Utopia.worthy i hp) (zero_le_one.trans (M.pole.stencil.active))
  by_cases hg:z∈ X.catastrophe (o.ξ/2) R.beta (blaze i); rw [Set.indicator_of_mem hg]; exact ht
  rw [Set.indicator_of_notMem hg]; change Weigh j s v 0 _ S'
  refine ⟨ht.slope,ht.smooth,fun y hy' n hn=> ((FullVolume.Ray.Scout.still U.normed (0:ℝ)).enlarged (by simp)).replace (fun t h => ?_)⟩ -- before price
  have he' := U.lay h; let z':=U.pole.flow t • z; let q:= M.plot t he'; let K:=U.beams t he'
  have hZ: Healthy (Pressure.temp X.x) (K.unionP i) X.V:= by rw [← U.stage]; exact hZ
  have hx':= q.stencil.acreage i l ((U.troupe_hold t he' i).1 hp) hx hv hm he hZ hU ((q.rays F X hx he hv hm E U₀ s hy hU).2 z'|>.1)
  have hf': z' ∉ X.catastrophe (o.ξ/2) (U.notes t).beta (blaze i):= fun H=> hg ((bells X he' i z _).1 H)
  rw [Set.indicator_of_notMem hf'] at hx'; exact (norm_le_zero_iff.mp ((point_norm hx' hn (v:=y) hy').trans_eq (zero_mul _))).symm
end Lyre
end YM.ConnectedActivityE6.Empire
