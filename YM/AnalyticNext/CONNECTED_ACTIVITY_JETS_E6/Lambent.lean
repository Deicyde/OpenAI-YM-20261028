import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Icosa
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Plateau

/-! # Carrying Jet integral sector budget on an arc component

Masks frozen under chosen Representation. Pay L² controls on products.
Must still use DOMINATION near x for analytic kernel price. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Silica.Utopia
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter
open Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a A α β γ d η σ W s b μ r p q C C' v : ℝ} {j n l : ℕ} {Q : YM.ConnectedActivityE6.Target G P}
variable {V : E→ Config G c} {w : E → Directions G f} {u : E→ Air f G} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}
variable (Ξ : Utopia H j v d r C' χ)

def flair := rates Ξ.goalsK Ξ.goalsL (Ξ.M*Ξ.rad)
def tag := stout S Q.halo (radiusB s) (Q.costs L μ R.beta s C') Ξ.goalsK Ξ.goalsL Ξ.M
def fare := stout S Q.halo (radiusB s) (Q.costs L μ R.beta s C') Ξ.goalsK Ξ.goalsL (Ξ.M*Ξ.rad)
def meant (p : Molecule S) (k : ℕ) := if H.ticketsP 0 0 0 p then (∏ i∈p, Ξ.fare i)*(1+H.shapeW p)^k else 0

lemma accrues : Mixed.Accounts S Q.halo (radiusB s) (Q.costs L μ R.beta s C') H.birth Ξ.flair (lengths T R)
    (steamP S (Q.costs L μ R.beta s C')) := by
  exact ⟨fun i _=> ⟨mul_nonneg Ξ.lives.capture (Real.exp_pos _).le,le_rfl⟩,Ξ.uses.nonneg,fun _=>Nat.cast_nonneg _, Ξ.uses.hit⟩
lemma tagged (i : Head S) : 0 ≤ Ξ.tag i := by
  rcases i with i|i|i|i
  · unfold tag stout Mixed.costs; dsimp only [Sum.elim]; split
    next hz=> exact (Ξ.accrues.packetBound _ hz).1
    next => rfl
  · exact Ξ.uses.nonneg (Sum.inl i)
  · exact Ξ.uses.nonneg (.inr (.inl i))
  exact Ξ.positive
lemma remixes (p : Molecule S) : (∏ i∈p,Ξ.fare i)=(∏ i∈p,Ξ.tag i)*Ξ.rad^(blaze p).card := by
  rw [cumulate p,cumulate p];
  let P:=p.toRight
  have hp : (∏ i ∈ p.toLeft, Ξ.fare (.inl i))=∏ i∈p.toLeft,Ξ.tag (.inl i) := prod_congr rfl fun i _=> rfl
  have hs: (∏ i∈P,Ξ.fare (.inr i))=(∏ i∈P, Ξ.tag (.inr i))*Ξ.rad^(blaze p).card := by
    rw [cumulate P,cumulate P]
    let f i:= Ξ.fare (.inr (.inr i)); let g i:=Ξ.tag (.inr (.inr i))
    change (∏ i∈ P.toLeft, Ξ.goalsK i)* (∏ i∈P.toRight, f i)= ((∏ i∈ P.toLeft, Ξ.goalsK i)* (∏ i∈P.toRight,g i))*_
    rw [mul_assoc,cumulate P.toRight f,cumulate P.toRight g]; apply congrArg
    change (∏ i∈ P.toRight.toLeft, Ξ.goalsL i)*(∏ _i ∈ blaze p, Ξ.M*Ξ.rad)=((∏ i∈ P.toRight.toLeft, Ξ.goalsL i)*(∏ _i∈ blaze p, Ξ.M))*_
    rw [Finset.prod_const,Finset.prod_const,mul_pow,mul_assoc]
  rw [hp,hs,mul_assoc]
lemma fares (i : Head S) : 0≤Ξ.fare i := by
  have he:= Ξ.remixes {i}; rw [prod_singleton,prod_singleton] at he; rw [he]; exact
      mul_nonneg (Ξ.tagged i) (pow_nonneg Ξ.awake _)
lemma paid (k : ℕ) : Ac.Hit H.unionP (radiusB s) (fun p=> Ξ.meant p k) Q.exp (Q.overture L μ s k) := by
  let B:=Q.costs L μ R.beta s C'
  have hh:= Mixed.mixed_hit S Q.halo (radiusB s) B H.birth Ξ.flair (lengths T R) (steamP S B) Ξ.lives Ξ.accrues 0 k 0 0
  exact hh
lemma meant_nonneg (k : ℕ) (p : Molecule S) : 0 ≤ Ξ.meant p k := by
  unfold meant; split
  next h => exact mul_nonneg (prod_nonneg fun i _=> Ξ.fares i) (by have hx:= H.positive_volume p; positivity)
  exact le_rfl

omit Ξ in
lemma lengthP (P : Molecule S) (hp : troupe T R Q.halo (radiusB s) P) (i : Head S) (hi : i∈P) : 1≤ coverNumber (radiusB s) (H.supportP i) := by
  let B:=radiusB s
  have hl : (H.supportP i).Nonempty := by
    rcases i with i|i|i|i
    · have hh := (hp.1.checkpoints _ (mem_toLeft.mpr hi)).1
      obtain ⟨v,hx⟩ := hh
      refine ⟨anchor S v,?_⟩
      exact halo_subset _ i.place (Packets.place_reads S i ▸ mem_biUnion.mpr ⟨v,hx, contains ..⟩)
    · let p:= (R.activities.forced i)
      obtain ⟨j,h⟩ := p.inventory_ne; refine ⟨S.ratio.parent j,?_⟩; exact halo_subset _ _ (mem_image_of_mem _ (show j∈ RG.inspected p.support from mem_union_left _ (p.inventory_sup h)))
    · exact exChart ..
    exact ⟨_,crucial S i ..⟩
  suffices hh : coverNumber B (H.supportP i) ≠0 from Nat.pos_of_ne_zero hh
  intro hf; obtain ⟨D,hZ,h⟩:= coverNumber_realized B (H.supportP i); rw [hf,card_eq_zero] at h
  obtain ⟨x,hx⟩:= hl; have he:=halo_spec.mp (hZ.1 hx); rw [h] at he; simp at he
omit Ξ in
lemma worthy (P : Molecule S) (hp : troupe T R Q.halo (radiusB s) P) :
    ∑ i∈ P, spanW T R (radiusB s) Q.halo i ≤ 2*H.shapeW P := by
  unfold Cash.shapeW Mixed.charges Reserves.setPrice; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i hi=> ?_
  have hh:(1:ℝ)≤ coverNumber (radiusB s) (H.supportP i) := by exact_mod_cast lengthP (H:=H) P hp i hi
  rcases i with i|i
  · have he := mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg (α:=ℝ) i.shares); change 1 ≤ 2*((coverNumber _ (H.supportP _):ℝ)+
      H.faresP.extraSeed*i.shares); unfold Cash.faresP Cash.supportP at *; linarith
  change 1+(coverNumber (radiusB s) (H.supportP (.inr i))+lengths T R i) ≤ 2*((↑(coverNumber (radiusB s) (H.supportP (.inr i))):ℝ)+lengths T R i)
  linarith [show 0≤ lengths T R i from Nat.cast_nonneg _]

variable [FiniteDimensional ℝ E]
lemma acreage (P : Molecule S) (k : Finset ℕ) (hp : troupe T R Q.halo (radiusB s) P) (hf:X.x=s) (hΞ : X.χ=χ) (ht:X.manifest)
    (h : X.width=o.K) (hv : Healthy (Pressure.temp X.x) (H.unionP P) X.V) (hV : Mode V x j v) (hr : Clutch X z o.a R.beta d x j V w u) :
    Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze P)).indicator (fun _=>∏ i∈P,Ξ.tag i) z) (r*(2*H.shapeW P))
      (fun y=> Polar.floating (vary X (V y)) o.a R W Q.table (u y) k Q.halo P) x := by
  let f i (t:E):=Polar.ember (vary X (V t)) o.a R W Q.table (w t) (X.input (worldZ X R.beta z)) (u t) k Q.halo i
  have hU : (fun y=> Polar.floating (vary X (V y)) o.a R W Q.table (u y) k Q.halo P)=ᶠ[𝓝 x] fun y=>∏ i∈P,f i y := by
    filter_upwards [hr.patch] with y hy; unfold Polar.floating; rw [hr.moving y]
    let T:=H.laws.intake; obtain ⟨hp,hV⟩ := (show Room _ S _ (vary X (V y)).x ∧ Intake _ _ (vary X (V y)).x R from
      ⟨(show Room _ S _ X.x from hf.symm ▸ H.laws.data.room), (show Intake _ _ X.x R from hf.symm ▸ H.laws.intake)⟩)
    exact Finset.prod_congr rfl fun i _=> (plastic hy hr.pulse).reeled hp W Q.table k Q.halo hV i (u y)
  apply Brush.shimmy _ hU
  let S' := X.catastrophe (o.ξ/2) R.beta (blaze P)
  have hΞ' := Ξ.stream E F X V w u x z hf h hΞ ht hV hr
  have ht':r≥0 := zero_le_one.trans Ξ.active
  by_cases hy:z∈S'
  · rw [Set.indicator_of_mem hy]
    have he i (hi : i∈P) : Brush j (Ξ.tag i) (r*spanW T R X.B Q.halo i) (f i) x := by
      have hx := hΞ' k i (Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP hi) hv)
      unfold tag; rw [← show X.B=radiusB s from congr_arg radiusB hf]; exact hx
    apply (Brush.all_prod _ f _ _ he).climb le_rfl
    rw [← Finset.mul_sum,show X.B=radiusB s from congr_arg radiusB hf]; exact mul_le_mul_of_nonneg_left (worthy P hp) ht'
  rw [Set.indicator_of_notMem hy]; refine Brush.zi ?_ le_rfl (mul_nonneg ht' (mul_nonneg (by norm_num) (H.positive_volume P)))
  unfold S' catastrophe Poll.Crash at hy; change ¬(∀ i∈_,∃ j, _≤_ ∧ _≤_) at hy; push Not at hy
  obtain ⟨i,hi,hp'⟩:= hy
  have hc : Cash W X.x μ L Q o C T R := hf.symm ▸ H
  have hx := hr.sleek hc hV Ξ.clock ht h i (fun i hi=> (hp' i hi).le) k
  filter_upwards [hx] with t hZ
  exact Finset.prod_eq_zero (mem_toRight.mp (mem_toRight.mp (mem_toRight.mp hi))) hZ
end YM.ConnectedActivityE6.Blaze.Silica.Utopia
