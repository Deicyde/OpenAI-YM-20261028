import YM.UVExtension.Wick.Bursary

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R}

def tabs (S : StepData c f) (K : Mixed.Costs) (B A : ℕ) (t : Alphabet c f → ℝ) :=
    Mixed.costs S A B (steamP S K) t
-- Keep peeled alarms: probability already paid. ℝ coin introduced for ALL terms not from sector total.
structure Copal (H : Cash W x μ L Q o a T R) (b : Mixed.Costs) (V : ι → Juice G f) (B : ℝ) (β : ℂ) where
    peeled : Alphabet c f → ℝ
    fee : Alphabet c f → ℝ
    peeled_nn : ∀ i,0 ≤ peeled i
    added : Mixed.Accounts S Q.halo (radiusB x) b H.birth fee (lengths T R) (steamP S b)
    paper : b.Buy L Q.halo (radiusB x)
    posts : ∀ p : Molecule S,H.alarms^(blaze p).card*(∏ i∈p,tabs S b (radiusB x) Q.halo peeled i) ≤ ∏ i∈p,tabs S b (radiusB x) Q.halo fee i
    height : β.re=R.beta
    voice : ∀ (v : ι → ℂ), (∀ i, ‖v i‖≤B) → ∀ (F : Tree.Forest S.ratio) (X : Coat T F), X.x=x→X.width=o.K→X.manifest→
      ∀ (p : Head S) (k : Finset ℕ) (z: Air f G), ‖fireball X R Q.table W o.a k Q.halo V β v z p‖≤tabs S b (radiusB x) Q.halo peeled p

namespace Copal
lemma cost (h: Q.rate+δ<γ) (he:γ<0) (hd:0<δ) {C:ℝ} (hg:0≤C) (N:ℕ) (W:ℝ) (hp: 0<μ) : ∃ a : ℝ,0≤a ∧∀ᶠ x in atTop,
    ∀ (c f:Side) (S:StepData c f) (T:Tube G S) (o:Target.Order G W) (R: Rep G f) (H:Cash W x μ L Q o C T R) (β:ℂ) (κ: Type) [Fintype κ]
      (V: κ → Juice G f), Fintype.card κ=N → β∈aisle (betaF G x L)→ β.re=R.beta → (∀ i,Nonempty (Cash W x μ L Q o C T (chunk R (V i) R.beta))) →
      Nonempty (Copal H ((stalk Q (by linarith : Q.rate≤γ) he).costs L μ R.beta x a) V (betaF G x L ^ δ) β) := by
  have hx : Q.rate≤γ := by linarith
  let g:= stalk Q hx he
  obtain ⟨b,hb,hY⟩:= trunkfit G L
  have hW' := indulgent P L Q γ δ 2 N hd (by linarith only [h])
  refine ⟨C+b,add_nonneg hg hb,?_⟩
  filter_upwards [hY,hW',g.pay_for L hp (add_nonneg hg hb),permits G L,(Rate.power (G:=G) (a:=γ) (L:=L)).below he 1 zero_lt_one,
    Delay.shift_pos G L] with x hY hW hP hT hz hD c f S T o R H β κ _ V heq hF hv he'
  let V' (i:κ):=Classical.choice (he' i)
  let d:=g.costs L μ R.beta x (C+b); let u:=R.beta; let C':= betaF G x L^δ; let a:=H.opt; let v' i:=(V' i).opt
  have hH:= H.laws; have ht:= hH.data.funds.length_eq
  let t i:= 2*platK a v' C' i; let t' : Alphabet c f → ℝ:= rates (fun i=>t (.inl i)) (fun i=> t (.inr (.inl i))) (topStorm S.patch)
  have hu:= H.laws.intake.positive
  let D : Alphabet c f→ℕ:= Sum.elim (forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)
  have hC:0≤ C':= by unfold C'; positivity
  have hhV i: Sales (radiusB x) Q.relative Q.ε H.birth (v' i) D (Q.goal L x):=(V' i).fares
  have hz': |(2:ℝ)|= 2:= abs_of_pos (by norm_num)
  specialize hW _ _ S T R _ heq a v' H.fares hhV
  simp_rw [hz'] at hW
  have h: Sales (radiusB x) Q.relative Q.ε H.birth t D d.optionalHit:= hW
  have hv : 0 ≤ Q.relative:= by unfold Target.relative; linarith [Q.bound,Q.usable,Q.pos]
  have hy:= hP R.beta (ht ▸ hH.intake.window.1)
  refine ⟨⟨t',t,(by rintro (i|i|i); exact h.nonneg (.inl i); exact h.nonneg (.inr (.inl i)); exact zero_le_one.trans (topStorm_one _)), ⟨fun i _=>⟨mul_nonneg hy.capture (Real.exp_pos _).le,le_rfl⟩,h.nonneg,fun _=>Nat.cast_nonneg _, h.hit⟩, hy,?_,‹β.re=R.beta›,?_⟩⟩
  · -- Posts with extra ignored for alarms.
    intro p; rw [cumulate p,cumulate p]; let X := p.toRight; let Y:=X.toRight; let q:= H.alarms
    -- down
    have hW : q^(blaze p).card * (∏ i∈ X, t' i) ≤ ∏ i∈X, t i:= by
      rw [cumulate X,cumulate X]; let L' i:= t (.inr i); let V i:=t' (.inr i)
      change _ * ((∏ i∈ X.toLeft,t (.inl i))* (∏ i∈ Y,V i)) ≤ (∏ i∈ X.toLeft,t (.inl i)) * ∏ i∈Y,L' i
      rw [mul_left_comm]
      rw [cumulate Y,cumulate Y]; apply mul_le_mul_of_nonneg_left _ (prod_nonneg (fun i _=>h.nonneg (.inl i)))
      change _ * ((∏ i∈Y.toLeft,t (.inr (.inl i))) * (∏ _i ∈ blaze p,topStorm S.patch)) ≤ (∏ i∈Y.toLeft,t (.inr (.inl i)))*∏ i∈blaze p,L' (.inr i)
      rw [mul_left_comm,← Finset.prod_const, ← prod_mul_distrib]; apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun i _=> h.nonneg (.inr (.inl i)))
      apply prod_le_prod (fun i _=> mul_nonneg H.pos (zero_le_one.trans (topStorm_one _)))
      intro i _; let k:Alphabet c f:= .inr (.inr i); have hh:0≤ C'*(∑ i,v' i k) := mul_nonneg hC (sum_nonneg fun i _=> (V' i).earns k)
      have he:0≤ H.alarms*topStorm S.patch:= mul_nonneg H.pos (zero_le_one.trans (topStorm_one _)); change _ ≤ 2*(2*(H.alarms*topStorm S.patch)+C'*(∑ i,v' i k)); linarith only [hh,he]
    let A i:= tabs S d (radiusB x) Q.halo t (Sum.inl i)
    change _ * ((∏ i∈ p.toLeft,A i)* _)≤(∏ i∈p.toLeft,A i)*_
    rw [mul_left_comm]; refine mul_le_mul_of_nonneg_left hW (prod_nonneg fun i hi=>?_); unfold A tabs Mixed.costs; dsimp only [Sum.elim]; split; exact mul_nonneg hy.capture (Real.exp_pos _).le; exact le_rfl
  intro v hL F X hp hK hX p k z
  have hh:‖β‖/β.re≤2:= (hT _ _ S _ ht hF).2; have ha:X.B=radiusB x:= congr_arg _ hp
  let y:= X.μ+X.atmos z
  rcases p with s|i|i|i
  · change ‖warmth _ _ _ _ _ * (rawP X (flight R 1) _ _ _ _ _ s y:ℂ)‖≤ _
    have h'f:R.beta=β.re:= ‹β.re=R.beta›.symm; rw [warmth_same X (v:=R.beta) β _ _ hu, mul_comm (warmth X 1 R.beta s _), mul_assoc,
      ← steam_warm X y s zero_lt_one hu Q.table_exists]
    change ‖_* (rawP X R _ _ _ _ _ _ y:ℂ)‖ ≤ tabs S d (radiusB x) Q.halo t' (Sum.inl s)
    rw [norm_mul,Complex.norm_real]; unfold tabs Mixed.costs; dsimp only [Sum.elim]; split
    next ht' =>
      rw [rawP,ha, if_pos ht']
      apply (mul_le_mul (show ‖warmth X R.beta β s (barks X y s)‖≤ Wick.chimney s b G L x from (by rw [h'f]; exact hY c f S T F X hp ht s (barks X y s) β hF)) (show ‖X.Pack R Q.table k W o.a s y‖ ≤ steamP S (Q.costs L μ R.beta x C) s from H.quotes F X hp hK hX|>.2.2.1 y k s) (norm_nonneg _) (Real.exp_pos _).le).trans_eq
      exact growfit b C s
    next hz => rw [rawP,ha,if_neg hz, norm_zero,mul_zero]
  · change ‖∑ j,_ * (X.bag _ _ y i:ℂ)‖ ≤ t (.inl i)
    apply (norm_sum_le ..).trans; unfold t platK
    have H' := sum_le_sum (s:=Finset.univ) (g:=fun j=> C'* v' j (.inl i)) (fun j _ => show ‖v j * (X.bag (chunk R (V j) 1) o.a y i:ℂ)‖ ≤ _ from (by rw [norm_mul,Complex.norm_real]; apply mul_le_mul (hL _) ((V' j).quotes F X hp hK hX|>.1 i y) (abs_nonneg _) hC))
    apply H'.trans; rw [← mul_sum]; have hh : 0≤ ∑ j, v' j (.inl i):= sum_nonneg fun j _=> (V' j).earns _; have he :0≤a (.inl i):= H.earns _; nlinarith only [he,hC,hh]
  · change ‖Complex.exp _-1‖ ≤ 2*platK H.w (fun i=> (V' i).w) C' _
    have hh := draws H V (‹β.re=_›.symm) V' v hL z hh hp hK hX i hC
    have hl : t (.inr (.inl i)) ≤ 1 := (h.atom hv Q.usable.le (.inr (.inl i)) (exChart ..)).trans ((le_abs_self _).trans hz)
    change 2*platK H.w (fun k=> (V' k).w) (betaF G x L^δ) i ≤ _ at hl
    exact (Complex.norm_exp_sub_one_le (show ‖_‖≤1 from (by linarith only [hh,hl]))).trans (mul_le_mul_of_nonneg_left hh (by norm_num))
  change ‖(X.detect _ W o.a R k i:ℂ)‖≤topStorm S.patch; rw [Complex.norm_real]; exact X.fires_at ..
end Copal
end YM.UVExtension.Wick
