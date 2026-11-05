import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.March
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Gnomon
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
variable (M:Leaf R)(X:Coat T F)(H:Cash W x μ L Q o C T R) (a' : ℝ) (u:ConnectedActivityE6.Alphabet c f→ℝ)
    {q A B b e a χ' v d:ℝ}{j n:ℕ}{χ:Chi} (Ξ : Utopia H j v d r q χ)
open Itinerary Animals
lemma flare_erase (_hp :M.turn.badge S∈p):blaze (p.erase (M.turn.badge S))=blaze p:=by
  rw [← sparkPath]; ext i
  simp only [blaze,mem_toRight,mem_erase, and_iff_right_iff_imp]; cases M.turn <;> simp [sparkling]

lemma photo (i:ℕ) (ht:Ac.Spark H.supportP p)(hp:M.turn.badge S∈p):
    jewelDebt M Q L x * persona M H q Ξ.flair 0 i 0 p=(M.weight*∏ j∈p.erase (M.turn.badge S),Ξ.tag j)*Ξ.rad^(blaze p).card*(1+H.shapeW p)^i:=by
  let l:=M.turn.badge S; unfold persona; rw [if_pos ⟨(H.attends p).2 ht,hp⟩, ←mul_prod_erase _ _ hp, ← mul_assoc (jewelDebt ..), ← mul_assoc (jewelDebt ..), nose, ← (dew M H).2.2]
  rw [show (∏ i∈ p.erase l, needle M H q Ξ.flair i)= ∏ i∈p.erase l, Ξ.fare i from prod_congr rfl (fun i hi=> sleeve M H q _ i (ne_of_mem_erase hi)), Ξ.remixes, flare_erase M hp]; rw [← mul_assoc]
section
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {V:E→Config G c} {y:E} {f':E→Directions G f}{z':Air f G} {B':ℝ}{I:Finset (Bond f)}{k:ℕ}
lemma score (he : troupe T R Q.halo (radiusB x) p)(hA : M.turn.badge S∈p) (hX:X.x=x)(ht:X.width=o.K)(hF:X.χ=χ)(hu:X.manifest)(hv:Healthy (Pressure.temp X.x) (H.unionP p) X.V)(hV : Mode V y j v)(hr: Clutch X z' o.a R.beta d y j V f' (fun i=>course X A R.beta z' (V i))) (hB : 0≤B)
    (hC : Brush j M.weight (B*spanW T R X.B Q.halo (M.turn.badge S)) (fun t=> M.fond (vary X (V t)) o.a (f' t) (X.input (worldZ X R.beta z'))) y)
    (hT : Brush j 1 (B'*facescale I z'^k) (fun i=> scalp I X (V i) R.beta A z') y)(h':0≤B') :
    let K':=M.weight * ∏i∈p.erase (M.turn.badge S), Ξ.tag i
    Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator (fun z=> K'*(1+B'+2*(r+B))^j*(1+H.shapeW p)^j*facescale I z^(k*j)) z') 1
      (fun i=> M.chimes X p I (V i) A Q.table W o.a Q.halo z') y := by
  intro P'; have hD:=(hT.paints (acreage M X H Ξ he hA (own p) hX ht hF hu hv hV hr hB hC)).trim
  refine hD.climb ?_ le_rfl; by_cases hx:z'∈X.catastrophe (o.ξ/2) R.beta (blaze p)
  swap; · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,mul_zero,zero_mul]
  rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,one_mul]; change P'* _ ≤ _
  let f:=facescale I z'; let g := r+B; let D:=1+H.shapeW p; have ht':1≤g:=Ξ.active.trans (le_add_of_nonneg_right hB); have hF:1≤f:= (Flux.expenses ..).1; have hv':1≤D:=le_add_of_nonneg_right (H.positive_volume p)
  have h₁:1≤ f^k:= one_le_pow₀ hF; have h₂ : 1+(B'*f^k+g*(2*H.shapeW p))≤(1+B'+2*g)*D*f^k:=by
    have hc : f^k ≤ D*f^k:= le_mul_of_one_le_left (zero_le_one.trans h₁) hv'
    have hS:H.shapeW p ≤ D*f^k:= (show H.shapeW p ≤ D from le_add_of_nonneg_left zero_le_one).trans (le_mul_of_one_le_right (zero_le_one.trans hv') h₁)
    have ha:1≤ D*f^k:= h₁.trans hc
    -- nlinarith
    nlinarith only [mul_le_mul_of_nonneg_left hc h', mul_le_mul_of_nonneg_left hS (zero_le_one.trans ht'),ha]
  have he : 0 ≤ 1+(B'*f^k+g*(2*H.shapeW p)):=add_nonneg zero_le_one (add_nonneg hT.pos (mul_nonneg (zero_le_one.trans ht') (mul_nonneg zero_le_two (H.positive_volume p))))
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he h₂ j) (show 0≤P' from mul_nonneg M.profit (prod_nonneg fun _ _=>Ξ.tagged _))).trans_eq ?_
  rw [mul_pow,mul_pow,pow_mul]; unfold f g D; ring
end
structure Herd (H:Cash W x μ L Q o C T R)(Ξ:Utopia H j v d r q χ)(A B:ℝ)(l:ℕ):Prop where
  unmarked : FlareW H Ξ A B l
  nil (M:Leaf R) : ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (F : Forest S.ratio) (X : Coat T F)
    (U:E→ Config G c) (y:E) (p:Molecule S), X.χ=χ → X.manifest → X.x=x → X.width=o.K → Healthy (Pressure.temp X.x) (H.unionP p) X.V →
    troupe T R Q.halo (radiusB x) p → Ac.Spark H.supportP p → M.turn.badge S∈p → Mode U y j v → U y=X.V →
    let m:=(F.order G).prod X.dice
    ∃ f, Integrable f m ∧ (∫ y,f y ∂m) ≤ B*(jewelDebt M Q L x *persona M H q Ξ.flair 0 l 0 p) ∧
      ∀ z, Brush j (f z) 1 (fun t=> M.carat (edgesM S (H.unionP p) (radiusB x)) X (U t) A Q.table p W o.a Q.halo z) y

/-- Chosen post L. `FlareW` transport introduces NO final recognizer. -/
lemma timing (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W)
      (A f : ℝ), Canary G A f → ∀ (V : ℝ→ℝ), Rate G L (-(1/2)) V → (∀ᶠ x in atTop,0≤V x) →
    ∃ (C : ℝ) (q r p : ℝ→ℝ) (l:ℕ), Rate G L (-(1/2)) q ∧ Rate G L 0 p ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), S.patch=D → Stamp T →
      ∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R), 8*o.a* Pressure.fiery G x L ≤ A/2 ∧
      ∃ Ξ : Utopia H i (V x) (q x) (r x) C χ, Herd H Ξ A (|p x|) l := by
  obtain ⟨n,hN⟩:= Utopia.whittle P Q
  refine ⟨n,fun L hL D hD i χ W hW μ hm o A f hA V hV hv=>?_⟩
  obtain ⟨B,Z,hB,hZ,hX⟩:= Silica.clips hA P L i χ hV
  have hb:= hB.compare (v:=fun x=>|B x|) (Eventually.of_forall fun x=>(abs_abs _).le)
  obtain ⟨C,r,hC,hr,hχ⟩:= hN L hL D hD i χ W hW μ hm o V (fun x=>|B x|) hV hv hb
  obtain ⟨k,U,hU,hΓ⟩:= rump P L D hD o.K o.γ W o.a χ i hV hB hv hZ o.indexPay o.f A
  let s:= payE o.eta o.gap o.ample (tubularPrice G L)
  obtain ⟨F,K,hF,hΨ⟩:= walksW G L s (k*i*2)
  obtain ⟨J',hJ',hP',hX'⟩:= Clutch.central G L χ i hb (2*o.a)
  let e x:= 1+|F x|; let v x:=(1+|U x|+2*(r x+J' x))^i; let p x:=e x*v x
  have hh {V:ℝ→ℝ} (h:Rate G L 0 V):= h.compare (v:=fun x=> |V x|) (Eventually.of_forall fun z=> (abs_abs _).le)
  have he:= Rate.const (G:=G) (L:=L) 1
  refine ⟨C,(fun x=> |B x|),r,p,K+i,hb,by unfold p; simpa only [zero_mul,zero_add] using! ((he.add (hh hF)).mul (((he.add
    (hh hU)).add ((hr.add hJ').mul_left 2)).pow i)),?_⟩
  filter_upwards [hχ,hΓ,hX,hX', ((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hA.warm)] with
    x Hx h hx hW hp c f S T hS hT R C' H
  obtain ⟨Ξ⟩:= Hx _ _ S T hS hT R C' H
  have hθ:=H.laws.data; have hh:=hθ.funds; have hy := H.laws.intake
  have hp := (le_abs_self _).trans hp
  refine ⟨hp,Ξ,⟨⟨?_⟩,?_⟩⟩
  · intro E _ _ _ F' X Y y p' hζ hη ht hK hr hu he hf hy' m
    let I:= edgesM S (H.unionP p') (radiusB x); let J:= X.catastrophe (o.ξ/2) R.beta (blaze p')
    let f(z : Air f G):= facescale I z^(k*i); let S':=1+H.shapeW p'; let X' z:= J.indicator f z
    let a:=(∏ i∈p', Ξ.tag i)*v x*S'^i
    have hR:= hθ.localP F' X ht hK hη
    have hx':(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p')
    have ha:a≥0 := mul_nonneg (mul_nonneg (prod_nonneg fun _ _=> Ξ.tagged _) (pow_nonneg (by have hq:= Ξ.active; have h:= hP' x; positivity) _)) (pow_nonneg (zero_le_one.trans hx') _)
    have hQ:MeasurableSet J := Poll.sounded ..
    have hm:=globes I hR.sails (k*i*2)
    have hV := (globes I hR.sails (k*i)).1
    have hTax : Integrable (X': Air _ G→ℝ) X.dice := hV.indicator hQ
    have hE: ∫ x,X' x ∂X.dice ≤ (e x*S'^K)*Ξ.rad^(blaze p').card := by
      let i':ℝ:= I.card; let V:ℝ:= (lensS I G).card
      have hI: i'≤ S'*ballCost (radiusB x)* (Itinerary.density L:ℝ) := by
        have h:= crewsC H p'; rw [hh.length_eq] at h; apply h.trans; unfold S'; gcongr; linarith
      have he: 1≤e x:= le_add_of_nonneg_right (abs_nonneg _)
      have hV' : V=i'*Fintype.card G.ColorIndex := by simp [V,i',lensS]
      have hp := hm.2.trans (hΨ x i' V S' hx' (Nat.cast_nonneg _) hI hV')
      have hc : ∫ x,f x^2 ∂X.dice ≤ (e x*S'^K)^2 := by
        unfold f; simp_rw [← pow_mul]; apply hp.trans
        exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans hx') _)).trans
          (le_self_pow₀ (one_le_mul_of_one_le_of_one_le he (one_le_pow₀ hx')) (by omega))
      refine divideC _ f hV _ (by positivity) _ hQ (by rw [← pow_mul, Nat.mul_comm]; rw [pow_mul]; exact Ξ.ship _ X ht hK hζ hη (blaze p')) (pow_nonneg Ξ.awake _) ?_ hc
      unfold f; simp_rw [← pow_mul]; exact hm.1
    have hhP: Integrable (fun z:F'.Slice G × Air _ G=> a*X' z.snd) m := (hTax.const_mul a).comp_snd _
    refine ⟨fun z=> a*X' z.2,hhP,?_,?_⟩
    · rw [integral_prod _ hhP]
      dsimp only; simp_rw [integral_const_mul]; rw [ integral_const]; simp only [probReal_univ,one_smul]; rw [Utopia.meant,if_pos ((H.attends _).2 he),Ξ.remixes]
      apply (mul_le_mul_of_nonneg_left hE ha).trans
      unfold a S' p; rw [abs_of_nonneg (by unfold e v; have h:=Ξ.active; have hp:=hP' x; positivity : 0 ≤ e x*v x)]; apply le_of_eq; ring
    intro ⟨v',z⟩
    let X:= X.wrapY v'; have hZ:= hθ.localP F' X ht hK hη
    obtain ⟨hw,hD⟩:= hx _ _ S T F' X ht hh hζ R.beta hy.positive z E Y y hy' hf
    have hp := hD o.a (mul_pos o.large hZ.sails.room.fiery) (by unfold Coat.t; rw [show X.x=_ from ht,hh.length_eq]; exact hp)
    have hq := h c _ S T hh hS hθ.access E y Y F' X z R ht hK hζ hZ hy hf hp hw I
    apply (accent Ξ X hf _ hu hη hr ht hζ hK hp hq (abs_nonneg _)).climb _ le_rfl
    by_cases h:z∈J
    · change J.indicator _ z≤a * X' z; unfold a X'
      rw [Set.indicator_of_mem h,Set.indicator_of_mem h]
      have hq : (∏ i∈p', Ξ.tag i)*(1+|U x|+2*r x)^i≤(∏ i∈ p', Ξ.tag i)*v x:=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by have hv:=Ξ.active; positivity) (by have he':= hP' x; linarith) _ ) (prod_nonneg fun _ _=>Ξ.tagged _)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq (pow_nonneg (zero_le_one.trans hx') _)) (pow_nonneg (zero_le_one.trans (Flux.expenses ..).1) _)
    change J.indicator _ z≤a * X' z; unfold X'; rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,mul_zero]
  intro M E _ _ _ F' X Y y p' hζ hη ht hK hr hu he htM hf hy' m
  let I:= edgesM S (H.unionP p') (radiusB x); let J:= X.catastrophe (o.ξ/2) R.beta (blaze p')
  let f(z : Air f G):= facescale I z^(k*i); let S':=1+H.shapeW p'; let X' z:= J.indicator f z
  let Y' := p'.erase (M.turn.badge S)
  let a:=(M.weight*(∏ i∈Y', Ξ.tag i))*v x*S'^i
  have hR:= hθ.localP F' X ht hK hη
  have hx':(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p')
  have ha:a≥0 := mul_nonneg (mul_nonneg (mul_nonneg M.profit (prod_nonneg fun _ _=> Ξ.tagged _)) (pow_nonneg (by have hq:= Ξ.active; have h:= hP' x; positivity) _)) (pow_nonneg (zero_le_one.trans hx') _)
  have hQ:MeasurableSet J := Poll.sounded ..
  have hm:=globes I hR.sails (k*i*2)
  have hV := (globes I hR.sails (k*i)).1
  have hTax : Integrable (X': Air _ G→ℝ) X.dice := hV.indicator hQ
  have hE: ∫ x,X' x ∂X.dice ≤ (e x*S'^K)*Ξ.rad^(blaze p').card := by
    let i':ℝ:= I.card; let V:ℝ:= (lensS I G).card
    have hI: i'≤ S'*ballCost (radiusB x)* (Itinerary.density L:ℝ) := by
      have h:= crewsC H p'; rw [hh.length_eq] at h; apply h.trans; unfold S'; gcongr; linarith
    have he: 1≤e x:= le_add_of_nonneg_right (abs_nonneg _)
    have hV' : V=i'*Fintype.card G.ColorIndex := by simp [V,i',lensS]
    have hp := hm.2.trans (hΨ x i' V S' hx' (Nat.cast_nonneg _) hI hV')
    have hc : ∫ x,f x^2 ∂X.dice ≤ (e x*S'^K)^2 := by
      unfold f; simp_rw [← pow_mul]; apply hp.trans
      exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans hx') _)).trans
        (le_self_pow₀ (one_le_mul_of_one_le_of_one_le he (one_le_pow₀ hx')) (by omega))
    refine divideC _ f hV _ (by positivity) _ hQ (by rw [← pow_mul, Nat.mul_comm]; rw [pow_mul]; exact Ξ.ship _ X ht hK hζ hη (blaze p')) (pow_nonneg Ξ.awake _) ?_ hc
    unfold f; simp_rw [← pow_mul]; exact hm.1
  have hhP: Integrable (fun z:F'.Slice G × Air _ G=> a*X' z.snd) m := (hTax.const_mul a).comp_snd _
  refine ⟨fun z=> a*X' z.2,hhP,?_,?_⟩
  · rw [integral_prod _ hhP]
    dsimp only; simp_rw [integral_const_mul]; rw [ integral_const]; simp only [probReal_univ,one_smul]; 
    apply (mul_le_mul_of_nonneg_left hE ha).trans
    unfold a S' p; rw [abs_of_nonneg (by unfold e v; have h:=Ξ.active; have hq:=hP' x; positivity : 0 ≤ e x*v x)]; apply le_of_eq
    rw [photo M H Ξ (K+i) he htM]; unfold Y'; ring
  intro ⟨v',z⟩
  let X:= X.wrapY v'; have hZ:= hθ.localP F' X ht hK hη
  obtain ⟨hw,hD⟩:= hx _ _ S T F' X ht hh hζ R.beta hy.positive z E Y y hy' hf
  have hp := hD o.a (mul_pos o.large hZ.sails.room.fiery) (by unfold Coat.t; rw [show X.x=_ from ht,hh.length_eq]; exact hp)
  have hq := h c _ S T hh hS hθ.access E y Y F' X z R ht hK hζ hZ hy hf hp hw I
  have hA': areas R T 0 X.B (M.turn.badge S) ⊆ H.supportP (M.turn.badge S):=by
    change _⊆ areas R T Q.halo (radiusB x) _
    simp_rw [M.turn.badge_area]; exact Corona.halo_mono (by simp) (Subset.refl _)
  have he' :0<o.a*X.t:= hp.pulse
  have hM:= hW c _ S T F' X ht hζ hh.length_eq (show 0<(2*o.a)*X.t from by rw [mul_assoc]; positivity) E z o.a R.beta y Y _ _ hp _ _ hA'
  have hR' : Brush i M.weight (J' x*spanW T R X.B Q.halo (M.turn.badge S)) (fun x=> M.fond (vary X (Y x)) o.a (steer X A (worldZ X R.beta z) (Y x)) (X.input (worldZ X R.beta z))) y:= by
    have hh := (Brush.certified (d:=0) (x:=y) (k:=i) (le_refl 0) (M.ingredient (X.input (worldZ X R.beta z)))|>.climb (M.earn _) (le_refl _)).paints hM
    rw [mul_one,zero_add] at hh; apply hh.climb le_rfl
    apply mul_le_mul_of_nonneg_left _ (hP' _); rw [← sparkPath]
    change (coverNumber X.B (footprints T R _ (radiusB x) _):ℝ) ≤ 1+(_ + _)
    rw [← show X.B=radiusB x from congr_arg radiusB ht]
    apply le_trans _ (le_add_of_nonneg_left zero_le_one); exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  apply (score (z':=z) M X H Ξ hu htM ht hK hζ (show X.manifest from hη) hr hf hp (hP' _) hR' hq (abs_nonneg _)).climb _ le_rfl
  by_cases h:z∈J
  · change J.indicator _ z≤ a * X' z; unfold a X'; rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  change J.indicator _ z≤a * X' z; unfold X'; rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,mul_zero]

end YM.PhysicalNext.Repeat.Daisy
