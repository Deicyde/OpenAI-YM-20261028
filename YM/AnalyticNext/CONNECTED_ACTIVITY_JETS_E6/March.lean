import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Cirrus
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Lambent
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.LogosG
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Splay

/-! # Release input from Constructor at coarse Phi. These budgets hold
 simultaneously on all V,Y,F,etc. Integral Kernel must be paid in P.interpolation.
 Purchase does not supply analyzed cards: until remaining Meristem.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {H : Cash W s μ L Q o C T R}
variable {Ξ : Utopia H j v d r C' χ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config G c} {x : E} {w:E → Directions G f}
variable {z : Air f G}

-- Given proper Skull growth on nearby support chart,
-- the BP(Orbit) of recoil.
lemma accent (Ξ : Utopia H j v d r C' χ) (X : Coat T F) (hp : Mode V x j v) (p : Molecule S)
    (he : troupe T R Q.halo (radiusB s) p) (hM : X.manifest) (hv : Healthy (Pressure.temp X.x) (H.unionP p) X.V) (hX : X.x=s)
    (hF : X.χ=χ) (hK : X.width=o.K) (h : Clutch X z o.a R.beta d x j V w (fun v=>course X A R.beta z (V v)))
    (hT : Brush j 1 (B*facescale I z^k) (fun y=>scalp I X (V y) R.beta A z) x) (hB : 0≤ B) :
    let P' :=(∏ i∈ p,Ξ.tag i); let W':= (1+H.shapeW p)
    Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator (fun z=> P'*(1+B+2*r)^j*W'^j*facescale I z^(k*j)) z) 1
      (fun i=> recoil I X (V i) A Q.table p R W o.a Q.halo z) x := by
  intro P W'; have hD := (hT.paints (Ξ.acreage p (own p) he hX hF hM hK hv hp h)).trim
  refine hD.climb ?_ le_rfl; by_cases hu:z∈X.catastrophe (o.ξ/2) R.beta (blaze p)
  · rw [Set.indicator_of_mem hu,Set.indicator_of_mem hu,one_mul]; change P*_ ≤ _
    have hh :1≤ W':= le_add_of_nonneg_right (H.positive_volume p)
    have hy:r≥1:=Ξ.active; let x:=facescale I z; have hx : 1≤x:= (expenses ..).1
    have hv : 1+(B*facescale I z^k+r*(2*H.shapeW p)) ≤ (1+B+2*r)*W'*facescale I z^k := by
      have he := one_le_pow₀ (n:=k) hx; have h0:0≤2*r:=by positivity
      calc
        _ ≤ W'*x^k + (B*(W'*x^k)+2*r*(W'*x^k)) := by
          have hM : x^k≤ W'*x^k:= le_mul_of_one_le_left (by positivity) hh
          have ht : H.shapeW p ≤ W'*x^k := le_trans (show H.shapeW p ≤ W' from le_add_of_nonneg_left zero_le_one)
            (le_mul_of_one_le_right (zero_le_one.trans hh) he)
          unfold x at *; nlinarith only [ht,hx,hM,hB,hy,mul_le_mul_of_nonneg_left ht h0,one_le_mul_of_one_le_of_one_le hh he]
        _ = _ := by unfold x; ring
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ hv j) (show 0≤P from prod_nonneg fun i _=> Ξ.tagged i)).trans_eq
    swap
    · exact add_nonneg zero_le_one (add_nonneg hT.pos (mul_nonneg (zero_le_one.trans hy) (mul_nonneg (by norm_num) (H.positive_volume p))))
    rw [mul_pow,mul_pow,pow_mul]; ring
  rw [Set.indicator_of_notMem hu,Set.indicator_of_notMem hu, mul_zero,zero_mul]

-- Given polynomial support allowance, `integrable p` price on the old theta.
structure FlareW (H : Cash W s μ L Q o C T R) (Ξ : Utopia H j v d r C' χ) (A B : ℝ) (l : ℕ) : Prop where
  tents : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F : Forest S.ratio) (X : Coat T F)
    (U:E→ Config G c) (y:E) (p:Molecule S), X.χ=χ → X.manifest → X.x=s → X.width=o.K → Healthy (Pressure.temp X.x) (H.unionP p) X.V →
    troupe T R Q.halo (radiusB s) p → Ac.Spark H.supportP p → Mode U y j v → U y=X.V →
    let m:=(F.order G).prod X.dice
    ∃ f, Integrable f m ∧ (∫ x,f x ∂m) ≤ B*Ξ.meant p l ∧
      ∀ x, Brush j (f x) 1 (fun t=> rhythm (edgesM S (H.unionP p) (radiusB s)) X (U t) A Q.table p R W o.a Q.halo x) y

/-- Chosen post L. `FlareW` transport introduces NO final recognizer. -/
lemma launch (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W)
      (A f : ℝ), Canary G A f → ∀ (V : ℝ→ℝ), Rate G L (-(1/2)) V → (∀ᶠ x in atTop,0≤V x) →
    ∃ (C : ℝ) (q r p : ℝ→ℝ) (l:ℕ), Rate G L (-(1/2)) q ∧ Rate G L 0 p ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), S.patch=D → Stamp T →
      ∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R), 8*o.a* Pressure.fiery G x L ≤ A/2 ∧
      ∃ Ξ : Utopia H i (V x) (q x) (r x) C χ, FlareW H Ξ A (|p x|) l := by
  obtain ⟨n,hN⟩:= Utopia.whittle P Q
  refine ⟨n,fun L hL D hD i χ W hW μ hm o A f hA V hV hv=>?_⟩
  obtain ⟨B,Z,hB,hZ,hX⟩:= Silica.clips hA P L i χ hV
  have hb:= hB.compare (v:=fun x=>|B x|) (Eventually.of_forall fun x=>(abs_abs _).le)
  obtain ⟨C,r,hC,hr,hχ⟩:= hN L hL D hD i χ W hW μ hm o V (fun x=>|B x|) hV hv hb
  obtain ⟨k,U,hU,hΓ⟩:= rump P L D hD o.K o.γ W o.a χ i hV hB hv hZ o.indexPay o.f A
  let s:= payE o.eta o.gap o.ample (tubularPrice G L)
  obtain ⟨F,K,hF,hΨ⟩:= walksW G L s (k*i*2)
  let e x:= 1+|F x|; let v x:=(1+|U x|+2*r x)^i; let p x:=e x*v x
  have hh {V:ℝ→ℝ} (h:Rate G L 0 V):= h.compare (v:=fun x=> |V x|) (Eventually.of_forall fun z=> (abs_abs _).le)
  have he:= Rate.const (G:=G) (L:=L) 1
  refine ⟨C,(fun x=> |B x|),r,p,K+i,hb,by unfold p; simpa only [zero_mul,zero_add] using! ((he.add (hh hF)).mul (((he.add
    (hh hU)).add (hr.mul_left 2)).pow i)),?_⟩
  filter_upwards [hχ,hΓ,hX, ((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hA.warm)] with
    x Hx h hx hp c f S T hS hT R C' H
  obtain ⟨Ξ⟩:= Hx _ _ S T hS hT R C' H
  have hθ:=H.laws.data; have hh:=hθ.funds; have hy := H.laws.intake
  have hp := (le_abs_self _).trans hp
  refine ⟨hp,Ξ,⟨?_⟩⟩
  intro E _ _ _ F' X Y y p' hζ hM ht hK hr hu he hf hy' m
  let I:= edgesM S (H.unionP p') (radiusB x); let J:= X.catastrophe (o.ξ/2) R.beta (blaze p')
  let f(z : Air f G):= facescale I z^(k*i); let S':=1+H.shapeW p'; let X' z:= J.indicator f z
  let a:=(∏ i∈p', Ξ.tag i)*v x*S'^i
  have hR:= hθ.localP F' X ht hK hM
  have hx':(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p')
  have ha:a≥0 := mul_nonneg (mul_nonneg (prod_nonneg fun _ _=> Ξ.tagged _) (pow_nonneg (by have hq:= Ξ.active; positivity) _)) (pow_nonneg (zero_le_one.trans hx') _)
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
    refine divideC _ f hV _ (by positivity) _ hQ (by rw [← pow_mul, Nat.mul_comm]; rw [pow_mul]; exact Ξ.ship _ X ht hK hζ hM (blaze p')) (pow_nonneg Ξ.awake _) ?_ hc
    unfold f; simp_rw [← pow_mul]; exact hm.1
  have hhP: Integrable (fun z:F'.Slice G × Air _ G=> a*X' z.snd) m := (hTax.const_mul a).comp_snd _
  refine ⟨fun z=> a*X' z.2,hhP,?_,?_⟩
  · rw [integral_prod _ hhP]
    dsimp only; simp_rw [integral_const_mul]; rw [ integral_const]; simp only [probReal_univ,one_smul]; rw [Utopia.meant,if_pos ((H.attends _).2 he),Ξ.remixes]
    apply (mul_le_mul_of_nonneg_left hE ha).trans
    unfold a S' p; rw [abs_of_nonneg (by unfold e v; have h:=Ξ.active; positivity : 0 ≤ e x*v x)]; apply le_of_eq; ring
  intro ⟨v',z⟩
  let X:= X.wrapY v'; have hZ:= hθ.localP F' X ht hK hM
  obtain ⟨hw,hD⟩:= hx _ _ S T F' X ht hh hζ R.beta hy.positive z E Y y hy' hf
  have hp := hD o.a (mul_pos o.large hZ.sails.room.fiery) (by unfold Coat.t; rw [show X.x=_ from ht,hh.length_eq]; exact hp)
  have hq := h c _ S T hh hS hθ.access E y Y F' X z R ht hK hζ hZ hy hf hp hw I
  apply (accent Ξ X hf _ hu hM hr ht hζ hK hp hq (abs_nonneg _)).climb _ le_rfl
  by_cases h:z∈J
  · change J.indicator _ z≤ a * X' z; unfold a X'; rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  change J.indicator _ z≤a * X' z; unfold X'; rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,mul_zero]
end YM.ConnectedActivityE6.Blaze.Flux
