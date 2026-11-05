import YM.RemainderComparison.Halo.Graft
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Halo
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Raw Itinerary Opacity Cascade Graft March Captain
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}
lemma seeds (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P):∃ l:ℕ, ∀ (L:Side), l≤L.val → ∀ (D:Patch), D.Branches P.bind G →
   ∀ (j:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o: ConnectedActivityE6.Target.Order G W),
   ∃ (A a C C':ℝ)(d v t B r T' p w:ℝ→ℝ)(k : ℕ), 0≤ C∧0≤C'∧ Gear G L (-(1/2)) d ∧ Gear G L (-(1/2)) v ∧ Rate G L 0 B ∧ Rate G L 0 r ∧ Rate G L 0 T' ∧ Reserve G L p ∧ (∀ z, 0≤T' z∧0≤p z)∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D→Stamp T→∀ (R:Rep G f) (C'':ℝ) (H:Cash W x μ L Q o C'' T R),
      ∃ N:Captain H j C (d x) (v x) (t x) A a (r x) (B x) (w x) k χ, Heavy N.conduit ∧ Heroes H N.conduit A (B x) k ∧ Quarry H N.conduit A C' (T' x) (p x) k := by
   obtain ⟨l,hℓ⟩:=Utopia.twinkles P Q
   refine ⟨l,fun L hL D hD i χ W hW μ hm o=>?_⟩
   obtain ⟨Z,hZ,hq⟩:= March.oar G i; obtain ⟨A,f,hA⟩:= Eider.weave G
   let t x:= 2*Pressure.fiery G x L; let V x:=((i:ℝ)+1)*Z*t x
   have he : Gear G L (-(1/2)) t:= Gear.flame.mul_left _
   have hV : Gear G L (-(1/2)) V:= he.mul_left _
   have ha : ∀ᶠ x:ℝ in atTop,0<t x:= Delay.shift_pos G L|>.mono fun x hx=>mul_pos (by norm_num) (Work.E09.temp_pos hx)
   have hv : ∀ᶠ x in atTop,0≤V x:=ha.mono fun x hx=>by unfold V; positivity
   obtain ⟨C',hC',hC₀⟩:= Halo.pending G i
   obtain ⟨B,F,hB,hF,hX⟩:= stripped hA P L i χ hV
   obtain ⟨C,r,hC,hr,hχ⟩:= hℓ L hL D hD i χ W hW μ hm o V (fun x=> |B x|) hV.rate hv hB.absG.rate
   obtain ⟨k,U,hU,hΓ⟩:= scoreP P L D hD o.K o.γ W o.a χ i hV hB hF o.indexPay o.f A
   obtain ⟨F',K,hF',hΨ⟩:= walkersP G L (payE o.eta o.gap o.ample (tubularPrice G L)) (k*i*2)
   obtain ⟨J,hJ,hJ',hp⟩:= canopyG G L χ hB.absG i (2*o.a)
   let e (f:ℝ→ℝ) (x:ℝ):=Graft.charge i |F' x| |U x| (f x); let Y:=e (fun x=> r x+J x); let E:=e fun x=> r x+J x+J x; let V':= e fun x=> J x+J x
   have hh {f : ℝ→ℝ} (h : Reserve G L f):= h.absolute
   have h₁ (F:ℝ→ℝ)(h:Rate G L 0 F): Rate G L 0 (e F) := by
      have H:= Rate.const (G:=G) (L:=L) (1:ℝ)
      unfold e Graft.charge; simpa only [zero_mul,zero_add] using! ((H.add (hh hF').rate).mul (((H.add (hh hU).rate).add (h.mul_left 2)).pow _))
   have hE : Reserve G L V':= ((Reserve.const _).add (hh hF')).mul ((((Reserve.const _).add (hh hU)).add (Reserve.mul (Reserve.const _) (hJ.add hJ))).pow _)
   refine ⟨A,f,C,C',(fun x=>|B x|),V,t,Y,r,(fun x=>|E x|),(fun x=>|V' x|), fun x=>Z*t x,K+i,hC,hC',hB.absG,hV,h₁ _ (hr.add hJ.rate), hr,
     (h₁ _ ((hr.add hJ.rate).add hJ.rate)).compare (Eventually.of_forall fun x=>by simp [E]), hh hE,fun z=> ⟨abs_nonneg _,abs_nonneg _⟩,?_⟩
   filter_upwards [hχ,hΓ,hX, ((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hA.warm), Glass.portal P D L hD i χ hV.rate hv o.K o.γ W o.indexPay o.f, ha] with
    x Hx h hx hA' hPo ht c f S T hS hT R C'' H
   obtain ⟨Ξ,hΞ⟩:= Hx _ _ S T hS hT R C'' H
   have hθ:=H.laws.data; have hh:= hθ.funds; have hy:= H.laws.intake; have hy':= (le_abs_self _).trans hA'
   have hf : Graft H Ξ A |F' x| (J x) |U x| k K:=by
      refine ⟨hJ' x,abs_nonneg _,hΨ x,abs_nonneg _,?_⟩
      intro E _ _ _ F X Z z _ hζ hη he hP hQ hf z'; have hZ:= hθ.localP F X he hP hη
      obtain ⟨hw,hD⟩:= hx _ _ S T F X he hh hζ R.beta hy.positive z' E Z z hf hQ
      have hp' := hD o.a (mul_pos o.large hZ.sails.room.fiery) (by unfold Coat.t; rw [show X.x=_ from he,hh.length_eq]; exact hy')
      have he' :0<o.a*X.t:= hp'.pulse
      exact ⟨_, hp', h c _ S T hh hS hθ.access E z Z F X z' R he hP hζ hZ hy hQ hp' hw,
        hp x c _ S T F X he hζ hh.length_eq (show 0<(2*o.a)*X.t from by rw [mul_assoc]; positivity) E z' o.a R.beta z Z _ _ hp'⟩
   have hg: Heroes H Ξ A (Y x) (K+i):= hf.legacy H Ξ
   have hb:= hf.bark; have hs':0≤r x:=zero_le_one.trans Ξ.active
   have he':0 ≤ Y x:= zero_le_one.trans (hf.grants H Ξ (show 0 ≤ r x+J x from by positivity))
   refine ⟨⟨Ξ,⟨hA,hy', hg.unmarked H Ξ,fun F X hX hF hv hm=> hPo c f S T hS hh hθ.access F X hv hF hX (hθ.localP F X hX hv hm)⟩,mul_nonneg hZ.le ht.le,ht.le,(by have he:= hθ.room.temperatures; rw [hh.length_eq] at he; exact he), (by unfold V; positivity),he',⟨fun c=>hq c _ ht.le⟩,(by unfold V; nlinarith [mul_nonneg hZ.le ht.le])⟩,hΞ,hg,?_⟩
   change Quarry H Ξ _ _ _ _ _
   rw [abs_of_nonneg (show 0 ≤ V' x from zero_le_one.trans (hf.grants H Ξ (show 0≤ J x+J x from by positivity)))]
   exact hf.acorn H Ξ hC' (le_abs_self (E x)) (fun F E _ _ X hX f' V U g y E' w e hP hh he=> hC₀ c f L S T F P W x μ C'' R Q o H X E' w e hh he hX E f' V U g y (J x) hb hP)
end YM.RemainderComparison.Halo
