import YM.RemainderComparison.Cascade.Environment
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Mettle

/-!
# High grade budget; real and post-L

Team of any size, reflecting actual mark addresses and forced replacements.
For candidate high pruning (complement via `heavy`); use different epoch
of the same Input.Price to deal with inherited remainders. Forges from
`Patrons` after purchasing `twinkles`. Triumphed includes the companion
unmarked captain's supplies as consumers of the same cash (no postulating
any derivative estimates for inserted masks).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cascade
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R)(X:Coat T F)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n:ℕ}{χ:Chi} (Ξ : Utopia H j v d r q χ)

def Seminar (M:Team R) (H:Cash W x μ L Q o C T R) (p:Molecule S) (j:ℕ) (A:ℝ) (χ:Chi) (B v : ℝ):Prop:=
   ∀ (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (F : Forest S.ratio) (X : Coat T F)
    (U:E→ Config G c) (y:E), X.χ=χ → X.manifest → X.x=x → X.width=o.K → Healthy (Pressure.temp X.x) (H.unionP p) X.V →
    troupe T R Q.halo (radiusB x) p → Ac.Spark H.supportP p → M.signs S⊆p → Mode U y j v → U y=X.V →
    let m:=(F.order G).prod X.dice
    ∃ f, Integrable f m ∧ (∫ y,f y ∂m) ≤ B ∧
      ∀ z, Brush j (f z) 1 (fun t=> M.carat (edgesM S (H.unionP p) (radiusB x)) X (U t) A Q.table p W o.a Q.halo z) y

def Heroes (H:Cash W x μ L Q o C T R)(Ξ:Utopia H j v d r q χ)(A B:ℝ)(k:ℕ):Prop:=
   ∀ (M:Team R) (p:Molecule S), Seminar M H p j A χ ((B*M.weight)*(∏i∈p\M.signs S,Ξ.fare i)*(1+H.shapeW p)^k) v

lemma Heroes.unmarked (h : Heroes H Ξ A B n) : FlareW H Ξ A B n:=by
   constructor; intro E _ _ _ F X U y p hχ hv hx hw hP hT hS hQ hh m
   let M : Team R := ⟨∅,fun _ h=> by simp at h⟩
   have he : M.signs S=∅:=by simp [Team.signs,M]
   obtain ⟨f,hf,hA,hp⟩:=h M p E F X U y hχ hv hx hw hP hT hS (he ▸ empty_subset _) hQ hh
   refine ⟨f,hf,?_,fun x=>?_⟩
   · rw [Utopia.meant,if_pos ((H.attends p).2 hS)]
     refine hA.trans_eq ?_; rw [he,show M.weight=1 from prod_empty]; have h: p\(∅:Finset _) = p:=sdiff_empty
     rw [h]; ring
   apply (hp x).shimmy; filter_upwards with i; unfold rhythm recoil Team.carat Team.chimes Team.floret; rw [he,if_pos (empty_subset _)]
   have h: p\(∅:Finset _)=p:=sdiff_empty
   apply congrArg; rw [h, show ∀ (X:Coat T F) a u, M.paidU X a u=1 from fun _ _ _=> prod_empty]; simp

abbrev Lower {P:Teller G} (Q: ConnectedActivityE6.Target G P) := ∀ {c f:Side} {S:StepData c f} {T:Tube G S} {R:Rep G f} {L:Side}
      {W x μ C:ℝ} {o:ConnectedActivityE6.Target.Order G W}(H:Cash W x μ L Q o C T R) {j:ℕ} {u v A r:ℝ} {χ:Chi}, Utopia H j u v A r χ → Prop

abbrev Calls {P:Teller G} (Q: ConnectedActivityE6.Target G P) (w':Lower Q) (n:ℕ):Prop := ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0 < W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W) (v w : ℝ→ℝ),
    Rate G L (-(1/2)) v → (∀ᶠ x in atTop,0≤v x) → Rate G L (-(1/2)) w → ∃ (C':ℝ) (r:ℝ→ℝ), 0≤C' ∧ Rate G L 0 r ∧
    ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), S.patch=D → Stamp T → ∀ (R:Rep G f) (C:ℝ) (H:Cash W x μ L Q o C T R),
      ∃ Ξ : Utopia H i (v x) (w x) (r x) C' χ, w' H Ξ
lemma shuttledFor (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) (w': Lower Q) (n:ℕ) (hN:Calls Q @w' n): ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W)
      (A f₀ : ℝ), Canary G A f₀ → ∀ (V : ℝ→ℝ), Rate G L (-(1/2)) V → (∀ᶠ x in atTop,0≤V x) →
    ∃ (C : ℝ) (q r p : ℝ→ℝ) (l:ℕ), 0 ≤ C ∧ Rate G L (-(1/2)) q ∧ Rate G L 0 p ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), S.patch=D → Stamp T →
      ∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R), ∃ Ξ : Utopia H i (V x) (q x) (r x) C χ, w' H Ξ ∧ Heroes H Ξ A (|p x|) l ∧ Oboe H i (V x) (|p x|) l A f₀ Ξ := by
  intro L hL D hD i χ W hW μ hm o A f hA V hV hv
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
  refine ⟨C,(fun x=> |B x|),r,p,K+i,hC,hb,by unfold p; simpa only [zero_mul,zero_add] using! ((he.add (hh hF)).mul (((he.add
    (hh hU)).add ((hr.add hJ').mul_left 2)).pow i)),?_⟩
  filter_upwards [hχ,hΓ,hX,hX', ((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hA.warm), Glass.portal P D L hD i χ hV hv o.K o.γ W o.indexPay o.f] with
    x Hx h hx hW hp hPo c f S T hS hT R C' H
  obtain ⟨Ξ,hΞ⟩:= Hx _ _ S T hS hT R C' H
  have hθ:=H.laws.data; have hh:=hθ.funds; have hy := H.laws.intake
  have hp := (le_abs_self _).trans hp
  suffices hf: Heroes H Ξ A |p x| (K+i) from ⟨Ξ,hΞ,hf, hA,hp,hf.unmarked H Ξ,fun F X hX hF hv hm=> hPo c f S T hS hθ.funds hθ.access F X hv hF hX (hθ.localP F X hX hv hm)⟩
  intro M p' E _ _ _ F' X Y y hζ hη ht hK hr hu he htM hf hy' m
  have hk:= keeps_blaze (S:=S) (p:=p') M
  have hhP := hP' x
  have hS': r x≥1:=Ξ.active
  unfold p e v; rw [abs_of_nonneg (by positivity), Ξ.remixes,hk]
  -- align multiplies
  obtain ⟨g,hg,hE,hq⟩:= patrons M X H Ξ ht hζ hK hη p' htM hu (abs_nonneg _) (k:=k) (l:=K) (T':=|F x|) (show Prints _ _ _ _ from hΨ x) hhP (abs_nonneg (U x)) (zero_le_one.trans hS') (fun j _=>Ξ.tagged j) hf (A:=A) (fun U z=> by
    let X:= X.wrapY U; have hZ:= hθ.localP F' X ht hK hη
    obtain ⟨hw,hD⟩:= hx _ _ S T F' X ht hh hζ R.beta hy.positive z E Y y hy' hf
    have hp := hD o.a (mul_pos o.large hZ.sails.room.fiery) (by unfold Coat.t; rw [show X.x=_ from ht,hh.length_eq]; exact hp)
    have he' :0<o.a*X.t:= hp.pulse
    refine ⟨_, hp, h c _ S T hh hS hθ.access E y Y F' X z R ht hK hζ hZ hy hf hp hw _, fun m _=>leaf_bright X H m ht hp hhP (hW c _ S T F' X ht hζ hh.length_eq (show 0<(2*o.a)*X.t from by rw [mul_assoc]; positivity) E z o.a R.beta y Y _ _ hp), fun j hj=> ?_⟩
    have he':j∈p':=(Finset.mem_sdiff.mp hj).1
    have hy := Ξ.stream E _ X Y _ _ y z ht hK hζ hη hf hp (own p') j (Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP he') hr)
    unfold Utopia.tag; rw [← show X.B=radiusB x from congr_arg radiusB ht]; exact hy)
  refine ⟨g,hg,hE.trans_eq ?_,hq⟩; ring

lemma triumphedFor (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) (w': Lower Q) (n:ℕ) (hN:Calls Q @w' n): ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W),
    ∃ (A a C : ℝ) (d v t r B q : ℝ→ℝ) (k:ℕ), 0 ≤ C ∧ Rate G L 0 B ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D→Stamp T→∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R),
        ∃ N: Captain H i C (d x) (v x) (t x) A a (r x) (B x) (q x) k χ, w' H N.conduit ∧ Heroes H N.conduit A (B x) k := by
  intro L hL D hD i χ W hW μ hm o
  obtain ⟨A,a,hA⟩:= Eider.weave G; obtain ⟨Z,hZ,hq⟩:= March.oar G i
  let t x := 2*Pressure.fiery G x L
  have he : Rate G L (-(1/2)) t:= Rate.flame.mul_left 2
  let v x := ((i:ℝ)+1)*Z*t x
  have hh : Rate G L (-(1/2)) v:= he.mul_left _
  have hp : ∀ᶠ x : ℝ in atTop, 0<t x := ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x h=> mul_pos (by norm_num) (Work.E09.temp_pos h)
  obtain ⟨C,d,r,B,k,hC,-,hB,ht⟩:= shuttledFor P Q @w' n hN L hL D hD i χ W hW μ hm o A a hA v hh (hp.mono (fun x hh=> by unfold v; positivity))
  let B' x:= |B x|; have hb' : Rate G L 0 B':= hB.compare (Eventually.of_forall fun x=> by simp [B'])
  refine ⟨A,a,C,d,v,t,r,B',fun x=> Z*t x,k,hC,hb',?_⟩
  filter_upwards [hp,ht] with x hx hD' c f S T hS hT R B' H
  obtain ⟨Ξ,hΞ,hF,hF'⟩:=hD' c f S T hS hT R _ H; have hZ := hZ; have h:= H.laws.data
  exact ⟨⟨Ξ,hF',mul_nonneg hZ.le hx.le,hx.le,(by have he:= h.room.temperatures; rw [h.funds.length_eq] at he; exact he),
    (by unfold v; positivity),abs_nonneg _, ⟨fun c=> hq c _ hx.le⟩,(by unfold v; nlinarith [mul_nonneg hZ.le hx.le])⟩,hΞ,hF⟩

abbrev simpleW {P:Teller G} (Q: ConnectedActivityE6.Target G P): Lower Q:= fun {_ _ _ _ _ _ _ _ _ _ _} H {_ _ _ _ _ _} Ξ=> Silica.Heavy (H:=H) Ξ

lemma shuttled (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W)
      (A f₀ : ℝ), Canary G A f₀ → ∀ (V : ℝ→ℝ), Rate G L (-(1/2)) V → (∀ᶠ x in atTop,0≤V x) →
    ∃ (C : ℝ) (q r p : ℝ→ℝ) (l:ℕ), 0 ≤ C ∧ Rate G L (-(1/2)) q ∧ Rate G L 0 p ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), S.patch=D → Stamp T →
      ∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R), ∃ Ξ : Utopia H i (V x) (q x) (r x) C χ, Heavy Ξ ∧ Heroes H Ξ A (|p x|) l ∧ Oboe H i (V x) (|p x|) l A f₀ Ξ := by
    obtain ⟨n,hN⟩:= Utopia.twinkles P Q
    exact ⟨n,shuttledFor P Q (simpleW Q) n hN⟩

lemma triumphed (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W),
    ∃ (A a C : ℝ) (d v t r B q : ℝ→ℝ) (k:ℕ), 0 ≤ C ∧ Rate G L 0 B ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D→Stamp T→∀ (R:Rep G f) (C':ℝ) (H:Cash W x μ L Q o C' T R),
        ∃ N: Captain H i C (d x) (v x) (t x) A a (r x) (B x) (q x) k χ, Heavy N.conduit ∧ Heroes H N.conduit A (B x) k := by
    obtain ⟨n,hN⟩:= Utopia.twinkles P Q
    exact ⟨n,triumphedFor P Q (simpleW Q) n hN⟩

end YM.RemainderComparison.Cascade
