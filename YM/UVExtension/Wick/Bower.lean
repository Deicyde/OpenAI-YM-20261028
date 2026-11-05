import YM.UVExtension.Wick.Aurora

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
variable {x y γ W μ δ e b B C u D d r q' A v' g w : ℝ} {K:ℕ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
variable {χ : Chi} {j i : ℕ}

/-- ONE choice, including stalls for all parameters from a Molecule. Paid after L. -/
structure Bower (Q : ConnectedActivityE6.Target G P) (o : Target.Order G W) (L : Side) (D:Patch) (μ : ℝ) (χ: Chi) (A b x : ℝ) (j k:ℕ)
    (u B C r d n : ℝ) : Prop where
    roof : 0≤B
    bay : Canary G A b
    foot : 8*o.a* Pressure.fiery G x L ≤ A/2
    granted : ∀ (c f:Side) (S:StepData c f) (T:Tube G S) (R:Rep G f) (v:ℝ) (H:Cash W x μ L Q o v T R), Stamp T→ S.patch=D→
      Nonempty (Utopia H j u d r C χ) ∧ ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
        (Y:E→ Config G c) (F:Forest S.ratio) (X:Coat T F) (z:E), X.x=x → X.χ=χ → X.width=o.K → X.manifest →
        Y z=X.V → Mode Y z j u → Glass P X Y z j W ∧ ∀ w:Air f G, let u:= worldZ X R.beta w; let F' x:= steer X A u (Y x)
        Clutch X w o.a R.beta d z j Y F' (fun x=>course X A R.beta w (Y x)) ∧
        (∀ I:Finset (Bond f),Brush j 1 (B*facescale I w^k) (fun i=> scalp I X (Y i) R.beta A w) z) ∧
        ∀ (T:Stores S), ¬ (fun i=> X.enforce o.a (F' i) (X.plaza (T.dome (304*X.B))))=ᶠ[𝓝 z] (fun _=>0) →
          ∀ (U:Config G f), let f i:= plumeLog (vary X (Y i)) o.a R Q.table (F' i) U T; Brush j (n*T.shares) 1 (fun i=> f i-f z) z

lemma pales (Q: ConnectedActivityE6.Target G P) : ∃ m:ℕ,∀ (L:Side),m ≤ L.val → ∀ D:Patch,D.Branches P.bind G → ∀ (j:ℕ) (χ:Chi) (W μ:ℝ),0<W→0<μ→ ∀ o:Target.Order G W,
    ∀ (A b:ℝ), Canary G A b → ∀ u:ℝ→ℝ, Rate G L (-(1/2)) u → (∀ᶠ i in atTop,0≤u i) → ∃ (k:ℕ) (C:ℝ) (B r d n:ℝ→ℝ),
      0≤ C ∧ Rate G L 0 B ∧ Rate G L 0 r ∧ Rate G L 1 n ∧ ∀ᶠ x in atTop, 0≤ n x ∧ Bower Q o L D μ χ A b x j k (u x) (B x) C (r x) (d x) (n x) := by
  obtain ⟨N,hN⟩:= Utopia.whittle P Q; refine ⟨N,fun L hL D hD i χ W μ hW hm o A f hA V hV hv=>?_⟩
  obtain ⟨B,Z,hB,hZ,hX⟩:= Silica.clips hA P L i χ hV
  have hb:= hB.compare (v:=fun x=>|B x|) (Eventually.of_forall fun x=>(abs_abs _).le)
  obtain ⟨C,r,hC,hr,hχ⟩:= hN L hL D hD i χ W hW μ hm o V (fun x=>|B x|) hV hv hb
  obtain ⟨k,U,hU,hΓ⟩:= rump P L D hD o.K o.γ W o.a χ i hV hB hv hZ o.indexPay o.f A
  obtain ⟨E,hE,hF⟩:= Clutch.stilly P L D hD o.K o.γ W o.a χ i Q.table_exists hV hv hb o.indexPay o.f
  have he:= Glass.portal P D L hD i χ hV hv o.K o.γ W o.indexPay o.f
  have hh {u:ℝ→ℝ} {t} (h:Rate G L t u): Rate G L t fun x=>|u x|:=h.compare (Eventually.of_forall fun i=> (abs_abs _).le)
  refine ⟨k,C,_,r,(fun x=>|B x|),_,hC,hh hU,hr,hh hE,?_⟩
  filter_upwards [hχ,hΓ,hX, ((Rate.flame (G:=G) (L:=L)).mul_left (8*o.a)).below (by norm_num) _ (half_pos hA.warm),hF,he]
    with x hx hU hX hp hF he
  have hp:= (le_abs_self _).trans hp
  refine ⟨abs_nonneg _,abs_nonneg _,hA,hp,fun c f S T R v H hT hS=>?_⟩
  -- assumes Branch S.patch=D !!! Producer restrict D.

  have heq:= H.laws.data; have hhP:=heq.funds; have hi:= H.laws.intake
  refine ⟨hx _ _ S T hS hT R v H,fun E _ _ _ Y F X z hZ hΞ hv hg ht hf=>?_⟩
  have hy:=heq.localP F X hZ hv hg
  refine ⟨he c f S T hS heq.funds heq.access F X hv hΞ hZ hy E Y z ht hf,?_⟩ -- let intro binder
  intro w u F'
  have he :8*o.a*X.t≤ A/2:=by unfold Coat.t; rw [hZ,hhP.length_eq]; exact hp
  obtain ⟨hW,hY⟩:= hX c f S T F X hZ hhP hΞ R.beta hi.positive w E Y z ht hf
  have hY:= hY o.a (mul_pos o.large hy.sails.room.fiery) he; refine ⟨hY,hU c f S T hhP hS heq.access E z Y F X w R hZ hv hΞ hy hi hf hY hW,fun P' h V=> ?_⟩
  exact hF _ _ S T hS hhP heq.access E z Y F X R F' w _ hZ hΞ hv hy hf hi hY P' _ h
end YM.UVExtension.Wick
