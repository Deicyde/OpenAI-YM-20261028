import YM.RemainderComparison.Halo.Nexus
import YM.RemainderComparison.Halo.Must
/-!
 # Horizon with inherited recurrence budgets

 Post L in actual tracks. Output `A₁`, `S'` etc correspond to actual stage
 Cohort. Contains simultaneous proof at every Toll demand exponent (contractive
 gains per surplus unmarked occurrence when in era); SUM budget with any fixed
 η. Disjoint notes used after RU grammar alignment. Does not by itself assert
 that disjoint validation representing prescribed input tags exists. Root growth
 of outputs supplied on the SAME strings (don’t tear). No assertion
 singleton ERA is already paid at `const/L`; next. Smooth as germ before
 re-expression.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Halo
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling Raw Itinerary Opacity Graft Cascade Lyric Daisy
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J:ℕ}(χ:Chi)
variable (N: Captain H j q d v u A b r B e n χ) (Ξ:Utopia H j v d r q χ)
variable (l:ι→ℝ) (E:Set ℕ)(w:ℕ→ℝ){T' S' p' δ B' τ ε:ℝ}

lemma ramp (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P):∃ l:ℕ, ∀ (L:Side), l≤L.val → ∀ (D:Patch), D.Branches P.bind G →
   ∀ (j:ℕ)(ε a:ℝ), 0≤a→0<ε→ a+ε+ε≤Q.exp →∀ (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:ConnectedActivityE6.Target.Order G W),
    ∃ (A a' B C':ℝ)(d v t r F B₀ T K :ℝ→ℝ)(k:ℕ), Rate G L 0 F ∧ Reserve G L T ∧ Gear G L (-(1/2)) v ∧ ∀ I J:ℕ, ∀ (Y:ℝ→ℝ)(n:ℝ→ℕ), Reserve G L Y → Reserve G L (fun x=>(n x:ℝ)) →
    ∃ (V S':ℝ→ℝ)(q:ℝ), q<0 ∧ Reserve G L V∧ Gear G L q S' ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S:StepData c f) (T':Tube G S), S.patch=D→Stamp T'→∀ (R:Rep G f) (C'':ℝ) (H:Cash W x μ L Q o C'' T' R),
      ∃ N:Captain H j B (d x) (v x) (t x) A a' (r x) (F x) (B₀ x) k χ, Heavy N.conduit ∧ Heroes H N.conduit A (F x) k ∧
      ∀ (ι P':Type) [Fintype ι] [Fintype P'](M:ι→ Lotus.Leaf R)(X' : P'→ Site f)(L':ι→ Finset P')(l:ι→ℝ) (σ:ℝ)(E:Set ℕ)(w:ℕ→ℝ) (δ:ℝ),
        Lyric.Scale X' L' M l (n x) σ (Y x) S → radiusCost Q L σ→ Presents R E w δ → δ ≤ incomingE G L x →
        let f₀:=melod M H (rails H N.conduit E w C' (K x)) (T x) k
        Lyric.Paid M H χ N f₀ ∧
        ∀ m:ℕ,Ac.Hit (Captain.reachability (H:=H)) (radiusB x) (fun z=>∑ i:Syllable M H z, if (dyed M H E z i ∧ 1+m≤gross M H z i) ∧ Lyric.notes M H z i≤I then
       Lyric.Bill M H f₀ z l j i J else 0) a (V x*(S' x)^m*δ):=by
   obtain ⟨m,hM⟩:= seeds P Q; obtain ⟨m',hm'⟩:= halos P Q
   refine ⟨max m m', fun L hL D hD j ε a ha ht he χ W hW μ hm o=>?_⟩
   obtain ⟨A,a',C₀,C',d,v,t,B,r,T,p,w,k,hC,hC',hF,hv,hB,hR,htP,hp,h,hH'⟩:= hM L ((le_max_left ..).trans hL) D hD j χ W hW μ hm o
   refine ⟨A,a',C₀,C',d,v,t,r,B,w,p,T,k,hB,hp,hv,fun I J Y n hY hJ=> ?_⟩
   -- restore ignored Rate T
   obtain ⟨V',hV, τ,γ,S',hT,hP,hS,hB⟩:= gear_writ Q (j:=j) (n:=k) (κ:=C') C₀ hY p hp hm ε (show Rate G L 0 T by assumption) n hJ
   let b x:= τ x^I *τ x * (collars G ε x j J*(rebate Q (p x) (γ x) j k*(1-1/2)⁻¹))
   have hb:= Halo.lumens (j:=j) (k:=k) Q ε hp hP
   have hK:= Halo.lumens (j:=j) (k:=J) Q ε hp hP
   refine ⟨b,fun x=>(S' x)⁻¹, -V', neg_lt_zero.mpr hV, ((hT.pow _).mul hT).mul (hK.2.mul (hb.1.mul (Reserve.const _))),hS,?_⟩
   filter_upwards [hH',hB,hm' L ((le_max_right ..).trans hL)] with x hh hv hh' c f S T' ht' hs R C'' H
   obtain ⟨N,hy,hK,hr⟩:=hh c f S T' ht' hs R C'' H
   refine ⟨N,hy,hK,?_⟩
   intro ι P' _ _ M X' L' l σ E w' δ hP hδ he' hh f₀
   have hT:= H.laws.data.funds.length_eq
   have h': δ≤1:= hh.trans hv.cap; have hz: 0≤ T x:= (h x).1; have ha': 0≤ p x:= (h x).2
   refine ⟨Halo.earns M H χ N _ k (p x) ha' (rails_nonneg H N.conduit E w' C' (T x) he' hC' hz) (fun M p=>hr.ready M E w' _ he' h' p),fun m=>?_⟩
   have ht':R.p.B ≤ 2*radiusB x:=by rw [H.laws.intake.sizes,hT]; exact hv.shape
   have hF := wishes M H χ N l E w' C' (T x) (p x) hP ht' hδ he' (hh' S T' R hT H.laws.intake E w' δ he') hr hv.pace hv.income hC' h' hz ha'
      hv.awake (show _ ≤ γ x from hv.beat) ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (zero_le_one.trans hv.pace)) (zero_le_one.trans hv.income)).trans hv.fits) hv.warmth he ha ht hv.height I m J
   convert hF using 1; rw [inv_pow]; unfold b; ring
end YM.RemainderComparison.Halo
