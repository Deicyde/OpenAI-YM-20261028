import YM.UVExtension.Linden.Nurse
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Linden
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} 
open Animals Reserves Wick Festa PhysicalNext.Repeat.Lotus
open PhysicalNext.Repeat Daisy Willow Wick Wick.Bower
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι → Juice G f}
variable {v₁ v₀ b₀ K' w g θ A r B' D d n' n : ℝ} {k j K : ℕ} {χ:Chi}
lemma canopy (Q: YM.ConnectedActivityE6.Target G P) : ∃ m:ℕ,∀ (L:Side),m ≤ L.val →∀ (D:Patch) (χ:Chi) (W μ:ℝ) (o:Target.Order G W), D.Branches P.bind G → 0<W → 0<μ → ∀ (u:ℝ→ℝ), Rate G L (-(1/2)) u → (∀ᶠ x in atTop,0≤u x) → ∀ (N j : ℕ) (γ e q :ℝ),0<q → q≤ Q.exp → ∀ (he:0<e) (hQ: Q.rate+e<γ) (hl:γ<0), ∃ θ ξ:ℝ→ℝ,
    Rate G L γ θ ∧ Rate G L 0 ξ ∧ ∀ᶠ x in atTop, ∃ (A b B C r d n:ℝ) (k:ℕ) (U Z c M : ℝ) (l : ℕ),
      θ x= Outliner.award G (stalk Q (by linarith : Q.rate≤γ) hl) x U Z r L μ j l ∧ ξ x=scalarM Q x U Z M r l j ∧ Mojo Q o L μ A x d M j χ ∧ ∃ K:Bower Q o L D μ χ A b x j k (u x) B C r d n,
      ∀ (c' f:Side) (S:StepData c' f) (T:Tube G S) (a:ℝ) (R:Rep G f) (H:Cash W x μ L Q o a T R), Stamp T →∀ hp:D=S.patch,
      ∀ (ι:Type) [Fintype ι], Fintype.card ι=N →∀ (V:ι→ Juice G f) w, ∀ (F:Festa Q L H V w (betaF G x L^e)),
        Outliner (hp ▸ K) F γ (by linarith) hl U Z c q l:= by
  obtain ⟨n,hN⟩:= satin Q; refine ⟨n,fun L hL D χ W μ o hD hW hm u hu hU N j γ e q hq hq' he hQ hl=> ?_⟩
  have hv: Q.rate≤γ:= by linarith
  let Q0:= stalk Q hv hl
  obtain ⟨A,b,hC⟩:= Eider.weave G
  obtain ⟨k,C,B,r,d,s,h',hp,hK,hp',hc,h₁⟩:= hN L hL D hD j χ W μ hW hm o A b hC u hu hU
  obtain ⟨l,Z,hZ,hY⟩:= forestation P Q L W μ o A b χ he hQ hl hv N j k (d:=d) (u:=u) hm h' hK hp' hp
  obtain ⟨M,n,ht,hM⟩:= Lush.flutes L o (k*j*2)
  have hζ : Rate G L 0 (fun x=> M x*(1+Z x+2*r x)^j):= by
    convert ht.mul (((((Rate.const 1).add hZ).add (hK.mul_left 2))).pow j) using 1; ring
  obtain ⟨m,hr,hL'⟩:= craftsJ hc χ j Q o μ A
  refine ⟨(fun x=> Outliner.award G Q0 x (M x) (Z x) (r x) L μ j n), (fun x=>scalarM Q x (M x) (Z x) (m x) (r x) n j),by
    have hh:= Q0.rate_none L hm 0 (n+j) 0 -- cost β constant
    simpa only [zero_add] using! hζ.mul hh,?_ ,?_⟩
  · have hp:= ((ht.mul (((Rate.const 1|>.add hZ).add ((hr.add hK).mul_left 2)).pow j)).mul_right (polyPrice Q.ε (n+j))).mul_right (coined Q 0)
    rw [zero_mul,zero_add] at hp; exact hp
  filter_upwards [hL', h₁,hY,aisles G L q hq] with x hP hx hy he
  obtain ⟨hg,K'⟩:= hx
  obtain ⟨hH,hV⟩:= hy D hg K'; obtain ⟨hv,hM⟩:=hM x
  refine ⟨A,b,B x,C,r x,d x,s x,k,M x,Z x,l,m x,n,rfl,rfl,hP,K',fun c f S T a R H hS hp ι inst hL V w F=> ⟨by linarith, hM,hH,hv,hV _ _ S T R _ H hS hp _ hL V w F,fun t ht p=> ?_⟩⟩
  have hd': t none ∈ aisle (betaF G x L):=(marching t|>.1 ht).1
  have hk:= (he c f S (H.unionP p) _ H.laws.data.funds.length_eq hd').2.2.2; rwa [Fintype.card_coe] at hk

end YM.UVExtension.Linden
