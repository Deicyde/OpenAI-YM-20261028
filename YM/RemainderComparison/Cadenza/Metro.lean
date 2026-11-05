import YM.RemainderComparison.Cadenza.Cord
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cadenza
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler ThroughLaunch Bid Planned.JetPort
open YM.RemainderComparison.Aux Funk Herbal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {P:Teller G} {Q:ConnectedActivityE6.Target G P} {p:Patch} {L : Side} {K:KernelChoices} {j n r : ℕ}
variable {q o w : ℝ→ℝ}{W μ:ℝ} {A:ConnectedActivityE6.Target.Order G W}
namespace Scrollwork
variable (s:Scrollwork G L)
lemma keeled : Reserve G L (fun x=>(s.k x :ℝ)):=by
   refine ((Reserve.const (s.ℓ:ℝ)).mul (Reserve.field)).compare ?_; filter_upwards [s.growth] with x hx; rw [abs_of_nonneg (by positivity : 0 ≤ (s.k x:ℝ))]; exact (show (s.k x:ℝ) ≤ (s.ℓ:ℝ)*radiusB x by exact_mod_cast hx.2.2.2.2).trans (le_abs_self _)
lemma capped : Reserve G L (fun x=>(s.z x:ℝ)):=by
   refine s.keeled.compare ?_; filter_upwards [s.growth] with x hx; rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast (show s.z x ≤ s.k x from le_trans (by omega) hx.2.2.2.1)
lemma crimped : Reserve G L (fun x=>(s.n x:ℝ)):=by
   refine s.capped.compare ?_; filter_upwards [s.growth] with x hx; rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast (show s.n x ≤ s.z x from le_trans (by omega) hx.2.2.1)
lemma board : Reserve G L (fun x=> (s.halo x:ℝ)):=by
   refine s.crimped.compare ?_; filter_upwards [s.growth] with x hx; rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast (show s.halo x ≤ s.n x from le_trans (by omega) hx.2.1)
end Scrollwork
namespace Poster
variable (E E': RG.Stage)(K : KernelChoices)(Q:ConnectedActivityE6.Target G P) (D : Poster)
variable (g:Rays)(h:Scrollwork G p.L)(s:Songbook G p.L)
lemma quorum (hμ:0<μ)(hh:g.Heart E' Q.exp) : ∃ D:Poster,0<D.d∧PaintSupply G g.wind D.Z ∧ D.Financed G p.L ∧ ∀ᶠ x in atTop,Poster.Paid g E E' K Q (A:=A) (μ:=μ) D h s x:= by
   obtain ⟨R,hR,h₁⟩:= Arc.finance G p.L h.z h.capped E'.order
   let n:=g.wind
   have hN : 2 ≤ n:= by unfold n Rays.wind; have he:=hh.probe; omega
   obtain ⟨J⟩:= Uniform.pre_order G E.width E.paths p.J K (n:=n+3) (by omega)
   let L:= Classical.choice (Planned.JetPort.purchase Q.table Q.table_exists ((n+3)+1)); let C:=Classical.choice (BareRates.offered G E'.width E'.paths (n+3))
   let f:= h.volume
   let t x:=pam n Q.table E.clip p J (f x) (f x) L (ConnectedActivityE6.loopBill G p.L x)
   let F:= J.tables E.clip p
   have hv:Reserve G p.L t:= Aux.rents Q p J E.clip f h.votes L
   obtain ⟨d,hd,hD⟩:= Profile.observation Q A p J E.clip E'.clip f L R (h₁.mono fun x hx=>⟨hx.rich,hx.light.2⟩) h.votes hR hμ C (by omega)
   obtain ⟨Z,hZ⟩:= paint_supply G g.wind
   have hF : ∃ q r f' C:ℝ→ℝ, Reserve G p.L q ∧ Reserve G p.L r ∧ Reserve G p.L f' ∧ Reserve G p.L C ∧ ∀ᶠ x in atTop,
       Herbal.Airstrip (G:=G) p.L K d F.gap h.volume (fun x=> 2*R x) t (s.uptake d Z R t) E'.order g.p g.arm g.wind g.rank g.title Z q r f' C x:=by
      by_cases hp: 0<F.gap
      · exact Herbal.compile _ hp hd p.L _ _ _ _ _ h.votes ((Reserve.const _).mul hR) hv (s.etudes d Z R t hR hv hZ.1 hd).1 _ _ _ _ _ _ hh.probe le_rfl hZ
      refine ⟨_,_,_,_,Reserve.const 1,Reserve.const 1,Reserve.const 1,Reserve.const 1,?_⟩; apply Eventually.of_forall; intro x
      constructor; intro c f' S T F' k r O Q' R B V ι α hi m P' M L H hf hM hH ht z c' C Φ hv hW hc
      constructor; intro y he ht; exact (hp (hW _ he ht).paint.gap).elim
   obtain ⟨q,r,f',C',hq,hr,hf,hC,hF⟩:=hF
   refine ⟨⟨d,F.gap,Z,R,t,q,r,f',C'⟩,hd,hZ,⟨hv,hR,hq,hr,hf,hC⟩,?_⟩; filter_upwards [hF,h₁,hD] with x hx ht hC
   refine ⟨hx,ht,fun c f' S V F' hs hh hy h h' hv Λ h₀ r a b d Ω α hc he hf=>?_⟩
   obtain ⟨u,hu,h₁,h₂⟩:=hC c f' S V F' hs hh hy h h' hv Λ h₀ r a b d Ω α hc he hf; exact ⟨u,hu.critical,h₁,h₂⟩
end Poster
namespace Paid
variable (E E': RG.Stage)(K : KernelChoices)(Q:ConnectedActivityE6.Target G P) (D : Poster)
variable {g:Rays}{h:Scrollwork G p.L}{s:Songbook G p.L}{P₀:BudgetPoint} {x β :ℝ} {S:Teller G}
-- CROP eligibility known from publisher. Mints pilot now. Fit Quality with apertures.P register conditions.Growth proved.
lemma approved (A:ConnectedActivityE6.Target.Order G W) (hp: Poster.Paid g E E' K Q D h s (A:=A) (μ:=μ) x) (ht:Temper P₀ E' x G p.L)(he: inBand (betaF G x p.L) β)
   (hx : 0<h.halo x ∧ 2*h.halo x ≤ h.n x ∧ h.n x+5 ≤ h.z x ∧ 2*h.z x≤ h.k x ∧ h.k x ≤ h.ℓ * radiusB x) :
   Arc.Tracer P₀ G β (D.R x)∧ h.Ready x G P₀ β (D.R x):=by
   obtain ⟨hz,h⟩:= hp.soothe.contract β P₀ he ht.pressure ht.pact ht.order
   exact ⟨hz,fun hc=>⟨hx.2.1,hx.2.2.1,hx.2.2.2.1,hc.has,hc.shape,ht.pose.symm ▸ hx.2.2.2.2,h⟩,hx.1⟩ -- Lean Ready.set binder
end Paid
end YM.RemainderComparison.Cadenza
