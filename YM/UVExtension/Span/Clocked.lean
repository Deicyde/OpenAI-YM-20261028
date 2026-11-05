import YM.UVExtension.Span.Abbey
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Span
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
namespace Score
open Oriented Vine Concerted
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Score v T H k l χ A b u B N r d f' V Z)
variable {t:κ→Bool→ι}(h:∀ b,Tendsto (fun n=> t n b) qq v)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {τ:κ→ E} {Y:κ→ E→ Config G c}
variable {F:Forest S.ratio} {M:κ→ Hat G F}
-- states use explicit
variable (he:∀ᶠ i in qq,Mode (Y i) (τ i) k u)(hK:∀ᶠ i in qq,(M i).legal s ∧ Y i (τ i)=(M i).bill)
include p h he hK
open Matrix
lemma strongP : ∃ (D r:ℝ), 0<r ∧ ∀ᶠ i in qq,∀ b,(vary ((M i).order (T (t i b)) s χ U.K) (Y i (τ i))).plate ∈ Minaret.Town D r:=by
   let X i b:=(M i).order (T (t i b)) s χ U.K; obtain ⟨m,_,hx⟩:= (gram p h he (M:=M)).cap
   use m,U.gap; refine ⟨U.f.spans,?_⟩; filter_upwards [hx,hK] with i hi hp b; rw [hp.2]
   let q:= H (t i b); have hv:=(q.laws.data.localP F (X i b) rfl rfl hp.1).sails
   refine ⟨⟨mem_closedBall.mpr (by rw [dist_zero_right]; exact hp.2 ▸ ((hi b).bound)), (X i b).balanced⟩,hv.scale.ground⟩ -- proof eq
-- PDA uniform spectral frame, qualitative period. May carry integrating densities. A blank requests.
lemma trunks : Walt qq τ k (fun i b y=> (vary ((M i).order (T (t i b)) s χ U.K) (Y i y)).shreds) ∧
      Walt qq τ k (fun i b y=> (vary ((M i).order (T (t i b)) s χ U.K) (Y i y)).kernelA) ∧
      Walt qq τ k (fun i b y=> (vary ((M i).order (T (t i b)) s χ U.K) (Y i y)).relating) :=by
   let D:=Coat.frames G S (radiusB s); obtain ⟨a,r,hr,hx⟩:= strongP p h he hK
   have hv:=Minaret.suburbs (J:=Tubular f G) a r; have hA:=gram p h (M:=M) he
   exact ⟨Walt.company (Z:=D.flawed) hv (fun j hj=> (Minaret.youth D (Minaret.certified hj hr) k).2) hA hx,
     Walt.company (Z:=D.pad) hv (fun j hj=> Minaret.refer D (Minaret.certified hj hr) k) hA hx,
     Walt.company (Z:=D.frameMean) hv (fun j hj=> (Minaret.youth D (Minaret.certified hj hr) k).1) hA hx⟩
-- from here N orth curvature and flat bills. Blank not assume Bar manifest; actually legal from flag1.
lemma neutralP : Walt qq τ k (fun i b y=> (vary ((M i).order (T (t i b)) s χ U.K) (Y i y)).blank.plate) ∧
    ∃ d r:ℝ,0<r∧∀ᶠ i in qq,∀ b, (((M i).order (T (t i b)) s χ U.K).blank.plate)∈ Minaret.Town d r:=by
   let R i:Hat G F:=⟨⟨∅,∅,∅⟩,1,(M i).tag,(M i).Y⟩; let Y:κ→ E→ Config G c:= fun i z=>1; have hY:∀ᶠ i in qq,Mode (Y i) (τ i) k u:= he.mono fun i hi=> ⟨hi.pos,fun j=> a_oneB G _ hi.pos⟩
   have hR: ∀ᶠ i in qq,(R i).legal s∧ Y i (τ i)=(R i).bill:= by
        filter_upwards with i; refine ⟨?_,rfl⟩; exact Coat.bowed ((M i).order (T (t i false)) s χ U.K) (by apply temp_nonneg
          )
   have hE b n y U: (vary ((M n).order (T (t n b)) s χ U) y).blank=vary ((R n).order (T (t n b)) s χ U) 1 := rfl
   have hF b n U: ((M n).order (T (t n b)) s χ U).blank=vary ((R n).order (T (t n b)) s χ U) 1:= rfl
   simp_rw [hE,hF]; refine ⟨gram p h (M:=R) hY,?_⟩; obtain ⟨d,r,hr,hp⟩:= strongP p h (M:=R) hY hR; exact ⟨d,r,hr,hp⟩
lemma logPins (j : Bond f): Walt qq τ k (fun i b y=> (vary ((M i).order (T (t i b)) s χ U.K) (Y i y)).condensation j) :=by
   let D:=Coat.frames G S (radiusB s); obtain ⟨a,r,hr,hx⟩:= strongP p h he hK; have T:=Walt.company (Minaret.suburbs a r) (fun i hi=> (Minaret.mature D (Minaret.certified hi hr) k).2.2 j) (gram p h (M:=M) he) hx
   obtain ⟨hp,d,r,hr,h⟩:= neutralP p h he hK; have hx:=Walt.company (Minaret.suburbs d r) (fun i hi=> (Minaret.mature D (Minaret.certified hi hr) k).2.2 j) hp h
   exact (hx.minus T).plant (Z:=fun i=> i/2) (contDiff_id.div_const _)
lemma stampsA (j: Ledger f 3): Walt qq τ k (fun i b y=> ArmA (Coat.frames G S (radiusB s)) (vary ((M i).order (T (t i b)) s χ U.K) (Y i y)).plate j) ∧ Walt qq τ k (fun i b y=> ArmA (Coat.frames G S (radiusB s)) (vary ((M i).order (T (t i b)) s χ U.K) (Y i y)).blank.plate j):=by
   let D:=Coat.frames G S (radiusB s); obtain ⟨a,r,hr,hx⟩:= strongP p h he hK; refine ⟨Walt.company (Z:=fun v=> ArmA D v j) (Minaret.suburbs a r) (fun i hi=> (Minaret.mature D (Minaret.certified hi hr) k).1 j) (gram p h (M:=M) he) hx,?_⟩
   obtain ⟨hp,d,r,hr,h⟩:= neutralP p h he hK; exact Walt.company (Z:=fun v=> ArmA D v j) (Minaret.suburbs d r) (fun i hi=> (Minaret.mature D (Minaret.certified hi hr) k).1 j) hp h
lemma stampsS (j:Ledger f 1): Walt qq τ k (fun i b y=> ArmS (Coat.frames G S (radiusB s)) (vary ((M i).order (T (t i b)) s χ U.K) (Y i y)).plate j) :=by
   obtain ⟨a,r,hr,hx⟩:= strongP p h he hK
   exact Walt.company (Z:=fun v=> ArmS (Coat.frames G S (radiusB s)) v j) (Minaret.suburbs a r) (fun i hi=> (Minaret.mature _ (Minaret.certified hi hr) k).2.1 j) (gram p h (M:=M) he) hx

omit he hK h p [FiniteDimensional ℝ E] in lemma jetting {a b:Type} [Fintype a][Fintype b]{Y:κ→Bool→ E→ Matrix a b ℝ}{S:κ→Bool→ E→ (b→ℝ)}(h: Walt qq τ k Y)(p: Walt qq τ k S): Walt qq τ k (fun n x i=> Y n x i *ᵥ S n x i):=by
    apply Walt.assemble; intro i; unfold Matrix.mulVec dotProduct; apply Walt.schedule _ _; intro j hj
    let T:Matrix a b ℝ→ₗ[ℝ]ℝ:={ toFun:=fun M=> M i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
    exact (h.leaf T.toContinuousLinearMap).times (p.leaf (ContinuousLinearMap.proj j))
omit p he h hK [FiniteDimensional ℝ E] in lemma reweave {a b:Type} [Fintype a] [Fintype b] {Y:κ→Bool→ E→ Matrix a b ℝ}(p:Walt qq τ k Y): Walt qq τ k (fun i b y=> (Y i b y).transpose):=by
    exact p.leaf (show Matrix a b ℝ→L[ℝ] Matrix b a ℝ from LinearMap.toContinuousLinearMap { toFun:=Matrix.transpose,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl })
lemma stakes : Walt qq τ k (fun i b y=> leanB (vary ((M i).order (T (t i b)) s χ U.K) (Y i y))) :=by
   apply jetting (reweave (formG p h (M:=M) he)); apply Walt.assemble; rintro ⟨⟨i,j⟩,u⟩; apply (p.stocks h he hK i j).leaf ((LinearMap.comp (LinearMap.proj u) (WithLp.linearEquiv 2 ℝ _).toLinearMap : G.Color→ₗ[ℝ]ℝ).toContinuousLinearMap) -- apply
lemma wings : Walt qq τ k (fun i b y=> well (vary ((M i).order (T (t i b)) s χ U.K) (Y i y))) := (jetting (reweave (trunks p h he hK|>.2.1)) (stakes p h he hK)).leaf (-(ContinuousLinearMap.id ℝ _))
lemma pulses : Walt qq τ k (fun i b y=> voltage (vary ((M i).order (T (t i b)) s χ U.K) (Y i y))) := by
   let L : (Tubular f G→ℝ)→ₗ[ℝ] Directions G f:= { toFun:=erect G,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
   exact (p.wings h he hK).leaf L.toContinuousLinearMap
end Score
end YM.UVExtension.Span
#print axioms YM.UVExtension.Span.Score.logPins
#print axioms YM.UVExtension.Span.Score.pulses
