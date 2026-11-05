import YM.UVExtension.Strata.Axis
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Strata
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
namespace Polish
open Matrix MeasureTheory WithLp Shield
open Span Oriented Vine
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Span.Score v T H k l χ A b u B N r d f' V Z)
open Polar Silica Shield Score Flux Matter
-- provide one Bulb price tight with point domination absolute all measured legs
open Eider
variable {t:κ→Bool→ι}(h:∀ b,Tendsto (fun n=> t n b) qq v)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {τ:κ→ E} {Y:κ→ E→ Config G c}
variable {F:Forest S.ratio} (M:κ→ Hat G F)
variable (he:∀ i,Mode (Y i) (τ i) k u)(hK:∀ i,(M i).legal s ∧ Y i (τ i)=(M i).bill)(qV:StableR v R)
include h he p hK qV
-- Scar along s Health. Lens relation positive compact stamps. ratios never clipped.
variable [NeBot v]
set_option maxHeartbeats 600000 in
omit p he h qV hK in lemma scarves {J: Type} [Fintype J][DecidableEq J] {F:κ→ Bool→ E→ Matrix J J ℝ}{v:κ→ Bool→ E→ Poll.Body J}(hp:Walt qq τ k F)(hv:Walt qq τ k v){a r:ℝ}(hr:0<r)(hS:∀ᶠ n in qq,∀ b,F n b (τ n)∈ Minaret.Town a r): Walt qq τ k (fun i b x=> lens₀ (F i b x) (v i b x)) ∧ Walt qq τ k (fun i b x=> (lens₀ (F i b x) (v i b x))⁻¹):=by
   obtain ⟨b,h⟩:=hv.atProbe.1; let K:=(Minaret.Town (J:=J) a r).prod (closedBall (0:Poll.Body J) b); have hK:IsCompact K:=(Minaret.suburbs a r).prod (isCompact_closedBall ..)
   let Y i b x:=(F i b x,v i b x); have hx:∀ᶠ n in qq,∀ b,Y n b (τ n)∈ K:= by filter_upwards [h,hS] with i hi hx b; exact ⟨hx b,mem_closedBall_zero_iff.mpr (hi _)⟩
   let g(a:Matrix J J ℝ × Poll.Body J):=lens₀ a.1 a.2; have ht (i:Matrix J J ℝ × Poll.Body J) (hi:i∈K): ContDiffAt ℝ (↑k) g i:= smoothL k i.1 i.2 (Minaret.certified hi.1 hr)
   exact ⟨Walt.company (Z:=g) hK ht (hp.both hv) hx,Walt.company (Z:=fun v=> (g v)⁻¹) hK (fun i hi=>(ht _ hi).inv (show g i≠0 from (fullFuel i.1 i.2|>.ne'))) (hp.both hv) hx⟩
omit he hK in lemma phases :∀ t, Together qq (fun n b=> Wick.lint (R (‹κ→Bool→ι› n b)).beta t):= by
    intro s; have hp:= (Score.betP p h qV).2; exact hp.continuous (T:=fun x=> x^s) (by fun_prop)
variable (v': Air f G)

-- setup shifted arguments for fixed Slice y tag

def renew (y:F.Slice G)(W:Hat G F): Hat G F:={W with Y:=y}
def bend : Directions G f:= erect G (ofLp v')
-- lens and v tips originally.
omit h p he hK qV
lemma shoots (P:Tube G S)(M:Hat G F)(y:F.Slice G)(w:ℝ): (renew y M).order P s χ w=(M.order P s χ w).wrapY y:=rfl
lemma prizeRail (t:κ→ Bool→ι)(y:F.Slice G)(v:Air f G) (n:κ)(b:Bool): wound (R:=R) (t n b) (Score.Abide s χ U.K T M t n b) (y,v)=prize s χ U.K T R (fun i=>renew y (M i)) t (fun _=>bend v) n b:= rfl
include p h qV
variable (hm:∀ i,(M i).legal s)
include hm
lemma topicM (hn:0≤u)(x:F.Slice G × Air f G): Together qq (fun n b=>quilt (R:=R) (t n b) (Abide s χ U.K T M t n b) x):=by
   rcases x with ⟨z,x⟩; unfold quilt; simp_rw [prizeRail]; let v i:= renew z (M i); let Y:=Score.atR (Score.echo v); let τ:= Score.bracket (κ:=κ); have hx: ∀ᶠ i in qq, (v i).legal s ∧ Y i (τ i)=(v i).bill:= Eventually.of_forall fun i=> ⟨hm _,rfl⟩
   obtain ⟨a,r,b,hd,hb,hr,hφ⟩:= presidents p
   let F n b y:= (vary ((v n).order (T (t n b)) s χ U.K) (Y n y)).relating; have hZ : ∀ᶠ n in qq,∀ b,F n b (τ n)∈ Minaret.Town a r:= Eventually.of_forall fun n b=> (hφ _ _ _ rfl rfl (show ((v n).order (T (t n b)) s χ U.K).manifest from hm _)).1
   have hu:∀ i, Mode (Y i) (τ i) k u:=fun i=> ⟨hn,fun j=> a_oneB G _ hn⟩
   have hT := fundsW p h (Eventually.of_forall hu) hx qV (fun _=>bend x) ⟨_,Eventually.of_forall fun _=> le_refl _⟩
   have hf := (scarves (v:=_) (τ:=τ) (F:=F) (Score.trunks p h (Eventually.of_forall hu) hx|>.2.2) (Walt.stamp hT) hb hZ).1
   -- phases doesn't need he,hK
   exact ((Walt.stamp (phases p h qV _)).times hf).atProbe
-- S opacity K. angular comp of ratio. No positivity at offbranch U used. fixed clocks.
include he hK
omit hm
lemma wages (U':Finset (Bond f))(W:κ→ Directions G f)(hv:∃ r:ℝ,∀ᶠ n in qq, ‖W n‖≤r): Walt qq τ k (fun n b i=>scalp U' (Abide s χ U.K T M t n b) (Y n i) (R (t n b)).beta A (prize s χ U.K T R M t W n b)):=by
   obtain ⟨a,r,sT,hA,hr,hs,hφ⟩:= presidents p
   let X n b i:= vary (Abide s χ U.K T M t n b) (Y n i); let F n b:= prize s χ U.K T R M t W n b
   let i:= lensS U' G; let Y' n b z:= circuit i (X n b z).relating
   have hx:= p.trunks h (Eventually.of_forall he) (Eventually.of_forall hK)|>.2.2
   have ht : ∀ n b,X n b (τ n)= Abide s χ U.K T M t n b:=fun n b=> by unfold X; rw [(hK n).2]; rfl
   have hT : Walt qq τ k Y' := by
      refine hx.leaf (show Mat _ _→L[ℝ] Matrix (↥i) (↥i) ℝ from LinearMap.toContinuousLinearMap { toFun:=Pond.circuit i, map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl })
   obtain ⟨d,hd⟩:=hT.atProbe.1; have hV:∀ᶠ n in qq,∀ b,Y' n b (τ n) ∈ Minaret.Town d r := by
       filter_upwards [hd] with n h b; have hp:= (hφ _ (t n b) (X n b (τ n)) rfl rfl (by rw [ht]; exact (hK n).1)).1; exact ⟨⟨mem_closedBall_zero_iff.mpr (h _), (hp.1.2).submatrix _⟩,hp.2.restrict (Embedding.subtype _)⟩
   let L : Air _ G →ₗ[ℝ] Poll.Body (↥i):={ toFun:= Pond.swim i,map_add':=fun _ _ =>rfl,map_smul':=fun _ _=>rfl }
   have hp:= p.sailsW h (Eventually.of_forall he) (Eventually.of_forall hK) qV W hv; have hx:= p.fundsW h (Eventually.of_forall he) (Eventually.of_forall hK) qV W hv
   have hx':= scarves hT (hp.leaf L.toContinuousLinearMap) hr hV|>.1; have hy := scarves (Walt.stamp (k:=k) (x:=τ) hT.atProbe) (Walt.stamp (hx.scalar L.toContinuousLinearMap)) hr hV|>.2
   have hg j: Walt qq τ k (fun n b y=> steerJ (Abide s χ U.K T M t n b) A (W n) (Y n y) j):= by
      obtain ⟨d,hd⟩:=hv
      let r':=p.realm.bay
      let W' n b y:= (G.mat (Silica.action (Abide s χ U.K T M t n b) (Y n y) j),W n j)
      have hQ: Walt qq τ k W':=by
          have hW:Together qq (fun n (_:Bool)=> W n j):= ⟨⟨d,hd.mono (fun n hn i=> (norm_le_pi_norm _ _).trans hn)⟩,(by simp [tendsto_const_nhds])⟩
          apply Walt.both _ (Walt.stamp hW); refine Walt.twin (royalty G) u (Eventually.of_forall (fun n=> ⟨?_,rfl⟩)); exact chargeMode (Abide s χ U.K T M t n true) u (he n) j
      let K:= Set.prod ({(1:G.Mat)}) (closedBall (0:G.Color) d); have hp : IsCompact K:= isCompact_singleton.prod (isCompact_closedBall _ _);
      have hh:∀ᶠ n in qq,∀ b,W' n b (τ n)∈K:=by filter_upwards [hd] with n hn b; refine ⟨?_,mem_closedBall_zero_iff.mpr ((norm_le_pi_norm (W n) j).trans hn)⟩; unfold W'; rw [(hK n).2]; simp [Silica.action,Abide,Hat.order]
      apply Walt.company (Z:=uncurry (palm G χ A)) hp (fun (M,v) hu=>?_) hQ hh
      have he : M=1:=hu.1; subst M; exact Eider.lift r' χ _ _ (by simp [r'.side.le])
   have hW: Walt qq τ k (fun n b y=> jacL U' (Abide s χ U.K T M t n b) A (R (t n b)).beta (Y n y) (prize s χ U.K T R M t W n b)):=by unfold jacL prize; simp_rw [rent_bill (R (t _ _)).beta _ (H _|>.laws.intake.positive)]; exact caraffa U' _ fun j _=> hg j
   refine (hW.times (hx'.times hy)).same (Eventually.of_forall fun i v=> Eventually.of_forall fun y=>?_)
   unfold Flux.scalp; dsimp only; unfold Y'; rw [ht]; rw [div_eq_mul_inv]; rfl
end Polish
end YM.UVExtension.Strata
