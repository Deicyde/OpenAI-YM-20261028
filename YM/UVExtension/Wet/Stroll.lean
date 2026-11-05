import YM.UVExtension.Wet.Pru
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wet
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady PhysicalNext.Repeat Lotus
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Strata Strata.Polish Matrix MeasureTheory WithLp Shield
open Span Oriented Vine
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Span.Score v T H k l χ A b u B N r d f' V Z)
open Polar Silica Shield Score Flux Matter
variable {D : (i:ι)→ Lotus.Leaf (R i)} (hzM:Constant (v:=v) D)
variable [NeBot v](hu:0≤u)(qV:StableR v R)
variable {t:κ→Bool→ι}(h:∀ b,Tendsto (fun n=> t n b) qq v)[qq.IsCountablyGenerated]
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {τ:κ→ E} {Y:κ→ E→ Config G c}
variable {F:Forest S.ratio} (M:κ→ Hat G F)
variable (hpV:∀ i,Mode (Y i) (τ i) k u)(hK:∀ i,(M i).legal s ∧ Y i (τ i)=(M i).bill)
variable (X':Air f G→ℝ)(Z':ι→ Molecule S→ℝ)(hV: Roast (D:=D) (v:=v) (H:=H) (χ:=χ) (k:=k) (u:=u) (A:=A) X' Z')
include hzM p hu qV h hV
omit [FiniteDimensional ℝ E] in
lemma unfurled (K:Molecule S): Together qq (fun i b=> (D (t i b)).bloom (Abide s χ U.K T M t i b) w U.a Q.table Q.halo K):=by
   let X n b:=Abide s χ U.K T M t n b; let Z i := standsIn (X i false) (R (t i false)) Q.halo K
   let f i b j:= (D (t i b)).tithe ((planted (X i b) K).taggedL j) (own K) w U.a Q.table Q.halo K
   have ht j : Walt qq bracket 0 (fun i b (_:ℝ)=> f i b j):= by
       let P i:= bod K (M i) s j
       exact Walt.stamp (keeps p hzM hu qV h P X' Z' hV (fun _=>rfl) K (fun i=> own K))
   have he := ((Walt.ready ((Fintype.card S.Choices:ℝ)⁻¹)).pay (Walt.schedule Finset.univ _ (fun j _=> ht j))) -- header
   apply (Walt.choose Z (he.excuse _) (Walt.ready 0)).atProbe.shimmy; filter_upwards with i; ext1 b'; unfold Leaf.bloom; simp only [show standsIn (Abide s χ U.K T M t i b') _ _ K=Z i from p.chairs qV.toKept K (t i b') (t i false) (M i)]; split <;> rfl

-- point lemma only analytic moments at health. no request progress on op q.
section stencil
omit h hu hV qV hzM [qq.IsCountablyGenerated]
variable (i:ι)(X:Coat (T i) F)(Y:E→ Config G c)(τ:E)(P:Molecule S)(hE : X.x=s)(ht:X.width=U.K)(hv:X.χ=χ)
      (hy:Mode Y τ k u)(hz : Y τ=X.V)(hh:(roster P).flags=∅)(hx:Healthy (temp s) ((H i).unionP P) X.V)

def spruce (t:S.Choices)(y:E):= let X':=(planted X P).taggedL t; ∫ x: F.Slice G × Air f G, (D i).carat (edgesM S ((H i).unionP P) (radiusB s)) X' (Y y) A Q.table P w U.a Q.halo x ∂((F.order G).prod X'.dice)

include hE hv ht hx hh hz hy p
lemma drove : (fun y=> (D i).picture (vary X (Y y)) P w U.a Q.table Q.halo)=ᶠ[𝓝 τ] if docked (H:=H) i P then (fun y=> (Fintype.card S.Choices:ℝ)⁻¹ * ∑ j,spruce (D:=D) (A:=A) (H:=H) i X Y P j y) else 0:=by
   let U' t:=(planted X P).taggedL t; let Y' i':= (D i).grove (vary X (Y i')) P w U.a Q.table Q.halo
   have he j:= ((p.realm.granted _ _ S _ _ _ (H i) (p.rails _) rfl).2 E Y F (U' j) τ hE hv ht (planted_valid X P) hz hy).1
   apply Filter.EventuallyEq.trans ((D i).runV X P (H i) hE ht hh hx he) (show Y' =ᶠ[𝓝 τ] _ from ?_)
   let I:=podium S G ((H i).unionP P) (radiusB s); let g j y:=(D i).cinema (vary (U' j) (Y y)) P w U.a Q.table Q.halo I
   have hh' : ∀ᶠ y in 𝓝 τ,∀ j,g j y=spruce (D:=D) (A:=A) (H:=H) i X Y P j y:= by
      apply eventually_all.mpr; intro j
      have hJ : Cash w ((U' j).x) q L Q U C (T i) (R i) := hE.symm ▸ H i
      have hU:= (D i).chutes (U' j) P hJ ht (planted_valid X P) (he j) p.realm.bay (by rw [show (U' j).x=s from hE,(H i).laws.data.funds.length_eq]; exact p.realm.foot)
      have hq : hJ.unionP P=(H i).unionP P:=by change ground _ _ Q.halo (radiusB X.x) _=_; rw [hE];rfl
      filter_upwards [hU] with v he; rw [hq, show (U' j).B=radiusB s from congr_arg _ hE] at he; exact he
   split
   next hv=>
      filter_upwards [hh'] with y hy; simp_rw [← hy]; unfold Y' Leaf.grove; rw [show (vary X (Y y)).B=radiusB s from congr_arg _ hE,if_pos (show Ac.Spark (areas (R i) (T i) Q.halo (radiusB s)) P ∧ troupe (T i) (R i) Q.halo (radiusB s) P from hv)]; apply congr_arg likely; funext t; exact ((D i).casin X P (H i) hE hh hx t (Y y) (Y y) (fun _ _ _=>rfl)).symm
   next hn=> filter_upwards with y; unfold Y' Leaf.grove; rw [show (vary X (Y y)).B=radiusB s from congr_arg _ hE,if_neg (show ¬(Ac.Spark (areas (R i) (T i) Q.halo (radiusB s)) P ∧ troupe (T i) (R i) Q.halo (radiusB s) P) from hn)]; rfl
end stencil
include hpV
lemma uplifts (K:Molecule S)(hh:(roster K).flags=∅)(hy:∀ n b,Healthy (temp s) ((H (t n b)).unionP K) (Y n (τ n)))(hz:∀ n,Y n (τ n)=(M n).bill) : Walt qq τ k (fun n b y=> (D (t n b)).picture (vary (Abide s χ U.K T M t n b) (Y n y)) K w U.a Q.table Q.halo):=by
   obtain ⟨y₀,h₀⟩:= (show ∀ᶠ i in v,True from by simp).exists; let n':= H y₀
   have hA i l : (H i).supportP l=(H y₀).supportP l:= congr_fun (p.zones qV.toKept i y₀ Q.halo (radiusB s)) l
   let q :=docked (H:=H) y₀ K
   have hx i : docked (H:=H) i K=q:=by unfold q docked; rw [funext (hA _),qV.toKept.phalanx T Q.halo (radiusB s) i]
   have hr i : (H i).unionP K= n'.unionP K:= p.riders qV.toKept i y₀ K
   let t0:=edgesM S (n'.unionP K) (radiusB s)
   let U' n b:=Abide s χ U.K T M t n b; let f j n b:= spruce (D:=D) (A:=A) (H:=H) (t n b) (U' n b) (Y n) K j
   have ht j: Walt qq τ k (f j):=by
      let P i:= bod K (M i) s j; have hp:= bough p hzM hu qV h P hpV (fun i=>⟨rfl,hz i⟩) X' Z' hV t0 K hy
      unfold f spruce; simp_rw [hr]; exact hp
   have hg i b:= drove (D:=D) p (t i b) (U' i b) (Y i) (τ i) K rfl rfl rfl (hpV i) (hz i) hh (by have hk:=hy i b; rw [hz] at hk; exact hk)
   by_cases hK:q
   · apply ((Walt.ready ((Fintype.card S.Choices:ℝ)⁻¹)).times (Walt.schedule _ f (fun j (_:j∈Finset.univ)=> ht _))).same
     filter_upwards with i b; have hu:= hg i b; rwa [hx,if_pos hK] at hu
   apply (Walt.ready (0:ℝ)).same; filter_upwards with i b; have hu:= hg i b; rw [hx,if_neg hK] at hu; exact hu
end YM.UVExtension.Wet
