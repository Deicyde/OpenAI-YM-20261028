import YM.TraceExtension.Weir.Vole
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Weir
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels Next.Fluctuations Planned.AtomRegular.Foliage Next.SectorChange
open Wicket Outer.Nodes
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{x C:ℝ} {R:Rep G n}{S:Stage}{J:Dart G n}{A:Finset GreenA}{Q:Finset ℕ}
abbrev rimW(R:Rep G n)(Q:Finset ℕ)(x:ℝ)(Y:Axis→Gal G n)(b:Axis):Peat G n:= rill (loopP R x Q) (Y b)
abbrev swellW(R:Rep G n)(Q:Finset ℕ)(x:ℝ)(Y:Axis→Gal G n)(b:Axis):Peat G n:= rill (Zech R x Q) (Y b)
private lemma rho_cm(k:ℕ)(T:Collar G S.order)(a:Axis)(Λ:ℝ) (h: Splendor (boom (Meld J x) a 0) (ExtS n x) k (thinM x) C)(hp: HearthV (rill (mainP R x A) (YCore x J a)) (ExtS n x) k (thinM x) C)(hk:Age S x Λ R)(ha:S.order≤ k)(hx:∀ v:Directions G n,‖v‖≤ Cube.fee T→ Allows k (minor (relic R J x A a) (sash S x)) v (swole x))(hT:Cube.Wire R.p (high x) (hk.rank.symm ▸ T))(ht:1≤ x)(hn:20*(high x+10)<n.val) : Snow R (relic R J x A a) x (composeCost S.order (swole x) (Cube.fee T)):=by
   let P:=ExtS n x;let Z(U):= hp.choir (Directions G n) (increment U) _ (incrementA U 0); let f:= relic R J x A a; let F:= boom (Meld J x) a 0; let Q':= tempQ x (n:=n)
   have hL: LocalOn P f:= fun u v hx=> congr_arg (R.beta •·) (congr_arg₂ (· - ·) (h.locale u v hx) (hp.pillar u v hx))
   have hR:R.p.Regular Q' f:= regularAi (fun k U=> congr_arg (R.beta •·) (congr_arg₂ (·-·) (h.symm k U) (hp.symU k U))) (fun U V hv=> hL U V (agrees_mono hv (coe_subset.mpr (dec_b ..|>.2)))) (fun U=> ((ContDiffAt.const_smul (c:=R.beta) ((h.lit U).sub (Z U))).of_le le_top));
   refine ⟨hR,?_⟩; let T':Collar G R.p.order:=hk.rank.symm ▸ T; have ht':=fees_eq T hk.rank.symm; have hC := lends hR (fun _ h=>h) hL (by omega) T' hT (show 0 ≤ swole x by unfold swole; positivity) (fun u hu=> ?_); rotate_left
   · rw [← shifts x S Λ R hk]; exact Offset.Through.control ((hx u (ht' ▸ hu)).order (hk.rank.le.trans ha))
   rw [ht',hk.rank] at hC; exact hC
-- package gym
structure Merch (R:Rep G n)(x:ℝ)(J:Dart G n)(A:Finset GreenA)(Q:Finset ℕ)(m:ℕ): Prop where
   relicC i: Snow R (relic R J x A i) x (crumb x)
   loop i : ClimateJ R (rimW R Q x (YCore x J) i) x (trayF x) (wideM x)
   lones i : ClimateJ R (swellW R Q x (YCore x J) i) x (crumb x) (calorie x)
   weld i : rimW R Q x (YCore x J) i = rill (quietL R x Q) (YCore x J i)-swellW R Q x (YCore x J) i
   bloom i:20*(high x+rim x+10)< n.val→ Loft.Holt i (fun b=>rill (quietL R x Q) (YCore x J b) ∘ input G n)=0
   tune i: Snow R (kerr x m (YCore x J i) (ochre R x A Q)) x (crumb x)
abbrev hornA(R:Rep G n)(J:Dart G n)(x:ℝ)(m l:ℕ)(b:Axis):Peat G n:=callX R (Shepherd.field R l) (YCore x J b) (peace x) m (Bay n x)
structure Wholesome (R:Rep G n) (x:ℝ)(J:Dart G n)(v m q:ℕ)(S:Stage)(Z Λ C:ℝ):Prop where
   base : ToolF m q (Cleft x q) x (peace x) R
   solace: Craft S x R J v C
   pay : Wealth S R x J
   season b: Garden x Λ m Z S R (YCore x J b)
   crops(ε:ℝ)(hv:0< ε):∀ᶠ A:Finset GreenA in atTop,∀ᶠ Q:Finset ℕ in atTop,∀ᶠ P:Finset ℕ in atTop, Merch R x J A Q m ∧ Drift _ (ochre R x A Q) ∧ ∀ b:Axis,
       let K:= shelves n A Q P; let Y:=YCore x J b; Depot R x K q m Y (ochre R x A Q) (swole x) ∧ ∀ u:Config G n,|hornA R J x m q b u- callX R (cabinet R q K) Y (peace x) m (Bay n x) u| ≤ ε
lemma Inspires(G:Gauge)(h:G.Simple)(S:Stage)(m d:ℕ)(hm:48≤ m)(T:Collar G S.order):∃ Z C:ℝ,0 < Z∧0 ≤ C∧∀ᶠ x:ℝ in atTop,∀ (q:ℕ),1100≤ q→ q≤ towerH x d→∀ (Λ:ℝ)(n:Side)(R:Rep G n)(J:Dart G n), Sight x R J→ Age S x Λ R→20*(high x+10)<n.val→ Wholesome R x J (S.order+m+1) m q S Z Λ C:=by
   let k:=S.order+m+1
   have hk:S.order≤k:=by unfold k;omega
   obtain ⟨C,hC,H⟩:=net G h S k hk T
   obtain ⟨K,hK,hp⟩:= shimmer G S k hk T
   obtain ⟨A,hA,hF⟩:= pack G S m d T (by omega)
   obtain ⟨Z,U,hZ,hU,hP⟩:=glory G S m d k T
   let T':=Cube.fee T; have ht:1 ≤T':= Cube.fee_one T
   obtain ⟨D,L,hD,hL,hc,hx⟩:= rocket G h S T' (C+K+A+U) ht S.order m (by have hr:=S.order_ge; omega) hm
   obtain ⟨W,hW,hD'⟩:=cast_shape G S m d T
   have hc1:C ≤ L:= le_trans (by linarith only [hK,hA,hU] : C ≤ C+K+A+U) hc; have hc2:K ≤ L:=by linarith
   have hc3:A ≤ L:=by linarith
   have hc4:U ≤ L:=by linarith
   refine ⟨Z,L,hZ,hL,?_⟩;
   filter_upwards [H,hF,hx,hP,hD',wnt S T' ht S.order,eventually_gt_atTop (1:ℝ),Work.E01.radiusB_tendsto.eventually_ge_atTop 2] with x hx hA hQ hg hd hh he hR q hq hq' Λ n R J hj hS hn
   have HT:=hQ n R J hS.hM hj hS.beta; obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇⟩:=hd q hq hq' Λ n R hS
   have H1: Craft S x R J k L:= HT.1; refine ⟨h₁,H1,hx _ _ _ _ _ hS h₅ hn H1 hc1,fun i=> hg n Λ _ _ hS (H1.cloud _) (Zn.follower _ _ _ _ _ _ hc4 (H1.climate i) le_rfl),fun ε hε=>?_⟩
   have hpU(b:Axis): ∀ᶠ X:Vest n in atTop,∀ u:Config G n,|hornA R J x m q b u-callX R (cabinet R q X) (YCore x J b) (peace x) m (Bay n x) u| ≤ ε:= recallH R _ m _ _ hε hS.good hS.coverage hS.dialect hS.high (H:=H1.cloud _)
   obtain ⟨Y,hY⟩:= eventually_atTop.mp (eventually_all.mpr hpU)
   filter_upwards [HT.2,tallShelves n Y,H1.cores] with l hl hL H2
   filter_upwards [hl,hL,H1.milks] with i hi hQ H3
   filter_upwards [hQ] with p hN
   let Tl:= ochre R x l i; have HV:Tl=Tl:=rfl; obtain ⟨ht,hv,hE,hX⟩:=hi; obtain ⟨ht₁,ht₂,ht₃,h4,h5,h6,h7⟩:=H3; refine ⟨⟨fun b=> ?_,fun b=>?_,fun b=> ?_, h4, h7,fun b=>?_⟩,hv,fun b=> ⟨?_,hY _ hN b⟩⟩
   · let u:=boom (Meld J x) b; have hP: Splendor (u 0) (ExtS n x) k (thinM x) L:= ((H1.bounce b).read 0).up (sprout_mono _ (by unfold high; omega)) le_rfl
     exact (rho_cm k T b Λ hP (H2.2.2.2.1 b) hS hk (hX b) h₅ he.le hn).raise hh.2.2.2
   · exact (hp x Λ n R hS h₅ (by omega) _ _ (Or.inr (mot k _ _ _ _ _ _ hc2 (h5 b) le_rfl))).plus (hh.1 _ le_rfl) le_rfl
   · exact (hp x Λ n R hS h₅ (by omega) _ _ (Or.inr (mot k _ _ _ _ _ _ hc2 (h6 b) le_rfl))).plus (hh.2.2.1) le_rfl
   · exact (caskCover m T x he.le Λ D R (hE b) hS h₅ hn).raise hh.2.2.2
   exact hA q hq hq' n Λ R hS (YCore x J b) _ _ (H1.cloud _) (Zn.follower _ _ _ _ _ _ hc3 (H1.climate b) le_rfl) (Zn.post k _ _ _ _ _ _ hc3 ht le_rfl) hv hn
end YM.Trace.Weir
#print axioms YM.Trace.Weir.Inspires
