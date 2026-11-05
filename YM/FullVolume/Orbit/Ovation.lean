import YM.FullVolume.Orbit.Bear
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Apse
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Empire
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {K : Teller G} {p a W U : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' Q : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi} {F : Tree.Forest S.ratio}
variable {P:BudgetPoint}
open Match Refrain
variable {s:Signed}{b:Site c}
-- permutations match true lexicon. From local T any chamber with same label layout. No assertion comparing N,m until stable address. Use π of given E.
def footing (H:Cash W p a L₀ X o U T R) (K:R.activities.Moves s (S.ratio.embed b)) := Refrain.congo (badge H) (Equiv.sumCongr (Refrain.congo (Refrain.gate H (staple (J:=H) rfl rfl rfl)) (Refrain.gate H (Match.swing H K))) (Equiv.prodCongr (Equiv.refl ℕ) (StepData.sendSites s b)))
def changeling (H:Cash W p a L₀ X o U T R) (K:R.activities.Moves s (S.ratio.embed b)) : Emote := ⟨congo (Song.pennant H) (Song.whirl s b), Apse.footing H K⟩
lemma changing (H:Cash W p a L₀ X o U T R) (P:BudgetPoint)(K:R.activities.Moves s (S.ratio.embed b))(l:ℕ)(γ:ℝ):
   amid (changeling H K) ((Beam.marquee H P).read (Meadow.timbres (staple (H:=H) (J:=H) rfl rfl rfl) (χ:=χ) γ l)) s b:=by
  let X:=staple (J:=H) (H:=H) rfl rfl rfl; let T : Equiv.Perm (Refrain.Leaf H):= congo (Refrain.gate H X) (Refrain.gate H (swing H K))
  let f:= Equiv.sumCongr T (Equiv.prodCongr (Equiv.refl ℕ) (StepData.sendSites s b)); let a:=Song.pennant H; let k:=badge H
  have hη : ∀ i:Refrain.Annual H,(reserve H (f i)).support = (reserve H i).support.image (affine s b) ∧ (reserve H (f i)).inventory=(reserve H i).inventory.image (affine s b) ∧ ∀ U, ((reserve H (f i)).extraTest U↔(reserve H i).extraTest (pull s b U)) ∧ fuse H X χ (f i) U=fuse H X χ i (pull s b U):=by
    rintro (i|⟨i,b'⟩)
    · have hk U := buoyant H X χ s b K T i U (perch (Refrain.gate H X) _ i)
      simp only [f,Equiv.sumCongr_apply,Sum.map_inl]
      exact ⟨(hk 1).1,(hk 1).2.1,fun U=> ⟨Iff.rfl,(hk U).2.2⟩⟩
    simp only [f,Equiv.sumCongr_apply,Sum.map_inr]; simp [Refrain.reserve,Refrain.fuse,Lattice.affine]; rfl
  let e:=Song.whirl (ι:=Magazine H) s b
  have hk i : k (congo k f i)=_ := perch k f i; have ha i : a (congo a e i)=_ := perch a e i
  let j:= Meadow.hKeep X (χ:=χ) γ l; let h x:= spirit (Beam.contents H P) j s b x
  refine ⟨⟨congo a e,congo k f,fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_,fun i V=>?_,fun i V=>?_,fun i V=>?_⟩,rfl,rfl⟩
  · change (revolve _ (a (congo a e i))).site=_; rw [ha]; exact (h _).1
  · change (revolve _ (a (congo a e i))).support=_; rw [ha]; exact (h _).2.1
  · change (reserve H (k (congo k f i))).support=_; rw [hk]; exact (hη _).1
  · change (reserve H (k (congo k f i))).inventory=_; rw [hk]; exact (hη _).2.1
  · change (reserve H (k (congo k f i))).extraTest V ↔ _; rw [hk]; exact ((hη (k i)).2.2 V).1
  · change choir _ (a (congo a e i)) V=_; rw [ha]; exact congr_fun (h (a i)).2.2 V
  change fuse H X χ (k (congo k f i)) V=_; rw [hk]; exact ((hη (k i)).2.2 V).2
lemma changeling_eq (Y:R.activities.Moves s (S.ratio.embed b))(Z:R'.activities.Moves s (S.ratio.embed b)) (h:R.path=R'.path)(hv:R.activities.reg=R'.activities.reg) (hf:R.activities.forced=R'.activities.forced)(he:Y.ep=Z.ep)(hh:Y.kp=Z.kp): changeling H Y=changeling I Z:=by
  rcases R with ⟨u,c,⟨e',s,v,k⟩,p,b,t⟩; rcases R' with ⟨u',d,⟨a,D,V,i⟩,p',b',t'⟩; cases h; cases hv; cases hf; rcases Y with ⟨e,f,_,_,_,_,_,_,_⟩; rcases Z with ⟨y,z,_,_,_,_,_,_,_⟩; cases he; cases hh; rfl
end YM.PhysicalNext.Repeat.Apse
