import YM.TraceExtension.Zn.Smoke
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Zn
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft Xo
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {F:ℝ→ℝ}{a b c:ℝ}{k:ℕ}{G:Gauge}{n:Side}
def thinM(x:ℝ):ℝ:=Wave (1/200) x
def wideM(x:ℝ):ℝ:= Wave (1/50) x
def humble(x:ℝ):ℝ:=Wave (1/1000) x * 2
abbrev Meld (J:Dart G n)(x:ℝ):= paceX (rim x) J
def puff(x:ℝ):=4*(rim x+1+1)
def high(x:ℝ):=1800*(radiusB x + rim x)+puff x
abbrev Bay (n:Side)(x:ℝ):=sprout (0:Site n) (puff x)
abbrev ExtS(n:Side)(x:ℝ):=sprout (0:Site n) (high x)
abbrev YCore(x:ℝ)(J:Dart G n)(b):= lakesY 0 (rim x) (J.Y b 0)
def Made (S:Stage)(x:ℝ)(R:Rep G n):Prop:= R.clip=S.clip ∧ R.p.B=radiusB x ∧ R.path.Bounds S.clip S.width S.paths (humble x)
abbrev Sight (x:ℝ)(R:Rep G n) (Q:Dart G n):Prop:= Viz Q R.clip R.path (Perfect.east x) (fun _=> trophy x) (fun _=>shock x) (shock x) ∧ Q.March
def eastD(x:ℝ):=Perfect.east x/100
def calorie(x:ℝ):ℝ:= (x^(30:ℕ))⁻¹
abbrev mainP (R:Rep G n)(x:ℝ)(U:Finset GreenA):= prun R legF (Bay n x) (spikes R legF U (rim x))
abbrev loopP (R:Rep G n)(x:ℝ)(U:Finset ℕ):= prun R loopF (Bay n x) (spikes R loopF U (rim x))
-- sigma quiet + misc for PSC
abbrev leafL (R:Rep G n)(x:ℝ)(L:Finset ℕ):= ink (spikes R loopF L (rim x)) R.path.loop
abbrev Zech (R:Rep G n)(x:ℝ)(L:Finset ℕ):= paper univ (leafL R x L) (n:=n)
abbrev quietL (R:Rep G n)(x:ℝ)(L:Finset ℕ):= paper (swat (spikes R loopF L (rim x))) (shade (spikes R loopF L (rim x)) R.path.loop) (n:=n)
structure Craft (S:Stage) (x:ℝ)(R:Rep G n)(J:Dart G n)(k:ℕ)(A:ℝ):Prop where
   -- Perturbed stress stencils. Can use Bond.through any radius k stage.
   peak (i j:Axis) : Turret.Bond (J.J i j) (Meld J x i j) k (puff x+1) (eastD x) (thinM x) (calorie x) A
   plum (i): Turret.Bond (J.Q i) (pluck (rim x) J i) k (puff x) (eastD x) (thinM x) (calorie x) A
   pearl (i j a:Axis) : Turret.Bond (J.twist i j a) (pluckD (rim x) J i j a) k (puff x) (eastD x) (thinM x) (calorie x) A
   bounce (i): Turret.Bond (boom J.J i) (boom (Meld J x) i) k (puff x+1+4) (eastD x) (thinM x) (calorie x) A
   cloud (a:Axis) : Clouded (YCore x J a) (Bay n x)
   climate (i): Climate (YCore x J i) k (thinM x) A
   errors (a:Axis): Estate (0:Site n) (bottom (J.Y a 0-YCore x J a)) (eastD x) (fun _=> calorie x)
   earning (i:G.ColorIndex) : |midPay i J -(Holt i (fun b=>stubJ (lush (YCore x J b)) ∘ input G n)).re| ≤ calorie x
   -- all sufficient finite cuts.Capital stress response
   cores : ∀ᶠ L:Finset GreenA in atTop,
       Splendor (mainP R x L) (ExtS n x) k (thinM x) A ∧ Drift _ (mainP R x L) ∧ (∀ i, rill (mainP R x L) (YCore x J i)= rill (piste R legF (spikes R legF L (rim x))) (YCore x J i))∧(∀ i, HearthV (rill (mainP R x L) (YCore x J i)) (ExtS n x) k (thinM x) A) ∧
       ∀ i,Allows 4 ((boom (Meld J x) i 0-rill (mainP R x L) (YCore x J i)) ∘ input G n) 0 (calorie x)
   milks : ∀ᶠ L:Finset ℕ in atTop,
       Splendor (loopP R x L) (ExtS n x) k (wideM x) A ∧ Drift _ (loopP R x L) ∧ (∀ i, rill (loopP R x L) (YCore x J i)= rill (piste R loopF (spikes R loopF L (rim x))) (YCore x J i))∧
       (∀ i, rill (loopP R x L) (YCore x J i)=rill (quietL R x L) (YCore x J i)-rill (Zech R x L) (YCore x J i)) ∧ (∀ i, HearthV (rill (loopP R x L) (YCore x J i)) (ExtS n x) k (wideM x) A)∧
       (∀ i, HearthV (rill (Zech R x L) (YCore x J i)) (ExtS n x) k (calorie x) A) ∧ ∀ a:G.ColorIndex, 20*(high x+rim x+10)< n.val→ Holt a (fun i=>rill (quietL R x L) (YCore x J i) ∘ input G n)=0
   jack(i):Drift _ (stubJ (lush (YCore x J i)))
   jump(i):∀ (X:Type)[NormedAddCommGroup X][NormedSpace ℝ X](V:X→ Config G n)(o:X), (∀ e,Allows (k+1) (fun y=>G.mat (V y e)) o A)→Allows k (lush (YCore x J i) ∘ V) o (thinM x)
end YM.Trace.Zn
