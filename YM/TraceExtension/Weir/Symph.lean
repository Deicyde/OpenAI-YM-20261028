import YM.TraceExtension.Weir.Dolio
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Weir
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels Next.Fluctuations Planned.AtomRegular.Foliage Next.SectorChange
open Wicket Outer.Nodes
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{x Λ C:ℝ} {R:Rep G n}{S:Stage}{J:Dart G n}{A:Finset GreenA}{Q:Finset ℕ}
abbrev altF(R:Rep G n)(x:ℝ)(J:Dart G n)(m:ℕ)(A:Finset GreenA)(Q:Finset ℕ)(b:Axis):Peat G n:= relic R J x A b+ stubJ (lush (YCore x J b))-rimW R Q x (YCore x J) b + kerr x m (YCore x J b) (ochre R x A Q)
abbrev rotateK(R:Rep G n)(x:ℝ)(m:ℕ)(J:Dart G n)(b:Axis)(A:Finset GreenA)(Q:Finset ℕ)(i:Tides n G) : Peat G n:= (teas i m/peace x) • (radarT R (YCore x J b) (ochre R x A Q) (peace x) i)
abbrev composedZ(R:Rep G n)(x:ℝ)(J:Dart G n)(m:ℕ)(q:ℕ)(A:Finset GreenA)(Q D:Finset ℕ)(b:Axis):Peat G n:=altF R x J m A Q b+∑ j∈stemsM R (shelves n A Q D) x m q,rotateK R x m J b A Q j
lemma outE(X Y:Peat G n)(h:Drift _ X)(hx:Drift _ Y)(U:Config G n)(K:Gal G n)(v:ℝ):rill (v • X-Y) K U=v*rill X K U - rill Y K U:=by
    unfold rill beamG; have hv:Army (fun y:Link G n=>input G n y*U) 0:= (Army.powL (v:=id) contDiffAt_id).mul (Army.park U _)
    have hy : DifferentiableAt ℝ (bal U X) 0:= (h _ _ _ hv).differentiableAt (by simp)
    rw [show bal U (v•X-Y)=v • bal U X-bal U Y from rfl,fderiv_sub (hy.const_smul _) (show DifferentiableAt ℝ (bal U Y) 0 from (hx _ _ _ hv).differentiableAt (by simp)),fderiv_const_smul hy];rfl
-- relation sign checked: ∆ boom investor.Anc=Lush(const)-Beta stressMetric + Corrections. Rotational average taken later cancels `const`.
lemma Symphony (m q k:ℕ)(R:Rep G n)(h:Age S x Λ R)(hp:ToolF m q (Cleft x q) x (peace x) R)(hX:Craft S x R J k C)(hn:1 ≤ x)(A:Finset GreenA)(Q D:Finset ℕ)(b:Axis) (hV:Depot R x (shelves n A Q D) q m (YCore x J b) (ochre R x A Q) (swole x))(he: Drift _ (ochre R x A Q)) (U:Config G n)(hv:Healthy (R.p.threshold/16) (tower (Cleft x q)) U):
   let Y:= YCore x J b; let G':= cabinet R q (shelves n A Q D); callX R G' Y (peace x) m (Bay n x) U/peace x= composedZ R x J m q A Q D b U - R.beta* boom (Meld J x) b 0 U+ lush Y 1:=by
   intro Y V; let u:= peace x; let F:= ochre R x A Q; let Z:=atuneU m Y F u (ExtS n x); let X:=stemsM R (shelves n A Q D) x m q; have hz:0 < u:= (pet x hn S).2.1
   have hZ: callX R V Y u m (Bay n x) U= tDust m Y F (ExtS n x) u U +∑ i∈ X,teas i m*radarT R Y F u i U :=calls_sum A Q D R m q (Cleft x q) _ (hX.cloud _) h.good hp he hV.flag hv
   have hu : ∑ i∈X, (rotateK R x m J b A Q i U)= (∑ i∈X,teas i m*radarT R Y F u i U)/peace x:=by rw [Finset.sum_div]; refine sum_congr rfl (fun i _=>?_); change (teas i m /peace x)*radarT R Y F u i U=_; ring
   change callX R V Y u m (Bay n x) U/u =_; rw [hZ,erum m F Y (ExtS n x) ((hX.cloud b).wider (dec_b ..|>.1)) he]; rw [show rill F Y U= (- R.beta*rill (mainP R x A) Y U - rill (loopP R x Q) Y U) from outE _ _ (Pills.hymn R legF _ _) (Pills.hymn R loopF _ _) U Y (-R.beta)]
   unfold composedZ; rw[Pi.add_apply,Finset.sum_apply, show ∑ i∈_, _= _ from hu]
   change (Z U + u*_ +_ )/_= (R.beta*(boom (Meld J x) b 0 U-rill (mainP R x A) Y U)+(lush Y U-lush Y 1)-rill (loopP R x Q) Y U+u⁻¹*Z U)+ (∑ i∈X,_)/u -_+_
   field_simp; ring
end YM.Trace.Weir
#print axioms YM.Trace.Weir.Symphony
