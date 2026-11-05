import YM.RG08.Cast.Rate
import YM.Extra.WILSON_STARTUP.Design

/-!
# Diagonal analytic substitution on genuine curvature chart
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Crown
open Carrel Camera Room Cloud Glyph Function Finset MvPolynomial Filter Lattice
open Wilson WilsonStartup Design Exterior
open scoped ContDiff Topology PowerSeries BigOperators Classical RealInnerProductSpace
variable {G:YM.Gauge}{P:Side}

def pixel (G:YM.Gauge) (m:ℕ)(x:Forms.Tape m G.ColorIndex):ℝ:= Tensor.coeff (inK G) m 0 (fun i=>EuclideanSpace.basisFun G.ColorIndex ℝ (x i))
lemma happens (m:ℕ)(x:Forms.Tape m G.Color): Rudder.Symmetry.sing (pixel G m) x=Tensor.coeff (inK G) m 0 x:=extract_poly (Classical.arbitrary _) _ x

def orient (G:YM.Gauge):Still G.ColorIndex:=inK G ∘ heavy G
lemma guru (G:YM.Gauge):Camera.Pace (orient G):= ContDiffAt.comp (0:Cellar G.ColorIndex) (g:=inK G) (f:=heavy G) (by rw [(heavy G).map_zero];exact inK_diff) (heavy G).contDiff.contDiffAt

lemma orient_photo (G:YM.Gauge)(e:ℕ) :tap e (flask (orient G))=parley (pixel G e):=by
 apply MvPolynomial.funext;intro x
 rw [glimpses (guru G), parley, map_sum]
 let T:=(heavy G).toContinuousLinearMap
 have ht : iteratedFDeriv ℝ e (orient G) 0 (fun _=>x)=iteratedFDeriv ℝ e (inK G) 0 (fun _=>heavy G x):=by
   have he : ContDiffAt ℝ e (inK G) (T 0):=by rw [map_zero];exact inK_diff.of_le le_top
   unfold orient;change iteratedFDeriv ℝ e (inK G ∘ T) 0 _=_
   rw [Next.Foundations.jets_linear T he] -- lemma?
   rfl
 rw [ht]
 simp_rw [word,MvPolynomial.smul_eq_C_mul,eval_mul,eval_C,map_prod,eval_X] -- map_prod first unused
 exact (happens e (fun _=>heavy G x)).symm

lemma nil (G:YM.Gauge) : tap 0 (flask (orient G))=0:=by
 rw [flute,print];simp [orient,(inK_low (G:=G)).1,map_zero]
lemma absent (G:YM.Gauge)(e:ℕ)(he:Odd e):tap e (flask (orient G))=0:=by
 apply MvPolynomial.funext;intro x
 rw [orient_photo,parley,map_sum,map_zero];simp only [smul_eq_C_mul,eval_mul,eval_C,word,map_prod,eval_X]
 exact (happens e (fun _=>heavy G x)).trans (odd_diagonal _ e he)

-- now charge actual plaquette `g ⇒ exp(g)` energy, product in Same symbol, finite site

def sheet (G:YM.Gauge)(p:Site P)(i:PlaqAxes)(k:ℕ): Still (Bedge G P):= showAtom (extractAtom G i (Tensor.coeff (inK G) k 0)) p
def curvatureCells (p:Site P)(i:PlaqAxes):Camera.Strip G.ColorIndex (Bedge G P):= fun j=> Kiss G p (Design.plaquette i) j
lemma thumb(p:Site P)(i:PlaqAxes)(x:Cellar (Bedge G P)) : heavy G (Camera.roll (curvatureCells p i) x) = G.curvature (Lattice.faceValue (offers G x) (p,i)):=by
 ext j;change (Design.plaquette i).atSite (offers G x) p j=_;rw [at_plaquette]

lemma wardFace (p:Site P)(i:PlaqAxes):
    flask (fun x:Cellar (Bedge G P)=>G.price (faceValue (offers G x) (p,i)))=belt (rescaleFields (curvatureCells p i)) (flask (orient G)):=by
 rw [←flask_comp (h:=curvatureCells p i) (fun k=>filmed G 0 ..) (show Camera.roll _ 0=0 from funext (fun j=>by simp [Camera.roll,curvatureCells,kiss0])) (guru G)]
 apply flask_same
 have he: Tendsto (fun x:Cellar (Bedge G P)=>faceValue (offers G x) (p,i)) (𝓝 0) (𝓝 1):=by
    have ht : Continuous fun x:Cellar (Bedge G P)=>offers G x:= continuous_pi (fun i=>G.lieExp_cont.comp (offer G i).continuous)
    have hh := (Wilson.continuous_travel (G:=G) (square i.val.1 i.val.2) p).comp ht |>.tendsto 0
    rw [Function.comp_apply,offers_z] at hh
    simpa [Function.comp_def,faceValue,Lattice.square,travel,Step.read] using hh -- goal faceValue need unfold
 filter_upwards [he.eventually (recover_left G)] with x hx
 change G.price _= inK G (heavy G _); rw [thumb,inK,hx]
lemma article (p:Site P)(i:PlaqAxes)(k:ℕ) : flask (sheet G p i k)= PowerSeries.X^k * belt (rescaleFields (curvatureCells p i)) (liftInn (parley (pixel G k))):=by
 let f(j:G.ColorIndex):=curvatureCells (G:=G) p i j
 have he(j):Camera.Pace (f j):=filmed G 0 ..
 let U(b:Forms.Tape k G.ColorIndex):= ∏ l,f (b l)
 have ht b:Camera.Pace (U b):=by simpa only [U,←Finset.prod_apply] using (contDiffAt_prod (t:=univ) (f:=fun l=> f (b l)) (fun l _=>he _))
 have h:sheet G p i k=∑ b,(pixel G k b) • U b:=by funext z; simp only [Finset.sum_apply,U,Pi.smul_apply,Finset.prod_apply,sheet, showAtom,RG.Atom.unmasked,RG.Atom.poly,extractAtom,smul_eq_mul];rfl
 let Y:=rescaleFields (curvatureCells (G:=G) p i)
 have hb j: flask (f j) = PowerSeries.X * Y j:=(bumpout (show tap 0 _=0 from by simp [tap,f,curvatureCells,flask,print,kiss0])).symm
 rw [h,slurry _ _ (fun b _=>show Camera.Pace (pixel G k b • U b) from (ht b).const_smul (pixel G k b)), parley,map_sum,map_sum,Finset.mul_sum];apply sum_congr rfl; intro b _
 rw [flask_scale (ht b)];unfold U; rw [slurry_prod _ _ (fun _ _=>he _),MvPolynomial.smul_eq_C_mul,word];simp_rw [hb,Finset.prod_mul_distrib,_root_.map_mul,map_prod]
 change (pixel G k b) • _=(PowerSeries.X^k)* (belt _ (liftInn (MvPolynomial.C _))*∏ l,belt _ (rod (b l)))
 simp_rw [belt_x]
 rw [belt_c]
 unfold lug; rw [aeval_C];simp [Algebra.smul_def]; unfold Y; ring
end YM.RG08.Crown
