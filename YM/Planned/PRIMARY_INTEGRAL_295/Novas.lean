import YM.Planned.PRIMARY_INTEGRAL_295.Pomp
/-!
# exact no-hole LXE candidate physical covariance

This isolates all main-cost CHART equations for one represented true
history height in one Spec.Core compatible Tube.A (pre.H). ρ real actual threshold.
Not any existence theorem, kernel identity etc. Lantern inv on ACTUAL V even
if α outside not-yet declared weak region. Will restrict calls after. Shape of
post-I gives Passport canonical.Axis high for forward costs. Accounts masks soft
entropy *elsewhere separately*. H oriented law for integral requires Teller.Branches,
PSD of destination (from activated Charter). -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Novas
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform Sparks Night Hives Candles Barges Hoods Flairs Pomp
open Next.Fluctuations Work.E03 Icebergs Tropics Kelps Nimbuses
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G:Gauge} {c f : Side} {d:ℕ} {F:Labels.Frame G d} {S:StepData c f}

structure Torch (G:Gauge)(S:StepData c f) where
    clan : Bank G S
    tube : Tube G S
    k : S.Choices
    R : ℕ
    ε : ℝ
    shine : Pulse G

namespace Torch
variable (P:Torch G S)
def core : Core G S:= ⟨P.tube,P.clan.tree,P.k,P.R⟩

abbrev Index:= P.clan.keys
abbrev Starry:=Sky P.Index
def rolled (A:Matrix (Acres f G) (Acres f G) ℝ): Matrix P.Index P.Index ℝ:= P.clan.homes.coin (head P.clan A)
def muster (A:Matrix (Acres f G) (Acres f G) ℝ) (w:Temps G f):P.Starry := WithLp.toLp 2 (P.clan.homes.morn (head P.clan A) (w ∘ Subtype.val))

-- Gush data.LXE absolute.V t denominator in epithelial b/y Norman.
-- profile on I. Held.Eta log time.
def staged (V:Config G c):Matrix P.Index P.Index ℝ:= rolled P (dark P.core V)
def stamp (V:Config G c)(t:ℝ):P.Starry:= muster P (dark P.core V) (t⁻¹ • foams P.core V)

def mist := footage P.clan.tree G P.clan.held

def keel (V:Config G c)(t ξ:ℝ)(x:P.Starry): Config G f:= lifting P.clan.tree V (t • (P.mist (P.stamp V t)+ ξ • P.mist x))

@[fun_prop] lemma keel_fine (V:Config G c)(t ξ:ℝ):Continuous (P.keel V t ξ):=by
   unfold keel lifting; apply Forest.continuous_drape P.clan.tree|>.comp
   apply continuous_pi; intro i; fun_prop

def lamps (ξ:ℝ):= halo P.clan.held P.shine ξ P.ε -- ambiguity lattice.halo?
lemma lamps_fine (ξ:ℝ): Continuous (P.lamps ξ):=continuous_finsetProd _ fun _ _=> P.shine.hk.continuous.comp (ContinuousLinearMap.continuous _)

def heap (V:Config G c) (t ξ:ℝ)(T:SectionData F)(i:F.Index):= fun x:P.Starry=> P.lamps ξ x • ((t^(F.grades i).2)⁻¹ •
       T.places (Place.copy F i) 0 (P.keel V t ξ x))

def quest (V:Config G c)(t ξ:ℝ)(T:SectionData F)(i:F.Index):ℂ:=∫ x:P.Starry,P.heap V t ξ T i x∂multivariateGaussian 0 (P.staged V)

variable (z:Site c → G.El) (V:Config G c)(hb:S.patch.Branches S.kernel G)
def vapor (z:Site c→ G.El): (P.Starry→L[ℝ]P.Starry) := MapB P.Index ((harp P.clan).paint (flatten (S:=S) z))
lemma vapor_cloud (x:P.Starry) (i:P.clan.held):
      facet P.clan.held G i (P.vapor z x)= G.adjoint (flatten (S:=S) z i.val.val) (facet P.clan.held G i x):=by
   let h:= harp P.clan; let w:=flatten (S:=S) z; ext j
   have he := congr_fun (Hive.pigment h w (WithLp.ofLp x)) (i,j); exact he
lemma vapor_mist (x:P.Starry)(i:P.clan.tree.Free): P.mist (P.vapor z x) i=G.adjoint (flatten (S:=S) z i.val) (P.mist x i) :=by
   unfold mist; rw [Icebergs.withered,Icebergs.withered]; split
   · exact P.vapor_cloud z x _
   rw [map_zero]
lemma vapor_lamps (x:P.Starry) (ξ:ℝ):P.lamps ξ (P.vapor z x)=P.lamps ξ x :=by
   unfold lamps Icebergs.halo; apply Finset.prod_congr rfl; intro y _
   let c:= ξ/P.ε; let Q:=facet P.clan.held G y;
   change P.shine.χ (c • Q (P.vapor z x))= P.shine.χ (c • Q x); refine P.shine.radial _ _ ?_
   rw [norm_smul,norm_smul, show Q (P.vapor z x)=G.adjoint (flatten (S:=S) z y.val.val) (Q x) from P.vapor_cloud z x y,G.norm_adjoint]
include hb

lemma garment (t:ℝ): let W:=Lattice.gauge z V; let M:=P.clan
      Crown (harp M) (harp M) (flatten (S:=S) z) (flatten (S:=S) z) (P.staged V) (P.staged W) ∧ P.vapor z (P.stamp V t) = P.stamp W t :=by
   obtain ⟨hx,hf⟩:= kernels P.core z V hb
   intro W M; let z':=flatten (S:=S) z; let A:=head M (dark P.core V); let q:= (t⁻¹ • foams P.core V) ∘ (Subtype.val:M.grounds→_)
   let hA:= tilted M hx
   refine ⟨coincided (inward M) M.homes hA (members M) (stay M),?_⟩
   let g:=(t⁻¹ • foams P.core W) ∘ (Subtype.val:M.grounds→_)
   have ht : (housing M).burn z' q = g:=by
     have he:= (literal (harvest (f:=f) (G:=G)) _ (heldFull M)).list (t⁻¹ • foams P.core V) z'
     refine he.symm.trans ?_; unfold g W; rw [hf,map_smul]
   have hg:=morale (inward M) M.homes hA (members M) (stay M) q
   apply PiLp.ext; intro i
   unfold vapor stamp muster; unfold MapB; rw [toEuclideanCLM_toLp,Hive.pigment]; exact congr_fun (hg.trans (congr_arg _ ht)) i

lemma broad (t ξ:ℝ)(x:P.Starry): P.keel (Lattice.gauge z V) t ξ (P.vapor z x) = Lattice.gauge (z∘S.ratio.parent) (P.keel V t ξ x):=by
   have he:= (P.garment z V hb t).2; let W:= P.clan.tree; unfold keel; rw [← he]
   let a:=z∘S.ratio.parent; funext i; by_cases hp : i∈ W.trunks
   · have hm : S.ratio.parent (i.1+step i.2)=S.ratio.parent i.1:=W.trunk_internal hp -- check
     unfold Lattice.gauge; exact (W.on_tree _ ⟨i,hp⟩).trans (by symm; rw [show lifting W V _ i=1 from W.on_tree _ ⟨i,hp⟩]; simp [Function.comp_apply,hm]) --rw weak
   let q : W.Free:=⟨i,hp⟩
   have hz (V:Config G c) (b:AxisChart G W):lifting W V b i=G.lieExp (b q)*replica S.ratio V i:= W.off_tree _ q
   let A:=P.vapor z; let y:=P.stamp V t; let D:= t • (P.mist y+ ξ • P.mist x); let E:= t • (P.mist (A y)+ ξ • P.mist (A x))
   change lifting W _ E i=a _*lifting W _ D i*(a _)⁻¹; rw [hz,hz,← copied S.ratio S.patch.odd_side]
   have hs : E q=G.adjoint (a i.1) (D q):=by
      unfold E D A; simp only [Pi.smul_apply,Pi.add_apply,P.vapor_mist,map_smul,map_add]; rfl
   rw [hs]
   have he (x:G.El)(v:G.Color):G.lieExp (G.adjoint x v) = x*G.lieExp v*x⁻¹:=by apply G.mat_injective; simp [G.mat_adjoint,G.exp_conjugate]; rfl
   rw [he]; unfold Lattice.gauge; change a i.1 * _*(a i.1)⁻¹ * (a i.1*_*(a _)⁻¹)=_; group

end Torch
end YM.Planned.PrimaryIntegral295.Novas
