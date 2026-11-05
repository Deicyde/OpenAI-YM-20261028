import YM.Planned.PRIMARY_INTEGRAL_295.Chrysalis
import YM.Planned.PRIMARY_INTEGRAL_295.Honey
/-!
# group preGram (for genuine V on the same physical step)

Represents only no-hole calculation! Raw identity with labels not supplied. This
NOT an effective kernel. D2 here defined by curvature of relative group
Q (derivative exactly Q-row of E at identity, when paid). Useful to have
equivariant total definition on irrelevant inputs, e.g. for Q's far away
arg positions outside stencil. Poster supplies actually USED K in weak V
stencil; never uses fderiv-junk there. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Night
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice RG Wilson Pressure Labels Source Extra.Histories -- no Source.Drops
open Warehouse Precision Exterior Tree Carrier Bloch Next.Free Progress.StationaryScenes Bazaars Launch Shapes
open Next.Foundations Vintage Spurs 
open Streets
open Villa Floor Glints Fizz Fizz.Gush   Cabins  Little Density Little.Core Push.Uniform Honey 
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n c f : Side} {d : ℕ} {F : Labels.Frame G d} {S:StepData c f}

variable (K:Core G S)
-- absolute radius stencil. tree free normalized by p implicit, derivative
-- directions here ALL unnormalized, including v-axis. default off-charge.
def upload (V : Config G c)(a:Temps G f):= increment (replica S.ratio V) (collect G (K.reachable a))

def owl (s:Signed) (V:Config G c)(a:Temps G f):=pull s 0 (upload K V a)
def corn (s:Signed) (V:Config G c)(a:Temps G f):=S.prediction (owl K s V a) (Push.SectorMeasure.Oriented.choice s K.k)

-- E.ff0 actual physical b before derivative. oriented profile averaged
-- through d rows in one Cov.Comment separately.
def voile (s:Signed) (V:Config G c)(p:Twin f):= K.tube.Xf K.R (owl K s V 0) p - Pressure.zip (K.tube.Φ K.R (pull s 0 V)) (K.tube.Xn K.R (pull s 0 V)) p
def soave (s:Signed) (V:Config G c)(p:Bond c):= Pressure.Tube.Z S (corn K s V 0) (pull s 0 V) p - Pressure.zip (K.tube.Φ' K.R (pull s 0 V)) (K.tube.Xn K.R (pull s 0 V)) p
def garth (v:Drops c f) (V:Config G c):= v.2.elim (voile K v.1 V) (soave K v.1 V)

def crease (s:Signed) (V:Config G c)(p:Twin f)(a:Temps G f):= if p.2 then ∑' i,K.mbTerm (owl K s V 0) (owl K s V a) p.1 i else shoot K.tube.high (owl K s V a) p.1
def gruel (s:Signed) (V:Config G c)(p:Bond c)(a:Temps G f):= (-Real.sqrt S.kernel.penalty) • G.curvature (corn K s V a p*(corn K s V 0 p)⁻¹)
def logs (v:Drops c f) (V:Config G c)(a:Temps G f):= v.2.elim (fun p=>crease K v.1 V p a) (fun p=>gruel K v.1 V p a)

def F₀ (V:Config G c) (i:Seats G c f) := ballast * garth K i.1 V i.2
def keel (v:Drops c f) (V:Config G c) := fderiv ℝ (logs K v V) 0

def dowel (V:Config G c): Matrix (Seats G c f) (Acres f G) ℝ := Matrix.of fun i j=> ballast * keel K i.1 V (Pi.single j 1) i.2

def dark (V:Config G c): Matrix (Acres f G) (Acres f G) ℝ:= (dowel K V).transpose*dowel K V+ K.fires
def foams (V:Config G c) : Temps G f:= (dowel K V).transpose.mulVec (F₀ K V)

section Verdicts
lemma F₀_eq (a:Dir G c): F₀ K (represent a)=K.F0 a:=by rfl
-- Fréchet derivative equal
private lemma curv_d(G:Gauge)(z:ℝ): HasFDerivAt (fun x:G.Color=>z • G.curvature (G.lieExp x)) (z • ContinuousLinearMap.id ℝ _) (0:G.Color):=by
   refine HasFDerivAt.const_smul (f:=fun y:G.Color=> G.curvature (G.lieExp y)) (f':=ContinuousLinearMap.id ℝ _) ?_ z; let f:=G.curvature∘G.lieExp
   have hx : ContDiffAt ℝ ω f 0 := Next.Fluctuations.curvature_diff_mat _ _ G.exp_jet.contDiffAt
   have hu : HasFDerivAt f (fderiv ℝ f 0) 0:= (hx.differentiableAt (by simp)).hasFDerivAt
   have h:fderiv ℝ f 0=ContinuousLinearMap.id ℝ G.Color:=by
     ext1 x; exact (YM.Push.side f (hx.differentiableAt (by simp)) x).unique (G.leading_curvature x)
   rw [h] at hu; exact hu
private lemma ups_d {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℝ Y] (g:Y→G.El)(v:ℝ) (he:g 0=1) (hf:ContDiffAt ℝ ω (G.mat ∘ g) 0): fderiv ℝ (fun y=>v • G.curvature (g y)) 0 = fderiv ℝ (fun y=> v • G.plog (G.mat (g y))) 0:=by
   let f:=G.plog ∘ G.mat ∘ g
   have hh : ContDiffAt ℝ ω f 0:=by
       have hv := show ContDiffAt ℝ ω G.plog ((G.mat ∘ g) 0) from by rw [comp_apply,he,G.mat_one]; exact G.plog_diff
       exact hv.comp _ hf
   have h : HasFDerivAt f (fderiv ℝ f 0) 0 := (hh.differentiableAt (by simp)).hasFDerivAt
   have hx: f 0=0:=by unfold f; simp [he]
   have hy := (hx.symm ▸ curv_d G v : HasFDerivAt (fun y=> v • G.curvature (G.lieExp y)) _ (f 0)).comp _ h
   have hm:∀ᶠ a in 𝓝 0, G.lieExp (f a)=g a:=by
      have he': ContinuousAt g 0:= (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.isInducing.continuousAt_iff.mpr hf.continuousAt
      exact he'.eventually (he.symm ▸ G.plog_right : ∀ᶠ a in 𝓝 (g 0), G.lieExp (G.plog (G.mat a)) = a)
   change _= fderiv ℝ (v • f) 0
   rw [(hy.congr_of_eventuallyEq ?_).fderiv,(h.const_smul v).fderiv]; ext; rfl
   filter_upwards [hm] with x hp; simp only [Function.comp_def, hp]

-- radius after-L purchasable.
def trust (p:Patch)(Q:KernelChoices)(G:Gauge):= (Honey.binning G 1 Q p).choose

lemma keel_live (v:Dir G c)(x:Drops c f)(ht:‖v‖≤trust S.patch S.kernel G): keel K x (represent v) = K.note x v:=by
    obtain ⟨i,j|j⟩:=x; · rfl
    obtain ⟨C,hc,hC,hh,h⟩:= (Honey.binning G 1 S.kernel S.patch).choose_spec
    let u:=trust S.patch S.kernel G
    let F(s:Temps G f):= corn K i (represent v) s j
    have hg : ContDiffAt ℝ ω (G.mat∘ F) 0:=by
       have hz : ‖((v,0): Hollow G c f)‖≤u:= by rw [Prod.norm_def,norm_zero]; apply max_le ht hc.le
       have hv := (h c f S rfl rfl K i j ((v,0):Hollow G c f) hz).1
       exact hv.comp (f:=fun y:Temps G f =>(v,y)) 0 (contDiffAt_const.prodMk contDiffAt_id)
    let g:=fun y=> F y*(F 0)⁻¹
    have hh':ContDiffAt ℝ ω (G.mat ∘ g) 0 := by unfold g; simp only [Function.comp_def,G.mat_mul]; exact (hg.mul contDiffAt_const)
    exact ups_d g _ (mul_inv_cancel _) hh'
lemma studio (v:Dir G c) (hv:‖v‖ ≤ trust S.patch S.kernel G):dark K (represent v)= K.Gram v ∧ foams K (represent v)= K.epoxy v := by
   have hx : dowel K (represent v)=K.D v:= by ext i j; unfold dowel D; rw [Matrix.of_apply,Matrix.of_apply,keel_live K v i.1 hv]
   unfold dark foams; rw [hx,F₀_eq]; exact ⟨rfl,rfl⟩
end Verdicts
end YM.Planned.PrimaryIntegral295.Night
