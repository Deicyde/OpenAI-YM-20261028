import YM.Next.STATIONARY.OneLoop.Propagators

set_option autoImplicit false
/-!
# Transverse vector/ghost colour polarizations on GL_n. Signature
using Fstar v2 thermo. Scalar continuum determinant mixing α per shape.
 -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι κ α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {G : Gauge} {S : Burst ι (Fslot G)} {p k : Track} {X : ℂ}
lemma taxPerl (b : G.ColorIndex) : inner ℝ (pearl b) (pearl b)=1 := by rw [pearl_dotted]; change (Pi.single b (1:ℝ) : G.ColorIndex→ℝ) b=1; rw [Pi.single_eq_same]
lemma tintTrace (b : G.ColorIndex) (hG : G.Simple) : trace (tintX b * tintX b)= -(G.casimir:ℂ) := by
  have ht := Gauge.trace_adjoint hG (pearl b) (pearl b); let A := EuclideanSpace.basisFun G.ColorIndex ℝ
  have he i : pearl i=A i := by
    rw [show A i=EuclideanSpace.single i 1 from EuclideanSpace.basisFun_apply ..]; rfl
  rw [taxPerl, mul_one,LinearMap.trace_eq_matrix_trace ℝ A.toBasis, LinearMap.toMatrix_mul] at ht
  let f:=G.ad (pearl b)
  let T := LinearMap.toMatrix A.toBasis A.toBasis f
  have hh : tintX b=approached T := by
    ext i j; unfold T approached; simp only [Matrix.of_apply,Matrix.map_apply,LinearMap.toMatrix_apply]
    change ((cosetR b i j:ℝ):ℂ) = ((A.toBasis.repr (f (A.toBasis j)) i:ℝ):ℂ)
    rw [A.coe_toBasis_repr_apply, A.coe_toBasis]; change ↑(cosetR b i j)=(((f (A j)) i:ℝ):ℂ)
    unfold cosetR; rw [he j]
  rw [hh,← prom_mul,trace_realized]; rw [show trace (T*T)= - G.casimir from neg_eq_iff_eq_neg.mp ht]; push_cast; rfl
-- component trace tensors
abbrev TypesM := CompM Axis Axis
def flail (M : TypesM) (T : CompM G.ColorIndex G.ColorIndex) : CompM (Fslot G) (Fslot G) := of fun i j=> M (chosenAxis i) (chosenAxis j)*T i.2 j.2
def shunt (T : CompM G.ColorIndex G.ColorIndex) : CompM (Foot G) (Foot G) := of fun i j=>T i.2 j.2
lemma chosen_eq (i : Axis) (b : G.ColorIndex) : chosenAxis (G:=G) (coord i,b)=i := axisEquiv.symm_apply_apply _
lemma flailTrace (M N : TypesM) (V Y : CompM G.ColorIndex G.ColorIndex) : trace (flail M V * flail N Y) = trace (M*N)*trace (V*Y) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,Fintype.sum_prod_type]
  -- TypeFace→ b
  rw [← Equiv.sum_comp axisEquiv]
  simp_rw [← Equiv.sum_comp axisEquiv]
  simp_rw [flail,Matrix.of_apply, coord_map,chosen_eq,sum_mul,mul_sum]; apply sum_congr rfl; intro i _; rw [sum_comm];
  apply sum_congr rfl; intro j _; simp_rw [mul_assoc];
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
lemma shuntTrace (T K : CompM G.ColorIndex G.ColorIndex) : trace (shunt T * shunt K)=trace (T*K) := by
  simp only [Matrix.trace,Matrix.diag_apply, Matrix.mul_apply,Fintype.sum_prod_type,shunt,Matrix.of_apply]
  have he (t : ℂ) : ∑ _ : TypeFace 0,t=t := by rw [sum_eq_single vac] <;> simp [vac_only]
  simp_rw [he]

section trans
-- choose axial test. E and I names.

def perL (k : Track) := -2*tachy k 1

def plaid (t : ℝ) : TypesM := of fun i j=> 2*((Complex.I*(t:ℂ))*deer j 0*deer i 1 - (Complex.I*(t:ℂ))*deer i 0*deer j 1)
lemma braidVec (i : G.ColorIndex) (k : Track) (t : ℝ) : herr (coord 1,i) (t • step 0) k=flail ((perL k) • 1 + plaid t) (tintX i) := by
  have he (i : Axis) : tachy (t • step 0) i=(Complex.I*(t:ℂ))*deer i 0 := by by_cases h : i=0 <;> simp [h,tachy,deer,ite_mul,mul_ite]
  ext ⟨b,c⟩ ⟨a,d⟩; obtain ⟨x,rfl⟩:=axisEquiv.surjective b; obtain ⟨y,rfl⟩:=axisEquiv.surjective a
  rw [coord_map,coord_map,herr_pitch]; unfold vectorC ghostC; simp_rw [he];
  simp only [flail,plaid, Matrix.of_apply,Matrix.add_apply,chosen_eq,Matrix.smul_apply]; unfold perL deer; rw [if_neg (by decide : (1:Axis)≠0),Matrix.one_apply]; simp only [smul_eq_mul,chosen_eq]; ring
lemma braidSap (i : G.ColorIndex) (k : Track) (t : ℝ) : hurr (coord 1,i) (t • step 0) k= shunt ((perL k) • (tintX i)) := by
  ext ⟨b,c⟩ ⟨a,d⟩; rw [vac_only b,vac_only a,hurr_pitch]; unfold shunt ghostC perL; rw [show tachy (t • step 0) 1=0 by simp [tachy,show (1:Axis)≠ 0 by decide]]; simp [mul_assoc]
lemma plaidSurge (t : ℝ) (p : ℂ) : trace (((p • 1 : TypesM)+plaid (-t))* (p • 1+plaid t))=4*p^2- (8:ℂ)*(t:ℂ)^2 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp [Fin.sum_univ_succ,plaid,deer, Matrix.one_apply]; ring_nf
  rw [sq Complex.I, Complex.I_mul_I]; ring
end trans
end YM.Stationary
end

/-!
# Exact continuum Taylor along axis. Coefficient `flareY` raw; mixed t²
 coefficient = D²/2. No orientation average here. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι κ α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {G : Gauge} {S : Burst ι (Fslot G)} {p k : Track} {X : ℂ}

section integral
-- peak polynomial and continuum integrand on rays

def laxa (x : Track) (t : ℝ) := pebb (x+t • step 0)
lemma axa (x : Track) (t : ℝ) : laxa x t=pebb x+2*(t:ℂ)*(x 0:ℂ)+(t:ℂ)^2 := by
  unfold laxa pebb; simp [Fin.sum_univ_succ]; ring
lemma laxa_green (x : Track) : AnalyticAt ℝ (laxa x) 0 := by rw [funext (axa x)]; exact (analyticAt_const.add ((analyticAt_const.mul (Complex.ofRealCLM.analyticAt 0)).mul analyticAt_const)).add ((Complex.ofRealCLM.analyticAt 0).pow _)
lemma laxa_nz (h : 0<flay k) : pebb k≠0 := by rw [pebbFl]; exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr h.ne')
lemma loiterShift (k : Track) (t : ℝ) : perL (k+t • step 0)=perL k := by simp [perL,tachy,show (1:Axis)≠0 by decide]
lemma troopTrace (x y : Track) (A B : CompM α α) (h : pebb x ≠ 0) (ht : pebb y ≠ 0) : ((skull x α)⁻¹ *A * (skull y α)⁻¹* B).trace = (pebb x)⁻¹ * (pebb y)⁻¹ * trace (A*B) := by
  have hv (x : Track) (h : pebb x ≠ 0) : (skull x α)⁻¹ = (pebb x)⁻¹ • 1 := by apply inv_eq_right_inv; unfold skull; rw [Matrix.mul_smul, Matrix.mul_one, smul_smul,inv_mul_cancel₀ h,one_smul]
  simp_rw [hv x h,hv y ht,Matrix.mul_smul,Matrix.smul_mul,Matrix.one_mul,Matrix.mul_one,trace_smul,smul_eq_mul]; ring
variable (b : G.ColorIndex) (k' : Track) (hk : 0<flay k') (i : ι) (hS : G.Simple) (hb : S.boost i=step 0) (hv : S.mark i=(coord 1,b)) (hx : S.lens i=k')
include hS hb hv hx hk
lemma waveOrb : (fun t=> trace (haloC S (hurr (G:=G)) i t))=ᶠ[𝓝 0] fun t => (pebb k')⁻¹ * (laxa k' t)⁻¹ * (perL k')^2 * (-(G.casimir:ℂ)) := by
  have ht := (laxa_green k').continuousAt.eventually_ne (show laxa k' 0≠0 by simpa only [laxa,zero_smul,add_zero] using laxa_nz hk)
  filter_upwards [ht] with t ht
  dsimp only [haloC,shone, stroll,panL,panT,Pi.zero_apply]; rw [hb,hx,hv,smul_zero,add_zero,smul_neg, ← neg_smul]
  rw [troopTrace _ _ _ _ (laxa_nz hk) ht, braidSap,braidSap,loiterShift,shuntTrace,Matrix.mul_smul,Matrix.smul_mul, trace_smul,trace_smul,tintTrace b hS]; simp only [smul_eq_mul,laxa]; ring
lemma waveVec : (fun t=> trace (haloC S (herr (G:=G)) i t))=ᶠ[𝓝 0] fun t => (pebb k')⁻¹ * (laxa k' t)⁻¹ * ((4*(perL k')^2-8*(t:ℂ)^2) * (-(G.casimir:ℂ))) := by
  filter_upwards [(laxa_green k').continuousAt.eventually_ne (show laxa k' 0≠0 by simpa only [laxa,zero_smul,add_zero] using laxa_nz hk)] with t ht
  dsimp only [haloC, shone, stroll,panL,panT,Pi.zero_apply]
  rw [hb,hx,hv,smul_zero,add_zero,smul_neg,← neg_smul, braidVec,braidVec,loiterShift,troopTrace _ _ _ _ (laxa_nz hk) ht,flailTrace,plaidSurge,tintTrace _ hS]
  rfl
end integral
lemma flare_tape {n : ℕ} {x y : ℝ→ ℂ} (h : x=ᶠ[𝓝 0] y) : flareY n x=flareY n y := by unfold flareY; rw [(h.iteratedFDeriv ℝ n).eq_of_nhds]
lemma flare1 (x : ℝ→ℂ) : flareY 1 x=deriv x 0 := by rw [flareY,iteratedFDeriv_one_apply]; rfl
lemma binomialV (a b c : ℂ) : flareY 2 (fun t : ℝ => a+b*(t:ℂ)+c*(t:ℂ)^2)=2*c ∧ flareY 1 (fun t : ℝ => a+b*(t:ℂ)+c*(t:ℂ)^2)=b := by
  let L := fun t : ℝ=>(t:ℂ); let U := fun t : ℝ=> a+b*(t:ℂ)
  have hp : AnalyticAt ℝ L 0 := Complex.ofRealCLM.analyticAt _
  have hU : AnalyticAt ℝ U 0 := analyticAt_const.add (analyticAt_const.mul hp)
  have hx : flareY 1 L=1 := by rw [flare1,show L=Complex.ofRealCLM from rfl,deriv]; rw [Complex.ofRealCLM.fderiv]; simp
  have ht : flareY 2 L=0 := by unfold flareY; rw [iteratedFDeriv_two_apply]; change (fderiv ℝ (fderiv ℝ L) 0 (1:ℝ)) (1:ℝ)=_; rw [show fderiv ℝ L=fun _=> Complex.ofRealCLM from funext fun _=> Complex.ofRealCLM.fderiv,show fderiv ℝ (fun _ : ℝ => Complex.ofRealCLM) 0=0 from (hasFDerivAt_const ..).fderiv]; simp
  let M (t : ℝ) := c*(L t)^2
  have hM : AnalyticAt ℝ M 0 := analyticAt_const.mul (hp.pow 2)
  have h₀ i : flareY i U=flareY i (fun _ : ℝ=>a)+ b*flareY i L := (flare_add (n:=i) analyticAt_const (AnalyticAt.mul (analyticAt_const (v:=b)) hp)).trans (congr_arg₂ _ rfl (flare_scale hp b))
  have hv i : flareY i M=c*flareY i (L*L) := by unfold M; simp_rw [sq]; exact flare_scale (hp.mul hp) c
  change flareY 2 (U+M)=2*c ∧ flareY 1 (U+M)=b
  rw [flare_add hU hM,flare_add hU hM,h₀,h₀,hv,hv, flare_second hp hp,flare_first hp hp,hx,ht,show L 0=0 from Complex.ofReal_zero, flare_oneZ _ (by decide),flare_oneZ _ (by decide)]; constructor <;> ring
lemma divCatch (g h : ℝ→ℂ) (hg : AnalyticAt ℝ g 0) (h1 : AnalyticAt ℝ h 0) (he : g 0≠0) : flareY 2 (h/g)=flareY 2 h / g 0 - 2 * flareY 1 h* flareY 1 g / g 0^2 - h 0* flareY 2 g / g 0^2 + 2*h 0* flareY 1 g^2 /g 0^3 := by
  let U:= h/g
  have hU : AnalyticAt ℝ U 0 := hg |> fun hx=> h1.div hx he
  have hh : U * g =ᶠ[𝓝 0] h := by filter_upwards [hg.continuousAt.eventually_ne he] with t ht; simp [U,ht]
  have hx := flare_tape (n:=1) hh; have hy := flare_tape (n:=2) hh
  rw [flare_first hU hg] at hx; rw [flare_second hU hg] at hy
  have hp : U 0=h 0/g 0 := rfl
  have hv : flareY 1 U=(flareY 1 h-U 0*flareY 1 g)/g 0 := (eq_div_iff he).mpr (by rw [← hx]; ring)
  rw [← hy,hv]; change flareY 2 U=_; rw [hp]; field_simp; ring

-- continuum kernel expression after vector/scalar sign and 1/2 weight.
def poleVec (G : Gauge) (p : Track) : ℝ := 4*G.casimir*((p 1)^2 / flay p^6 - 4*(p 1)^2*(p 0)^2/flay p^8 - (flay p^4)⁻¹)
-- tad cost bounded; bubble NEG of halo. `poleVec` = orbital plus spin (precision after negative).
lemma haloRate (b : G.ColorIndex) (h : G.Simple) (i : ι) (hp : 0<flay (S.lens i)) (hS : S.boost i=step 0) (hv : S.mark i=(coord 1,b)) : flareY 2 (fun t=> (haloC S (hurr (G:=G)) i t).trace) -(1/2:ℂ)*flareY 2 (fun t=> (haloC S (herr (G:=G)) i t).trace)=2* (poleVec G (S.lens i):ℂ) := by
  let k := S.lens i; let r := flay k; let x : ℂ := pebb k; let D := laxa k; let C := -(G.casimir:ℂ); let L := (perL k)^2
  let U (t : ℝ) := x⁻¹ * L * C
  let M (t : ℝ) := x⁻¹ * ((4*L-8*(t:ℂ)^2)*C)
  have hU : (fun t=> (haloC S hurr i t).trace)=ᶠ[𝓝 0] U/D := (waveOrb b k hp i h hS hv rfl).trans (Eventually.of_forall fun t=>by unfold U D; rw [Pi.div_apply]; unfold x L C; ring)
  have hV : (fun t=> (haloC S herr i t).trace)=ᶠ[𝓝 0] M /D := (waveVec b k hp i h hS hv rfl).trans (Eventually.of_forall fun t=> by unfold M D; rw [Pi.div_apply]; unfold x L C; ring)
  have hz : x≠0 := laxa_nz hp; have ht : D 0=x := by unfold D laxa x; simp
  have hh : D=fun t:ℝ => x+(2*(k 0:ℂ))*(t:ℂ)+ (1:ℂ)*(t:ℂ)^2 := by ext1 a; unfold D; rw [axa]; unfold x; ring
  have hm : M=fun t:ℝ => x⁻¹*(4*L*C)+0*(t:ℂ)+(x⁻¹*(-8)*C)*(t:ℂ)^2 := by ext1 t; unfold M; ring
  have he : AnalyticAt ℝ M 0 := analyticAt_const.mul ((analyticAt_const.sub (AnalyticAt.mul analyticAt_const ((Complex.ofRealCLM.analyticAt 0).pow 2))).mul analyticAt_const)
  have hx : D 0≠0 := by rw [ht]; exact hz
  rw [flare_tape hU, flare_tape hV, divCatch D U (laxa_green k) analyticAt_const hx, divCatch D M (laxa_green k) he hx]; rw [show flareY 1 D= _ from hh ▸ (binomialV ..).2,show flareY 2 D=_ from hh ▸ (binomialV ..).1]
  rw [show flareY 2 M=_ from hm ▸ (binomialV ..).1,show flareY 1 M=_ from hm ▸ (binomialV ..).2,show flareY 2 U=0 from flare_oneZ _ (by decide), show flareY 1 U=0 from flare_oneZ _ (by decide),ht]
  have he : perL k ^ 2=-4*(k 1:ℂ)^2 := by unfold perL tachy; linear_combination 4*(k 1:ℂ)^2 * Complex.I_mul_I
  unfold U M C L x; rw [he,pebbFl]; unfold k poleVec; push_cast; field_simp [hp.ne']; ring
end YM.Stationary
end

/-!
# Kinetic tally with Ξ. Positive tally means actual logdet precision
not potential, so spin sign arrives opposite. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι κ α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {G : Gauge} {P : Patch} {V U : Jar G} {σ A D C ζ r ε η : ℝ} {k : Track} {T μ : ι →ℝ} {n : ℕ}

def strolls (p : Momentum→Momentum→ℂ) (k : Track) := (1/2:ℂ)*flareY 2 (fun t=> p (axes ((t:ℝ) • step 0)) (axes k))
def keelRay (u : Award G) (b : G.ColorIndex) := strolls (u (coord 1,b) (coord 1,b))
section payment
variable {F Y : KPath ι κ α α} {W : κ→Track→Track→CompM α α} [Fintype κ] {X : Burst ι κ} (h : Fleet X T μ F Y W r)
def rod (X : Burst ι κ) (F : KPath ι κ α α) (i) t := (F i).figure (X.mark i) (X.mark i) (springM X i t) (axes (X.lens i))
include h
lemma rod_diff (i) : AnalyticAt ℝ (rod X (atopY F Y) i) 0 := by unfold rod; simp_rw [framePing]; exact (h.lacy i).1.sub (h.lacy i).2

lemma rod_plucked (i) : flareY 2 (rod X (atopY F Y) i)= flareY 2 (fun t=> trace (upperJet X (atopY F Y) i t))-flareY 2 (fun t=> trace (lowerJet X (atopY F Y) i t)) := by unfold rod; simp_rw [framePing]; exact flare_dec (h.lacy i).1 (h.lacy i).2
lemma rod_bill : ∃ A : ℝ, 0≤A ∧ ∀ i, ‖flareY 2 (rod X (atopY F Y) i)‖≤ A/T i^4 := by
  obtain ⟨A,hA,hP⟩ := Fleet.focus_bill h.bubbleHV.1 h.2.2.2.lower; obtain ⟨B,hB,hS⟩ := h.bubbleControl
  refine ⟨A+B,by positivity,fun i=>?_⟩; rw [rod_plucked h]; exact (norm_sub_le ..).trans ((add_le_add (hP i) (hS i)).trans_eq (by simp; ring))
end payment
section stars
variable {X : Burst ι (Fslot G)} {F : KPath ι (Fslot G) (Fslot G) (Fslot G)}
abbrev membrana (G : Gauge) (μ : ι→ℝ) : KPath ι (Fslot G) (Foot G) (Foot G) := fun i=>chisel G (μ i)
abbrev distaff (G : Gauge) (μ : ι→ℝ) : KPath ι (Fslot G) (Fslot G) (Fslot G) := fun i=>graniteF G (μ i)
structure Rally (X : Burst ι (Fslot G)) (T μ : ι→ℝ) (F : ι→KindF G) (r : ℝ) (b : ι→ G.ColorIndex) : Prop where
    first : Fleet X T μ (fun i=>granary G (F i)) (distaff G μ) (herr (G:=G)) r
    spare : Fleet X T μ (fun _=>quarry G) (membrana G μ) (hurr (G:=G)) r
    desires i : X.mark i=(coord 1,b i)
    upright i : X.boost i=step 0
variable {b : ι→G.ColorIndex} (h : Rally X T μ F r b)
def Rally.bait (G : Gauge) (F : ι→ KindF G) (μ : ι→ℝ) (i) := amena (μ i) G (F i)
include h
lemma Rally.coin (i) : keelRay (Rally.bait G F μ i) (b i) (X.lens i)= (1/2:ℂ)*((1/2:ℂ)*flareY 2 (rod X (fun i=> massif G (μ i) (F i)) i)-flareY 2 (rod X (fun i=>coring G (μ i)) i)) := by
  let V i := massif G (μ i) (F i); let Y i := coring G (μ i)
  let f := rod X V i; let g := rod X Y i; let c := (1/2:ℂ)
  have hf : AnalyticAt ℝ f 0 := rod_diff h.first _; have hg : AnalyticAt ℝ g 0 := rod_diff h.spare _
  unfold keelRay strolls; rw [show (fun t:ℝ=>Rally.bait G F μ i (coord 1,b i) (coord 1,b i) (axes (t • step 0)) (axes (X.lens i)))=(fun t=> c*f t)-g from funext (fun t=> by
    unfold f g rod springM c V Y; rw [h.upright,h.desires]; simp only [bait,amena,Pi.sub_apply,Pi.smul_apply,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,smul_eq_mul]), flare_dec (x:=fun t => c*f t) (analyticAt_const.mul hf) hg, flare_scale hf c]

lemma Rally.register : ∃ A : ℝ,0≤A ∧ ∀ i, ‖keelRay (Rally.bait G F μ i) (b i) (X.lens i)‖≤ A/T i^4 := by
  obtain ⟨A,hA,h1⟩ := rod_bill h.first; obtain ⟨B,hB,h2⟩ := rod_bill h.spare
  let c := (1/2:ℂ); have ht (x : ℂ) : ‖c*x‖≤ ‖x‖ := by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (by unfold c; norm_num)
  refine ⟨A+B,by positivity,fun i=> ?_⟩; rw [h.coin i]
  exact (ht _).trans ((norm_sub_le ..).trans ((add_le_add ((ht _).trans (h1 i)) (h2 i)).trans_eq (by ring)))
lemma Rally.shell (hG : G.Simple) (he : T=flay ∘ X.lens) (hr : 0≤r) :
    ∃ A : ℝ,0≤A ∧ ∀ i, ‖keelRay (Rally.bait G F μ i) (b i) (X.lens i)- ↑(poleVec G (X.lens i))‖≤ A/ T i^3+ A*μ i^2/T i^6 := by
  obtain ⟨A,hA,hL⟩ := h.first.haloControl he; obtain ⟨B,hB,hG'⟩ := h.spare.haloControl he
  obtain ⟨u,v,hU,hV,f⟩ := h.first.tadControl; obtain ⟨x,y,hX,hY,g⟩ := h.spare.tadControl
  let P := max (u*r+x*r + A+B) (A+B+v+y)
  have hP : 0≤ P := (show 0≤u*r+x*r+A+B by positivity).trans (le_max_left ..)
  refine ⟨P,hP,fun i=>?_⟩
  let J := X.lens i; let V := atopY (fun i=>granary G (F i)) (distaff G μ); let W:=atopY (fun _=>quarry G) (membrana G μ)
  let t := upperJet X V; let j := upperJet X W
  let L := lowerJet X V; let M := lowerJet X W
  let V' := haloC X (herr (G:=G)); let T' := haloC X (hurr (G:=G))
  let d := flareY 2 (fun z=> trace (L i z)); let c := flareY 2 (fun z=> trace (M i z)); let d' := flareY 2 (fun z=> trace (V' i z)); let c' := flareY 2 (fun z=> trace (T' i z))
  let D := flareY 2 (fun z=> trace (t i z)); let Y := flareY 2 (fun z=>trace (j i z))
  let a := T i; let w := μ i; let C := (1/2:ℂ)
  have hk : 0<a := h.first.2.2.2.lower _; have hp : a=flay J:=congr_fun he i
  have he : keelRay (Rally.bait G F μ i) (b i) (X.lens i)-(poleVec G (X.lens i):ℂ) = C*(C*D-Y)+C*((c-c')- C*(d-d')) := by
    rw [h.coin]; change C*(C*flareY 2 (rod X V i)-flareY 2 (rod X W i))- _=_
    have ht : c' - C*d'= (2:ℂ)*(poleVec G J:ℂ) := haloRate (b i) hG i (hk.trans_eq hp) (h.upright i) (h.desires i)
    rw [show flareY 2 (rod X V i)=D-d from rod_plucked h.first i,show flareY 2 (rod X W i)= Y-c from rod_plucked h.spare i,show (poleVec G (X.lens i):ℂ)= C*(c'-C*d') from (by rw [ht]; unfold C J; ring)]
    unfold C; ring
  rw [he]; have ht (x : ℂ) : ‖C*x‖≤ ‖x‖ := by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (by unfold C; norm_num)
  let Q:= rimEdge T μ i
  have hl' : ‖C*D-Y‖≤ (u/a^2+ v*w^2/a^6) + (x/a^2 +y*w^2/a^6) := (norm_sub_le ..).trans (add_le_add ((ht _).trans (f i)) (g i))
  have hx' : ‖(c-c')-C*(d-d')‖ ≤ B*Q/a^4+A*Q/a^4 := (norm_sub_le ..).trans (add_le_add (hG' i) ((ht _).trans (hL i)))
  refine (norm_add_le ..).trans ((add_le_add ((ht _).trans hl') ((ht _).trans hx')).trans ?_)
  have hh : a≤r := h.first.2.2.2.upper _
  change _ ≤ P/a^3+P*w^2/a^6; calc
   _ = (u*a+x*a+A+B)/a^3+(A+B+v+y)*w^2/a^6 := by
     change _ + (B*(a+w^2*(a^2)⁻¹)/a^4+A*(a+w^2*(a^2)⁻¹)/a^4)=_; field_simp; ring
   _ ≤ _ := by
     have hx : u*a+x*a+A+B ≤ P := (show u*a+x*a+A+B ≤ u*r+x*r+A+B by nlinarith [mul_le_mul_of_nonneg_left hh hU,mul_le_mul_of_nonneg_left hh hX]).trans (le_max_left ..)
     apply add_le_add (div_le_div_of_nonneg_right hx (by positivity)); gcongr; exact le_max_right ..
end stars
end YM.Stationary
end

/-!
# Angular fees honored even off-shell. Pre-L constants homogeneous families
(scope ALL shapes passing one cost). This is quantit derivative at p=0 of
actual per-cell limit integrand X.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience Metric
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {ι κ : Type} {G : Gauge} {P : Patch} {V U : Jar G} {σ A D C ζ r a ε η : ℝ} {T μ : ι →ℝ} {p : Track}

section usingG
variable {X : Burst ι (Fslot G)} {S : Skuta ι G}
lemma getReals (h : S.Live η D ε A V) (hp : V.grey) (he : V.fees η C) (hσ : 0<η) (hv : ColdR X T S.μ r) (hε : 0<ε)
    (b : ι→G.ColorIndex) (hk : ∀ i,X.mark i=(coord 1,b i)) (hX : ∀ i,X.boost i=step 0) : Rally X T S.μ (S.useJar V) r b := by
  obtain ⟨hx,hV⟩ := glaze hv
  refine ⟨⟨Floe.vector h hσ hp he X _,hV, granaryTall hv (F:=S.useJar V) (ε:=ε) (B:=S.terra) (p:=S.top) (fun i => (h i).1) hε,hv⟩,
          ⟨Floe.ghost _ _,hx,grainTall hv,hv⟩,hk,hX⟩
structure Orion (V : Jar G) (η D ε A : ℝ) where
    σ : ℝ
    μ : ℝ
    a : G.ColorIndex
    b : Bed
    c : Clip
    l : Jar G
    rate : HouseWord G b c D ε σ D μ (l.combine V|>.cast)
    boat : l.fees η A
    burst : l.soft 3

def FrontBox (p : Track) := Nave (axes p)
structure Hstar (V : Jar G) (η D ε A : ℝ) where
    x : Track
    p : Orion V η D ε A
    path : FrontBox x

section fees
abbrev furthest := 1+2*Real.pi
lemma furthest_pos : 0≤ furthest := by unfold furthest; positivity

def BundleS (F : ι→ Hstar V η D ε A) : Skuta ι G := ⟨fun i => (F i).p.l,fun i=> (F i).p.b,fun i=> (F i).p.c,fun i=> (F i).p.σ, fun i=> (F i).p.μ⟩
def Looming (F : ι→ Hstar V η D ε A) : Burst ι (Fslot G) := ⟨fun i=> (F i).x,fun _=>step 0,fun i => (coord 1,(F i).p.a)⟩
lemma Bundled (F : ι→ Hstar V η D ε A) : (BundleS F).Live η D ε A V := fun i=>⟨(F i).p.rate,(F i).p.boat,(F i).p.burst⟩
lemma singleStep (i : Axis) : ‖(step i:Track)‖ ≤ (1:ℝ) := (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun j =>by by_cases h:j=i <;> simp [step,h])
lemma Looms (F : ι→ Hstar V η D ε A) :
    let X:= Looming F; let T:=BundleS F; ColdR X ((flay ∘ X.lens)+T.μ) T.μ furthest := by
  intro X T
  have hx i : FrontBox (X.lens i) := (F i).path
  have hp i : 0<T.μ i ∧ T.μ i ≤ 1 := (F i).p.rate.amount
  exact ⟨furthest_pos, fun i=> add_pos_of_nonneg_of_pos (orbit_nonneg _) (hp i).1,fun i=> (add_le_add (orbit_boundary _ (hx i)) (hp i).2).trans_eq (add_comm ..),fun i=> singleStep 0,fun i=> le_add_of_nonneg_right (hp i).1.le,fun i=>(hp i).1,fun _=> le_rfl,fun i=> le_add_of_nonneg_left (orbit_nonneg _),fun i=> (hp i).2,hx⟩
def Waves1 (A : ℝ) (p : ℝ) (G : Track→ℂ) := ∀ k, FrontBox k → ‖G k‖ ≤ A/(flay k+p)^4
def Waves2 (C : ℝ) (p : ℝ) (F : Track→ℂ) (G : Gauge) := ∀ k, FrontBox k→p≤flay k→ ‖F k-↑(poleVec G k)‖ ≤ C/flay k^3+C*p^2/flay k^6
lemma astronomy (h : V.fees η C) (hv : V.grey) (he : 0<ε) (hp : 0<η) (ht : G.Simple) (D A : ℝ) : ∃ i j : ℝ, 0 ≤ i ∧ 0≤j ∧ ∀ p : Orion V η D ε A,
    let X := amena p.μ G (p.l.combine V|>.cast)
    Waves1 i p.μ (keelRay X p.a) ∧ Waves2 j p.μ (keelRay X p.a) G := by
  let f (p : Hstar V η D ε A) := p
  let J := Looming f; let Q := BundleS f
  let M := fun i: Hstar V η D ε A=> i.p.a
  obtain ⟨i,hi,h1⟩ := Rally.register (X:=J) (F:=Q.useJar V) (b:=M) (getReals (Bundled f) hv h hp (Looms f) he _ (fun _=>rfl) (fun _=>rfl))
  let E := {q : Hstar V η D ε A // q.p.μ ≤ flay q.x}
  let v : E → Hstar V η D ε A:=Subtype.val; let m:= Looming v; let S:=BundleS v; let K := flay ∘ m.lens
  let μ := S.μ; have hh := Looms v
  have hF : ColdR m K μ furthest := by
    have hQ i : μ i ≤ K i := i.property
    refine ⟨furthest_pos,fun i=>(hh.pos i).trans_le (hQ i), fun i=> le_trans (b:=K i+μ i) (le_add_of_nonneg_right (hh.pos i).le) (hh.upper i), fun i=> singleStep _, fun i=> le_rfl,hh.pos,fun i=> le_add_of_nonneg_right (hh.pos i).le,hQ,hh.slim,hh.stage⟩
  obtain ⟨x,hx,h2⟩ := Rally.shell (F:=S.useJar V) (getReals (Bundled v) hv h hp hF he (M∘v) (fun _=>rfl) (fun _=>rfl)) ht rfl furthest_pos
  exact ⟨i,x,hi,hx,fun p=> ⟨fun k hk=> h1 ⟨k,p,hk⟩,fun k hk hx=> h2 ⟨⟨k,p,hk⟩,hx⟩⟩⟩
end fees
end usingG
end YM.Stationary
end
