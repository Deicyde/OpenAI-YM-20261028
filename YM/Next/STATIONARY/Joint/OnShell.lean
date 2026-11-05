import YM.LocalH.Haar
import YM.Next.STATIONARY.Joint.Symmetry
import YM.Work.B16




set_option autoImplicit false
/-! # Simultaneous color of the centered coordinate germ. Invariant
field gradients of any such scalar vanish at origin jointly, including the
frame variables. Lie action on THE physical coordinates actually used.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f}

variable (u : G.El)

def solid : Coats G n := fun _ => u
def sigil (x : G.El) := u*x*u⁻¹
lemma ever_focus : ∀ᶠ v : G.Mat in 𝓝 1, G.focus (G.conjugate u v) = sigil u (G.focus v) := by
  have he : Tendsto (G.conjugate u) (𝓝 1) (𝓝 1) := by
    have hv := (G.conjugateL u).continuous.tendsto 1
    rw [show G.conjugateL u 1=1 by simp [Gauge.conjugate]] at hv; exact hv
  filter_upwards [G.nearest_is_focus,he.eventually G.nearest_is_focus] with x hx hy
  obtain ⟨v,h⟩ := G.nearest_exists x; rw [← hx v h]
  exact (hy _ <| (G.nearest_right u⁻¹ (u*v) _).2 <| (G.nearest_left u v _).2 h).symm

lemma solid_arm (u : G.El) : wages S (solid u) (solid u) (1 : Joint G c f) = 1 := by ext i <;> simp [wages,solid,Lattice.gauge]
lemma flare_color (b : Vault G c f) :
    Stationary.extend (armUp (solid u) (solid u) b)=wages S (solid u) (solid u) (Stationary.extend b) := by
  have hi := arm_root (S:=S) (solid u) (solid u) b (1:Joint G c f)
  rwa [solid_arm,mul_one,mul_one] at hi
lemma tincture : stain (m:=n) u = armor (solid u) := by
  ext1 x; apply edgeColor.injective; funext i
  rw [armor_at]
  change arm G n 1 (stain u x) _= _; simp only [stain,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,(arm _ _ _).apply_symm_apply]; rfl

variable (t : S.Choices) (h : S.patch.Branches S.kernel G)
include h
lemma frame_sig (i : Site c) (U : Config G f) :
    prospect S t (Lattice.gauge (solid u) U) i=G.conjugate u (prospect S t U i) := by
  have hp j : S.frames (Lattice.gauge (solid u) U) t.1 i j=u*S.frames U t.1 i j*u⁻¹ := by
    rw [StepData.frames,expandAt_gauge,(S.patch.frame_gauged h ..).2]; rfl
  unfold prospect Gauge.conjugate
  simp only [hp,G.mat_mul,G.mat_inv,Finset.mul_sum,Finset.sum_mul,smul_mul_assoc,mul_smul_comm]
lemma fedora_u {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {U : X → Joint G c f} (H : Thaw U 0) (he : (U 0).1=1) :
    ∀ᶠ z in 𝓝 0, enroll S t (wages S (solid u) (solid u) (U z))=wages S (solid u) (solid u) (enroll S t (U z)) := by
  have hv (i) : ∀ᶠ z in 𝓝 0,bears S t (Lattice.gauge (solid u) (U z).1) i=u*bears S t (U z).1 i*u⁻¹ := by
    simp_rw [bears,frame_sig u t h]; apply Filter.Tendsto.eventually _ (ever_focus u)
    let L z := prospect S t (U z).1 i
    have hp : ContDiffAt ℝ ω L 0 := ContDiffAt.sum fun j _ => (H.1.frame h t he i j).const_smul _
    have ht : L 0=1 := by simp [L,he,prospect_zero S t h]
    exact ht ▸ hp.continuousAt.tendsto
  filter_upwards [eventually_all.mpr hv] with z hz
  refine Prod.ext rfl ?_; funext i
  simp only [wages,enroll,solid,Pi.mul_apply,Pi.inv_apply]; rw [hz]; group
end YM.Stationary
end

/-! # Invariance under color forces field-gradients to vanish on scalar full or compare
matrices (off shell at flat, in joint coordinates). `Simple` REAL. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f}

lemma color_pitch (x y : G.Color) : HasDerivAt (fun t : ℝ => G.adjoint (G.lieExp (t • x)) y) (G.ad x y) 0 := by
  have hh := G.projectColor.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ)
    (((exp_ray x).mul_const (G.colorMat y)).mul (exp_ray x).star)
  change HasDerivAt _ (G.projectColor (G.colorMat x*G.colorMat y-G.colorMat y*G.colorMat x)) _
  convert! hh using 1; simp [G.colorMat_skew]; rfl

lemma color_fixed_at (h : G.Simple) (x : G.Color) (he : ∀ u, G.adjoint u x=x) : x=0 := by
  have hi a : G.ad a x=0 := HasDerivAt.unique (color_pitch a x) (by simp only [he]; exact hasDerivAt_const 0 x)
  let P := Submodule.span ℝ ({x} : Set G.Color)
  have ht (a : G.Color) (y : G.Color) (p : y∈P) : G.ad a y=0 := by
    obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp p
    rw [map_smul,hi,smul_zero]
  have hf : P≠⊤ := fun hv => by
    obtain ⟨a,y,ha⟩ := h.nonabelian; exact ha (ht a y (by simp only [hv,Submodule.mem_top]))
  have hs : P=⊥ := (h.ideals P (fun i j hj => by rw [ht _ _ hj]; exact P.zero_mem)).resolve_right hf
  exact Submodule.mem_bot ℝ |>.mp (hs ▸ (Submodule.subset_span (show x∈ ({x}:Set G.Color) from Set.mem_singleton _) : x∈P))

lemma color_fixed (h : G.Simple) {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (F : G.Color →L[ℝ] X)
    (he : ∀ u x, F (G.adjoint u x)=F x) : F=0 := by
  let P := F.toLinearMap.ker
  have hp (x y : G.Color) : F (G.ad x y)=0 := by
    have hx := F.hasFDerivAt.comp_hasDerivAt 0 (color_pitch x y)
    change HasDerivAt (fun v : ℝ => F (G.adjoint (G.lieExp (v • x)) y)) _ _ at hx
    simp_rw [he] at hx; exact hx.unique (hasDerivAt_const ..)
  have hh : P≠⊥ := by
    obtain ⟨x,y,he⟩ := h.nonabelian
    intro h
    refine he (Submodule.mem_bot ℝ |>.mp (h ▸ (show G.ad x y ∈ P from hp x y)))
  have hv := (h.ideals P (fun i j _ => (show G.ad i j∈P from hp i j))).resolve_left hh
  ext m; exact (show m∈P from hv.symm ▸ Submodule.mem_top)

section slots
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
lemma chain_fixed {F : X→Y} (A : X→L[ℝ] X) (h : F∘A=ᶠ[𝓝 0] F) (hp : DifferentiableAt ℝ F 0) (x : X) :
    fderiv ℝ F 0 (A x)=fderiv ℝ F 0 x := by
  have hv := h.fderiv_eq (𝕜:=ℝ)
  rw [fderiv_comp 0 (by rw [map_zero]; exact hp) A.differentiableAt,map_zero,A.fderiv] at hv
  exact DFunLike.congr_fun hv x

variable (h : G.Simple)
include h
lemma slot_fixed {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → G.Color) →L[ℝ] X) (he : ∀ u : G.El, ∀ v : ι→ G.Color, f (fun z => G.adjoint u (v z))=f v) :
    ∀ y,f y=0 := by
  have hp i (x : G.Color) : f (Pi.single i x)=0 := by
    let F : G.Color→L[ℝ] X := f ∘L ContinuousLinearMap.single ℝ (φ:=fun _ => G.Color) i
    apply DFunLike.congr_fun (color_fixed h F ?_) x
    intro u y; change f (Pi.single i _)=f (Pi.single i y)
    rw [← he u (Pi.single i y)]; congr; funext k; by_cases hv : k=i <;> simp [hv]
  intro y; rw [← show ∑ i,Pi.single i (y i)=y by ext1 i; simp [Finset.sum_apply,Pi.single_apply], map_sum]; simp only [hp, Finset.sum_const_zero]
lemma oneFlag (f : Link G n →L[ℝ] X) (he : ∀ u : G.El, ∀ v,f (armor (solid u) v)=f v) : ∀ x, f x=0 := by
  have ht (x : Edge (Site n) → G.Color) : f (edgeColor.symm x)=0 := by
    apply slot_fixed h (f ∘L edgeColor.symm.toContinuousLinearMap) ?_ x
    intro u y; change f (edgeColor.symm _)=f (edgeColor.symm y); rw [← he u (edgeColor.symm y)]
    apply congr_arg f; apply edgeColor.injective; funext i; rw [armor_at]; simp [solid]
  intro x; simpa only [edgeColor.symm_apply_apply] using ht (edgeColor x)
lemma flagSite (f : BaseSites G n →L[ℝ] X) (he : ∀ u : G.El, ∀ v,f (armorG (solid u) v)=f v) : ∀ x,f x=0 := by
  have ht (x : Site n → G.Color) : f (gaugeColor.symm x)=0 := by
    apply slot_fixed h (f ∘L gaugeColor.symm.toContinuousLinearMap) ?_ x
    intro u y; change f (gaugeColor.symm _)=f (gaugeColor.symm y); rw [← he u (gaugeColor.symm y)]
    apply congr_arg f; apply gaugeColor.injective; funext i; rw [armorG_at]; simp [solid]
  intro x; simpa only [gaugeColor.symm_apply_apply] using ht (gaugeColor x)
end slots

def starsky (u : G.El) : Point G c f →L[ℝ] Point G c f :=
    (armor (solid u)).prodMap (armUp (solid u) (solid u))
lemma triple_star (h : G.Simple) {F : Point G c f → ℝ} (p : ∀ u : G.El, F∘starsky u =ᶠ[𝓝 0] F) (he : DifferentiableAt ℝ F 0) : fderiv ℝ F 0=0 := by
  let A := fderiv ℝ F 0
  have hp (u : G.El) (x : Point G c f) : A (starsky u x)= A x := chain_fixed _ (p u) he x
  let L := ContinuousLinearMap.inl ℝ (Link G c) (Vault G c f)
  let P := ContinuousLinearMap.inr ℝ (Link G c) (Vault G c f)
  let M := P ∘L ContinuousLinearMap.inl ℝ (Link G f) (BaseSites G c)
  let N := P ∘L ContinuousLinearMap.inr ℝ (Link G f) (BaseSites G c)
  have hl (u : G.El) x : starsky u (L x)=L (armor (solid u) x) := Prod.ext rfl (map_zero (armUp (solid (n:=f) u) (solid (n:=c) u)))
  have hm (u : G.El) x : starsky u (M x)=M (armor (solid u) x) := Prod.ext (map_zero (armor (solid (n:=c) u))) (Prod.ext rfl (map_zero (armorG (solid (n:=c) u))))
  have hn (u : G.El) x : starsky u (N x)=N (armorG (solid u) x) := Prod.ext (map_zero (armor (solid (n:=c) u))) (Prod.ext (map_zero (armor (solid (n:=f) u))) rfl)
  apply ContinuousLinearMap.ext; intro v
  rw [show v=L v.1 + M v.2.1 + N v.2.2 by
    apply Prod.ext
    · change v.1=v.1+0+0; simp
    exact Prod.ext (by change v.2.1=0+v.2.1+0; simp) (by change v.2.2=0+0+v.2.2; simp),map_add,map_add]
  change A _ + A _ + A _= 0
  have ha (x) : A (L x) = 0 := oneFlag h (A ∘L L) (fun u x => (congr_arg A (hl u x).symm).trans (hp u (L x))) x
  have hw (x) : A (M x) = 0 := oneFlag h (A ∘L M) (fun u x => (congr_arg A (hm u x).symm).trans (hp u (M x))) x
  have he (x) : A (N x) = 0 := flagSite h (A ∘L N) (fun u x => (congr_arg A (hn u x).symm).trans (hp u (N x))) x
  rw [ha,hw,he]; simp
end YM.Stationary
end

/-!
# Simultaneous constant-color covariance in centered patch. Used before
linearizing on the graph, so NOT assuming stationarity during this transport.
Group logarithm in rocket/shield still means the real germ.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f}

lemma point_shifts (u : G.El) (x : Point G c f) :
    Stationary.extend (starsky u x).2 = wages S (solid u) (solid u) (Stationary.extend x.2) := flare_color ..
lemma solid_color (u : G.El) (x : Point G c f) : input G c (starsky u x).1 = Lattice.gauge (solid u) (input G c x.1) := by
  change input G c (armor (solid u) _)=_; rw [← tincture, ← stain_cons]; rfl

section ramp
variable {p : Clip} {R : PathData G} {μ σ C Λ : ℝ}
    (h : S.patch.Branches S.kernel G) (t : S.Choices) (u : G.El)

include h
def ColorX (z : Point G c f) := Stationary.extend (starsky u z).2
def ColorV (z : Point G c f) := input G c (starsky u z).1
local notation "χ" => solid (n:=c) u
local notation "Χ" => solid (n:=f) u

omit h in
lemma tilt_f (U : Joint G c f) (L : Vault G c f) :
    Stationary.extend (armUp Χ χ L)*wages S Χ χ U=wages S Χ χ (Stationary.extend L*U) := arm_root ..
lemma enhance : ∀ᶠ z : Point G c f × Vault G c f in 𝓝 0,
    atire (fedora S t) (ColorX u z.1) (armUp Χ χ z.2) =
      wages S Χ χ (atire (fedora S t) (Stationary.extend z.1.2) z.2) := by
  let Y := Point G c f
  let Q := fun z : Y × Vault G c f => Stationary.extend z.2 * Stationary.extend z.1.2
  have he : Thaw Q 0 := (Thaw.through contDiffAt_snd).mul (Thaw.through (v:=fun y : Y × Vault G c f => y.1.2) contDiffAt_fst.snd)
  filter_upwards [fedora_u u t h he (by simp [Q])] with z hz; simp only [ColorX,atire,point_shifts (S:=S),arm_root]; exact hz

lemma drag :
    ∀ᶠ z : Point G c f × Vault G c f in 𝓝 0,
      rocket S t (fedora S t) (ColorX u z.1) (armUp Χ χ z.2)=armorG Χ (rocket S t (fedora S t) (Stationary.extend z.1.2) z.2) := by
  let Y := Point G c f × Vault G c f
  let F : Y → Joint G c f := fun z => Stationary.extend z.1.2
  let K := fedora S t (G:=G)
  let A (z : Y) : Coats G f := (shield S t (dress K (F z)))⁻¹ * shield S t (atire K (F z) z.2)
  have ht : A 0=1 := by simp [A]
  have hf : Thaw F 0 := Thaw.through contDiffAt_fst.snd
  have h0 : (F 0).1=1 := by simp [F]
  have hp : Thaw (fun z : Y => atire K (F z) z.2) 0 := sport_thaw (fedora_style h t) ((Thaw.through contDiffAt_snd).mul hf) (by simp [h0])
  have hb : Army A 0 := ((sport_thaw (fedora_style h t) hf h0).shields h t h0).inv.mul (hp.shields h t (he:=by simp [atire_zero]; exact h0))
  filter_upwards [enhance h t u,fedora_u u t h hf h0,(show Tendsto A (𝓝 0) (𝓝 1) from ht ▸ hb.cont.tendsto).eventually (frame_log_shift Χ)] with z hz hx hy
  rw [rocket,rocket, hz,map_neg]; apply congr_arg Neg.neg; change _=armorG Χ (frameLog (A z)); rw [← hy]
  rw [ColorX,point_shifts (S:=S),enroll_dress]
  simp only [show enroll S t (wages S Χ χ (Stationary.extend z.1.2))=_ from hx, shields S t h,A]; apply congr_arg frameLog; funext i
  simp only [← enroll_dress,Pi.mul_apply,Pi.inv_apply,F,K]
  group

variable (hp : R.Bounds p σ C Λ) (hy : 0<μ)
include hp hy

theorem veneration : ∀ᶠ z : Point G c f in 𝓝 0,
    bounty S p R μ t (fedora S t) (ColorV u z) (ColorX u z)= bounty S p R μ t (fedora S t) (input G c z.1) (Stationary.extend z.2) := by
  let U := fun z : Point G c f => Stationary.extend z.2
  let V := fun z : Point G c f => input G c z.1
  have hV (z : Point G c f) : ColorV u z=Lattice.gauge χ (V z) := solid_color u z
  have hU (z : Point G c f) : (ColorX u z).1=Lattice.gauge Χ (U z).1 := congrArg Prod.fst (point_shifts (S:=S) u z)
  let K := fedora S t (G:=G)
  let F := fun x : Point G c f × Vault G c f => atire K (ColorX u x.1) x.2
  have H := Thaw.through (v:=fun x : Point G c f => x.2) (x:=0) contDiffAt_snd
  have hX : Thaw (ColorX u (f:=f) (c:=c)) 0 := Thaw.through (v:=fun x : Point G c f => (starsky u x).2) (starsky u).contDiff.contDiffAt.snd
  have hx : ColorX u (0:Point G c f)=1 := by simp [ColorX]
  have he : Thaw F 0 := sport_thaw (fedora_style h t)
    ((Thaw.through contDiffAt_snd).mul (Thaw.comp (w:=Prod.fst) (g:=ColorX u (f:=f) (c:=c)) hX (x:=0) contDiffAt_fst)) (by simp [hx])
  have hl : ContDiffAt ℝ ω (fun z : Point G c f × Vault G c f => burnJoint S t p R K (ColorV u z.1) (ColorX u z.1) z.2) 0 := he.earn h t
    (by change (atire K (ColorX u (0:Point G c f)) 0).1=_; rw [atire_zero,hx]; rfl) (Army.powL (v:=fun z : Point G c f × Vault G c f => (starsky u z.1).1) (((starsky u).contDiff.contDiffAt.comp (f:=Prod.fst) (x:=0) contDiffAt_fst).fst)) hp
  have hu := explosive S t h (fedora_style h t) H (by simp)
  have hw : Tendsto (fun z : Point G c f => (z,(0 : Vault G c f))) (𝓝 0) (𝓝 0) := tendsto_id.prodMk_nhds tendsto_const_nhds
  filter_upwards [hw.eventually (hl.eventually (by simp)),hu,
    explosive S t h (fedora_style h t) hX (by rw [hx]; rfl),hw.eventually (eventually_eventually_nhds.mpr (drag h t u)), hw.eventually (eventually_eventually_nhds.mpr (enhance h t u))] with z hz hH hi hd he
  let L : Vault G c f →L[ℝ] Vault G c f := armUp Χ χ
  let D := tactics Χ χ
  have hf : ContDiffAt ℝ ω (burnJoint S t p R K (ColorV u z) (ColorX u z)) 0 := Work.F05.hold_jet (V:=fun z => burnJoint S t p R K (ColorV u z) (ColorX u z)) hz
  have hp' : burnJoint S t p R K (ColorV u z) (ColorX u z) ∘ L =ᶠ[𝓝 0] burnJoint S t p R K (V z) (U z) := by
    filter_upwards [Work.F05.hold_near (x:=z) (y:=(0:Vault G c f)) (V:=fun z => atire K (ColorX u z.1) (L z.2)=wages S Χ χ (atire K (U z.1) z.2)) he] with x hx'; simp only [hV,Function.comp_apply,burnJoint]; exact (congr_arg (muster S t p R _) hx').trans (root_wages S t h _ _ _ p R hp _)
  have hx' : indexX S t K (ColorX u z)*D= troop Χ *indexX S t K (U z) := by
    have he : rocket S t K (ColorX u z) ∘ L =ᶠ[𝓝 0] armorG Χ ∘ rocket S t K (U z) := Work.F05.hold_near (x:=z) (y:=0) hd
    exact rate_transfer (helmets _ _ _) (pocket (Lines G f 0)) _ _ he (market S t K _ hi) (market S t K _ hH)
  have hP := battery (U z).1 hy Χ
  have ht : cannonade S t μ K (ColorX u z)*D=troop Χ*cannonade S t μ K (U z) := by
    rw [cannonade,Matrix.add_mul, Matrix.mul_assoc, show rearM G c f*D=_ from rear_tactics Χ χ, ← Matrix.mul_assoc,hU,(troop_orthogonal Χ).transpose_cross (trench_orthogonal Χ) (mail_carry Χ _), Matrix.mul_assoc,cannonade,Matrix.mul_add, Matrix.mul_assoc (cannon μ _),hx', ← Matrix.mul_assoc (cannon μ _),hP.1,Matrix.mul_assoc]
  have hh : Dᵀ * medals S t p R μ K (ColorV u z) (ColorX u z) * D=medals S t p R μ K (V z) (U z) := by
    rw [medals,Matrix.mul_add, Matrix.add_mul,medals]; exact congr_arg₂ _ ((damage_rate _ (helmets G c f) _ _ hf).symm.trans (damage_congr _ hp')) (gram_bend _ _ _ (troop_orthogonal _) ht)
  have HG : (grenade μ (ColorX u z).1).det=(grenade μ (U z).1).det := by
    rw [hU]; exact (troop_orthogonal Χ).turn_det ((troop_orthogonal Χ).back hP.2)
  exact congr_arg₂ (fun x y => _ * Real.log x-Real.log y) ((tactics_orthogonal Χ χ).turn_det hh) HG
end ramp
end YM.Stationary
end

/-!
# Linear soldier sufficient for the quadratic bounty. Inherited loop
read here inherits the SAME stationarity choice/period; costs not given
by these fixed-mesh identities.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F : Forest S.ratio}

variable (p : Clip) (R : PathData G) (μ : ℝ) (S) (t : S.Choices)

def elevation (x : Point G c f) := bounty S p R μ t (fedora S t) (input G c x.1) (Stationary.extend x.2)
def saluteLe (W : Matrix (Body 1 f) (Body 1 c) ℝ) : Link G c →L[ℝ] Point G c f := (ContinuousLinearMap.id _ _).prod (endorse W)

lemma bonanza (V : Config G c) (U : Joint G c f) (K : Robe G c f) (he : Apparel K U) (hp : Explosives S t 1 (dress K U)) (hh : Shell S t p R V (dress K U)) :
    bounty S p R μ t K V U=bounty S p R μ t 1 V (dress K U) := by
  simp only [bounty,abides S t p R μ K V U he hp hh, Matrix.det_mul,det_transpose, shear_det K U he,mul_one,one_mul]; rfl

variable {S t p R μ} {σ A Λ η : ℝ} {P : ChartRatio G} {W : Matrix (Body 1 f) (Body 1 c) ℝ}
    {ρ : fieldDir G c 1 → AxisChart G F}

section step
variable (hc : Critical F p R ρ) (h : S.patch.Branches S.kernel G) (hp : R.Bounds p σ A Λ) (t : S.Choices) (hμ : 0<μ)
include hc h hp hμ
lemma moment_track (hz : PriceGap F p R η) (he : 0<η) :
    0<(medals S t p R μ (fedora S t) 1 1).det ∧ ContDiffAt ℝ ω (elevation S p R μ t) 0 := by
  obtain ⟨P,hP⟩ := LocalH.actual G
  have ht : 0 < (medals S t p R μ 1 (1:Config G c) 1).det := by simpa only [input_zero,encamp_zero hc] using (tribute hc h hp hz he hμ t hP).self_of_nhds.1
  let U := (1:Joint G c f)
  have hu : Thaw (fun _ : ℝ => U) 0 := Thaw.fixed _ _
  let K := fedora S t (G:=G)
  have hK := fedora_style h t
  have hf : dress K U=U := dressed_one hK
  have hi := (explosive S t h root_customs hu rfl).self_of_nhds
  have hh := (atire_out hK hu rfl).self_of_nhds
  have H : Shell S t p R 1 U := by simpa only [input_zero, encamp_zero hc] using (camp_station hc h hp t).self_of_nhds
  have h1 : 0 < (medals S t p R μ K 1 U).det := by
    have hb := abides S t p R μ K 1 U hh (by rw [hf]; exact hi) (by rw [hf]; exact H)
    rwa [hb,Matrix.det_mul,Matrix.det_mul,det_transpose,shear_det K U hh,one_mul,mul_one,hf]
  refine ⟨h1,?_⟩
  let Q := fun x : Point G c f => Stationary.extend x.2
  let V := fun x : Point G c f => input G c x.1
  have hQ : Q 0=1 := by simp [Q]
  have hV : V 0=1 := by simp [V]
  have hp' : Thaw Q 0 := Thaw.through (x:=0) contDiffAt_snd
  have hM := Memo.det_val (ammo_pay Q V hp' (by rw [hQ]; rfl) (by apply Army.powL (v:=Prod.fst); exact contDiffAt_fst) K hK h t hp hμ).2.1
  exact ContDiffAt.sub (ContDiffAt.mul contDiffAt_const (hM.log (by rw [hV,hQ]; exact h1.ne')))
    ((Memo.det_val (memo_flash hμ hp'.1).2.2).log (grenade_safe (Q 0).1 hμ).det_pos.ne')

lemma elect (hG : G.Simple) (W : Matrix (Body 1 f) (Body 1 c) ℝ) (hw : Guessed F W ρ) (hv : PriceGap F p R η) (hz : 0<η) :
    iteratedFDeriv ℝ 2 (honorarium F t μ p R ρ) 0 = iteratedFDeriv ℝ 2 (elevation S p R μ t ∘ saluteLe (G:=G) W) 0 := by
  let E := elevation S p R μ t
  have he : ∀ u : G.El, E ∘ starsky u =ᶠ[𝓝 0] E := fun u => veneration h t u hp hμ
  have hE : ContDiffAt ℝ ω E 0 := (moment_track hc h hp t hμ hv hz).2
  have hd : fderiv ℝ E 0=0 := triple_star hG he (hE.differentiableAt (by simp))
  let D := soldier F W t ρ
  let L := fun x : Link G c => (x,D x)
  let X := fun x => Stationary.extend (D x)
  let K := fedora S t (G:=G)
  have hm : Thaw X 0 := Thaw.through (soldier_diff hc h t)
  have hD : D 0=0 := soldier_zero hc h t
  have hX : (X 0).1=1 := by unfold X; rw [hD,extend_zero]; rfl
  have hh : Thaw (liftedUp F W ρ) 0 := liftedThaw hc
  have hl : E ∘ L=ᶠ[𝓝 0] honorarium F t μ p R ρ := by
    filter_upwards [atire_out (fedora_style h t) hm hX, explosive S t h root_customs (camp_thaw hc) (by rw [encamp_zero hc]; rfl),explosive S t h root_customs hh (by rw [lift_origin hc]; rfl), veteran_status hc h t (W:=W) hp,wage_live hc h (W:=W) t]
      with z hz hn hH hr ht
    have H : dress K (X z)=liftedUp F W ρ z := ht
    change bounty S p R μ t K (input G c z) (X z)=_
    rw [bonanza S p R μ t _ _ _ hz (by rw [H]; exact hH) (by rw [H]; exact hr), H]
    have he := bounty_carry h t (salute F W z) 1 (encamp F ρ z) (input G c z) hp hn hH hμ (by rw [gauge_one]; exact hr.1)
    rw [gauge_one] at he; exact he
  let T := saluteLe (G:=G) W
  have hT : HasFDerivAt L T 0 := by
    have hd := (soldier_diff hc h t (W:=W)).differentiableAt (by simp) |>.hasFDerivAt
    rw [soldier_known hc h t hw] at hd
    exact (hasFDerivAt_id _).prodMk hd
  have H : L 0=0 := Prod.ext rfl hD
  rw [← (hl.iteratedFDeriv ℝ 2).eq_of_nhds]
  ext1 v
  rw [show v=![v 0,v 1] by funext i; fin_cases i <;> rfl]
  rw [(Work.F03.hessian_comp H (hE.of_le le_top) (contDiffAt_id.prodMk (soldier_diff hc h t |>.of_le le_top)) hd).2, hT.fderiv,
       (Work.F03.hessian_comp (g:=T) T.map_zero (hE.of_le le_top) (T.contDiff.contDiffAt) hd).2,T.fderiv]

omit hμ
include t
lemma inherited_le (W : Matrix (Body 1 f) (Body 1 c) ℝ) (hw : Guessed F W ρ) :
    iteratedFDeriv ℝ 2 (burnished F R ρ) 0=iteratedFDeriv ℝ 2 ((turnSeries (m:=f) R.loop) ∘ uniformM (G:=G) W) 0 := by
  let D := soldier F W t ρ
  have hf : burnished F R ρ =ᶠ[𝓝 0] (turnSeries (m:=f) R.loop) ∘ (fun z => (D z).1) := by
    filter_upwards [wage_live (W:=W) hc h t] with z hz
    have hp : (Precision.loop R ((liftedUp F W ρ z).1))=Precision.loop R (encamp F ρ z).1 := Work.F05.loop_gauge hp ..
    rw [← hz] at hp; exact hp.symm
  have he := turns_analytic R.loop hp.width hp.two (m:=f)
  have hd : fderiv ℝ (turnSeries R.loop (m:=f)) 0=0 := by
    have hv := turns_low R.loop hp.width hp.two (m:=f)
    have ht := (rays_jet he _).1 hv 1 (by decide)
    apply ContinuousLinearMap.ext; intro x
    simpa  [iteratedFDeriv_one_apply] using DFunLike.congr_fun ht ![x]
  have hD : D 0=0 := soldier_zero hc h t
  have ht : fderiv ℝ (fun z => (D z).1) 0=uniformM W := by
    let L := ContinuousLinearMap.fst ℝ (Link G f) (BaseSites G c)
    have hp := fderiv_comp (0:Link G c) (g:=L) (f:=D) L.differentiableAt ((soldier_diff hc h t).differentiableAt (by simp))
    rw [L.fderiv, show fderiv ℝ D 0=_ from soldier_known hc h t hw] at hp; exact hp
  let T := uniformM (G:=G) W
  rw [(hf.iteratedFDeriv ℝ 2).eq_of_nhds]; ext1 v
  rw [show v=![v 0,v 1] by funext i; fin_cases i <;> rfl]
  rw [(Work.F03.hessian_comp (show (D 0).1=0 from congrArg Prod.fst hD) he.contDiffAt ((soldier_diff hc h t |>.of_le le_top).fst) hd).2, ht,
    (Work.F03.hessian_comp (g:=T) T.map_zero he.contDiffAt (T.contDiff.contDiffAt) hd).2,T.fderiv]
end step
end YM.Stationary
end

/-! # Matrix trace-log derivatives, real and in finite counting conventions. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module Finset
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f}
variable {j m k : Type} {X Y : Type}
section vectors
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def directionM (M : X → Matrix j k ℝ) (x u : X) := Matrix.of fun i b => fderiv ℝ (fun a => M a i b) x u
def bendM (M : X → Matrix j k ℝ) (x u v : X) := Matrix.of fun i b => iteratedFDeriv ℝ 2 (fun a => M a i b) x ![u,v]
lemma directions_congr {M N : X→ Matrix j k ℝ} {x u : X} (he : M =ᶠ[𝓝 x] N) : directionM M x u=directionM N x u := by
  ext i j; simp only [directionM,Matrix.of_apply,show fderiv ℝ (fun a => M a i j) x=fderiv ℝ (fun a => N a i j) x from Filter.EventuallyEq.fderiv_eq (he.mono fun a ha => congr_arg (fun f => (f : Matrix _ _ ℝ) i j) ha)]
lemma direction_zero (L : Matrix j k ℝ) (x y : X) : directionM (fun _ => L) x y=0 := by ext; simp [directionM]
lemma divided {M : X→ Y} {x} (u v : X) (h : ContDiffAt ℝ ω M x) : fderiv ℝ (fun a => fderiv ℝ M a v) x u=iteratedFDeriv ℝ 2 M x ![u,v] := by
  have hv := (ContinuousLinearMap.apply ℝ Y v).hasFDerivAt.comp x ((h.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)).hasFDerivAt
  change HasFDerivAt (fun a => fderiv ℝ M a v) _ _ at hv
  rw [iteratedFDeriv_two_apply,hv.fderiv]; rfl
lemma memo_corner {M : X → Matrix j k ℝ} {x} (h : Memo M x) (u) : Memo (fun a => directionM M a u) x := fun i j => ((h i j).fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const
lemma coins_M {M : X → Matrix j k ℝ} {x} (h : Memo M x) (u v : X) : directionM (fun a => directionM M a v) x u=bendM M x u v := by
  ext i j; exact divided _ _ (h i j)
lemma direction_prod [Fintype k] {U : X→Matrix j k ℝ} {V : X→Matrix k m ℝ} {x} (hu : Memo U x) (hv : Memo V x) (y) :
    directionM (fun u => U u * V u) x y = directionM U x y * V x + U x * directionM V x y := by
  ext i j; simp only [directionM,Matrix.of_apply,Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]; rw [fderiv_fun_sum, _root_.sum_apply]
  · refine Finset.sum_congr rfl fun k _ => ?_; rw [fderiv_fun_mul ((hu i k).differentiableAt (by simp)) ((hv k j).differentiableAt (by simp))]; simp; ring
  intro k _; exact ((hu i k).mul (hv k j)).differentiableAt (by simp)

variable [Fintype k] [DecidableEq k]
omit [DecidableEq k] in
lemma eventually_memo {U : X→Funds k} {x} (h : Memo U x) : ∀ᶠ y in 𝓝 x, Memo U y :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => (h i j).eventually (by simp)
lemma direction_inverse {U : X→Funds k} {x} (h : Memo U x) (he : (U x).det ≠ 0) (y) :
    directionM (fun a => (U a)⁻¹) x y= -((U x)⁻¹ * directionM U x y * (U x)⁻¹) := by
  let F := fun a => (U a)⁻¹
  have heq : (fun a => F a * U a) =ᶠ[𝓝 x] fun _ => (1:Funds k) := by
    filter_upwards [h.det_val.continuousAt.eventually_ne he] with i hi
    exact nonsing_inv_mul _ hi.isUnit
  have hu : directionM (fun z => (U z)⁻¹ * U z) x y=0 := (directions_congr heq).trans (direction_zero ..)
  rw [direction_prod (Memo.flip h he) h] at hu
  have hp := eq_neg_of_add_eq_zero_left hu
  have hv := congr_arg (fun b => b * (U x)⁻¹) hp
  simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ he.isUnit, neg_mul] using hv

omit [DecidableEq k] in
lemma direction_trace {U : X→Funds k} {x} (h : Memo U x) (u : X) : fderiv ℝ (fun z => (U z).trace) x u=(directionM U x u).trace := by
  simp only [trace,diag_apply,directionM,Matrix.of_apply]; rw [fderiv_fun_sum,_root_.sum_apply]
  exact fun i _ => (h i i).differentiableAt (by simp)

open Polynomial
-- jacobi formula checked at unit; route to any det-ne-zero real matrix
private lemma identity_line (M : Funds k) : HasDerivAt (fun x : ℝ => ((1:Funds k)+x • M).det) M.trace 0 := by
  let P := (1:Matrix k k (Polynomial ℝ)) + (Polynomial.X:Polynomial ℝ) • M.map Polynomial.C
  have h := (Polynomial.hasDerivAt P.det 0)
  rw [show eval 0 (Polynomial.derivative P.det)=_ from derivative_det_one_add_X_smul M] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  change _=eval x P.det; rw [eval_det]
  change (1+x • M).det=_
  apply congr_arg Matrix.det; ext i j; rw [matPolyEquiv_eval]
  unfold P; by_cases h : i=j <;> simp [h] <;> ring

lemma det_line (M A : Funds k) (h : A.det≠0) :
    HasDerivAt (fun x : ℝ => (A+x • M).det) (A.det*(A⁻¹*M).trace) 0 := by
  refine ((identity_line (A⁻¹*M)).const_mul _).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [← det_mul, Matrix.mul_add, Matrix.mul_one,Matrix.mul_smul,← mul_assoc A (A⁻¹), Matrix.mul_nonsing_inv A h.isUnit,Matrix.one_mul]

end vectors
end YM.Stationary
end

/-! # Real log trace derivatives. Uses determinant NE ZERO; sign in clients. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module Finset
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {c f n : Side} {S : StepData c f}

-- choose Pi instances explicitly for calculus here only
section matrix
open scoped Matrix.Norms.Elementwise
variable {ι : Type} [Fintype ι] [DecidableEq ι]
private lemma funds_smooth (U : Funds ι) : ContDiffAt ℝ ω (fun x : Funds ι => x.det) U := by
  apply Memo.det_val (P:=fun x => x)
  intro i j
  exact (contDiffAt_apply ℝ ℝ j _).comp _ (contDiffAt_apply ℝ (ι→ℝ) i _)
lemma det_one_way {M : ℝ→Funds ι} (x : ℝ) (L : Funds ι) (hp : ∀ i j, HasDerivAt (fun z => M z i j) (L i j) x) (hv : (M x).det≠0) :
    HasDerivAt (fun z => (M z).det) ((M x).det * ((M x)⁻¹ *L).trace) x := by
  let A := M x
  have hm : HasDerivAt M L x := hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr (hp i)
  have hf := (funds_smooth A).differentiableAt (by simp) |>.hasFDerivAt
  have he : HasDerivAt (fun v : ℝ => A+v • L) L 0 := (ray_id L).const_add A
  have hh := (det_line L A hv).unique ((show HasFDerivAt (fun x : Funds ι => x.det) (fderiv ℝ (fun x : Funds ι => x.det) A) (A+(0:ℝ) • L) by rw [zero_smul, add_zero]; exact hf).comp_hasDerivAt 0 he)
  change HasDerivAt _ (A.det * (A⁻¹*L).trace) x
  rw [hh]; exact hf.comp_hasDerivAt x hm
end matrix
section trace
variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {P Q : X → Funds ι} {x u v : X}
lemma trace_log_first (h : Memo P x) (hp : (P x).det≠0) (u) :
    fderiv ℝ (fun z => Real.log (P z).det) x u=((P x)⁻¹*directionM P x u).trace := by
  let F := fun z => Real.log (P z).det
  let U := P x
  have he : ContDiffAt ℝ ω F x := h.det_val.log hp
  let g := fun a : ℝ => x+a • u
  have hh : g 0=x := by simp [g]
  have hx : HasDerivAt g u 0 := by unfold g; simpa using! (ray_id u).const_add x
  have hh' := (show HasFDerivAt F (fderiv ℝ F x) (g 0) by rw [hh]; exact (he.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt 0 hx
  let L := directionM P x u
  apply hh'.unique
  have hm := det_one_way (M:=fun a => P (g a)) 0 L (fun i j => HasFDerivAt.comp_hasDerivAt 0
    (show HasFDerivAt (fun v => P v i j) (fderiv ℝ (fun v => P v i j) x) (g 0) by rw [hh]; exact ((h i j).differentiableAt (by simp)).hasFDerivAt) hx) (show (P (g 0)).det≠0 by rw [hh]; exact hp)
  have hu : HasDerivAt (F ∘ g) ((P (g 0)).det * ((P (g 0))⁻¹*L).trace / (P (g 0)).det) 0 := hm.log (by rw [hh]; exact hp)
  rw [hh,mul_div_cancel_left₀ _ hp] at hu; exact hu

lemma trace_log (h : Memo P x) (u v : X) (he : (P x).det≠0) : iteratedFDeriv ℝ 2 (fun y => Real.log (P y).det) x ![u,v] =
    ((P x)⁻¹*bendM P x u v).trace - ((P x)⁻¹ * directionM P x u * (P x)⁻¹ * directionM P x v).trace := by
  have hp : (fun i => fderiv ℝ (fun y => Real.log (P y).det) i v)=ᶠ[𝓝 x]
      fun i => ((P i)⁻¹ * directionM P i v).trace := by
    filter_upwards [h.det_val.continuousAt.eventually_ne he,eventually_memo h] with i hi hv; exact trace_log_first hv hi v
  let F := fun z => (P z)⁻¹
  let L := fun i => directionM P i v
  have hF : Memo F x := h.flip he
  have hL : Memo L x := memo_corner h v
  rw [← divided u v (h.det_val.log he),hp.fderiv_eq, direction_trace (Memo.cross hF hL) u,direction_prod hF hL u]
  unfold F L; rw [direction_inverse h he,coins_M h,neg_mul,Matrix.trace_add, Matrix.trace_neg]; abel
omit [Fintype ι] [DecidableEq ι] in
lemma direction_add (h : Memo P x) (he : Memo Q x) (u) : directionM (P+Q) x u=directionM P x u+directionM Q x u := by
  ext i j; simp only [directionM,Matrix.of_apply,Pi.add_apply, Matrix.add_apply,fderiv_fun_add ((h i j).differentiableAt (by simp)) ((he i j).differentiableAt (by simp)), _root_.add_apply]
omit [Fintype ι] [DecidableEq ι] in
lemma bend_add (h : Memo P x) (he : Memo Q x) (u v) : bendM (P+Q) x u v=bendM P x u v+bendM Q x u v := by
  ext i j
  have hr := iteratedFDeriv_add_apply (i:=2) (f:=fun z => P z i j) (g:=fun z => Q z i j) (h i j |>.of_le le_top) (he i j |>.of_le le_top)
  exact congr($(hr) (![u,v]))
lemma after_contact (h : Memo P 0) (he : Memo Q 0) (hp : (P 0).det≠0) (hy : Q 0=0) (u v) :
    iteratedFDeriv ℝ 2 (fun y => Real.log ((P+Q) y).det) 0 ![u,v] =
    iteratedFDeriv ℝ 2 (fun y => Real.log (P y).det) 0 ![u,v] + iteratedFDeriv ℝ 2 (fun y => ((P y)⁻¹ * Q y).trace) 0 ![u,v] -
      ((P 0)⁻¹ * directionM Q 0 u * (P 0)⁻¹ * directionM Q 0 v).trace := by
  have hx := h.flip hp
  let F := fun y => (P y)⁻¹
  let M := P 0
  let G := Q
  have hh : Memo (fun y => F y*Q y) 0 := Memo.cross hx he
  have hs : ContDiffAt ℝ ω (fun y => (F y*Q y).trace) 0 := ContDiffAt.sum fun i _ => hh i i
  have hk : (fun a => fderiv ℝ (fun y => (F y * Q y).trace) a v)=ᶠ[𝓝 0]
      fun a => (directionM F a v *Q a + F a *directionM Q a v).trace := by
    filter_upwards [eventually_memo (U:=F) hx,eventually_memo he] with x h h'; rw [direction_trace (U:=fun y => F y * Q y) (Memo.cross h h'),direction_prod h h']
  rw [trace_log (Memo.twice h he) _ _ (by simp [hp,hy]),trace_log h _ _ hp, ← divided u v hs,hk.fderiv_eq]
  have hm := direction_trace (U:= (fun y => directionM F y v *Q y) + fun y => F y *directionM Q y v)
    (Memo.twice (Memo.cross (memo_corner (M:=F) hx v) he) (Memo.cross hx (memo_corner he v))) u
  rw [direction_add (Memo.cross (memo_corner (M:=F) hx v) he) (Memo.cross hx (memo_corner he v)) _] at hm
  rw [direction_prod (U:=fun a => directionM F a v) (memo_corner hx v) he u,direction_prod hx (memo_corner he v) u] at hm
  unfold F at hm; simp only [hy, Matrix.mul_zero,zero_add] at hm
  simp only [Pi.add_apply] at hm
  unfold F
  rw [hm,Pi.add_apply,hy,add_zero,bend_add h he,direction_add h he,direction_add h he]
  simp only [Matrix.mul_add, Matrix.add_mul,Matrix.trace_add,direction_inverse h hp,coins_M he,neg_mul,Matrix.trace_neg]
  have ht (A B C : Funds ι) : (A * B * A * C).trace=(A * C * A * B).trace := by rw [mul_assoc (A*B),trace_mul_comm, ← mul_assoc]
  rw [ht _ (directionM P 0 v) (directionM Q 0 u)]; abel
end trace
end YM.Stationary
end
