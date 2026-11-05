import YM.Next.STATIONARY.Joint.Drift

set_option autoImplicit false
/-! # Third/fourth tensors of the scalar stationary envelope. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module Finset
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

open Analysis
lemma threeFold (F : X → Y) (x u v w : X) : iteratedFDeriv ℝ 3 F x ![u,v,w] =
    fderiv ℝ (fderiv ℝ (fderiv ℝ F)) x u v w := by
  rw [iteratedFDeriv_succ_apply_right,iteratedFDeriv_two_apply]; rfl
lemma direction2 (F : X→Y) (x u v : X) (h : ContDiffAt ℝ ω F x) :
    D u (D v F) x=iteratedFDeriv ℝ 2 F x ![u,v] := divided u v h
lemma combine3 {F : Y → Z} {g : X → Y} {x : X} (h : ContDiffAt ℝ ω F (g x))
    (p : ContDiffAt ℝ ω g x) (a b c : X) :
    let i := g x
    let t a := fderiv ℝ g x a
    let u a b := iteratedFDeriv ℝ 2 g x ![a,b]
    iteratedFDeriv ℝ 3 (F ∘ g) x ![a,b,c]=
      iteratedFDeriv ℝ 3 F i ![t a,t b,t c]
        + iteratedFDeriv ℝ 2 F i ![t a,u b c]+
          iteratedFDeriv ℝ 2 F i ![u a b,t c]+
          iteratedFDeriv ℝ 2 F i ![t b,u a c]+
          fderiv ℝ F i (iteratedFDeriv ℝ 3 g x ![a,b,c]) := by
  intro i t u
  let A (y : X) := fderiv ℝ F (g y)
  let B (y : X) := fderiv ℝ (fderiv ℝ F) (g y)
  let c' y := fderiv ℝ g y c
  let b' y := fderiv ℝ g y b
  let d y := fderiv ℝ (fderiv ℝ g) y b c
  have hu : (fun z => iteratedFDeriv ℝ 2 (F ∘ g) z ![b,c])=ᶠ[𝓝 x] (fun y => A y (d y)+B y (b' y) (c' y)) := by
    filter_upwards [p.eventually (by simp),p.continuousAt.tendsto.eventually (h.eventually (by simp))] with z ht hh
    rw [pay_second hh ht,iteratedFDeriv_two_apply,iteratedFDeriv_two_apply]; rfl
  have hl : iteratedFDeriv ℝ 3 (F ∘ g) x ![a,b,c]= D a (fun z => iteratedFDeriv ℝ 2 (F∘g) z ![b,c]) x := cons_jet ((h.comp _ p).of_le le_top) _ _
  have hp n := h.of_le (show (n:WithTop ℕ∞)≤ω from le_top)
  have hx := (h.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  have hB := ((h.fderiv_right (m:=ω) (by simp)).fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  have hG := p.differentiableAt (by simp)
  have ha : DifferentiableAt ℝ A x := hx.comp _ hG
  have hb : DifferentiableAt ℝ B x := hB.comp _ hG
  have ht (u) : DifferentiableAt ℝ (D u g) x := (dSmooth p u (m:=ω) (by simp)).differentiableAt (by simp)
  have hm : DifferentiableAt ℝ d x := by
    have hu := ((p.fderiv_right (m:=ω) (by simp)).fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
    exact ((hu.clm_apply (u:=fun _ => b) (differentiableAt_const _)).clm_apply (u:=fun _ => c) (differentiableAt_const _))
  have he y : iteratedFDeriv ℝ 2 g y ![b,c]=d y := by rw [iteratedFDeriv_two_apply]; rfl
  have hD : fderiv ℝ d x a=iteratedFDeriv ℝ 3 g x ![a,b,c] := (by
    have hi : iteratedFDeriv ℝ 3 g x ![a,b,c]= D a (fun z => iteratedFDeriv ℝ 2 g z ![b,c]) x := cons_jet (p.of_le le_top) a ![b,c]; simp_rw [he] at hi; exact hi.symm)
  rw [hl,GermD a hu,D,fderiv_fun_add (ha.clm_apply hm) ((hb.clm_apply (u:=b') (ht b)).clm_apply (u:=c') (ht c)), fderiv_clm_apply ha hm,fderiv_clm_apply (hb.clm_apply (u:=b') (ht b)) (u:=c') (ht c), fderiv_clm_apply hb (u:=b') (ht b)]
  simp only [_root_.add_apply, ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_apply]
  rw [show fderiv ℝ A x=_ from fderiv_comp _ hx hG, show fderiv ℝ B x=_ from fderiv_comp _ hB hG,show fderiv ℝ b' x a=u a b from direction2 g x a b p, show fderiv ℝ c' x a=u a c from direction2 g x a c p,hD]
  simp only [ContinuousLinearMap.comp_apply]
  rw [threeFold F i,iteratedFDeriv_two_apply,iteratedFDeriv_two_apply,iteratedFDeriv_two_apply]; rw [show d x=u b c from (he x).symm]; change
    A x (iteratedFDeriv ℝ 3 g x ![a,b,c])+ B x (t a) (u b c)+
      (B x (t b) (u a c)+(B x (u a b) (t c)+fderiv ℝ (fderiv ℝ (fderiv ℝ F)) i (t a) (t b) (t c)))=fderiv ℝ (fderiv ℝ (fderiv ℝ F)) i (t a) (t b) (t c)+B x (t a) (u b c)+B x (u a b) (t c)+B x (t b) (u a c)+A x (iteratedFDeriv ℝ 3 g x ![a,b,c])
  abel
end YM.Stationary
end

/-!
# Stationary differentiation while V varies. Tested on fixed real
period. Does not assume any volume-independent analysis; inputs from
actual representative of same tag. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module Finset Analysis
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable (F : X×Y → ℝ) (S : X→Y)
def viewS (x : X) : X×Y := (x,S x)
def fieldT (x : X) := fderiv ℝ (viewS S) 0 x
def fieldU (x y : X) : X×Y := iteratedFDeriv ℝ 2 (viewS S) 0 ![x,y]

structure Stayed : Prop where
  origin : ContDiffAt ℝ ω F 0
  zero : S 0=0
  path : ContDiffAt ℝ ω S 0
  rate : ∀ᶠ v in 𝓝 0, fderiv ℝ (fun y : Y => F (v,y)) (S v)=0
variable {F S} (hs : Stayed F S)
include hs
namespace Stayed
lemma H0 : viewS S 0=0 := Prod.ext rfl hs.zero
lemma hl : ContDiffAt ℝ ω (viewS S) 0 := contDiffAt_id.prodMk hs.path
lemma center : ContDiffAt ℝ ω (F ∘ viewS S) 0 := (show ContDiffAt ℝ ω F (viewS S 0) by rw [H0 hs]; exact hs.origin).comp 0 (hl hs)
lemma margin : ∀ᶠ v in 𝓝 0, ∀ y : Y, fderiv ℝ F (viewS S v) (0,y)=0 := by
  filter_upwards [hs.rate, ((hl hs).continuousAt.tendsto).eventually (by rw [H0 hs]; exact hs.origin.eventually (by simp))] with i hi hp y
  let g := fun y : Y => (i,y)
  let J := ContinuousLinearMap.inr ℝ X Y
  have he : HasFDerivAt g J (S i) := (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  exact DFunLike.congr_fun (((hp.differentiableAt (by simp) |>.hasFDerivAt.comp (S i) he).fderiv ).symm.trans hi) y
lemma rim (a : X) : (fderiv ℝ (viewS S) 0 a).1=a := by
  have hp := (hl hs).differentiableAt (by simp)
  let L := ContinuousLinearMap.fst ℝ X Y
  have hx := fderiv_comp (0:X) L.differentiableAt hp
  change fderiv ℝ id 0=fderiv ℝ L _ ∘L fderiv ℝ (viewS S) 0 at hx; rw [fderiv_id,L.fderiv] at hx
  exact (DFunLike.congr_fun hx a).symm
lemma pledge (a : X) : D a (F ∘ viewS S)=ᶠ[𝓝 0] D (fieldT S a) F ∘ (viewS S) := by
  filter_upwards [margin hs,(hl hs).eventually (by simp), ((hl hs).continuousAt.tendsto).eventually (by rw [H0 hs]; exact hs.origin.eventually (by simp))] with i hi he hp
  have hg := he.differentiableAt (by simp)
  have ht : (fderiv ℝ (viewS S) i a).1=a := by
    let L := ContinuousLinearMap.fst ℝ X Y
    have hx := fderiv_comp i L.differentiableAt hg
    change fderiv ℝ id i=fderiv ℝ L _ ∘L fderiv ℝ (viewS S) i at hx; rw [fderiv_id,L.fderiv] at hx
    exact (DFunLike.congr_fun hx a).symm
  rw [D,fderiv_comp _ (hp.differentiableAt (by simp)) hg, ContinuousLinearMap.comp_apply]
  change _= fderiv ℝ F (viewS S i) (fieldT S a)
  apply sub_eq_zero.mp; rw [← map_sub]
  rw [show _-fieldT S a=(0,(fderiv ℝ (viewS S) i a).2-(fieldT S a).2) from Prod.ext (by rw [Prod.fst_sub,ht,show (fieldT S a).1=a from rim hs a,sub_self]) rfl,hi]
lemma lower (a b : X) : fieldU S a b=(0,(fieldU S a b).2) := by
  refine Prod.ext ?_ rfl
  let L := ContinuousLinearMap.fst ℝ X Y
  have hp : iteratedFDeriv ℝ 2 (L ∘ viewS S) 0 ![a,b]=L (fieldU S a b) := by
    rw [ContinuousLinearMap.iteratedFDeriv_comp_left _ (hl hs) le_top]; rfl

  rw [show L ∘ viewS S=id from rfl,iteratedFDeriv_two_apply] at hp
  simp only [show fderiv ℝ (id:X→X)=fun _ => ContinuousLinearMap.id ℝ X from funext (fun _ => fderiv_id ..),show fderiv ℝ (fun _ : X => ContinuousLinearMap.id ℝ X) 0=0 from (hasFDerivAt_const ..).fderiv,_root_.zero_apply] at hp
  exact hp.symm
lemma under (a b c : X) : (iteratedFDeriv ℝ 3 (viewS S) 0 ![a,b,c]).1 = 0 := by
  let L := ContinuousLinearMap.fst ℝ X Y
  have hp : iteratedFDeriv ℝ 3 (L ∘ viewS S) 0 ![a,b,c]=L (iteratedFDeriv ℝ 3 (viewS S) 0 ![a,b,c]) := by
    rw [ContinuousLinearMap.iteratedFDeriv_comp_left _ (hl hs) le_top]; rfl
  rw [show L ∘ viewS S=id from rfl,threeFold] at hp
  simp only [show fderiv ℝ (id:X→X)=fun _ => ContinuousLinearMap.id ℝ X from funext (fun _ => fderiv_id ..),show fderiv ℝ (fun _ : X => ContinuousLinearMap.id ℝ X)=0 from funext (fun _ => (hasFDerivAt_const ..).fderiv), fderiv_zero, Pi.zero_apply, _root_.zero_apply] at hp
  exact hp.symm

-- k_p(Q grad) identities
lemma hedge (u : Y) (a : X) : iteratedFDeriv ℝ 2 F 0 ![fieldT S a,(0,u)]=0 := by
  have he : D (0,u) F ∘ viewS S=ᶠ[𝓝 0] 0 := (margin hs).mono (fun _ hp => hp u)
  have hh := (dSmooth hs.origin ((0:X),u) (m:=ω) (by simp)).differentiableAt (by simp)
  have hv : fderiv ℝ (D (0,u) F) 0 (fieldT S a)=0 := by
    have hp := he.fderiv_eq (𝕜:=ℝ)
    rw [fderiv_comp (0:X) (by rw [H0 hs]; exact hh) ((hl hs).differentiableAt (by simp)),H0 hs,fderiv_zero] at hp
    exact DFunLike.congr_fun hp a
  rwa [show fderiv ℝ (D ((0:X),u) F) 0 (fieldT S a)=iteratedFDeriv ℝ 2 F 0 ![fieldT S a,(0,u)] from divided _ _ hs.origin] at hv
lemma reserve (u : Y) (a b : X) : iteratedFDeriv ℝ 3 F 0 ![(0,u),fieldT S a,fieldT S b]= - iteratedFDeriv ℝ 2 F 0 ![fieldU S a b,(0,u)] := by
  have he : D (0,u) F ∘ viewS S=ᶠ[𝓝 0] 0 := (margin hs).mono (fun _ hp => hp u)
  have hh := dSmooth hs.origin ((0:X),u) (m:=ω) (by simp)
  have hv := DFunLike.congr_fun ((he.iteratedFDeriv ℝ 2).eq_of_nhds) ![a,b]
  rw [pay_second (by rw [H0 hs]; exact hh) (hl hs), H0 hs] at hv
  rw [show iteratedFDeriv ℝ 3 F 0 ![(0,u),fieldT S a,fieldT S b]=_ from cons_inner (hs.origin.of_le le_top) ((0:X),u) ![fieldT S a,fieldT S b]]
  apply eq_neg_of_add_eq_zero_right
  rw [show fderiv ℝ _ _ _=_ from (show fderiv ℝ (D ((0:X),u) F) 0 (iteratedFDeriv ℝ 2 (viewS S) 0 ![a,b])=iteratedFDeriv ℝ 2 F 0 ![fieldU S a b,(0,u)] from divided _ _ hs.origin) ] at hv
  simp only [iteratedFDeriv_two_apply,fderiv_zero,Pi.zero_apply,_root_.zero_apply] at hv
  rw [iteratedFDeriv_two_apply,iteratedFDeriv_two_apply]
  exact hv

lemma accrue (a b c : X) : iteratedFDeriv ℝ 3 (F∘viewS S) 0 ![a,b,c]=iteratedFDeriv ℝ 3 F 0 ![fieldT S a,fieldT S b,fieldT S c] := by
  let U := D (fieldT S a) F
  have he : ContDiffAt ℝ ω U (viewS S 0) := by rw [H0 hs]; exact dSmooth hs.origin _ (by simp)
  have hb : iteratedFDeriv ℝ 3 (F∘viewS S) 0 ![a,b,c]=iteratedFDeriv ℝ 2 (U∘viewS S) 0 ![b,c] := by
    rw [show iteratedFDeriv ℝ 3 (F∘viewS S) 0 ![a,b,c]=_ from cons_inner ((center hs).of_le le_top) a ![b,c]]; exact DFunLike.congr_fun (((pledge hs a).iteratedFDeriv ℝ 2).eq_of_nhds) _
  rw [hb,pay_second he (hl hs),H0 hs, show fderiv ℝ U 0 (iteratedFDeriv ℝ 2 (viewS S) 0 ![b,c])=_ from divided (fieldU S b c) (fieldT S a) hs.origin,
    Work.F03.hessian_symmetric (hs.origin.of_le le_top)]
  rw [lower hs b c, hedge hs,zero_add]; exact (cons_inner (hs.origin.of_le le_top) (fieldT S a) ![fieldT S b,fieldT S c]).symm
lemma tally (a b c d : X) :
    let P:=iteratedFDeriv ℝ 3 F 0
    iteratedFDeriv ℝ 4 (F∘viewS S) 0 ![a,b,c,d]=iteratedFDeriv ℝ 4 F 0 ![fieldT S a,fieldT S b,fieldT S c,fieldT S d]+
      P ![fieldU S c d,fieldT S a,fieldT S b]+
      P ![fieldU S b c,fieldT S a,fieldT S d]+
      P ![fieldU S b d,fieldT S a,fieldT S c] := by
  intro P
  let U := D (fieldT S a) F
  have he : ContDiffAt ℝ ω U 0 := dSmooth hs.origin _ (by simp)
  have hp : iteratedFDeriv ℝ 4 (F∘viewS S) 0 ![a,b,c,d]=iteratedFDeriv ℝ 3 (U∘viewS S) 0 ![b,c,d] :=
    (cons_inner ((center hs).of_le le_top) a ![b,c,d]).trans <| DFunLike.congr_fun (((pledge hs a).iteratedFDeriv ℝ 3).eq_of_nhds) _
  have ht := combine3 (show ContDiffAt ℝ ω U (viewS S 0) by rw [H0 hs]; exact he) (hl hs) b c d
  dsimp only at ht; rw [H0 hs] at ht
  let g := iteratedFDeriv ℝ 3 (viewS S) 0 ![b,c,d]
  have hi : fderiv ℝ U 0 g=0 := by
    rw [show fderiv ℝ U 0 g=_ from divided g (fieldT S a) hs.origin, Work.F03.hessian_symmetric _, show g=(0,g.2) from Prod.ext (under hs b c d) rfl, hedge hs]; exact hs.origin.of_le le_top
  have hw (x y) : P ![x,fieldT S a,y]=iteratedFDeriv ℝ 2 U 0 ![x,y] := by
    rw [show P ![x,fieldT S a,y]=P ![fieldT S a,x,y] from ?_]; exact cons_inner (hs.origin.of_le le_top) _ _
    have hb : ![x,fieldT S a,y]=![fieldT S a,x,y] ∘ (Equiv.swap (0:Fin 3) 1) := by ext1 i; fin_cases i <;> rfl
    rw [hb]; exact sym_Jet (hs.origin.of_le le_top) _ _
  rw [hp,ht,show fderiv ℝ U 0 _=0 from hi,add_zero,hw,hw,hw,
    show iteratedFDeriv ℝ 4 F 0 ![fieldT S a,fieldT S b,fieldT S c,fieldT S d]=_ from cons_inner (hs.origin.of_le le_top) (fieldT S a) ![fieldT S b,fieldT S c,fieldT S d]]
  rw [Work.F03.hessian_symmetric (he.of_le le_top) _ (fieldT S b),Work.F03.hessian_symmetric (he.of_le le_top) _ (fieldT S c)]; rfl
end Stayed
end YM.Stationary
end

/-!
# Classical exchange on linear stationary representative, ACTUAL grids.
Gauge invertibility and reference measure used (no marked-root sector removed).
Exact spatial germ matching to third & fourth.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module Finset Analysis
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio}

section projection
variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (N H : Funds n) (L : Matrix m n ℝ) (D : Matrix n m ℝ)
    (he : IsUnit N.det) (hi : IsUnit (L*D).det) (hv : H*D=0) (hH : Hᵀ=H) (hp : N=H+Lᵀ*L)
include he hi hv hH hp
lemma radiant (u v : Corn n) : dotProduct (H *ᵥ u) v= dotProduct (H *ᵥ u) (N⁻¹ *ᵥ (H *ᵥ v)) := by
  let A := N⁻¹ * H
  have hh : N*A=H := by rw [show A=N⁻¹*H from rfl, ← Matrix.mul_assoc, mul_nonsing_inv N he, one_mul]
  have h : Dᵀ*H=0 := (by rw [← transpose_transpose (Dᵀ*H), transpose_mul, transpose_transpose, hH, hv, transpose_zero])
  have he : L * A=0 := by
    have hx : (L*D)ᵀ*(L*A)=0 := calc
      _ = Dᵀ *N*A := by rw [hp,transpose_mul,Matrix.mul_add,h,zero_add]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Matrix.mul_assoc Dᵀ N,hh,h]
    change L*A=0
    conv_lhs => rw [← Matrix.one_mul (L*A)]
    rw [← nonsing_inv_mul (L*D)ᵀ (by rwa [det_transpose]),Matrix.mul_assoc,hx, Matrix.mul_zero]
  rw [hp, Matrix.add_mul, Matrix.mul_assoc Lᵀ,he,Matrix.mul_zero,add_zero] at hh
  rw [Matrix.mulVec_mulVec, show N⁻¹*H=A from rfl]; have ht x : dotProduct (H *ᵥ u) x= dotProduct u (H *ᵥ x) := by rw [← transposes H, hH]
  rw [ht,ht,Matrix.mulVec_mulVec,hh]
end projection
section ledgers
variable (S) (t : S.Choices) (p : Clip) (R : PathData G) (μ : ℝ)

def commonM := medals S t p R μ (fedora S t) 1 1
def postroom := cannonade S t μ (fedora S t) (1:Joint G c f)
def postmark := damage (helmets G c f) (fun x : Vault G c f => merit S t p R (0,x)) 0
lemma leaflet : medals S t p R μ (fedora S t) 1 1= postmark (G:=G) S t p R + (postroom (G:=G) S t μ)ᵀ * (postroom (G:=G) S t μ) := by
  unfold postmark medals
  rw [show burnJoint S t p R (fedora S t) 1 1=(fun x : Vault G c f => merit S t p R (0,x)) from funext (fun x => by simp only [burnJoint,merit,input_zero,atire,mul_one]; rfl)]; rfl

variable (W : Matrix (Body 1 f) (Body 1 c) ℝ)
/-- column of covector (`i` counting basis). Two B derivatives and
one arbitrary field direction. In particular MULTIPLY by two vs the
value for perturbing B along one ray to read off P3 gradient. -/
def fragment (x y : Link G c) : Corn (Bodies G c f) := fun i => iteratedFDeriv ℝ 3 (merit S t p R) 0 ![(0,helmets _ _ _ i),saluteLe W x,saluteLe W y]

def amount (x y z w : Link G c) := dotProduct (fragment S t p R W x y) ((commonM S t p R μ)⁻¹ *ᵥ fragment S t p R W z w)
end ledgers
section ridge
variable {p : Clip} {R : PathData G} {K : Matrix (Body 1 f) (Body 1 c) ℝ}
    {ρ : fieldDir G c 1→AxisChart G F} {σ A Λ μ η : ℝ}
    (h : Critical F p R ρ) (hp : R.Bounds p σ A Λ) (hS : S.patch.Branches S.kernel G) (t : S.Choices)
include h hp hS

lemma public_venue (hG : 0<μ) :
    ∃ P : Matrix (Bodies G c f) (Lines G f 0) ℝ,
      postmark S t p R*P=0 ∧ (postmark S t p R)ᵀ=postmark S t p R ∧ IsUnit ((postroom (G:=G) S t μ)*P).det := by
  let U := (1:Joint G c f)
  have hu : Thaw (fun _ : ℝ => U) 0 := Thaw.fixed _ _
  let C := fedora S t (G:=G)
  have hC := fedora_style hS t
  have hf : dress C U=U := dressed_one hC
  have hi : Explosives S t 1 U := (explosive S t hS root_customs hu rfl).self_of_nhds
  have hh := (atire_out hC hu rfl).self_of_nhds
  have H : Shell S t p R 1 U := by simpa only [input_zero, encamp_zero h] using (camp_station h hS hp t).self_of_nhds
  let M := postmark S t p R
  let T := damage (helmets G c f) (canon S t p R 1 U) 0
  let D := shear C U
  let P := stood S U
  let L := postroom S t μ (G:=G)
  let W := cannonade S t μ 1 U
  have hL : L=W*D := by unfold L postroom; rw [arsenal S t μ C U hh (hf.symm ▸ hi),hf]
  have he : D.det=1 := shear_det C U hh
  have hv : T*P=0 := honors S U hS hp t H
  have hs : D*(D⁻¹ *P)=P := by rw [← Matrix.mul_assoc, mul_nonsing_inv D (show IsUnit D.det by rw [he]; simp),Matrix.one_mul]
  have hw : M = Dᵀ*T*D := by
    have H := abides S t p R μ C 1 U hh (hf.symm ▸ hi) (hf.symm ▸ H)
    rw [hf] at H
    rw [show medals S t p R μ C 1 U=M+Lᵀ*L from leaflet ..,show medals S t p R μ 1 1 U=T+Wᵀ*W by unfold medals; rw [cannon_law]; rfl,hL, Matrix.mul_add,Matrix.add_mul] at H
    apply add_right_cancel (b:= (W*D)ᵀ*(W*D))
    simpa only [D,transpose_mul, Matrix.mul_assoc] using H
  refine ⟨D⁻¹ * P,?_,?_,?_⟩
  · change M*(D⁻¹*P)=0; rw [hw, Matrix.mul_assoc _ D,hs,Matrix.mul_assoc,hv,Matrix.mul_zero]
  · change Mᵀ=M; rw [hw,transpose_mul,transpose_mul,transpose_transpose, show Tᵀ=T from damage_symm _ H.1, ← Matrix.mul_assoc]
  change IsUnit (L * (D⁻¹ * P)).det
  rw [hL,Matrix.mul_assoc,hs, show W*P=_ from count_ammo S t μ hS hi]; exact fund_det (grenade_safe _ hG)

lemma mural (K : Matrix (Body 1 f) (Body 1 c) ℝ) : Stayed (merit S t p R) (soldier F K t ρ) :=
    ⟨merit_diff hS t hp,soldier_zero h hS t,soldier_diff h hS t,pension h hS t hp⟩
variable (hk : Guessed F K ρ)
include hk
omit hp in
lemma verge (x) : fieldT (soldier F K t ρ) x=saluteLe K x := by
  apply DFunLike.congr_fun (pace_deriv t h hk hS).fderiv
lemma triumph3 (x y z) : iteratedFDeriv ℝ 3 (victory F t p R ρ) 0 ![x,y,z]= iteratedFDeriv ℝ 3 (merit S t p R) 0 ![saluteLe K x,saluteLe K y,saluteLe K z] := by
  let U := soldier F K t ρ
  have he : merit S t p R ∘ viewS U=ᶠ[𝓝 0] victory F t p R ρ := salary h hS t hp K
  rw [← (he.iteratedFDeriv ℝ 3).eq_of_nhds,
      ← verge h hS t hk, ← verge h hS t hk, ← verge h hS t hk]
  exact (mural h hp hS t K).accrue ..
set_option maxHeartbeats 440000 in
lemma triumph4 (hv : 0<μ) (hH : PriceGap F p R η) (hh : 0<η) (a b c' d) :
    iteratedFDeriv ℝ 4 (victory F t p R ρ) 0 ![a,b,c',d]=
      iteratedFDeriv ℝ 4 (merit S t p R) 0 ![saluteLe K a,saluteLe K b,saluteLe K c',saluteLe K d] -
      amount S t p R μ K a b c' d - amount S t p R μ K a d b c' - amount S t p R μ K a c' b d := by
  let U := soldier F K t ρ
  let X := Link G c
  let M := merit S t p R
  let B := helmets G c f
  have he := mural h hp hS t K
  let Y := Vault G c f
  let C := postmark S t p R
  let L := commonM S t p R μ
  obtain ⟨W,hW,heC,hw⟩ := public_venue h hp hS t hv
  have hE (i j : Vault G c f) : iteratedFDeriv ℝ 2 M 0 ![((0:X),i),((0:X),j)] = dotProduct (cash B i) (C*ᵥ cash B j) := by
    rw [show dotProduct _ _ = _ from (show dotProduct (cash B i) (C*ᵥ cash B j)= _ from detracts B (fun x : Vault G c f => M (0,x)) 0 i j)]
    let E := ContinuousLinearMap.inr ℝ X Y
    change _= iteratedFDeriv ℝ 2 (M ∘ E) 0 ![i,j]
    rw [wired E (by rw [map_zero]; exact he.origin.analyticAt),map_zero]; congr 1
    ext1 k; fin_cases k <;> rfl
  let V x y := (fieldU U x y).2
  have hz x y : fieldU U x y=((0:X),V x y) := he.lower x y
  have hp' (x y : X) : fragment S t p R K x y= -(C *ᵥ cash B (V x y)) := by
    funext i; unfold fragment
    rw [← verge h hS t hk,← verge h hS t hk,he.reserve,hz x y,hE,dotProduct_mulVec, ← mulVec_transpose,heC]
    have hx : cash B (helmets G c f i)=Pi.single i 1 := by funext j; simp [cash,B,Pi.single_apply,eq_comm]
    rw [hx,dotProduct_single_one]; rfl
  have hg := radiant L C (postroom S t μ (G:=G)) W (moment_track h hS hp t hv hH hh |>.1.ne'.isUnit) hw hW heC (leaflet S t p R μ)
  have hc x y z w : iteratedFDeriv ℝ 3 M 0 ![fieldU U z w,fieldT U x, fieldT U y]= - amount S t p R μ K x y z w := by
    rw [hz z w,amount,hp', hp']; simp only [Matrix.mulVec_neg,dotProduct_neg,neg_dotProduct,neg_neg]; change _= -dotProduct (C*ᵥ cash B (V x y)) (L⁻¹ *ᵥ (C *ᵥ cash B (V z w)))
    rw [← hg]
    have hh : iteratedFDeriv ℝ 3 M 0 ![((0:X),V z w),fieldT U x,fieldT U y]=_ := he.reserve (V z w) x y
    rw [hh,hz x y,hE,dotProduct_mulVec, ← mulVec_transpose,heC]
  have hs : M ∘ viewS U=ᶠ[𝓝 0] victory F t p R ρ := salary h hS t hp K
  have ht : iteratedFDeriv ℝ 4 (M∘ viewS U) 0 ![a,b,c',d]=_ := he.tally a b c' d
  rw [← (hs.iteratedFDeriv ℝ 4).eq_of_nhds,ht]; rw [hc a b c' d,hc a d b c',hc a c' b d]; rw [verge h hS t hk,verge h hS t hk,verge h hS t hk,verge h hS t hk]; rfl
end ridge
end YM.Stationary
end
