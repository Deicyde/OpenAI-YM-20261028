import YM.Next.STATIONARY.Joint.Gauge
import YM.Work.A15

set_option autoImplicit false
/-! # Actual quadratic chamber in centered logs. -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix Finset
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {c f n : Side} {S : StepData c f}

lemma dotSite {i : ℕ} (x y : Corn (Lines G n i)) : dotProduct x y = ∑ a, inner ℝ (arm G n i x a) (arm G n i y a) := by
  unfold dotProduct; simp_rw [Fintype.sum_prod_type, Work.F03.inner_color]; rfl
lemma dotColor {i : ℕ} (x y : Corn (Lines G n i)) : dotProduct x y = ∑ a, dotProduct (parts G i (arm G n i x) a) (parts G i (arm G n i y) a) := by
  rw [dotSite]; simp_rw [Work.F03.inner_color]; rw [sum_comm]; rfl
lemma dotEdge (x y : Link G n) : dotProduct x y = ∑ a, inner ℝ (edgeColor x a) (edgeColor y a) := by
  rw [dotSite, ← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site n)) axisEquiv)]; rfl
lemma dotCoat (x y : BaseSites G n) : dotProduct x y = ∑ a, inner ℝ (gaugeColor x a) (gaugeColor y a) := by
  rw [dotSite,Fintype.sum_prod_type]; refine sum_congr rfl fun i _ => ?_; rw [sum_eq_single vac]
  · rfl
  · intro a _ h; exact False.elim (h (vac_only a))
  simp
lemma dotKin (B : Bed) (x y : Link G n) : dotProduct x (uniformM (Precision.K (B.metric.acts n)) y) = Bid.gaugeFiscal B (arm G n 1 x) (arm G n 1 y) := by rw [dotColor]; simp_rw [uniformC]; rfl

def expect (S : StepData c f) (x : Point G c f) : Link G c := x.1 - uniformM (Precision.mean S) x.2.1 + gradientA G c x.2.2
lemma expect_add (x y : Point G c f) : expect S (x+y)=expect S x+expect S y := by simp only [expect,Prod.fst_add,Prod.snd_add,map_add]; abel

def flash (B : Bed) (S : StepData c f) (x y : Point G c f) : ℝ :=
    dotProduct x.2.1 (uniformM (Precision.K (B.metric.acts f)) y.2.1) + S.kernel.penalty * dotProduct (expect S x) (expect S y)

-- tested actual group values, still accounts for coarse FRAME direction via centered change
lemma lit_scene (h : S.patch.Branches S.kernel G) (t : S.Choices) {p : Clip} {R : PathData G} {σ C Λ A Z : ℝ} (hp : R.Bounds p σ C Λ)
    {B : Bed} (hr : Floor B p f A Z) (hx : Attached B R) (hw : Bid.Sworn B f G) :
    merit S t p R 0=0 ∧ fderiv ℝ (merit S t p R) 0=0 ∧ ∀ x y, iteratedFDeriv ℝ 2 (merit S t p R) 0 ![x,y]=flash B S x y := by
  refine Work.F03.hessian_of_limit ((merit_diff h t hp).of_le le_top) ?_ ?_ ?_
  · intro x
    have hp := Work.F03.main_limit hp hx hr hw (arm G f 1 x.2.1)
    let U := fun v : ℝ => ribbon S t (enroll S t (Stationary.extend (v • x.2)))
    let V := fun v : ℝ => input G c (v • x.1)
    have he : V 0=1 := by simp [V]
    have hU : U 0=1 := by simp [U,enroll_zero S t h,ribbon_zero S t h]
    have hv (i : Edge (Site c)) : Tendsto (fun v => G.price (V v i*(U v i)⁻¹)/v^2) (𝓝[≠] 0) (𝓝 (inner ℝ (edgeColor (expect S x) i) (edgeColor (expect S x) i) / 2)) := by
      rw [real_inner_self_eq_norm_sq]
      apply Work.F03.price_limit (G:=G) (V:=fun v => V v i*(U v i)⁻¹) (by simp [he,hU])
      convert! (ray_input x.1 i).mul (centered_pred h t x.2 i).star using 1
      rw [G.colorMat_skew]; simp [expect,enroll_zero S t h,ribbon_zero S t h]; abel
    unfold merit muster flash
    change Tendsto (fun v : ℝ => (mainTerm p R (input G f (v • x.2.1))+tickets S (V v) (U v))/v^2) _ _
    simp_rw [dotKin, dotEdge,_root_.add_div, tickets, mul_div_assoc,Finset.sum_div,input,map_smul]
    exact hp.add ((tendsto_finsetSum _ (fun i _ => hv i)).const_mul _)
  · intro x y z; simp only [flash, Prod.fst_add,Prod.snd_add,expect_add, add_dotProduct, mul_add]; abel
  intro x y; simp only [flash,dotKin,Bid.gaugeFiscal]
  congr 1
  · refine sum_congr rfl fun i _ => ?_; rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,show (Precision.K (B.metric.acts f)).transpose=_ from ?_, dotProduct_comm]; unfold Precision.K; simp [hr.symmetric.1,Matrix.mul_assoc]
  rw [dotProduct_comm]
end YM.Stationary
end

/-! # Real counting-coordinate API for the finite-period determinants -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix Finset Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {c f n : Side}

section basis
variable {m n l : Type} [Fintype m] [Fintype n] [Fintype l] [DecidableEq m] [DecidableEq n] [DecidableEq l]
    {X Y P : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup P] [NormedSpace ℝ P]

def billsM (A : Basis m ℝ X) (B : Basis n ℝ Y) (F : X →L[ℝ] Y) := LinearMap.toMatrix A B F.toLinearMap
def damage (A : Basis m ℝ X) (F : X→ℝ) (x : X) := LinearMap.toMatrix₂ A A (Work.F05.bend F x)
def cash (A : Basis m ℝ X) := A.equivFun
abbrev pocket (m : Type) [Finite m] := Pi.basisFun ℝ m

omit [DecidableEq m] in
lemma cash_works (A : Basis m ℝ X) (x : X) (i : m) : cash A x i=A.repr x i := rfl
omit [DecidableEq m] in
lemma cash_pocket (x : Corn m) : cash (pocket m) x=x := by funext i; rw [cash_works]; simp
omit [DecidableEq m] [DecidableEq n] in
lemma cash_prod_left (A : Basis m ℝ X) (B : Basis n ℝ Y) (y : X × Y) (i) : cash (A.prod B) y (.inl i) = cash A y.1 i := by simp [cash]
omit [DecidableEq m] [DecidableEq n] in
lemma cash_prod_right (A : Basis m ℝ X) (B : Basis n ℝ Y) (y : X × Y) (i) : cash (A.prod B) y (.inr i) = cash B y.2 i := by simp [cash]
omit [DecidableEq m] [DecidableEq n] in
lemma dot_cash (A : Basis m ℝ X) (B : Basis n ℝ Y) (x y : X × Y) :
    dotProduct (cash (A.prod B) x) (cash (A.prod B) y)=dotProduct (cash A x.1) (cash A y.1)+dotProduct (cash B x.2) (cash B y.2) := by
  unfold dotProduct; rw [Fintype.sum_sum_type]; simp_rw [cash_prod_left,cash_prod_right]
omit [DecidableEq n] in
lemma bill_def (A : Basis m ℝ X) (B : Basis n ℝ Y) (F : X →L[ℝ] Y) (i j) : billsM A B F i j = cash B (F (A j)) i := LinearMap.toMatrix_apply ..
omit [DecidableEq n] in
lemma bill_at (A : Basis m ℝ X) (B : Basis n ℝ Y) (F : X →L[ℝ] Y) (x : X) : billsM A B F *ᵥ cash A x = cash B (F x) := LinearMap.toMatrix_mulVec_repr ..
omit [DecidableEq n] in
lemma bill_pay (F : Corn m →L[ℝ] Corn n) (x : Corn m) : billsM (pocket m) (pocket n) F *ᵥ x = F x := by
  have h := bill_at (pocket m) (pocket n) F x; rwa [cash_pocket,cash_pocket] at h
omit [DecidableEq l] in
lemma bill_multiply (A : Basis m ℝ X) (B : Basis n ℝ Y) (C : Basis l ℝ P) (F : X →L[ℝ] Y) (E : Y →L[ℝ] P) :
    billsM A C (E ∘L F)=billsM B C E*billsM A B F := LinearMap.toMatrix_comp ..


lemma detracts (A : Basis m ℝ X) (F : X→ℝ) (x v w) : dotProduct (cash A v) (damage A F x *ᵥ cash A w)=iteratedFDeriv ℝ 2 F x ![v,w] := by
  have hp : dotProduct (cash A v) (damage A F x *ᵥ cash A w) = Work.F05.bend F x (A.equivFun.symm (cash A v)) (A.equivFun.symm (cash A w)) := dotProduct_toMatrix₂_mulVec A A (Work.F05.bend F x) (cash A v) (cash A w)
  rw [hp]; unfold cash; rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]; exact Work.F05.bend_apply ..
lemma damage_comp (A : Basis n ℝ Y) (B : Basis m ℝ X) {F : X→ℝ} {H : Y→X} {y : Y}
    (hp : ContDiffAt ℝ ω F (H y)) (hq : ContDiffAt ℝ ω H y) (h : fderiv ℝ F (H y)=0) :
    damage A (F ∘ H) y=(billsM A B (fderiv ℝ H y))ᵀ * damage B F (H y) *billsM A B (fderiv ℝ H y) := by
  rw [damage,Work.F05.bend_comp_stationary hp hq h, LinearMap.toMatrix₂_compl₁₂ B B]; rfl
lemma damage_congr (A : Basis m ℝ X) {F H : X→ℝ} {x} (he : F=ᶠ[𝓝 x] H) : damage A F x=damage A H x := by simp [damage,Work.F05.bend_congr he]
lemma damage_symm (A : Basis m ℝ X) {F : X→ℝ} {x} (h : ContDiffAt ℝ ω F x) : (damage A F x)ᵀ=damage A F x := by
  ext i j; simp_rw [damage,transpose_apply,LinearMap.toMatrix₂_apply]; exact h.isSymmSndFDerivAt_of_omega _ _

omit [DecidableEq m] [DecidableEq n] in
lemma transposes (U : Matrix n m ℝ) (x : m→ℝ) (y : n→ℝ) : dotProduct x ((Uᵀ) *ᵥ y)=dotProduct (U *ᵥ x) y := by rw [dotProduct_mulVec,vecMul_transpose]
omit [DecidableEq m] [DecidableEq n] in
lemma square_cost (U : Matrix n m ℝ) (x y : m→ℝ) : dotProduct x ((Uᵀ*U)*ᵥ y)=dotProduct (U *ᵥ x) (U *ᵥ y) := by rw [← mulVec_mulVec,transposes]
omit [DecidableEq m] [DecidableEq n] in
lemma both_cost (U : Matrix n m ℝ) (H : Matrix n n ℝ) (V : Matrix n m ℝ) (x y) : dotProduct x ((Uᵀ*H*V)*ᵥ y)=dotProduct (U *ᵥ x) (H *ᵥ (V *ᵥ y)) := by rw [← mulVec_mulVec,← mulVec_mulVec,transposes]
lemma testers {M N : Matrix n m ℝ} (h : ∀ (x : Corn n) (y : Corn m), dotProduct x (M *ᵥ y)=dotProduct x (N *ᵥ y)) : M=N := by
  ext i j; simpa using h (Pi.single i 1) (Pi.single j 1)
lemma bill_eq (A : Basis m ℝ X) {M N : Matrix n m ℝ} (h : ∀ x : X,M *ᵥ (cash A x)=N *ᵥ (cash A x)) : M=N := testers fun x y => by obtain ⟨a,rfl⟩ := (cash A).surjective y; rw [h]
lemma damage_eq (A : Basis m ℝ X) {M N : Matrix m m ℝ} (h : ∀ x y : X, dotProduct (cash A x) (M *ᵥ cash A y)=dotProduct (cash A x) (N *ᵥ cash A y)) : M=N := by
  apply testers; intro x y; obtain ⟨x,rfl⟩ := (cash A).surjective x; obtain ⟨y,rfl⟩ := (cash A).surjective y; exact h x y

end basis

abbrev Bodies (G : Gauge) (c f : Side) := (Lines G f 1) ⊕ (Lines G c 0)
instance (G : Gauge) (c f : Side) : DecidableEq (Bodies G c f) := fun a b => instDecidableEqSum a b
def helmets (G : Gauge) (c f : Side) : Basis (Bodies G c f) ℝ (Vault G c f) := (pocket _).prod (pocket _)
lemma vault_bill (x y : Vault G c f) : dotProduct (cash (helmets _ _ _) x) (cash (helmets _ _ _) y)=dotProduct x.1 y.1+dotProduct x.2 y.2 := by
  unfold helmets; rw [dot_cash,cash_pocket,cash_pocket,cash_pocket,cash_pocket]
end YM.Stationary
end

/-! # On-shell Ward equation in joint field. Rooted tangent at arbitrary real
configuration: gauge acts on U *and* frame. Left-link Hessian annihilation on ALL
fine gauges, not pit-trimming (constant modes included in the regulator).
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {c f n : Side}

-- Left-link tangent of actual fine gauge at indicated field
def cant (U : Config G n) : BaseSites G n →L[ℝ] Link G n :=
    edgeColor.symm.toContinuousLinearMap ∘L (ContinuousLinearMap.pi fun e : Edge (Site n) =>
      ContinuousLinearMap.proj (φ:=fun _ : Site n => G.Color) e.1 - (G.adjoint (U e)).toContinuousLinearMap ∘L ContinuousLinearMap.proj (φ:=fun _ : Site n => G.Color) (e.1+step e.2)) ∘L gaugeColor.toContinuousLinearMap
lemma cant_at (U : Config G n) (x : BaseSites G n) (e : Edge (Site n)) :
    edgeColor (cant U x) e=gaugeColor x e.1-G.adjoint (U e) (gaugeColor x (e.1+step e.2)) := by simp [cant]
lemma cant_one (x : BaseSites G n) : cant 1 x=-gradientA G n x := by
  apply edgeColor.injective; funext i
  rw [map_neg,Pi.neg_apply,cant_at,Pi.one_apply,G.adjoint_one,show edgeColor (gradientA G n x) i=gaugeColor x (i.1+step i.2)-gaugeColor x i.1 from gradientC x i.1 i.2]; abel

def mail (U : Config G n) := billsM (pocket _) (pocket _) (cant U)
lemma mailed (U : Config G n) (x : BaseSites G n) : mail U *ᵥ x=cant U x := bill_pay ..
lemma mailed_zero : mail (1:Config G n)= - billsM (pocket _) (pocket _) (uniformM (G:=G) (d 0 n)) := testers fun i j => by rw [mailed,cant_one,first_uniform,neg_mulVec,bill_pay]

section rooted
variable (S : StepData c f) (U : Joint G c f)

def parade (x : BaseSites G f) : Vault G c f := retract (wages S (switchSite x) 1 U*U⁻¹)
def corps := fderiv ℝ (parade S U) 0
def stood := billsM (pocket _) (helmets _ _ _) (corps S U)
@[simp] lemma parade_zero : parade S U 0=0 := by simp [parade]
lemma parade_thaw : Thaw (fun x => wages S (switchSite x) 1 U*U⁻¹) 0 :=
    ((Thaw.fixed U _).wages S (Army.powG (v:=id) contDiffAt_id) (Army.park _ _)).mul (Thaw.fixed _ _)
lemma parade_diff : ContDiffAt ℝ ω (parade S U) 0 := (parade_thaw S U).log (by simp)
lemma parade_read : ∀ᶠ x in 𝓝 0, Stationary.extend (parade S U x)*U=wages S (switchSite x) 1 U := by
  let V x := wages S (switchSite x) 1 U * U⁻¹
  have he : V 0=1 := by simp [V]
  filter_upwards [(show Tendsto V (𝓝 0) (𝓝 1) from he ▸ (parade_thaw S U).cont.tendsto).eventually extend_retract] with x hx
  change Stationary.extend (retract (V x))*_= _; rw [hx]; unfold V; simp

-- check horizontal and vertical signs against actual exp coordinate around U
lemma soldier_mounted (x : BaseSites G f) :
    (corps S U x).1=cant U.1 x ∧ ∀ i, gaugeColor (corps S U x).2 i= -G.adjoint (U.2 i) (gaugeColor x (S.ratio.embed i)) := by
  let Y (v : ℝ) := switchSite (v • x)
  have he : Y (0:ℝ)=1 := by simp [Y]
  let Q v := wages S (Y v) 1 U * U⁻¹
  have hQ : Q (0:ℝ)=1 := by simp [Q,he]
  have hp (i) : HasDerivAt (fun v => G.mat ((Q v).1 i)) (G.colorMat (edgeColor (cant U.1 x) i)) 0 := by
    simp only [Q,wages,Lattice.gauge,Prod.fst_mul, Pi.mul_apply,Prod.fst_inv,Pi.inv_apply,G.mat_mul,G.mat_inv]
    have ht i := ray_power x i
    have hh : ∀ i, HasDerivAt (fun v => G.mat (Y v i)) (G.colorMat (gaugeColor x i)) 0 := ht
    convert! (((hh i.1).mul_const (G.mat (U.1 i))).mul (hh (i.1+step i.2)).star).mul_const (star (G.mat (U.1 i))) using 1
    rw [he]; simp [cant_at,G.colorMat_skew,Gauge.conjugate,add_mul, Matrix.mul_assoc]; rfl
  let v := gaugeColor.symm (fun i => -G.adjoint (U.2 i) (gaugeColor x (S.ratio.embed i)))
  have hv i : HasDerivAt (fun v => G.mat ((Q v).2 i)) (G.colorMat (gaugeColor v i)) 0 := by
    simp only [Q,wages,Pi.one_apply,one_mul, Prod.snd_mul,Prod.snd_inv,Pi.inv_apply,Pi.mul_apply,G.mat_mul,G.mat_inv,v,gaugeColor.apply_symm_apply]
    convert! (((ray_power x (S.ratio.embed i)).star.const_mul (G.mat (U.2 i))).mul_const (star (G.mat (U.2 i)))) using 1
    simp [G.colorMat_skew,Gauge.conjugate]
  have H : corps S U x=(cant U.1 x,v) :=
    (Push.side _ ((parade_diff S U).differentiableAt (by simp)) x).unique (show HasDerivAt (fun v : ℝ => parade S U (v • x)) (cant U.1 x,v) 0 from
      (ray_content (show (Q (0:ℝ)).1=1 by rw [hQ]; rfl) hp).prodMk (ray_frame (show (Q (0:ℝ)).2=1 by rw [hQ]; rfl) hv))
  rw [H]; simp only [v,gaugeColor.apply_symm_apply,and_self, implies_true]
lemma stands (x : BaseSites G f) : stood S U *ᵥ x=cash (helmets _ _ _) (corps S U x) := by
  conv_lhs => rw [← cash_pocket x]; rw [stood,bill_at]

theorem honors (hx : S.patch.Branches S.kernel G) {p : Clip} {R : PathData G} {σ A Λ : ℝ}
    {V : Config G c} (h : R.Bounds p σ A Λ) (t : S.Choices) (hs : Shell S t p R V U) :
    damage (helmets G c f) (canon S t p R V U) 0*stood S U=0 := by
  let X := Vault G c f
  let K := BaseSites G f
  let Q (z : K × X) : Joint G c f := wages S (switchSite z.1) 1 (Stationary.extend z.2 * U)*U⁻¹
  let H := fun z => retract (Q z)
  let F := canon S t p R V U
  have hQ : Q 0=1 := by simp [Q]
  have hH : H 0=0 := by simp [H,hQ]
  have he : Thaw Q 0 := by
    refine Thaw.mul ?_ (Thaw.fixed _ _)
    apply Thaw.wages S
    · exact (Thaw.through contDiffAt_snd).mul (Thaw.fixed _ _)
    · exact Army.powG contDiffAt_fst
    exact Army.park _ _
  have hp : ContDiffAt ℝ ω H 0 := he.log hQ
  let J := ContinuousLinearMap.inl ℝ K X
  let L := ContinuousLinearMap.inr ℝ K X
  have hv : ∀ᶠ z in 𝓝 0, Stationary.extend (H z) = Q z :=
    (show Tendsto Q (𝓝 0) (𝓝 1) from hQ ▸ he.cont.tendsto).eventually extend_retract
  have hd (x : K) : fderiv ℝ H 0 (J x) = corps S U x := by
    have hi : HasFDerivAt H (fderiv ℝ H 0) (J 0) := by rw [map_zero]; exact (hp.differentiableAt (by simp)).hasFDerivAt
    have hh := (hi.comp 0 J.hasFDerivAt).fderiv
    have hs : H ∘ J=parade S U := by funext y; change retract (_*U⁻¹)=_; simp only [J,ContinuousLinearMap.inl_apply, extend_zero,one_mul]; rfl
    rw [corps,← hs,hh]; rfl
  have hw (x : X) : fderiv ℝ H 0 (L x) = x := by
    have hi : HasFDerivAt H (fderiv ℝ H 0) (L 0) := by rw [map_zero]; exact (hp.differentiableAt (by simp)).hasFDerivAt
    have hL : H ∘ L =ᶠ[𝓝 0] id := by
      filter_upwards [retract_extend (G:=G) (c:=c) (f:=f)] with y hy
      change retract (wages S (switchSite 0) 1 (Stationary.extend y * U)*U⁻¹)=_; rw [switch_zero,wages_zero,mul_inv_cancel_right,hy]; rfl
    exact congr(($( ((hi.comp 0 L.hasFDerivAt).fderiv.symm.trans (hL.fderiv_eq.trans (fderiv_id ..)) ) ) : X →L[ℝ] X) x)
  have hh : F ∘ H =ᶠ[𝓝 0] F ∘ Prod.snd := by
    filter_upwards [hv] with z hz
    simp only [Function.comp_apply,F,canon,hz,Q,inv_mul_cancel_right]
    simpa only [gauge_one] using root_wages S t hx (Stationary.extend z.2*U) 1 (switchSite z.1) p R h V
  apply testers
  intro x y; obtain ⟨x,rfl⟩ := (cash (helmets _ _ _)).surjective x
  rw [← Matrix.mulVec_mulVec, stands, zero_mulVec, dotProduct_zero,detracts]
  have hF : ContDiffAt ℝ ω F (H 0) := by rw [hH]; exact hs.1
  have h1 := Work.F05.bend_comp_stationary hF hp (by rw [hH]; exact hs.2)
  have H₁ : fderiv ℝ Prod.snd (0:K×X) = ContinuousLinearMap.snd ℝ K X := fderiv_snd ..
  have h2 := Work.F05.bend_comp_stationary (g:=Prod.snd) (F:=F) (x:=(0:K×X)) hs.1 contDiffAt_snd hs.2
  rw [Work.F05.bend_congr hh,h2,H₁,hH] at h1
  have ht := DFunLike.congr_fun (DFunLike.congr_fun h1 (L x)) (J y)
  change Work.F05.bend F 0 x 0=Work.F05.bend F 0 (fderiv ℝ H 0 (L x)) (fderiv ℝ H 0 (J y)) at ht
  rw [hd,hw,map_zero,Work.F05.bend_apply] at ht; exact ht.symm
end rooted
end YM.Stationary
end

/-!
# Choice of gauge regulator: mass tail for *both* fine comparison fields.

Counting gauge Hessian will be `grenade`: Δ + μ² (μ² / (Δ+μ²))^9.
Unlike eq CLg and cMst in euclidean-existence this keeps just ordinary first-order R (not R with a polynomial S),
and matches the determinant against vectored fine regulator with the same tail.
It has an actual strictly-positive analytic germ on real finite orbits. Even with two
field derivatives later on a comparison term, T^9 thus retains an unhit T^3 factor
(use `pow` as a true operator composition). Powers supported are not assumed for Γ.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side}

section
variable {ι κ j : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype j] [DecidableEq j]
abbrev Funds (ι : Type) := Matrix ι ι ℝ
lemma pow_nine {M : Funds ι} (h : M.PosDef) : (M^9).PosDef := by
  let X := M^4
  have hp := h.conjTranspose_mul_mul_same (mulVec_injective_iff_isUnit.mpr (show IsUnit X from h.isUnit.pow 4))
  rw [show Xᴴ=X from (h.isHermitian.pow _),show X*M*X=M^9 by unfold X; noncomm_ring] at hp; exact hp
lemma fund_det {M : Funds ι} (h : M.PosDef) : IsUnit M.det := (Ne.isUnit h.det_pos.ne')

-- transfer to and from fixed orthogonal (counting coordinates)
structure Military (U : Funds ι) : Prop where
  right : Uᵀ*U=1
namespace Military
variable {U X : Funds ι} {Q : Funds κ} (h : Military U)
include h
lemma left : U*Uᵀ=1 := mul_eq_one_comm.mpr h.right
lemma det : U.det^2=1 := by simpa only [det_mul,det_transpose,← sq,det_one] using congr_arg Matrix.det h.right

lemma unit : IsUnit U := ⟨⟨U,Uᵀ,h.left,h.right⟩,rfl⟩
lemma carry {A B : Funds ι} (hp : A*U=U*B) : A=U*B*Uᵀ := (by rw [← hp,mul_assoc,h.left,mul_one])
lemma back {A B : Funds ι} (hp : A*U=U*B) : Uᵀ*A*U=B := by rw [mul_assoc,hp, ← mul_assoc,h.right,one_mul]
lemma pulls {A B : Funds ι} (hp : Uᵀ*A*U=B) : A*U=U*B := by rw [← hp,mul_assoc Uᵀ,← mul_assoc,h.left,one_mul]
lemma turn_det {A B : Funds ι} (hp : Uᵀ*A*U=B) : A.det=B.det := by rw [← hp,det_mul,det_mul,det_transpose]; calc
    _ = A.det*1 := (mul_one _).symm
    _ = _ := by rw [← h.det]; ring
lemma transpose_cross {A B : Matrix κ ι ℝ} (hx : Military Q) (hu : A*U=Q*B) : Aᵀ*Q=U*Bᵀ := by
  have hi : A=Q*B*Uᵀ := by rw [← hu,Matrix.mul_assoc,h.left,Matrix.mul_one]
  rw [hi,transpose_mul,transpose_mul,transpose_transpose,Matrix.mul_assoc,Matrix.mul_assoc,hx.right,Matrix.mul_one]
omit h in
lemma inverse_cross {A B : Funds ι} (p : IsUnit A.det) (q : IsUnit B.det) (hu : A*U=U*B) : A⁻¹*U=U*B⁻¹ := by
  calc
  _ = A⁻¹*(U*B*B⁻¹) := by rw [Matrix.mul_assoc U,mul_nonsing_inv B q,mul_one]
  _ = _ := by rw [← hu,Matrix.mul_assoc A, nonsing_inv_mul_cancel_left A _ p]
lemma transfer {A B : Funds ι} (hp : Uᵀ*A*U=B) (he : B.PosDef) : A.PosDef := by
  apply h.unit.posDef_star_left_conjugate_iff.mp
  rw [star_eq_conjTranspose]; exact hp ▸ he
end Military

lemma military_intro (U : Funds ι) (e : ∀ x y : ι → ℝ, dotProduct (U *ᵥ x) (U *ᵥ y)=dotProduct x y) : Military U :=
  ⟨testers fun i j => by rw [square_cost, e,one_mulVec]⟩
lemma armant (κ : ℕ) {A B U : Funds ι} (h : A*U=U*B) : A^κ*U=U*B^κ := by
  induction κ with
  | zero => simp
  | succ n ih => rw [pow_succ' A, pow_succ' B, mul_assoc,ih,← mul_assoc,h,mul_assoc]
end

-- Physical counting formulas per gauge. k∈Coats real
def troop (u : Coats G n) := billsM (pocket _) (pocket _) (armorG u)
def trench (u : Coats G n) := billsM (pocket _) (pocket _) (armor u)
def tactics (k : Coats G f) (u : Coats G c) := billsM (helmets G c f) (helmets G c f) (armUp k u)

private lemma adInner (u : G.El) (x y : G.Color) : inner ℝ (G.adjoint u x) (G.adjoint u y) = inner ℝ x y :=
    (show G.Color →ₗᵢ[ℝ] G.Color from ⟨G.adjoint u, G.norm_adjoint u⟩).inner_map_map _ _
lemma troop_orthogonal (u : Coats G n) : Military (troop u) := military_intro _ (fun i j => by simp_rw [troop,bill_pay,dotCoat,armorG_at,adInner])
lemma trench_orthogonal (u : Coats G n) : Military (trench u) := military_intro _ (fun i j => by simp_rw [trench,bill_pay,dotEdge,armor_at,adInner])
lemma tactics_orthogonal (k : Coats G f) (u : Coats G c) : Military (tactics k u) := by
  apply military_intro; intro x y
  obtain ⟨x,rfl⟩ := (cash (helmets G c f)).surjective x; obtain ⟨y,rfl⟩ := (cash (helmets G c f)).surjective y
  simp_rw [tactics,bill_at,vault_bill]
  change dotProduct (armor k x.1) (armor k y.1) + dotProduct (armorG u x.2) (armorG u y.2) = _
  simp_rw [dotCoat,dotEdge,armorG_at,armor_at,adInner]
lemma mail_carry (k : Coats G n) (U : Config G n) : mail (Lattice.gauge k U)*troop k=trench k*mail U := by
  refine testers fun i j => ?_; simp only [← mulVec_mulVec,mailed,troop,trench,bill_pay]
  congr 1; apply edgeColor.injective; funext i; rw [cant_at,armor_at,cant_at,armorG_at,armorG_at]
  simp only [map_sub, ← G.adjoint_mul, Lattice.gauge]; simp

section money
variable (μ : ℝ) (U : Config G n)

def tonic := (mail U)ᵀ*mail U
def ammo := tonic U+μ^2 • (1:Funds _)
def pebble := μ^2 • (ammo μ U)⁻¹
def cannon := μ^2 • pebble μ U^9
def grenade := tonic U+cannon μ U
lemma tonic_semi : (tonic U).PosSemidef := posSemidef_conjTranspose_mul_self (mail U)
variable {μ} (h : 0<μ)
include h
lemma ammo_safe : (ammo μ U).PosDef := PosDef.posSemidef_add (tonic_semi _) (PosDef.one.smul (by positivity))
lemma pebble_safe : (pebble μ U).PosDef := (ammo_safe U h).inv.smul (by positivity)
lemma cannon_safe : (cannon μ U).PosDef := (pow_nine (pebble_safe U h)).smul (by positivity)
lemma grenade_safe : (grenade μ U).PosDef := PosDef.posSemidef_add (tonic_semi _) (cannon_safe U h)

/-- Intertwining, applies equally to signed or translation *if* mail intertwines. -/
theorem artillery (V : Config G n) {P Q}
    (hp : Military P) (hq : Military Q) (he : mail V * P=Q * mail U) :
    cannon μ V * P=P*cannon μ U ∧ grenade μ V * P=P*grenade μ U := by
  have hT : tonic V * P=P*tonic U := by
    rw [tonic,tonic,Matrix.mul_assoc,he, ← Matrix.mul_assoc,hp.transpose_cross hq he,Matrix.mul_assoc]
  have hu : ammo μ V * P=P*ammo μ U := by rw [ammo,ammo, Matrix.add_mul,Matrix.mul_add,hT, smul_mul_assoc, Matrix.mul_smul]; simp
  have hi : pebble μ V * P=P*pebble μ U := by rw [pebble,pebble,smul_mul_assoc,Matrix.mul_smul,Military.inverse_cross (fund_det (ammo_safe V h)) (fund_det (ammo_safe U h)) hu]
  have hh : cannon μ V * P=P*cannon μ U := by rw [cannon,cannon,smul_mul_assoc,Matrix.mul_smul, armant _ hi]
  exact ⟨hh,by rw [grenade,grenade, Matrix.add_mul,Matrix.mul_add,hh,hT]⟩
lemma battery (k : Coats G n) :
    cannon μ (Lattice.gauge k U)* troop k=troop k * cannon μ U ∧ grenade μ (Lattice.gauge k U)*troop k=troop k*grenade μ U :=
  artillery U h _ (troop_orthogonal _) (trench_orthogonal _) (mail_carry ..)
end money
end YM.Stationary
end

/-! # Arbitrary shear to rooted, used for estimating in a centered outfit.

Left tangent of SHEARED variables. `K` only modifies frame at right; deploy
fractions `banks` and shear Jacob under actual derivatives near origin. -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix Finset Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

abbrev Robe (G : Gauge) (c f : Side) := Config G f → Coats G c

def dress (K : Robe G c f) (U : Joint G c f) : Joint G c f := (U.1,U.2*K U.1)
@[simp] lemma dress_one (U : Joint G c f) : dress 1 U=U := by simp [dress]
@[simp] lemma dress_inv (K : Robe G c f) (U : Joint G c f) : dress K⁻¹ (dress K U)=U := by simp [dress]
def fedora (S : StepData c f) (t : S.Choices) : Robe G c f := fun i => (bears S t i)⁻¹
lemma enroll_dress (S : StepData c f) (t : S.Choices) (U : Joint G c f) : dress (fedora S t) U=enroll S t U := rfl

structure Customs (K : Robe G c f) : Prop where
    star : K 1=1
    thaw : Army (K ∘ input G f) 0

lemma root_customs : Customs (1:Robe G c f) := ⟨rfl,Army.park 1 0⟩
lemma fedora_style (h : S.patch.Branches S.kernel G) (t : S.Choices) : Customs (fedora (G:=G) S t) :=
    ⟨by simp [fedora,bear_zero S t h], ((Army.powL (v:=id) contDiffAt_id).bear h t (u:=input_zero ..)).inv⟩

variable (K : Robe G c f)
section laws
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {U : X → Joint G c f} {x : X}
    {K} (h : Customs K)
include h
lemma sport_thaw (hv : Thaw U x) (he : (U x).1=1) : Thaw (fun z => dress K (U z)) x := by
  let F z := content (U z).1
  have hF : F x=0 := by simp [F,he]
  have hc : ContDiffAt ℝ ω F x := hv.1.logL he
  have hi : Army (K ∘ input G f ∘ F) x := Army.comp (g:=K ∘ input G f) (w:=F) (by rw [hF]; exact h.thaw) hc
  refine ⟨hv.1,hv.2.mul ?_⟩; intro i; refine (hi i).congr_of_eventuallyEq ?_
  have he : Tendsto (fun z => (U z).1) (𝓝 x) (𝓝 1) := he ▸ hv.1.cont.tendsto
  filter_upwards [he.eventually content_encodes] with z hz
  change _=G.mat (K (input G f (content (U z).1)) i); rw [hz]
lemma dressed_one : dress K (1:Joint G c f)=1 := by simp [dress,h.star]
end laws

section shear
variable (U : Joint G c f)
-- absolute frame Jacobian is one (uses left Haar tangent on both sides)

def atire (x : Vault G c f) := dress K (Stationary.extend x*U)
def tailor (x : Vault G c f) := retract (atire K U x * (dress K U)⁻¹)
def shear : Matrix (Bodies G c f) (Bodies G c f) ℝ := billsM (helmets _ _ _) (helmets _ _ _) (fderiv ℝ (tailor K U) 0)
@[simp] lemma atire_zero : atire K U 0=dress K U := by rw [atire,extend_zero,one_mul]
@[simp] lemma tailor_zero : tailor K U 0=0 := by rw [tailor,atire_zero,mul_inv_cancel,retract_one]

abbrev Apparel := Thaw (atire K U) 0

lemma tailor_diff (h : Apparel K U) : ContDiffAt ℝ ω (tailor K U) 0 := by
  apply Thaw.log (Thaw.mul h (Thaw.fixed _ _)) (by simp)
lemma tailor_suit (h : Apparel K U) : ∀ᶠ x in 𝓝 0, Stationary.extend (tailor K U x)*dress K U=atire K U x := by
  let V x := atire K U x*(dress K U)⁻¹
  have ht : V 0=1 := by simp [V]
  filter_upwards [(show Tendsto V _ (𝓝 1) from ht ▸ (h.mul (Thaw.fixed _ _)).cont.tendsto).eventually extend_retract] with x hx
  change Stationary.extend (retract (V x))*_= _; rw [hx]; unfold V; rw [inv_mul_cancel_right]

lemma atire_out {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {K} {U : X → Joint G c f}
    {x : X} (H : Customs K) (h : Thaw U x) (u : (U x).1=1) : ∀ᶠ z in 𝓝 x, Apparel K (U z) := by
  have he : Thaw (fun y : X × Vault G c f => atire K (U y.1) y.2) (x,0) :=
    sport_thaw H ((Thaw.through contDiffAt_snd).mul (Thaw.comp (w:=Prod.fst) (g:=U) h contDiffAt_fst)) (by simp [u])
  have hr : Tendsto (fun v : X => (v,(0 : Vault G c f))) (𝓝 x) (𝓝 (x,0)) := tendsto_id.prodMk_nhds tendsto_const_nhds
  have hx (a) : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ ω (fun i => G.mat ((atire K (U z) i).1 a)) 0 :=
    (hr.eventually ((he.1 a).eventually (by simp))).mono fun _ hz => Work.F05.hold_jet (V:=fun x i => G.mat ((atire K (U x) i).1 a)) hz
  have hy (a) : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ ω (fun i => G.mat ((atire K (U z) i).2 a)) 0 :=
    (hr.eventually ((he.2 a).eventually (by simp))).mono fun _ hz => Work.F05.hold_jet (V:=fun x i => G.mat ((atire K (U x) i).2 a)) hz
  exact (eventually_all.mpr hx).and (eventually_all.mpr hy)

lemma tailor_keeps (h : Apparel K U) (x : Vault G c f) : (fderiv ℝ (tailor K U) 0 x).1=x.1 := by
  let M := ContinuousLinearMap.fst ℝ (Link G f) (BaseSites G c)
  have hp : (M : Vault G c f→Link G f) ∘ (tailor K U)=ᶠ[𝓝 (0:Vault G c f)] M := by
    have he : ∀ᶠ x : Vault G c f in 𝓝 0, content (input G f x.1)=x.1 := ((continuous_fst).tendsto (0:Vault G c f)).eventually input_encodes
    filter_upwards [he] with y hy
    change content ((input _ _ y.1*U.1)*(U.1)⁻¹)=_; rw [mul_inv_cancel_right,hy]; rfl
  exact DFunLike.congr_fun ((M.hasFDerivAt.comp _ ((tailor_diff K U h).differentiableAt (by simp)).hasFDerivAt).fderiv.symm.trans (hp.fderiv_eq.trans M.fderiv)) x
lemma tailor_side (h : Apparel K U) (x : BaseSites G c) : (fderiv ℝ (tailor K U) 0 (0,x))=(0,x) := by
  let L := ContinuousLinearMap.inr ℝ (Link G f) (BaseSites G c)
  have he : tailor K U ∘ L =ᶠ[𝓝 (0:BaseSites G c)] L := by
    filter_upwards [frameLog_switch (G:=G) (n:=c)] with s hs
    change retract (dress K (Stationary.extend ((0:Link G f),s)*U)*(dress K U)⁻¹)=(0,s)
    have hi : dress K (Stationary.extend ((0:Link G f),s)*U)*(dress K U)⁻¹=(1,switchSite s) := by
      simp [dress,Stationary.extend]
    rw [hi]; exact Prod.ext content_one hs
  have ht : HasFDerivAt (tailor K U) (fderiv ℝ (tailor K U) 0) (L 0) := by
    rw [map_zero]; exact ((tailor_diff K U h).differentiableAt (by simp)).hasFDerivAt
  exact DFunLike.congr_fun ((ht.comp _ L.hasFDerivAt).fderiv.symm.trans (he.fderiv_eq.trans L.fderiv)) x

lemma shear_det (h : Apparel K U) : (shear K U).det=1 := by
  let M : Funds (Bodies G c f) := shear K U
  change M.det=1
  have ha (i : Lines G f 1) : helmets G c f (Sum.inl i)=((pocket _) i,0) := by simp [helmets]
  have hb (i : Lines G c 0) : helmets G c f (Sum.inr i)=(0,(pocket _) i) := by simp [helmets]
  have ht : M=fromBlocks (1:Funds (Lines G f 1)) 0 (M.toBlocks₂₁) (1:Funds (Lines G c 0)) := by
    ext (i|i) (j|j)
    · unfold M shear
      rw [bill_def,ha,fromBlocks_apply₁₁,show cash (helmets _ _ _) _ _ = cash _ _ _ from cash_prod_left ..,tailor_keeps K U h,cash_pocket]; change pocket _ j i = _
      rw [Pi.basisFun_apply,one_apply, Pi.single_apply]
    · unfold M shear
      rw [bill_def,hb,fromBlocks_apply₁₂,tailor_side K U h,show cash (helmets _ _ _) _ _ = cash _ _ _ from cash_prod_left ..,map_zero]; rfl
    · rfl
    unfold M shear
    rw [bill_def,hb,fromBlocks_apply₂₂,tailor_side K U h,show cash (helmets _ _ _) _ _ = cash _ _ _ from cash_prod_right ..,cash_pocket]; change pocket _ j i = _
    rw [Pi.basisFun_apply,one_apply, Pi.single_apply]
  rw [ht,det_fromBlocks_zero₁₂]; simp
end shear
end YM.Stationary
end

/-! # Rooted X left inverse and gauge determinant normalization -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side}

def rearM (G : Gauge) (c f : Side) := billsM (helmets G c f) (pocket _) (ContinuousLinearMap.fst ℝ (Link G f) (BaseSites G c))
lemma rear_cost (x : Vault G c f) : rearM G c f *ᵥ cash (helmets G c f) x=x.1 := by rw [rearM,bill_at,cash_pocket]; rfl
lemma shear_fine (K : Robe G c f) (U : Joint G c f) (p : Apparel K U) : rearM G c f * shear K U=rearM G c f :=
    bill_eq (helmets _ _ _) fun x => by rw [← Matrix.mulVec_mulVec,shear,bill_at, rear_cost,rear_cost,tailor_keeps K U p]
variable (S : StepData c f)

lemma corporal (U : Joint G c f) : rearM G c f * stood S U=mail U.1 := testers fun i j => by rw [← Matrix.mulVec_mulVec,stands,rear_cost,mailed,(soldier_mounted S U j).1]
variable (t : S.Choices)

/-- Negative RIGHT tangent of dressed Ψ. Real log (left/right signs
critical here). X=identity on rooted fine gauge column. -/
def rocket (K : Robe G c f) (U : Joint G c f) (x : Vault G c f) :=
    -frameLog ((shield S t (dress K U))⁻¹ * shield S t (atire K U x))
def indexX (K : Robe G c f) (U : Joint G c f) := billsM (helmets _ _ _) (pocket _) (fderiv ℝ (rocket S t K U) 0)
def cannonade (μ : ℝ) (K : Robe G c f) (U : Joint G c f) := (mail U.1)ᵀ * rearM G c f + cannon μ U.1 * indexX S t K U

structure Explosives (K : Robe G c f) (U : Joint G c f) : Prop where
  pins : Army (fun z => shield S t (atire K U z)) 0

lemma explosive (h : S.patch.Branches S.kernel G) {K : Robe G c f} (hk : Customs K) {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {U : X → Joint G c f} {x : X} (he : Thaw U x) (p : (U x).1=1) : ∀ᶠ z in 𝓝 x, Explosives S t K (U z) := by
  have hp : Thaw (fun y : X × Vault G c f => atire K (U y.1) y.2) (x,0) :=
    sport_thaw hk ((Thaw.through contDiffAt_snd).mul (Thaw.comp (w:=Prod.fst) (g:=U) he contDiffAt_fst)) (by simp [p])
  have hx := hp.shields h t (he:=by change (atire K (U x) 0).1=_; rw [atire_zero]; exact p)
  have ht : Tendsto (fun v : X => (v,(0:Vault G c f))) (𝓝 x) (𝓝 (x,0)) := tendsto_id.prodMk_nhds tendsto_const_nhds
  have hh (i) : ∀ᶠ v in 𝓝 x, ContDiffAt ℝ ω (fun y => G.mat (shield S t (atire K (U v) y) i)) 0 :=
      (ht.eventually ((hx i).eventually (by simp))).mono fun _ hv => Work.F05.hold_jet (V:=fun v y => G.mat (shield S t (atire K (U v) y) i)) hv
  filter_upwards [eventually_all.mpr hh] with v hv; exact ⟨hv⟩

lemma market (K : Robe G c f) (U : Joint G c f) (p : Explosives S t K U) :
    ContDiffAt ℝ ω (rocket S t K U) 0 :=
  ((Army.mul (Army.park _ _) p.pins).logG (show (shield S t (dress K U))⁻¹ * shield S t (atire K U 0)=1 by simp)).neg

lemma rocket_root (h : S.patch.Branches S.kernel G) (U : Joint G c f) :
    rocket S t 1 U ∘ (parade S U) =ᶠ[𝓝 0] id := by
  have he := ((continuous_neg).tendsto (0:BaseSites G f)).eventually (by rw [neg_zero]; exact frameLog_switch (G:=G) (n:=f))
  filter_upwards [parade_read S U,he] with x hx hp
  rw [Function.comp_apply,rocket,atire,dress_one,dress_one,hx,shields S t h]
  suffices he : (shield S t U)⁻¹ * (fun i => (1:Coats G c) (S.ratio.parent i)* shield S t U i * (switchSite x i)⁻¹)=switchSite (-x) by rw [he,hp,neg_neg]; rfl
  funext i
  simp [switch_color,Work.F03.exp_neg_color]

lemma carries (h : S.patch.Branches S.kernel G) {U : Joint G c f} (p : Explosives S t 1 U) : indexX S t 1 U * stood S U=1 := by
  have hp := (rocket_root S t h U).fderiv_eq (𝕜:=ℝ)
  have hv : DifferentiableAt ℝ (rocket S t 1 U) (parade S U 0) := by rw [parade_zero]; exact (market S t 1 U p).differentiableAt (by simp)
  rw [fderiv_comp _ hv ((parade_diff S U).differentiableAt (by simp)),parade_zero,fderiv_id] at hp
  refine testers fun x y => ?_
  rw [← Matrix.mulVec_mulVec,stands,indexX,bill_at,cash_pocket, one_mulVec]
  exact congr_arg _ (DFunLike.congr_fun hp y)
lemma count_ammo (μ : ℝ) (h : S.patch.Branches S.kernel G) {U : Joint G c f} (p : Explosives S t 1 U) : cannonade S t μ 1 U*stood S U=grenade μ U.1 := by
  rw [cannonade,Matrix.add_mul,Matrix.mul_assoc, corporal S U,Matrix.mul_assoc,carries S t h p,mul_one]; rfl

-- congruence under shear already holds off-shell
lemma missile (K : Robe G c f) (U : Joint G c f) (h : Apparel K U) (hp : Explosives S t 1 (dress K U)) :
    indexX S t K U=indexX S t 1 (dress K U)*shear K U := by
  let F := rocket S t 1 (dress K U)
  let Q := tailor K U
  have he : rocket S t K U=ᶠ[𝓝 0] F ∘ Q := by
    filter_upwards [tailor_suit K U h] with x hx
    simp only [Function.comp_apply,F,Q,rocket, show atire 1 (dress K U) (tailor K U x)=atire K U x from (dress_one ..).trans hx,dress_one]
  have hv : DifferentiableAt ℝ F (Q 0) := by rw [show Q 0=0 from tailor_zero K U]; exact (market S t 1 (dress K U) hp).differentiableAt (by simp)
  rw [indexX,he.fderiv_eq, fderiv_comp 0 hv ((tailor_diff K U h).differentiableAt (by simp)),show Q 0=0 from tailor_zero K U]
  exact bill_multiply _ (helmets G c f) _ _ _

lemma arsenal (μ : ℝ) (K : Robe G c f) (U : Joint G c f) (h : Apparel K U) (hp : Explosives S t 1 (dress K U)) :
    cannonade S t μ K U=cannonade S t μ 1 (dress K U)*shear K U := by
  rw [cannonade,cannonade,Matrix.add_mul,Matrix.mul_assoc (mail _)ᵀ,shear_fine K U h,Matrix.mul_assoc,missile S t K U h hp]; rfl
end YM.Stationary
end

/-! # Choose linear-jet actual joint stationary representative. -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f}

variable (F : Forest S.ratio) (W : Matrix (Body 1 f) (Body 1 c) ℝ)

/-- The tree tangent repair straightened **up** the tree (see `books`);
this generator takes us from tree gauge BACK to the Fourier representative. -/
def salute (x : Link G c) := switchSite (uniformM (straighten S F W) x)
def liftedUp (ρ : Bid.Dir G c → AxisChart G F) (x : Link G c) :=
    wages S (salute F W x) 1 (encamp F ρ x)
/-- Centered log representative. `extend` takes this back to group
    version near the origin. -/
def soldier (t : S.Choices) (ρ : Bid.Dir G c → AxisChart G F) (x : Link G c) :=
    retract (recruit S t (liftedUp F W ρ x))

def endorse (W : Matrix (Body 1 f) (Body 1 c) ℝ) : Link G c →L[ℝ] Vault G c f := (uniformM W).prod 0

variable {F W} {ρ : Bid.Dir G c → AxisChart G F} {p : Clip} {R : PathData G} (h : Critical F p R ρ)
include h
lemma liftedThaw : Thaw (liftedUp F W ρ) 0 :=
    (camp_thaw h).wages S (Army.powG (v:=⇑(uniformM _)) (uniformM _).contDiff.contDiffAt) (Army.park _ _)
lemma lift_origin : liftedUp F W ρ 0=1 := by rw [liftedUp,encamp_zero h,salute,map_zero,switch_zero,wages_zero]

variable (hb : S.patch.Branches S.kernel G) (t : S.Choices)
include hb
lemma soldier_zero : soldier F W t ρ 0=0 := by rw [soldier,lift_origin h,recruit_zero S t hb,retract_one]
lemma soldier_diff : ContDiffAt ℝ ω (soldier F W t ρ) 0 := by
  have hh : Thaw (fun z => recruit S t (liftedUp F W ρ z)) 0 :=
    (liftedThaw h).from_cap hb t (by rw [lift_origin h]; rfl)
  exact hh.log (by rw [lift_origin h,recruit_zero S t hb])
lemma wage_live : ∀ᶠ z in 𝓝 (0:Link G c), enroll S t (Stationary.extend (soldier F W t ρ z))=liftedUp F W ρ z := by
  have hf : Thaw (fun z => recruit S t (liftedUp F W ρ z)) 0 :=
    (liftedThaw h).from_cap hb t (by rw [lift_origin h]; rfl)
  filter_upwards [(show Tendsto (fun z => recruit S t (liftedUp F W ρ z)) (𝓝 0) (𝓝 1) from by
    convert hf.cont.tendsto using 2; rw [lift_origin h,recruit_zero S t hb]).eventually extend_retract] with z hz
  rw [soldier,hz,enroll_recruit]

lemma soldier_known (hk : Guessed F W ρ) : fderiv ℝ (soldier F W t ρ) 0=endorse (G:=G) W := by
  let K := uniformM (G:=G) (straighten S F W)
  let D := uniformM (G:=G) W
  ext1 x
  have e0 : arm G c 1 (0:Link G c)=0 := by rw [map_zero]
  let Y := fun v : ℝ => liftedUp F W ρ (v • x)
  have eY : Y 0=1 := by simp [Y,lift_origin h]
  let Q := fun v : ℝ => encamp F ρ (v • x)
  let E := uniformM (extracted S F W) x
  have hx := hk (arm G c 1 x)
  have hQ i : HasDerivAt (fun v => G.mat ((Q v).1 i)) (G.colorMat (edgeColor E i)) 0 := by
    let p := arm G c 1 x
    let q := fun v : ℝ => (v • p,ρ (v • p))
    let F' := fun a : Work.F03.ChartVars F G => G.mat (Work.F03.live F a i)
    let L : Bid.Dir G c × AxisChart G F := (p,relative (S:=S) F W p)
    have hu := ray_swap (V:=F') ((Work.F03.live_smooth F (G:=G) i).differentiableAt (by simp))
      (Work.F03.live_rate F i L) (u:=q) (by simp [q,h.1]) ((ray_id p).prodMk hx)
    unfold Q encamp input; simp_rw [map_smul]
    rw [show edgeColor E i=Bid.stretch F L (i.1,coord i.2) by ext j; exact (congr_fun (Work.F04.parts_stretch F W p j) _).symm]
    exact hu
  have hQ' : Q 0=1 := by simp [Q,encamp_zero h]
  let k := fun v : ℝ => salute F W (v • x)
  have hk' : k 0=1 := by simp [k,salute]
  have hu i : HasDerivAt (fun v => G.mat (k v i)) (G.colorMat (gaugeColor (K x) i)) 0 := by unfold k salute; simp_rw [map_smul]; exact ray_power ..
  have he : D x=E - gradientA G f (K x) := by
    funext i
    rw [Pi.sub_apply,first_uniform]
    change _ = (extracted S F W *ᵥ parts _ 1 (arm _ _ _ x) i.2.2) (i.1,i.2.1) - _
    rw [extracted,add_mulVec, Pi.add_apply, ← Matrix.mulVec_mulVec, show (uniformM (d 0 f) (K x) i)=_ from rfl]
    change _ = D x i + uniformM (d 0 f) (K x) i - _
    abel
  have hY i : HasDerivAt (fun v => G.mat ((Y v).1 i)) (G.colorMat (edgeColor (D x) i)) 0 := by
    rw [he]; exact ray_gauged hk' hu (show (Q 0).1=1 by rw [hQ']; rfl) hQ i
  have ht : HasDerivAt (fun v => content (Y v).1) (D x) 0 := ray_content (by rw [eY]; rfl) hY
  let Z := fun v => recruit S t (Y v)
  have eZ : Z 0=1 := by unfold Z; rw [eY,recruit_zero S t hb]
  have hz i : HasDerivAt (fun v : ℝ => G.mat ((Z v).2 i)) (G.colorMat (gaugeColor 0 i)) 0 := by
    have hv : HasDerivAt (fun v => G.mat (bears S t (Y v).1 i)) (-G.colorMat (gaugeColor (uniformM (fixRoot S) (D x)) i)) 0 := by
      let u b := G.mat (bears S t (input G f b) i)
      have hp : Army (input G f) 0 := Army.powL contDiffAt_id
      have hy : ∀ᶠ v in 𝓝 0, input G f (content (Y v).1)=(Y v).1 := by
        have hi : Tendsto (fun v => (Y v).1) (𝓝 0) (𝓝 1) := by
          rw [show (1:Config G f)=(Y 0).1 from (congrArg Prod.fst eY).symm]
          apply ContinuousAt.fst
          apply ContinuousAt.comp (g:=liftedUp F W ρ) (f:=fun s : ℝ => s • x)
          · rw [zero_smul]; exact (liftedThaw h).cont
          exact (ray_id x).continuousAt
        exact hi.eventually content_encodes
      refine HasDerivAt.congr_of_eventuallyEq (f:=fun v => u (content (Y v).1)) ?_ ?_
      · exact ray_swap (V:=u) ((hp.bear hb t (input_zero ..) i).differentiableAt (by simp)) (rooted_cap hb t (D x) i)
          (u:=fun v => content (Y v).1) (by simp [eY]) ht
      filter_upwards [hy] with v hv; unfold u; rw [hv]
    have hw v : (Y v).2 i=(k v (S.ratio.embed i))⁻¹ := by simp [Y,liftedUp,encamp,wages,abode,k]
    -- root slice Phi contributes -K_{Ly}; it cancels the cap variation.
    unfold Z; simp only [recruit,Pi.mul_apply, hw,G.mat_mul,G.mat_inv]
    have hl : gaugeColor (K x) (S.ratio.embed i) = - gaugeColor (uniformM (fixRoot S) (D x)) i := by
      ext j; exact congr_fun (Precision.centers F W (parts _ 1 (arm G c 1 x) j)) (i,vac)
    convert! (hu (S.ratio.embed i)).star.mul hv using 1
    rw [hl]; simp [G.colorMat_skew,eY,hk',bear_zero S t hb]
  have hy : HasDerivAt (fun v : ℝ => frameLog ((Z v).2)) 0 0 := ray_frame (by rw [eZ]; rfl) hz
  exact (Push.side _ ((soldier_diff h hb t).differentiableAt (by simp)) x).unique (show HasDerivAt (fun v : ℝ => soldier F W t ρ (v • x)) (D x,0) 0 from ht.prodMk hy)

variable {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ)
include hp
lemma veteran_status : ∀ᶠ z in 𝓝 (0:Link G c), Shell S t p R (input _ _ z) (liftedUp F W ρ z) := by
  filter_upwards [camp_station h hb hp t] with z hz
  simpa only [gauge_one, liftedUp] using hz.wage hb hp (salute F W z) 1
lemma salary (W : Matrix (Body 1 f) (Body 1 c) ℝ) : (fun z : Link G c => merit S t p R (z,soldier F W t ρ z))=ᶠ[𝓝 0]
    (fun z => tested F t p R (arm G c 1 z) (ρ (arm G c 1 z))) := by
  filter_upwards [wage_live (W:=W) h hb t] with z hz
  simp only [merit,hz]; rw [← camp_claim,liftedUp]
  have hu := root_wages S t hb (encamp F ρ z) 1 (salute F W z) p R hp (input G c z)
  rwa [gauge_one] at hu
lemma pension : ∀ᶠ z in 𝓝 0, fderiv ℝ (fun x : Vault G c f => merit S t p R (z,x)) (soldier F W t ρ z)=0 := by
  let U x := enroll S t (Stationary.extend (x : Vault G c f))
  have hu : Thaw U 0 := (Thaw.through (v:=id) contDiffAt_id).to_cap hb t (congrArg Prod.fst extend_zero)
  have he : ∀ᶠ x in 𝓝 0, Thaw U x := by
    have A := eventually_all.mpr fun i => (hu.1 i).eventually (by simp)
    have B := eventually_all.mpr fun i => (hu.2 i).eventually (by simp)
    exact A.and B
  let D := soldier F W t ρ
  have hv : Tendsto D (𝓝 0) (𝓝 0) := by
    rw [← soldier_zero (W:=W) h hb t]; exact (soldier_diff h hb t).continuousAt.tendsto
  filter_upwards [veteran_status (W:=W) h hb t hp,wage_live h hb (W:=W) t,hv.eventually he] with z hz hu hV
  exact hz.chain hV hu
end YM.Stationary
end
