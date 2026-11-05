import YM.Next.STATIONARY.Joint.OnShell

set_option autoImplicit false
/-!
# Drift calculus in output left coordinates. Read real values first.
`payee` first derivative of bond prices in Z. Flat answer mixed Hessian
in THE physical counting. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module Finset
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side}

variable (S : StepData c f)

def payee (V Z : Config G c) : Link G c := fun i => fderiv ℝ (inure S V Z) 0 (pocket _ i)
def priceless (v : Link G c × Link G c × Link G c) := inure S (input G c v.1) (input G c v.2.1) v.2.2
def hectic (v : Link G c × Link G c × Link G c) := v.1-(v.2.2+v.2.1)
lemma valence : ContDiffAt ℝ ω (priceless (G:=G) S) 0 := by
  have h := bent (S:=S) (input G c ∘ Prod.fst) (input G c ∘ Prod.snd)
    (show Army (fun i : Link G c × Link G c => input G c i.1) 0 from Army.powL contDiffAt_fst)
    (show Army (fun i : Link G c × Link G c => input G c i.2) 0 from Army.powL contDiffAt_snd)
  exact h.comp (f:=fun v : Link G c × Link G c × Link G c => ((v.1,v.2.1),v.2.2)) (x:=0) (by fun_prop)
lemma value_drops : priceless (G:=G) S 0=0 ∧ fderiv ℝ (priceless (G:=G) S) 0=0 ∧ ∀ x y : Link G c × Link G c × Link G c, iteratedFDeriv ℝ 2 (priceless S) 0 ![x,y] = S.kernel.penalty * dotProduct (hectic x) (hectic y) := by
  refine Work.F03.hessian_of_limit (valence S |>.of_le le_top) (fun x => ?_) ?_ ?_
  · rw [dotEdge]
    simp_rw [priceless, inure,tickets,mul_div_assoc,Finset.sum_div]
    refine Tendsto.const_mul _ (tendsto_finsetSum _ (fun i _ => ?_)); rw [real_inner_self_eq_norm_sq]; simp only [Pi.mul_apply, Prod.smul_snd, Prod.smul_fst]
    apply Work.F03.price_limit (G:=G) (V:=fun t : ℝ => input _ _ (t • x.1) i * (input G c (t • x.2.2) i * input G c (t • x.2.1) i)⁻¹) (by simp)
    convert! ((ray_input x.1 i).mul ((ray_input x.2.2 i).mul (ray_input x.2.1 i)).star) using 1
    simp [hectic,G.colorMat_skew,sub_eq_add_neg]; abel
  · intro x y z; rw [show hectic (x+y)=hectic x+hectic y by simp only [hectic,Prod.snd_add,Prod.fst_add]; abel, add_dotProduct,mul_add]
  intro x y; rw [dotProduct_comm]

lemma oriented_fee : payee S (1:Config G c) 1=0 := by
  funext i; unfold payee
  let L : Link G c →L[ℝ] (Link G c × Link G c × Link G c) := (0:Link G c→L[ℝ]Link G c).prod (ContinuousLinearMap.inr ..)
  have hv : inure S (1:Config G c) 1 = priceless S ∘ L := by
    funext j; change inure _ _ _ _=inure _ (input G c 0) (input G c 0) j; rw [input_zero]
  rw [hv,fderiv_comp 0 (by rw [map_zero]; exact (valence S).differentiableAt (by simp)) L.differentiableAt,map_zero,(value_drops (G:=G) S).2.1]; rfl
lemma pay_memo {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (V Z : X → Config G c) (h : Army V 0) (he : Army Z 0) : ContDiffAt ℝ ω (fun z => payee S (V z) (Z z)) 0 := by
  have hv := Work.F05.curve_partial (F:=fun x => inure S (V x) (Z x)) (bent (S:=S) V Z h he)
  exact contDiffAt_pi.mpr fun i => (hv.comp (f:=fun x : X => (x,0)) 0 (by fun_prop)).clm_apply contDiffAt_const
lemma pay_jet (x : Link G c × Link G c) : HasDerivAt (fun v : ℝ => payee S (input G c (v • x.1)) (input G c (v • x.2))) (S.kernel.penalty • (x.2-x.1)) 0 := by
  let A := Link G c
  let Z := A × A
  let Y := A × Z
  let F : Z → A := fun z => payee S (input G c z.1) (input G c z.2)
  let f : Z → Y := fun x => (x.1,(x.2,0))
  let K := priceless (G:=G) S
  have hV : ContDiffAt ℝ ω K 0 := valence S
  have hp : ContDiffAt ℝ ω F 0 := pay_memo S _ _ (Army.powL contDiffAt_fst) (Army.powL contDiffAt_snd)
  have hX : HasDerivAt (fun t : ℝ => F (t • x)) (fderiv ℝ F 0 x) 0 := Push.side F (hp.differentiableAt (by simp)) x
  suffices he : fderiv ℝ F 0 x=S.kernel.penalty • (x.2-x.1) by rw [he] at hX; exact hX
  have he : Tendsto (fun v : ℝ => f (v • x)) (𝓝 0) (𝓝 0) := by
    have he : Continuous f := by unfold f; fun_prop
    exact he.continuousAt.tendsto.comp (show Tendsto (fun t : ℝ => t • x) (𝓝 0) (𝓝 0) from by simpa using (ray_id x).continuousAt.tendsto)
  funext i
  let y := pocket _ i
  let v : Y := (0,(0,y))
  have hc : (fun a : ℝ => F (a • x) i)=ᶠ[𝓝 0] fun a => fderiv ℝ K (a • f x) v := by
    filter_upwards [he.eventually (hV.eventually (by simp))] with a ha
    rw [show a • f x=f (a • x) by
      apply Prod.ext
      · rfl
      exact Prod.ext rfl (smul_zero _)]
    let g : A → Y := fun z => ((a • x).1,(a • x).2,z)
    have hh : HasDerivAt (fun t : ℝ => g (t • y)) v 0 :=
      (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (ray_id y))
    have hz : g ((0:ℝ) • y)=f (a • x) := by rw [zero_smul]
    change fderiv ℝ _ _ _= _
    apply HasDerivAt.unique (f:=fun t : ℝ => K (g (t • y))) (x:=0)
    · refine Push.side (fun z => K (g z)) ?_ y
      exact DifferentiableAt.comp 0 (g:=K) (f:=g) (ha.differentiableAt (by simp)) (by unfold g; fun_prop)
    exact (show HasFDerivAt K (fderiv ℝ K (f (a • x))) (g ((0:ℝ) • y)) by rw [hz]; exact (ha.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt 0 hh
  have hk := (hasDerivAt_pi.mp hX i).congr_of_eventuallyEq hc.symm
  have ho := (hV.fderiv_right (m:=ω) (by simp)).clm_apply (g:=fun _ => v) contDiffAt_const
  have hu := hk.unique (Push.side (fun a : Y => fderiv ℝ K a v) (ho.differentiableAt (by simp)) (f x))
  rw [divided _ _ hV] at hu
  change fderiv ℝ F 0 x i=_
  rw [hu,(show iteratedFDeriv ℝ 2 K 0 ![f x,v] =_ from (value_drops (G:=G) S).2.2 _ _)]
  simp only [hectic,f,v,zero_add, add_zero,zero_sub,dotProduct_neg,Pi.smul_apply]
  rw [show y=Pi.single i (1:ℝ) from Pi.basisFun_apply ..]; simp
end YM.Stationary
end

/-! # Drift field as computed on actual periods. Rooted Y gauge transport.
Normalization from *mixed* Hessian (not diagonal coefficient). -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module Finset
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

section dross
variable (S) (t : S.Choices) (K : Robe G c f) (V : Config G c) (U : Joint G c f)

abbrev income := payee S V (ribbon S t (dress K U))

def lapel (a b : Bodies G c f) : Link G c := iteratedFDeriv ℝ 2 (worn S t K U) 0 ![helmets _ _ _ a,helmets _ _ _ b]
def smear (u : Link G c) := Matrix.of fun i j => dotProduct u (lapel S t K U i j)
def rind (p : Clip) (R : PathData G) (μ : ℝ) : Link G c :=
  let A := legion S t p R μ K V U
  ∑ i, ∑ j, (A⁻¹ i j) • (lapel S t K U j i)
lemma earn_ad (p : Clip) (R : PathData G) (μ : ℝ) (k) :
    dotProduct k (rind S t K V U p R μ) = ((legion S t p R μ K V U)⁻¹*smear S t K U k).trace := by
  -- sums of real coefficients
  simp only [rind,dotProduct_sum, trace, diag_apply,Matrix.mul_apply, smear, Matrix.of_apply,dotProduct_smul, smul_eq_mul]
lemma merits (u : Link G c) : fderiv ℝ (inure S V (ribbon S t (dress K U))) 0 u=dotProduct (income S t K V U) u := by
  let P := fderiv ℝ (inure S V (ribbon S t (dress K U))) 0
  unfold income payee
  nth_rewrite 1 [← show ∑ i,u i • pocket _ i=u from Basis.sum_repr (pocket _) _]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_; rw [P.map_smul]; exact mul_comm ..
lemma wear_smear (h : ContDiffAt ℝ ω (worn S t K U) 0) :
    contact S t K V U= smear S t K U (income S t K V U) := by
  ext i j
  let L := fderiv ℝ (inure S V (ribbon S t (dress K U))) 0
  simp only [smear,lapel,Matrix.of_apply,contact,damage,LinearMap.toMatrix₂_apply, Work.F05.bend_apply]
  rw [← merits, L.iteratedFDeriv_comp_left h le_top]; rfl
end dross
section parameters
variable (h : S.patch.Branches S.kernel G) {p : Clip} {R : PathData G} {σ A Λ μ : ℝ} (hp : R.Bounds p σ A Λ) (t : S.Choices)
    (u : Coats G c) (k : Coats G f) (U : Joint G c f) (V : Config G c)
include h
lemma lapel_shift (he : Teller S t p R 1 U) (hb : Teller S t p R 1 (wages S k u U)) (x : Link G c) :
    (tactics k u)ᵀ * smear S t 1 (wages S k u U) (armor u x) * tactics k u = smear S t 1 U x := by
  let D (x : Link G c) : Link G c →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ x)
  have hF (U : Joint G c f) (h : ContDiffAt ℝ ω (worn S t 1 U) 0) (y : Link G c) :
      smear S t 1 U y= damage (helmets _ _ _) (D y ∘ worn S t 1 U) 0 := by
    ext i j; simp only [damage,LinearMap.toMatrix₂_apply,Work.F05.bend_apply]
    rw [ContinuousLinearMap.iteratedFDeriv_comp_left _ h le_top]; rfl
  let F := D (armor u x) ∘ worn S t 1 (wages S k u U)
  have ht : ContDiffAt ℝ ω F 0 := (D _).contDiff.contDiffAt.comp _ hb.wist
  rw [hF _ hb.wist,hF _ he.wist,tactics, ← damage_rate (L:=armUp k u) (F:=F) _ _ _]
  · apply damage_congr
    filter_upwards [quota_k h t k u U he] with y hy
    let A := worn S t 1 U y
    change D _ ((worn S t 1 _ ∘ _) y)=D _ A
    rw [hy]; change dotProduct (armor u x) (armor u A)=dotProduct x A
    rw [← bill_pay (armor u) x,← bill_pay (armor u) A, ← square_cost]; change dotProduct x (((trench u)ᵀ*trench u)*ᵥA)=_; rw [(trench_orthogonal u).right,one_mulVec]
  exact ht

include hp
lemma rind_carry (hx : 0<μ) (he : Teller S t p R 1 U) (hb : Teller S t p R 1 (wages S k u U))
    (hv : Explosives S t 1 U) (hy : Explosives S t 1 (wages S k u U)) (hi : IsUnit (legion S t p R μ 1 V U).det) :
    rind S t 1 (Lattice.gauge u V) (wages S k u U) p R μ=armor u (rind S t 1 V U p R μ) := by
  let P := trench u
  let T := tactics k u
  let H := legion S t p R μ 1 V U
  let F := legion S t p R μ 1 (Lattice.gauge u V) (wages S k u U)
  have hP : Military P := trench_orthogonal _
  have hT : Military T := tactics_orthogonal _ _
  have hg : Tᵀ *F *T=H := legion_law h t k u U V hp hv hy hx he hb
  have hC : F⁻¹ = T *H⁻¹ * Tᵀ :=
    hT.carry (Military.inverse_cross ((hT.turn_det hg).symm ▸ hi) hi (hT.pulls hg))
  let y := rind S t 1 V U p R μ
  let A := wages S k u U
  let z := rind S t 1 (Lattice.gauge u V) A p R μ
  have hz : Pᵀ *ᵥ z = y := by
    funext i
    let x : Link G c := Pi.single i 1
    suffices he : dotProduct x (Pᵀ *ᵥ z)=dotProduct x y by simpa [x] using he
    rw [transposes,show P *ᵥ x=_ from (show _=armor u x from bill_pay _ x)]
    unfold z y; rw [earn_ad,earn_ad]; change (F⁻¹ * smear S t 1 A _).trace=_
    have Hz : Tᵀ * smear S t 1 A (armor u x) * T = smear S t 1 U x := lapel_shift h t u k U he hb x
    rw [hC,mul_assoc T, mul_assoc T,trace_mul_comm T, mul_assoc H⁻¹, mul_assoc H⁻¹, Hz]
  change z=_; change z=armor u y
  rw [← bill_pay (armor u), ← hz]; change z=P *ᵥ (Pᵀ *ᵥ z); rw [Matrix.mulVec_mulVec,hP.left,one_mulVec]
end parameters
end YM.Stationary
end

/-! # Read the drift field in rooted coordinates. Match to stationary branch
on EVERY mesh before taking analytic continuation. Ward at true cell gradient,
including zero modes of mesh Laplacian. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module Finset
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {p : Clip} {R : PathData G} {μ σ A Λ : ℝ}

lemma legion_origin (h : S.patch.Branches S.kernel G) (hp : R.Bounds p σ A Λ) (t : S.Choices) (K : Robe G c f) (hb : Customs K) (μ) :
    legion S t p R μ K 1 1=medals S t p R μ K 1 1 := by
  let P : ℝ → Joint G c f := fun _ => 1
  have hF : Teller S t p R K 1 := (awake t hp (U:=P) (Thaw.fixed 1 _) rfl h hb).self_of_nhds
  rw [hF.contact,wear_smear S t K 1 1 hF.wist]; simp only [income,dressed_one hb,ribbon_zero S t h,oriented_fee,smear,zero_dotProduct]
  rw [show Matrix.of (fun (_ _ : Bodies G c f) => (0:ℝ))=0 from rfl,add_zero]

section pricing
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [CompleteSpace X]
    (h : S.patch.Branches S.kernel G) (t : S.Choices) (hp : R.Bounds p σ A Λ) (U : X → Joint G c f) (he : Thaw U 0) (hU : U 0=1)
include h he hU
omit [FiniteDimensional ℝ X] [CompleteSpace X] in
lemma worn_wear : ContDiffAt ℝ ω (fun z : X × Vault G c f => worn S t 1 (U z.1) z.2) 0 := by
  let Q := fun z : X × Vault G c f => U z.1
  have hh : Thaw Q 0 := he.comp (g:=U) (w:=Prod.fst) (x:=0) contDiffAt_fst
  have ht : Q 0=1 := hU
  have hu := Thaw.mul (Thaw.through (v:=fun z : X × Vault G c f => z.2) (contDiffAt_snd (p:=0))) hh
  have H := hu.ribbons h t (he:=by simp [ht])
  have P := hh.ribbons h t (show (Q 0).1=1 from congrArg Prod.fst ht)
  simp_rw [worn,atire,dress_one]; exact (H.mul P.inv).logL (by simp)
omit [FiniteDimensional ℝ X] [CompleteSpace X] in
lemma lapel_manual (i j) : ContDiffAt ℝ ω (fun x : X => lapel S t 1 (U x) i j) 0 := by
  have hh := Work.F05.curve_partial (F:=fun v => fderiv ℝ (worn S t 1 (U v))) (Work.F05.curve_partial (F:=fun v => worn S t 1 (U v)) (worn_wear h t U he hU))
  simp_rw [lapel,iteratedFDeriv_two_apply]; exact (((hh.comp (f:=fun x => (x,0)) (0:X) (by fun_prop)).clm_apply contDiffAt_const).clm_apply contDiffAt_const)
include hp
omit [CompleteSpace X] in
lemma rind_diff (V : X→ Config G c) (hv : Army V 0) (hV : V 0=1) (hi : IsUnit (legion S t p R μ 1 1 1).det) (hμ : 0<μ) :
    ContDiffAt ℝ ω (fun x => rind S t 1 (V x) (U x) p R μ) 0 := by
  have hk := ammo_pay U V he (by rw [hU]; rfl) hv 1 root_customs h t hp hμ
  have ht : Memo (fun x => (legion S t p R μ 1 (V x) (U x))⁻¹) 0 := Memo.flip hk.2.2 (by rw [hU,hV]; exact hi.ne_zero)
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => (ht i j).smul (lapel_manual h t U he hU ..)
end pricing

section stations
variable {F : Forest S.ratio} {ρ : Bid.Dir G c → AxisChart G F} {η : ℝ}
    (h : Critical F p R ρ) (hp : R.Bounds p σ A Λ) (t : S.Choices) (he : S.patch.Branches S.kernel G) (hμ : 0<μ)
    (hy : PriceGap F p R η) (hz : 0<η)
include h hp he hμ hy hz
lemma unit_ud : IsUnit (legion S t p R μ 1 1 1).det := by
  obtain ⟨P,hP⟩ := LocalH.actual G
  have hx := (tribute h he hp hy hz hμ t hP).self_of_nhds.1
  rw [input_zero,encamp_zero h] at hx
  rw [legion_origin he hp t 1 root_customs]; exact hx.ne'.isUnit

lemma armor_rotation (u : G.El) :
    let y := rind S t 1 (1:Config G c) 1 p R μ
    y=armor (solid u) y := by
  intro y
  have hh : Teller S t p R 1 (1:Joint G c f) :=
      (awake t hp (U:=fun _ : ℝ => (1:Joint G c f)) (Thaw.fixed (1:Joint G c f) (0:ℝ)) (show (1:Joint G c f).1=1 from rfl) he root_customs).self_of_nhds
  have hi : Explosives S t 1 (1:Joint G c f) :=
      (explosive S t he root_customs (U:=fun _ : ℝ => (1:Joint G c f)) (Thaw.fixed (1:Joint G c f) (0:ℝ)) (show (1:Joint G c f).1=1 from rfl)).self_of_nhds
  have hv : Teller S t p R 1 (wages S (solid u) (solid u) 1) := by rw [solid_arm]; exact hh
  have hw : Explosives S t 1 (wages S (solid u) (solid u) 1) := by rw [solid_arm]; exact hi
  have ht := rind_carry he hp t (solid u) (solid u) 1 1 hμ hh hv hi hw (unit_ud h hp t he hμ hy hz)
  rw [solid_arm, show Lattice.gauge (solid u) (1:Config G c)=1 by ext i; simp [Lattice.gauge,solid]] at ht
  exact ht
lemma armor_zero (hG : G.Simple) : rind S t 1 1 1 p R μ=0 := by
  let y := rind S t 1 (1:Config G c) 1 p R μ
  have hp' (u : G.El) : y=armor (solid u) y := armor_rotation h hp t he hμ hy hz u
  apply edgeColor.injective
  rw [map_zero]; funext i
  change edgeColor y i = 0
  apply color_fixed_at hG _
  intro u
  exact (show G.adjoint u (edgeColor y i)=edgeColor (armor (solid u) y) i from Eq.symm (armor_at (solid u) y i)).trans (congr_arg (fun v => edgeColor v i) (hp' u).symm)
lemma remit {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [FiniteDimensional ℝ X]
    {U : X → Joint G c f} {V : X → Config G c} {k : X → Coats G f} {u : X → Coats G c} (hh : Thaw U 0) (hr : U 0=1)
    (hv : Army V 0) (hV : V 0=1) (hP : Thaw (fun z => wages S (k z) (u z) (U z)) 0) (hx : (wages S (k 0) (u 0) (U 0)).1=1) :
    ∀ᶠ x in 𝓝 0, rind S t 1 (Lattice.gauge (u x) (V x)) (wages S (k x) (u x) (U x)) p R μ=armor (u x) (rind S t 1 (V x) (U x) p R μ) := by
  have ht : (U 0).1=1 := congrArg Prod.fst hr
  have hx' := Memo.det_val (ammo_pay U V hh ht hv 1 root_customs he t hp hμ).2.2
  have hM : (legion S t p R μ 1 (V 0) (U 0)).det ≠ 0 := by rw [hr,hV]; exact (unit_ud h hp t he hμ hy hz).ne_zero
  filter_upwards [awake t hp hh ht he root_customs,awake t hp hP hx he root_customs,
    explosive S t he root_customs hh ht,explosive S t he root_customs hP hx,hx'.continuousAt.eventually_ne hM] with a ha hb hh hB hi
  exact rind_carry he hp t _ _ _ _ hμ ha hb hh hB hi.isUnit

def bountyY (F : Forest S.ratio) (ρ : Bid.Dir G c → AxisChart G F) (t : S.Choices) (p : Clip) (R : PathData G) (μ : ℝ) (x : Link G c) :=
    rind S t 1 (input G c x) (encamp F ρ x) p R μ

-- kills independently of signed orientation or coordinate permutation. Parameter produces z from 0 ONLY.
lemma guard_y (hG : G.Simple) (x : BaseSites G c) : fderiv ℝ (bountyY F ρ t p R μ) 0 (gradientA G c x)=0 := by
  let Y := bountyY F ρ t p R μ
  have h0 : Y 0=0 := by rw [show Y 0= _ from rfl]; unfold Y bountyY; rw [input_zero, encamp_zero h]; exact armor_zero h hp t he hμ hy hz hG
  let T := BaseSites G c
  let P := fun v : T => switchSite v
  let V := fun v : T => Lattice.gauge (P v) 1
  let L : T →L[ℝ] Swatch G c := ContinuousLinearMap.inl ..
  let A := moveField ∘ L
  have hp' := Army.powG (v:=fun z : T => z) (contDiffAt_id (x:=(0:T)))
  let U := encamp F ρ 0
  have heU : U=1 := encamp_zero h
  let K := fun v : T => wages S 1 (P v) U
  have heP : P 0=1 := switch_zero
  have hK : Thaw K 0 := (Thaw.fixed U _).wages S (Army.park 1 0) hp'
  have hK' : K 0=1 := by unfold K; rw [heP,wages_zero,heU]
  have hh : Shell S t p R 1 U := by simpa only [input_zero,U] using! (camp_station h he hp t).self_of_nhds
  have hz' (i) : Shell S t p R (V i) (K i) := hh.wage he hp 1 (P i)
  have hm := (show Tendsto L (𝓝 0) (𝓝 0) from by simpa using L.continuous.tendsto 0).eventually moveField_germ
  have hf : ∀ᶠ x in 𝓝 0, input G c (A x)=V x := hm.mono fun i hi => hi.trans (by change Lattice.gauge _ (input _ _ 0)=_; rw [input_zero]; rfl)
  have hv : ContDiffAt ℝ ω A 0 := (moveField_analytic (G:=G) (m:=c)).contDiffAt.comp (g:=moveField) (f:=L) _ L.contDiff.contDiffAt
  have hx : ∀ᶠ i in 𝓝 0, cloak S F (K i)=encamp F ρ (A i) := veterans h he hp hy hz t hK hK' hv (show A 0=0 from moveField_zero) (hf.mono (fun a ha => by rw [ha]; exact hz' a))
  have hi := remit h hp t he hμ hy hz (u:=P) (k:=fun _ : T => 1) (Thaw.fixed U _) heU (Army.park (1: Config G c) _) rfl hK (by rw [show (wages S 1 _ _) = _ from hK']; rfl)
  have hj := remit h hp t he hμ hy hz hK hK' (V:=V) (hp'.slant (Army.park (1:Config G c) 0)) (by unfold V; rw [heP,gauge_one]) (u:=fun _ => 1) (k:=fun z => boots S F (K z)) (cloak_lit S F hK) (by change (cloak S F (K 0)).1=_; rw [hK',cloak_zero S F]; rfl)
  have hk : Y ∘ A=ᶠ[𝓝 0] 0 := by
    filter_upwards [hx,hi,hj,hf] with a he' hw hq hh'
    unfold Y; simp only [Function.comp_apply,bountyY, ← he',hh']
    have H : rind S t 1 (V a) (K a) p R μ=0 := hw.trans (by rw [heU,armor_zero h hp t he hμ hy hz hG,map_zero])
    change rind S t 1 (Lattice.gauge 1 (V a)) (cloak S F (K a)) _ _ _=armor 1 _ at hq
    rw [gauge_one, H,map_zero] at hq; exact hq
  have hd := camp_thaw h
  have hY : ContDiffAt ℝ ω Y 0 := rind_diff he t hp (encamp F ρ) hd heU _ (Army.powL contDiffAt_id) (input_zero ..) (unit_ud h hp t he hμ hy hz) hμ
  have he' : fderiv ℝ (Y ∘ A) 0=0 := by rw [hk.fderiv_eq,fderiv_zero]; rfl
  rw [fderiv_comp _ (show DifferentiableAt ℝ Y (A 0) from (show A 0=0 from moveField_zero).symm ▸ (hY.differentiableAt (by simp))) (hv.differentiableAt (by simp)),show A 0=0 from moveField_zero] at he'
  have hg : fderiv ℝ A 0 x = - gradientA G c x := by
    unfold A; rw [fderiv_comp _ (by rw [map_zero]; exact moveField_analytic.differentiableAt) L.differentiableAt, map_zero, L.fderiv, ContinuousLinearMap.comp_apply, moveField_rate]; exact zero_sub _
  have hq := DFunLike.congr_fun he' x
  rw [ContinuousLinearMap.comp_apply,hg,map_neg, _root_.zero_apply, neg_eq_zero] at hq; exact hq
end stations
end YM.Stationary
end

/-! # Pull linear momentum test for drift. Along stationary x first compute
legion log in centered coordinates and contact separately in rooted. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module Finset
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

-- legislative subsidy OFF shell Hess only without contact
variable (S) (t : S.Choices) (p : Clip) (R : PathData G) (μ : ℝ)
def coreBoon (x : Point G c f) : ℝ := Real.log (legion S t p R μ (fedora S t) (input G c x.1) (Stationary.extend x.2)).det
def majorBoon (x : Point G c f) : ℝ := Real.log (medals S t p R μ (fedora S t) (input G c x.1) (Stationary.extend x.2)).det

variable {p R μ S}
lemma core_silence (u : G.El) (h : S.patch.Branches S.kernel G) {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ) (hμ : 0<μ) :
    coreBoon S t p R μ ∘ starsky u =ᶠ[𝓝 0] coreBoon S t p R μ := by
  let P := Point G c f
  let V z := input G c ((z:P).1)
  let K := fedora S t (G:=G)
  let W := starsky (c:=c) (f:=f) u
  let U := fun z : P => Stationary.extend z.2
  let X z := dress K (U z)
  have hk := fedora_style h t
  have hu : Thaw U 0 := Thaw.through contDiffAt_snd
  have hU : (U 0).1=1 := by simp [U]
  have hx : Thaw X 0 := sport_thaw hk hu hU
  have hv : Tendsto W (𝓝 0) (𝓝 0) := by simpa using W.continuous.tendsto 0
  have he := fedora_u u t h hu hU
  have HH := awake t hp hx hU h root_customs
  have he' := explosive S t h root_customs hx hU
  have ht : ∀ᶠ z in 𝓝 0, coreBoon S t p R μ z=Real.log (legion S t p R μ 1 (V z) (X z)).det := by
    filter_upwards [atire_out hk hu hU,HH,he'] with z ha hb hc
    change Real.log (legion S t p R μ K (V z) (U z)).det=_
    rw [fields S t p R μ K (V z) (U z) ha hc hb.wist,Matrix.det_mul,Matrix.det_mul,det_transpose,shear_det K (U z) ha,one_mul,mul_one]
  filter_upwards [hv.eventually ht,ht,he,hv.eventually HH,hv.eventually he', HH,he'] with z ht hE he hT hQ hb hc
  have hx : X (W z)=wages S (solid u) (solid u) (X z) :=
    (congr_arg (dress K) (point_shifts (S:=S) u z)).trans he
  rw [hx] at hT hQ ht
  rw [Function.comp_apply,show starsky u=W from rfl,ht,hE]
  rw [show V (W z)=_ from solid_color u z, (tactics_orthogonal _ _).turn_det (legion_law h t _ _ _ _ hp hc hQ hμ hb hT)]

lemma major_silence (u : G.El) (h : S.patch.Branches S.kernel G) {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ) (hμ : 0<μ) :
    majorBoon S t p R μ ∘ starsky u =ᶠ[𝓝 0] majorBoon S t p R μ := by
  filter_upwards [veneration h t u hp hμ] with z hz
  have hu : Stationary.extend (starsky u z).2=wages S (solid u) (solid u) (Stationary.extend z.2) := point_shifts ..
  have H := battery (Stationary.extend z.2).1 hμ (solid u) |>.2
  have hx : (grenade μ (ColorX u z).1).det=(grenade μ (Stationary.extend z.2).1).det := by unfold ColorX; rw [hu]; exact (troop_orthogonal _).turn_det ((troop_orthogonal _).back H)
  unfold bounty at hz; rw [hx] at hz
  exact mul_left_cancel₀ (show (1/2:ℝ)≠0 by norm_num) (sub_left_inj.mp hz)

lemma memo_dross (h : S.patch.Branches S.kernel G) {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ) (he : IsUnit (legion S t p R μ (fedora S t) 1 1).det) (hμ : 0<μ) :
    ContDiffAt ℝ ω (coreBoon S t p R μ) 0 ∧ ContDiffAt ℝ ω (majorBoon S t p R μ) 0 := by
  let V (x : Point G c f) := input G c (Prod.fst x)
  let U (x : Point G c f) := Stationary.extend x.2
  have H := ammo_pay U V (Thaw.through contDiffAt_snd) (by simp [U]) (Army.powL contDiffAt_fst) _ (fedora_style h t) h t hp hμ
  have hx : (legion S t p R μ (fedora S t) 1 1).det≠0 := he.ne_zero
  refine ⟨(Memo.det_val H.2.2).log (by simp only [V,U,Prod.fst_zero,Prod.snd_zero,input_zero, extend_zero]; exact hx),
    (Memo.det_val H.2.1).log (by simp only [V,U,Prod.fst_zero,Prod.snd_zero,input_zero, extend_zero]; rw [← legion_origin h hp t (fedora S t) (fedora_style h t)]; exact hx)⟩

section landmarks
variable (S) (W : Matrix (Body 1 f) (Body 1 c) ℝ)

def chevron (b : Link G c) := dress (fedora S t) (Stationary.extend (endorse W b))
def levy (b : Link G c) := income S t (1:Robe G c f) (input _ _ b) (chevron S t W b)
lemma chevron_lit (h : S.patch.Branches S.kernel G) : Thaw (chevron (G:=G) S t W) 0 := sport_thaw (fedora_style h t)
    (Thaw.through (v:=fun b : Link G c => endorse W b) (endorse W).contDiff.contDiffAt) (by simp)
lemma chevron_zero (h : S.patch.Branches S.kernel G) : chevron (G:=G) S t W 0=1 := by rw [chevron,map_zero,extend_zero]; exact dressed_one (fedora_style h t)

lemma got_leg (h : S.patch.Branches S.kernel G) (H T : Bed) (hv : Inputs S W (H.metric.acts f) (T.metric.acts c)) :
    fderiv ℝ (levy S t W) 0= - uniformM (G:=G) (Precision.K (T.metric.acts c)) := by
  let K := Precision.K (T.metric.acts c)
  let k := S.kernel.penalty
  let P x := ribbon S t (chevron S t W (x : Link G c))
  have hP : P 0=1 := by rw [show P 0=_ from rfl]; unfold P; rw [chevron_zero S t W h,ribbon_zero S t h]
  have hi : Army P 0 := (chevron_lit S t W h).ribbons h t (show (chevron S t W 0).1=1 by rw [chevron_zero S t W h]; rfl)
  have hp : levy S t W (G:=G)=fun x => payee S (input _ _ x) (P x) := by ext x; simp [levy,P,income]
  have hc := pay_memo S (input G c) P (Army.powL contDiffAt_id) hi
  apply ContinuousLinearMap.ext; intro x
  let Z := uniformM K x
  let Y := x - k⁻¹ • Z
  have he : uniformM (Precision.mean S) ((endorse (G:=G) W x).1) - gradientA G c ((endorse W x).2)=Y := by
    rw [show (endorse W x).2=(0:BaseSites G c) from rfl,map_zero,sub_zero]; ext i
    let b := parts G 1 (arm G c 1 x) i.2.2
    have hh : (Precision.mean S *ᵥ (W *ᵥ b))= b-k⁻¹ • (K *ᵥ b) := by rw [mulVec_mulVec,hv.dual,sub_mulVec,one_mulVec,smul_mulVec]
    exact congr_fun hh (i.1,i.2.1)
  have hx : HasDerivAt (fun a : ℝ => content (P (a • x))) Y 0 := by
    refine ray_content (show P ((0:ℝ) • x)=1 by rw [zero_smul,hP]) fun i => ?_
    rw [← he]; unfold P chevron; simp_rw [map_smul]; exact centered_pred h t (endorse W x) _
  rw [hp]
  refine (Push.side _ (hc.differentiableAt (by simp)) x).unique ?_
  let f (x : Link G c × Link G c) := payee S (input G c x.1) (input G c x.2)
  let z (a : ℝ) := (a • x,content (P (a • x)))
  have hl : HasDerivAt (fun a => f (z a)) (k • (Y-x)) 0 :=
      ray_swap (V:=f) ((pay_memo S _ _ (Army.powL (x:=(0: Link G c × Link G c)) contDiffAt_fst) (Army.powL contDiffAt_snd)).differentiableAt (by simp))
        (x:=(x,Y)) (pay_jet S (x,Y)) (u:=z) (by simp [z,hP]) ((ray_id x).prodMk hx)
  rw [show k • (Y-x)= -Z by unfold Y; rw [sub_right_comm,sub_self,zero_sub,smul_neg,smul_smul,mul_inv_cancel₀ (show k≠0 from S.kernel.penalty_pos.ne'),one_smul]] at hl
  refine hl.congr_of_eventuallyEq ?_
  have ht : Tendsto (fun t : ℝ => t • x) (𝓝 0) (𝓝 0) := by simpa using! (ray_id x).continuousAt.tendsto
  filter_upwards [ht.eventually ((show Tendsto P _ (𝓝 1) from hP ▸ hi.cont.tendsto).eventually content_encodes)] with a ha
  dsimp only [f,z]; rw [ha]
end landmarks
end YM.Stationary
end

/-!
# D_Z contributes NO Jacobian gradient omitted at this stage: exact
Ward pairing for the CONTACT contribution. Mixed derivative for twice
that part of the thermal response, all-mesh. Still need limit / strip
continuation & alpha. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module Finset
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio}

section dots
variable {ι X : Type} [Fintype ι] [NormedAddCommGroup X] [NormedSpace ℝ X]
lemma dot_quadr {P Q : X→Corn ι} (h : ContDiffAt ℝ ω P 0) (q : ContDiffAt ℝ ω Q 0) (he : P 0=0) (p : Q 0=0) (u v) : iteratedFDeriv ℝ 2 (fun x => dotProduct (P x) (Q x)) 0 ![u,v]=dotProduct (fderiv ℝ P 0 u) (fderiv ℝ Q 0 v)+dotProduct (fderiv ℝ P 0 v) (fderiv ℝ Q 0 u) := by
  let K : Corn ι →L[ℝ] Corn ι →L[ℝ] ℝ  := LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (Corn ι →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Corn ι →L[ℝ] ℝ)).toLinearMap ∘ₗ dotProductBilin ℝ ℝ)
  let G := K ∘ P
  have hp : ContDiffAt ℝ ω G 0 := K.contDiff.contDiffAt.comp _ h
  have hu' : G 0=0 := by simp [G,he]
  change iteratedFDeriv ℝ 2 (fun x => (G x) (Q x)) 0 ![u,v]=_
  have hx : (fun x => fderiv ℝ (fun a => (G a) (Q a)) x v)=ᶠ[𝓝 0] fun x => (G x) (fderiv ℝ Q x v)+(fderiv ℝ G x v) (Q x) := by
    filter_upwards [hp.eventually (by simp),q.eventually (by simp)] with x hx hy; rw [fderiv_clm_apply (hx.differentiableAt (by simp)) (hy.differentiableAt (by simp))]; rfl
  rw [← divided _ _ (hp.clm_apply q),hx.fderiv_eq]
  let V x := fderiv ℝ G x v
  let R x := fderiv ℝ Q x v
  have hi : DifferentiableAt ℝ V 0 := ((hp.fderiv_right (m:=ω) (by simp)).clm_apply (g:=fun _ => v) contDiffAt_const).differentiableAt (by simp)
  have hl : DifferentiableAt ℝ R 0 := ((q.fderiv_right (m:=ω) (by simp)).clm_apply (g:=fun _ => v) contDiffAt_const).differentiableAt (by simp)
  have hk := q.differentiableAt (by simp)
  have hg := hp.differentiableAt (by simp)
  rw [fderiv_fun_add (hg.clm_apply hl) (hi.clm_apply hk), fderiv_clm_apply hg hl,fderiv_clm_apply hi hk,_root_.add_apply, _root_.add_apply, _root_.add_apply]
  change (G 0) _ + _ + (V 0 (fderiv ℝ Q 0 u) + fderiv ℝ V 0 u (Q 0))=_
  simp only [hu',_root_.zero_apply,zero_add,p,map_zero,add_zero,ContinuousLinearMap.flip_apply]
  unfold V G; rw [fderiv_comp _ K.differentiableAt (h.differentiableAt (by simp)),K.fderiv]; rfl
end dots

variable (F) (ρ : fieldDir G c 1 → AxisChart G F) (W : Matrix (Body 1 f) (Body 1 c) ℝ)
    (p : Clip) (R : PathData G) (t : S.Choices) (μ : ℝ)

def pace (x : Link G c) : Point G c f := (x,soldier F W t ρ x)
def drossY (x : Link G c) : Link G c := rind S t 1 (input _ _ x) (chevron S t W x) p R μ

variable {F ρ W p R μ}
variable {σ A Λ η : ℝ} (h : Critical F p R ρ) (hp : R.Bounds p σ A Λ) (hk : Guessed F W ρ)
    (hy : S.patch.Branches S.kernel G) (hh : PriceGap F p R η) (hη : 0<η) (ht : 0<μ)
include h hk hy

lemma pace_deriv : HasFDerivAt (pace F ρ W t) (saluteLe (G:=G) W) 0 := by
  have hx := ((soldier_diff h hy t (W:=W)).differentiableAt (by simp)).hasFDerivAt
  rw [soldier_known h hy t hk] at hx
  exact (hasFDerivAt_id _).prodMk hx
-- replace station log by linear weight in derivative of any readout of (Point centered frame)
lemma stem_pay {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {M : Point G c f→X} (H : DifferentiableAt ℝ M 0) :
    fderiv ℝ (M ∘ pace F ρ W t) 0=fderiv ℝ (M ∘ saluteLe (G:=G) W) 0 := by
  let T := saluteLe (G:=G) W
  let P := pace F ρ W t
  have hp : P 0=0 := Prod.ext rfl (soldier_zero h hy t)
  have he := pace_deriv t h hk hy
  change fderiv ℝ (M ∘ P) _=fderiv ℝ (M ∘ T) _
  rw [fderiv_comp _ (by rw [hp]; exact H) (show DifferentiableAt ℝ P 0 from he.differentiableAt),hp,show fderiv ℝ P 0=T from he.fderiv,fderiv_comp _ (by rw [map_zero]; exact H) T.differentiableAt,map_zero,T.fderiv]

lemma stem_second (M : Point G c f → ℝ) (hr : ContDiffAt ℝ ω M 0) (hv : fderiv ℝ M 0=0) :
    iteratedFDeriv ℝ 2 (M ∘ pace F ρ W t) 0=iteratedFDeriv ℝ 2 (M ∘ saluteLe (G:=G) W) 0 := by
  ext1 v; let T := saluteLe (G:=G) W; let P := pace F ρ W t
  have hp : P 0=0 := Prod.ext rfl (soldier_zero h hy t)
  change iteratedFDeriv ℝ 2 (M ∘ P) _ v=iteratedFDeriv ℝ 2 (M ∘ T) _ v
  rw [show v=![v 0,v 1] by ext1 i; fin_cases i <;> rfl]; rw [(Work.F03.hessian_comp hp (hr.of_le le_top) (show ContDiffAt ℝ 2 P 0 from contDiffAt_id.prodMk ((soldier_diff h hy t).of_le le_top)) hv).2,
    show fderiv ℝ P 0=T from (pace_deriv t h hk hy).fderiv, (Work.F03.hessian_comp T.map_zero (hr.of_le le_top) (T.contDiff.contDiffAt (n:=2)) hv).2,T.fderiv]

include hp hh hη ht
lemma y_stems : fderiv ℝ (drossY W p R t μ) 0=fderiv ℝ (bountyY F ρ t p R μ) 0 := by
  let V z := input G c ((z:Point G c f).1)
  let U (z : Point G c f) := dress (fedora S t) (Stationary.extend z.2)
  let Y := fun z => rind S t 1 (V z) (U z) p R μ
  let K := pace F ρ W t
  have hu : Thaw U 0 := sport_thaw (fedora_style hy t) (Thaw.through contDiffAt_snd) (by simp)
  have hv : U 0=1 := by simp only [U,Prod.snd_zero,extend_zero]; exact dressed_one (fedora_style hy t)
  have he : ContDiffAt ℝ ω Y 0 := rind_diff hy t hp U hu hv V (Army.powL contDiffAt_fst) (by simp [V]) (unit_ud h hp t hy ht hh hη) ht
  have hr := remit h hp t hy ht hh hη (camp_thaw h) (encamp_zero h) (V:=input G c) (Army.powL contDiffAt_id) (input_zero ..) (u:=fun _ => 1) (k:=salute F W) (liftedThaw h) (by change (liftedUp F W ρ 0).1=1; rw [lift_origin h]; rfl)
  have hg : Y∘K=ᶠ[𝓝 0] bountyY F ρ t p R μ := by
    filter_upwards [hr,wage_live h hy (W:=W) t] with z hz hr
    change dress (fedora S t) (Stationary.extend (K z).2)=_ at hr
    change rind S t 1 (input _ _ z) (dress (fedora S t) _) _ _ _= _
    rw [hr]; change rind S t 1 (Lattice.gauge 1 _) (liftedUp F W ρ z) p R μ=armor 1 (bountyY F ρ t p R μ z) at hz
    rw [gauge_one] at hz; refine hz.trans ?_
    apply edgeColor.injective; funext i; rw [armor_at,Pi.one_apply,G.adjoint_one]
  change fderiv ℝ (Y ∘ saluteLe (G:=G) W) 0= _
  rw [← stem_pay t h hk hy (M:=Y) (he.differentiableAt (by simp)), show fderiv ℝ (Y ∘ pace F ρ W t) 0=_ from hg.fderiv_eq]

set_option maxHeartbeats 480000 in
lemma lean_drift (hG : G.Simple) (H T : Bed) (he : Inputs S W (H.metric.acts f) (T.metric.acts c)) (x y : Link G c) :
    let M := legion S t p R μ 1 1 1
    let Y := drossY W p R t μ
    let J : Link G c→ Link G c := - (fun z => uniformM (Precision.K (T.metric.acts c)) z)
    let A := saluteLe (G:=G) W
    let N := majorBoon S t p R μ ∘ A
    let Q := coreBoon S t p R μ ∘ A
    iteratedFDeriv ℝ 2 N 0 ![x,y]= iteratedFDeriv ℝ 2 Q 0 ![x,y] +
        (dotProduct (J x) (fderiv ℝ Y 0 y)+dotProduct (J y) (fderiv ℝ Y 0 x)) -
        ((M⁻¹*smear S t 1 1 (J x)*M⁻¹)*smear S t 1 1 (J y)).trace := by
  intro M Y J A N Q
  let D := pace F ρ W t
  let C := fedora (G:=G) S t
  let V := fun z : Link G c => input G c z
  let U := fun z => Stationary.extend (D z).2
  let X := dress C ∘ U
  have hi : IsUnit M.det := unit_ud h hp t hy ht hh hη
  have hh' := memo_dross t hy hp (μ:=μ) (by rw [legion_origin hy hp t _ (fedora_style hy t)]; exact (moment_track h hy hp t ht hh hη).1.ne'.isUnit) ht
  let E := majorBoon S t p R μ
  let P := coreBoon S t p R μ
  have hp' := stem_second t h hk hy P hh'.1 (triple_star hG (fun u => core_silence t u hy hp ht) (hh'.1.differentiableAt (by simp)))
  have he' := stem_second t h hk hy E hh'.2 (triple_star hG (fun u => major_silence t u hy hp ht) (hh'.2.differentiableAt (by simp)))
  change iteratedFDeriv ℝ 2 (E ∘ saluteLe (G:=G) W) _ _ = iteratedFDeriv ℝ 2 (P ∘ saluteLe (G:=G) W) _ _ + _ - _
  rw [← hp',← he']
  let K z := legion S t p R μ 1 (V z) (X z)
  have hU : Thaw U 0 := Thaw.through (soldier_diff h hy t)
  have hU' : U 0=1 := by change Stationary.extend (soldier F W t ρ 0)=1; rw [soldier_zero h hy t,extend_zero]
  have hc := fedora_style hy t
  have ha : (U 0).1=1 := by rw [hU']; rfl
  have hX : Thaw X 0 := sport_thaw hc hU ha
  have hX' : X 0=1 := by unfold X; rw [Function.comp_apply,hU',dressed_one hc]
  have hV : Army V 0 := Army.powL contDiffAt_id
  have hV' : V 0=1 := input_zero ..
  have hK : Memo K 0 := (ammo_pay X V hX (by rw [hX']; rfl) hV 1 root_customs hy t hp ht).2.2
  have hK' : K 0=M := by unfold K; rw [hV',hX']
  let B := fun z => income S t 1 (V z) (X z)
  let Gm z := smear S t 1 (X z) (B z)
  let Rm := fun z => rind S t 1 (V z) (X z) p R μ
  have hB : ContDiffAt ℝ ω B 0 := by
    have he : B=fun z => payee S (V z) (ribbon S t (X z)) := funext (fun z => by simp [B,income,dress_one])
    rw [he]; exact pay_memo S _ _ hV (hX.ribbons hy t (by rw [hX']; rfl))
  have hB' : B 0=0 := by simp [B,income,hX',hV',ribbon_zero S t hy,oriented_fee]
  have hY := rind_diff hy t hp X hX hX' V hV hV' hi ht
  have e : Rm 0=0 := by unfold Rm; rw [hX',hV']; exact armor_zero h hp t hy ht hh hη hG
  let W' (v : Point G c f) := dress C (Stationary.extend v.2)
  let V' (v : Point G c f) := input G c v.1
  have hv' : Army V' 0 := Army.powL contDiffAt_fst
  have hw : Thaw W' 0 := sport_thaw hc (Thaw.through contDiffAt_snd) (by simp)
  have hw' : W' 0=1 := by simp only [W',Prod.snd_zero,extend_zero]; exact dressed_one hc
  have hRm : fderiv ℝ Rm 0=fderiv ℝ Y 0 := stem_pay t h hk hy (M:=fun z => rind S t 1 (V' z) (W' z) p R μ) ((rind_diff hy t hp W' hw hw' V' hv' (by simp [V']) hi ht).differentiableAt (by simp))
  have hk' (x : Link G c) : fderiv ℝ B 0 x=J x := by
    let U' : Point G c f→ Link G c := fun z => income S t 1 (V' z) (W' z)
    have hw : ContDiffAt ℝ ω U' 0 := by
      unfold U'; simp only [income,dress_one]; exact pay_memo S V' _ hv' (hw.ribbons hy t (by rw [hw']; rfl))
    have heQ : fderiv ℝ B 0=fderiv ℝ (levy S t W) 0 := stem_pay t h hk hy (hw.differentiableAt (by simp))
    rw [heQ,got_leg S t W hy H T he]; rfl
  have hGm : Memo Gm 0 := by
    intro i j; unfold Gm smear; simp only [Matrix.of_apply,dotProduct]
    refine ContDiffAt.sum fun k _ => (contDiffAt_pi.mp hB k).mul ?_
    exact contDiffAt_pi.mp (lapel_manual hy t X hX hX' i j) _
  have hGm' : Gm 0=0 := by unfold Gm; simp only [smear,hB',zero_dotProduct]; rfl
  have heP : ∀ᶠ z : Link G c in 𝓝 0, Teller S t p R 1 (X z) ∧ Apparel C (U z) ∧ Explosives S t 1 (X z) ∧ Shell S t p R (V z) (X z) := by
    refine (awake t hp hX (by rw [hX']; rfl) hy root_customs).and ((atire_out hc hU ha).and ((explosive S t hy root_customs hX (by rw [hX']; rfl)).and ?_))
    filter_upwards [veteran_status (W:=W) h hy t hp, wage_live (W:=W) h hy t] with z hv hu
    change Shell _ _ _ _ _ (enroll S t (Stationary.extend (soldier F W t ρ z))); rw [hu]; exact hv
  have HN : E ∘ D =ᶠ[𝓝 0] (fun z => Real.log ((K+Gm) z).det) := by
    filter_upwards [heP] with z ⟨hb,ha,heX,hS⟩
    change Real.log (medals S t p R μ C (V z) (U z)).det=_
    rw [abides S t p R μ C (V z) (U z) ha heX hS,det_mul,det_mul,det_transpose,shear_det C (U z) ha,one_mul,mul_one]
    change Real.log (medals S t p R μ 1 (V z) (X z)).det=_
    rw [hb.contact,wear_smear S t 1 (V z) (X z) hb.wist]; rfl
  have HQ : P ∘ D =ᶠ[𝓝 0] (fun z => Real.log (K z).det) := by
    filter_upwards [heP] with z ⟨hb,ha,heX,_⟩
    change Real.log (legion S t p R μ C (V z) (U z)).det=_
    rw [fields S t p R μ C (V z) (U z) ha heX hb.wist,det_mul,det_mul,det_transpose, shear_det C (U z) ha, one_mul,mul_one]; rfl
  have hGx (u : Link G c) : directionM Gm 0 u=smear S t 1 1 (J u) := by
    ext i j
    let Q z := lapel S t 1 (X z) i j
    have heQ := lapel_manual hy t X hX hX' i j
    unfold directionM Gm smear; simp only [Matrix.of_apply,dotProduct]
    rw [fderiv_fun_sum, _root_.sum_apply]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have hiB := ContinuousLinearMap.proj (φ:=fun _ : Lines G c 1 => ℝ) k |>.hasFDerivAt (𝕜:=ℝ) (x:=B 0)
      have hu : fderiv ℝ (fun z => B z k) 0 u=J u k := by
        rw [← hk']; exact congr($( (hiB.comp 0 (hB.differentiableAt (by simp)).hasFDerivAt).fderiv ) u)
      rw [fderiv_fun_mul ((contDiffAt_pi.mp hB k).differentiableAt (by simp)) ((contDiffAt_pi.mp heQ k).differentiableAt (by simp)), _root_.add_apply]; simp [hB',hu,hX' ]; ring
    intro k _; exact ((contDiffAt_pi.mp hB k).mul (contDiffAt_pi.mp heQ k)).differentiableAt (by simp)
  have heT z : ((K z)⁻¹ * Gm z).trace=dotProduct (B z) (Rm z) := (earn_ad S t 1 (V z) (X z) p R μ (B z)).symm
  rw [(show iteratedFDeriv ℝ 2 (E∘pace F ρ W t) 0=_ from (HN.iteratedFDeriv ℝ 2).eq_of_nhds),
    (show iteratedFDeriv ℝ 2 (P∘pace F ρ W t) 0=_ from (HQ.iteratedFDeriv ℝ 2).eq_of_nhds),after_contact hK hGm (hK'.symm ▸ hi.ne_zero) hGm']
  simp_rw [heT]
  rw [dot_quadr (P:=B) (Q:=Rm) hB hY hB' e,hk',hk',hRm,hGx,hGx,hK']
end YM.Stationary
end
