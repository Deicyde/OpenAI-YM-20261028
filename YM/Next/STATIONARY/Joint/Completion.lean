import YM.Bid.Fetch
import YM.Next.STATIONARY.Joint.Regulator
import YM.Work.B02.Slab

set_option autoImplicit false
/-!
# Legitimate completed Hessian of joint stationary action. Scalar forms
in ROOTED variables and transport under shear. Recall `liftedUp` is rooted.
`medals` full accepts congruence with `Shell` only under shear, while `legion`
drops the contact term and accepts it already off shell.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side}

section chain
open Module
variable {X Y T : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup T] [NormedSpace ℝ T] {F : Y → T} {H : X → Y} {x : X}

lemma pay_second (h : ContDiffAt ℝ ω F (H x)) (p : ContDiffAt ℝ ω H x) (u v) :
    iteratedFDeriv ℝ 2 (F ∘ H) x ![u,v]=fderiv ℝ F (H x) (iteratedFDeriv ℝ 2 H x ![u,v])+iteratedFDeriv ℝ 2 F (H x) ![fderiv ℝ H x u,fderiv ℝ H x v] := by
  simp_rw [iteratedFDeriv_two_apply, cons_val_zero, cons_val_one]
  let g := fderiv ℝ F ∘ H
  let V := fderiv ℝ H
  have hp : fderiv ℝ (F ∘ H)=ᶠ[𝓝 x] fun y => (g y).comp (V y) := by
    filter_upwards [p.continuousAt.tendsto.eventually (h.eventually (by simp)),p.eventually (by simp)] with y he hh
    exact fderiv_comp y (he.differentiableAt (by simp)) (hh.differentiableAt (by simp))
  have hv := (h.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
  rw [hp.fderiv_eq, fderiv_clm_comp (c:=g) (d:=V) (hv.comp x (p.differentiableAt (by simp))) ((p.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)),show fderiv ℝ g x=_ from fderiv_comp x hv (p.differentiableAt (by simp))]; rfl

lemma damage_rate {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (B : Basis m ℝ X) (C : Basis n ℝ Y) (F : Y→ℝ) (L : X →L[ℝ] Y) [CompleteSpace X] (h : ContDiffAt ℝ ω F 0) :
    damage B (F ∘ L) 0=(billsM B C L)ᵀ*damage C F 0*billsM B C L := damage_eq B (fun x y => by
    rw [both_cost,bill_at,bill_at,detracts,detracts,wired L ?_,map_zero]; swap; · rw [map_zero]; exact h.analyticAt
    rw [show L ∘ (![x,y]:Fin 2 → X)=![L x,L y] by funext i; fin_cases i <;> rfl])
end chain

section le

def burn (p : Clip) (R : PathData G) (U : Config G n) (x : Link G n) := mainTerm p R (input _ _ x*U)
def flare (p : Clip) (R : PathData G) (U : Config G n) := damage (pocket _) (burn p R U) 0
variable (S : StepData c f) (t : S.Choices)

def inure (V Z : Config G c) (x : Link G c) := tickets S V (input _ _ x*Z)
def worn (K : Robe G c f) (U : Joint G c f) (x : Vault G c f) :=
    content (ribbon S t (atire K U x)*(ribbon S t (dress K U))⁻¹)
@[simp] lemma worn_zero (K : Robe G c f) (U : Joint G c f) : worn S t K U 0=0 := by simp [worn]

def quota (K : Robe G c f) (U : Joint G c f) := billsM (helmets _ _ _) (pocket _) (fderiv ℝ (worn S t K U) 0)
def damageC (K : Robe G c f) (V : Config G c) (U : Joint G c f) := damage (pocket _)
    (inure S V (ribbon S t (dress K U))) 0

def burnJoint (p : Clip) (R : PathData G) (K : Robe G c f) (V : Config G c) (U : Joint G c f) (x : Vault G c f) := muster S t p R V (atire K U x)

def militia (μ : ℝ) (K : Robe G c f) (U : Joint G c f) := (cannonade S t μ K U)ᵀ*cannonade S t μ K U
def medals (p : Clip) (R : PathData G) (μ : ℝ) (K : Robe G c f) (V : Config G c) (U : Joint G c f) :=
    damage (helmets _ _ _) (burnJoint S t p R K V U) 0 + militia S t μ K U
def legion (p : Clip) (R : PathData G) (μ : ℝ) (K : Robe G c f) (V : Config G c) (U : Joint G c f) :=
    (rearM G c f)ᵀ * flare p R U.1 * rearM _ _ _ +
    (quota S t K U)ᵀ * damageC S t K V U * quota S t K U + militia S t μ K U

def contact (K : Robe G c f) (V : Config G c) (U : Joint G c f) := damage (helmets _ _ _)
    (fderiv ℝ (inure S V (ribbon S t (dress K U))) 0 ∘ worn S t K U) 0

structure Teller (p : Clip) (R : PathData G) (K : Robe G c f) (U : Joint G c f) : Prop where
    known : ContDiffAt ℝ ω (burn p R U.1) 0
    thorn : Army (fun z => ribbon S t (atire K U z)) 0

lemma teller_fee (V Z : Config G c) : ContDiffAt ℝ ω (inure S V Z) 0 := by
  unfold inure tickets; refine ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun i _ => matrix_price_jet ?_)
  have h : Army (input G c) 0 := Army.powL contDiffAt_id
  exact contDiffAt_const.mul ((h.mul (Army.park Z _)).inv i)

variable (p : Clip) (R : PathData G) (μ : ℝ) (K : Robe G c f) (V : Config G c) (U : Joint G c f)
lemma cannon_law : burnJoint S t p R 1 V U=canon S t p R V U := by funext x; simp [burnJoint,atire,canon]
lemma abides (h : Apparel K U) (hv : Explosives S t 1 (dress K U)) (hp : Shell S t p R V (dress K U)) :
    medals S t p R μ K V U=(shear K U)ᵀ*medals S t p R μ 1 V (dress K U)*shear K U := by
  have H : burnJoint S t p R K V U=ᶠ[𝓝 0] burnJoint S t p R 1 V (dress K U) ∘ tailor K U := by
    filter_upwards [tailor_suit K U h] with x hx; rw [cannon_law]; change muster S t p R V _=muster S t p R V _; exact congr_arg (muster S t p R V) hx.symm
  rw [medals, damage_congr _ H,medals,Matrix.mul_add,Matrix.add_mul, cannon_law,damage_comp _ (helmets G c f) _ (tailor_diff K U h) _]
  · rw [tailor_zero]; congr 1
    rw [militia, militia, arsenal S t μ K U h hv, transpose_mul]; simp only [Matrix.mul_assoc]
  · rw [tailor_zero]; exact hp.1
  rw [tailor_zero]; exact hp.2

lemma quota_shear (h : Apparel K U)
    (hp : ContDiffAt ℝ ω (worn S t 1 (dress K U)) 0) : quota S t K U=quota S t 1 (dress K U)*shear K U := by
  have hh : worn S t K U =ᶠ[𝓝 0] worn S t 1 (dress K U) ∘ tailor K U := by
    filter_upwards [tailor_suit K U h] with x hx
    simp only [Function.comp_apply,worn,show atire 1 (dress K U) (tailor K U x)=atire K U x from (dress_one ..).trans hx,dress_one]
  rw [quota,hh.fderiv_eq,fderiv_comp 0 (by rw [tailor_zero]; exact hp.differentiableAt (by simp)) ((tailor_diff K U h).differentiableAt (by simp)),tailor_zero]
  exact bill_multiply _ (helmets G c f) _ _ _
lemma fields (h : Apparel K U) (hh : Explosives S t 1 (dress K U)) (he : ContDiffAt ℝ ω (worn S t 1 (dress K U)) 0) :
    legion S t p R μ K V U=(shear K U)ᵀ*legion S t p R μ 1 V (dress K U)*shear K U := by
  have hx : (shear K U)ᵀ*(rearM G c f)ᵀ=(rearM G c f)ᵀ := by rw [← transpose_mul,shear_fine K U h]
  rw [legion,legion, Matrix.mul_add,Matrix.add_mul, Matrix.mul_add, Matrix.add_mul,quota_shear S t K U h he, damageC, damageC, dress_one]
  congr 1
  · congr 1
    · simp only [Matrix.mul_assoc,shear_fine K U h]
      rw [← Matrix.mul_assoc (shear K U)ᵀ,hx]; rfl
    rw [transpose_mul]; simp only [Matrix.mul_assoc]
  rw [militia,militia,arsenal S t μ K U h hh, transpose_mul]; simp only [Matrix.mul_assoc]

variable {S t p R V K U}
lemma Teller.wist (h : Teller S t p R K U) : ContDiffAt ℝ ω (worn S t K U) 0 := (h.thorn.mul (Army.park _ _)).logL (by simp)
lemma Teller.shown (h : Teller S t p R K U) : ∀ᶠ x in 𝓝 0, input _ _ (worn S t K U x)*ribbon S t (dress K U)=ribbon S t (atire K U x) := by
  let F := fun x => ribbon S t (atire K U x)*(ribbon S t (dress K U))⁻¹
  have he : F 0=1 := by simp [F]
  have hp : Army F 0 := h.thorn.mul (Army.park _ _)
  filter_upwards [(show Tendsto F _ (𝓝 1) from he ▸ hp.cont.tendsto).eventually content_encodes] with x hx
  rw [show worn S t K U x=_ from rfl]
  change input G c (content (F x))*_= _; rw [hx]; simp [F]
lemma Teller.contact (h : Teller S t p R K U) :
    medals S t p R μ K V U = legion S t p R μ K V U + Stationary.contact S t K V U := by
  let F := inure S V (ribbon S t (dress K U))
  let Q := worn S t K U
  let L := ContinuousLinearMap.fst ℝ (Link G f) (BaseSites G c)
  have hh : burnJoint S t p R K V U=ᶠ[𝓝 0] (burn p R U.1 ∘ L)+(F ∘ Q) := by
    filter_upwards [h.shown] with x hx
    change mainTerm p R (input G f x.1*U.1) + _= _ + tickets _ _ (input G c _ * _)
    rw [hx]; rfl
  have hF := teller_fee S V (ribbon S t (dress K U))
  have hv : ContDiffAt ℝ ω F (Q 0) := by rw [show Q 0=0 from worn_zero ..]; exact hF
  have hp := h.wist
  have hi : ContDiffAt ℝ ω (burn p R U.1 ∘ L) 0 := by
    apply ContDiffAt.comp _ _ L.contDiff.contDiffAt
    rw [map_zero]; exact h.known
  apply damage_eq (helmets G c f); intro x y
  simp only [medals,legion,damage_congr _ hh,flare,quota,damageC,Stationary.contact, add_mulVec,dotProduct_add,detracts]
  rw [both_cost,rear_cost,rear_cost,both_cost, bill_at,bill_at,detracts]
  have ht := pay_second hv hp x y
  have hM := detracts (pocket _) (burn p R U.1) 0 x.1 y.1; rw [cash_pocket,cash_pocket] at hM
  rw [hM,iteratedFDeriv_add_apply (hi.of_le le_top) ((hv.comp (f:=Q) _ hp).of_le le_top),_root_.add_apply, ht,wired L (by rw [map_zero]; exact h.known.analyticAt),map_zero,show Q 0=0 from worn_zero .., show L ∘ (![x,y]:Fin 2 → Vault G c f)=![x.1,y.1] by ext1 i; fin_cases i <;> rfl]
  let T := fderiv ℝ F 0
  have heL := pay_second (F:=T) T.contDiff.contDiffAt hp x y
  have he : iteratedFDeriv ℝ 2 (T ∘ Q) 0 ![x,y]= T (iteratedFDeriv ℝ 2 Q 0 ![x,y]) := by
    rw [heL]; simp only [Q,iteratedFDeriv_two_apply, show fderiv ℝ T=fun _ => T from funext (fun _ => T.fderiv)]
    rw [show fderiv ℝ (fun _ : Link G c => T) (worn S t K U 0)=0 from (hasFDerivAt_const ..).fderiv]; simp
  unfold T F Q at he
  rw [he]; dsimp only [F,Q]; abel
end le
end YM.Stationary
end

/-! # Real-analytic fixed-period costs. Entrywise (the matrix norm for the finite
period can have terrible dimension dependence; no uniform claim). Includes
branched status for planted tag and stationary reparameterizations at x=0. -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix Finset Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f}

section matrix
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {ι κ n : Type} {x : X}
/-- no norm induced from accidental Matrix space instance -/
abbrev Memo (M : X → Matrix ι κ ℝ) (x : X) := ∀ i j, ContDiffAt ℝ ω (fun x => M x i j) x
namespace Memo
variable {U V : X → Matrix ι κ ℝ}
lemma cross {V : X → Matrix κ n ℝ} (h : Memo U x) (v : Memo V x) [Fintype κ] : Memo (fun z => U z*V z) x := fun i j =>
    ContDiffAt.sum fun k _ => (h i k).mul (v k j)
lemma spot (h : Memo U x) : Memo (fun z => (U z)ᵀ) x := fun i j => h j i
lemma twice (h : Memo U x) (he : Memo V x) : Memo (U+V) x := fun i j => (h i j).add (he i j)
lemma raw (U : Matrix ι κ ℝ) (x : X) : Memo (fun _ => U) x := fun _ _ => contDiffAt_const
lemma debit (c : ℝ) (h : Memo U x) : Memo (c • U) x := fun i j => (h i j).const_smul c
variable [Fintype ι] [DecidableEq ι] {P : X → Funds ι}
lemma tick (h : Memo P x) (i : ℕ) : Memo (fun z => P z ^ i) x := by
  induction i with
  | zero => simp only [pow_zero]; exact raw 1 x
  | succ i IH => simp_rw [pow_succ]; exact IH.cross h
lemma det_val (h : Memo P x) : ContDiffAt ℝ ω (fun z => (P z).det) x := by
  simp only [Matrix.det_apply]
  refine ContDiffAt.sum fun i _ => ?_
  simp only [Units.smul_def,zsmul_eq_mul]
  exact ContDiffAt.mul contDiffAt_const (contDiffAt_prod fun j _ => h _ _)
lemma flip (h : Memo P x) (p : (P x).det≠0) : Memo (fun i => (P i)⁻¹) x := by
  intro i j
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply]
  refine ((h.det_val.inv p).smul ?_)
  simp_rw [Matrix.adjugate_apply]
  refine Memo.det_val ?_
  intro k l
  simp only [Matrix.updateRow_apply]
  split
  · exact contDiffAt_const
  exact h _ _
end Memo
end matrix

section calculus
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

lemma blaze_fire (V : X → Config G n) (p : Clip) (R : PathData G) {σ A Λ : ℝ} (hv : R.Bounds p σ A Λ) (h : Army V 0) (he : V 0=1) :
    ContDiffAt ℝ ω (fun z : X × Link G n => burn p R (V z.1) z.2) 0 := by
  apply (Work.F02.answer _ _ _ _ _ _ hv).crown (A:=fun z : X × Link G n => input G n z.2 * V z.1) 0 n
  · simp [he]
  exact (Army.powL (v:=fun z : X × Link G n => z.2) contDiffAt_snd).mul (h.comp (g:=V) (w:=Prod.fst) contDiffAt_fst)
lemma awake {p : Clip} {R : PathData G} (t : S.Choices) {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ) {U : X → Joint G c f}
    (hu : Thaw U 0) (he : (U 0).1=1) (hb : S.patch.Branches S.kernel G) {K : Robe G c f} (hk : Customs K) :
    ∀ᶠ z in 𝓝 0,Teller S t p R K (U z) := by
  have hw : Thaw (fun y : X × Vault G c f => atire K (U y.1) y.2) 0 :=
    sport_thaw hk ((Thaw.through contDiffAt_snd).mul (Thaw.comp (w:=Prod.fst) (g:=U) (x:=0) hu contDiffAt_fst)) (by simp [he])
  have H : ∀ᶠ z in 𝓝 0, Army (fun i => ribbon S t (atire K (U z) i)) 0 := by
    apply eventually_all.mpr
    intro i
    have hp : Tendsto (fun z : X => (z,(0:Vault G c f))) (𝓝 0) (𝓝 0) := tendsto_id.prodMk_nhds tendsto_const_nhds
    filter_upwards [hp.eventually ((hw.ribbons hb t (he:=by change (atire K (U 0) 0).1=1; rw [atire_zero]; exact he) i).eventually (by simp))] with z hz
    exact Work.F05.hold_jet (V:=fun z x => G.mat (ribbon S t (atire K (U z) x) i)) hz
  have hd : Tendsto (fun z : X => (z,(0:Link G f))) (𝓝 0) (𝓝 0) := tendsto_id.prodMk_nhds tendsto_const_nhds
  filter_upwards [H,hd.eventually ((blaze_fire (fun v => (U v).1) _ _ hp hu.1 he).eventually (by simp))] with z hz hv
  exact ⟨Work.F05.hold_jet (V:=fun z => burn p R (U z).1) hv,hz⟩

section fund
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] {Y P : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ P]
omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ P] in
lemma memo_bill (B : Basis ι ℝ P) (C : Basis κ ℝ Y) {F : X → P →L[ℝ] Y} (h : ContDiffAt ℝ ω F 0) : Memo (fun z => billsM B C (F z)) 0 := by
  intro i j
  simp only [bill_def]
  exact (C.coord i).toContinuousLinearMap.contDiff.contDiffAt.comp 0 (h.clm_apply (g:=fun _ => B j) contDiffAt_const)
omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ P] in
lemma memo_rate (B : Basis ι ℝ P) (C : Basis κ ℝ Y) {F : X → P → Y} (h : ContDiffAt ℝ ω (uncurry F) 0) : Memo (fun z => billsM B C (fderiv ℝ (F z) 0)) 0 :=
    memo_bill B C ((Work.F05.curve_partial h).comp (f:=fun x : X => (x,0)) 0 (contDiffAt_id.prodMk contDiffAt_const))
omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
lemma memo_damage (B : Basis ι ℝ Y) {F : X → Y → ℝ} (h : ContDiffAt ℝ ω (uncurry F) 0) : Memo (fun z => damage B (F z) 0) 0 := by
  have hp := Work.F05.curve_partial (F:=fun z => fderiv ℝ (F z)) (Work.F05.curve_partial h)
  intro i j; unfold damage; simp only [LinearMap.toMatrix₂_apply,Work.F05.bend]
  exact (((hp.comp (f:=fun x : X => (x,0)) 0 (contDiffAt_id.prodMk contDiffAt_const)).clm_apply (g:=fun _ => B i) contDiffAt_const).clm_apply (g:=fun _ => B j) contDiffAt_const)
end fund

omit [FiniteDimensional ℝ X] in
lemma memo_flash {U : X→Config G n} {μ : ℝ} (h : 0<μ) (p : Army U 0) :
    Memo (fun z => mail (U z)) 0 ∧ Memo (fun z => cannon μ (U z)) 0 ∧ Memo (fun z => grenade μ (U z)) 0 := by
  have he : Memo (fun z => mail (U z)) 0 := by
    rintro ⟨x,i,k⟩ j; obtain ⟨i,rfl⟩ := axisEquiv.surjective i
    let A : BaseSites G n := (pocket _) j
    let K := fun v => edgeColor (cant (U v) A)
    let T := fun z => G.adjoint (U z (x,i)) (gaugeColor A (x+step i))
    have hi : ContDiffAt ℝ ω T 0 := by
      let F := fun z => G.conjugate (U z (x,i)) (G.colorMat (gaugeColor A (x+step i)))
      exact G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp (f:=F) _ (((p _).mul contDiffAt_const).mul
        ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (p _)))
    have hv (z : X) : K z (x,i)=gaugeColor A x - T z := cant_at ..
    simp only [mail,bill_def,cash_pocket]
    change ContDiffAt ℝ ω (fun z => K z (x,i) k) 0
    simp_rw [hv,PiLp.sub_apply]; refine ContDiffAt.sub contDiffAt_const ?_
    let L : G.Color →ₗ[ℝ] ℝ := LinearMap.comp (LinearMap.proj k) (WithLp.linearEquiv 2 ℝ _).toLinearMap
    exact L.toContinuousLinearMap.contDiff.contDiffAt.comp 0 hi
  refine ⟨he,?_⟩
  have ht : Memo (fun z => tonic (U z)) 0 := he.spot.cross he
  have hc : Memo (fun z => ammo μ (U z)) 0 := ht.twice (Memo.raw _ _)
  have hd : Memo (fun z => pebble μ (U z)) 0 := Memo.debit _ (Memo.flip hc (ammo_safe _ h).det_pos.ne')
  have hc : Memo (fun z => cannon μ (U z)) 0 := Memo.debit _ (Memo.tick hd _)
  exact ⟨hc,ht.twice hc⟩

omit [FiniteDimensional ℝ X] in
lemma bent (V W : X → Config G c) (hv : Army V 0) (hw : Army W 0) : ContDiffAt ℝ ω (fun z : X × Link G c => inure S (V z.1) (W z.1) z.2) 0 := by
  let S' (z : X × Link G c) := input G c z.2*W z.1
  have h' : Army S' 0 := (Army.powL contDiffAt_snd).mul (hw.comp (g:=W) (w:=Prod.fst) contDiffAt_fst)
  unfold inure tickets; refine ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun i _ => matrix_price_jet ?_)
  exact (Army.comp (g:=V) (w:=Prod.fst) hv (x:=0) contDiffAt_fst i).mul (h'.inv i)

lemma ammo_pay (U : X → Joint G c f) (V : X → Config G c) (hu : Thaw U 0) (he : (U 0).1=1) (hv : Army V 0)
    (K : Robe G c f) (H : Customs K) (w : S.patch.Branches S.kernel G) (t : S.Choices) {p : Clip} {R : PathData G} {σ A Λ : ℝ}
    (hp : R.Bounds p σ A Λ) {μ : ℝ} (hx : 0<μ) :
    Memo (fun v => militia S t μ K (U v)) 0 ∧ Memo (fun v => medals S t p R μ K (V v) (U v)) 0 ∧ Memo (fun v => legion S t p R μ K (V v) (U v)) 0 := by
  obtain ⟨u,u',_⟩ := memo_flash (μ:=μ) hx hu.1
  let F := fun z : X × Vault G c f => atire K (U z.1) z.2
  let P (z : X × Vault G c f) := dress K (U z.1)
  have hw : Thaw F 0 :=
    sport_thaw H ((Thaw.through contDiffAt_snd).mul (Thaw.comp (w:=Prod.fst) (g:=U) (x:=0) hu contDiffAt_fst)) (by simp [he])
  have hF : (F 0).1=1 := by change (atire K (U 0) 0).1=1; rw [atire_zero]; exact he
  have hQ : Thaw P 0 := sport_thaw H (Thaw.comp (w:=Prod.fst) (g:=U) hu contDiffAt_fst) he
  have hR := ((hQ.shields w t (he:=he)).inv.mul (hw.shields w t hF)).logG (show (shield S t (P 0))⁻¹ * shield S t (F 0)=1 by rw [show F 0=P 0 from atire_zero K (U 0),inv_mul_cancel])
  have hX : Memo (fun v => indexX S t K (U v)) 0 := memo_rate _ _ (F:=fun z => rocket S t K (U z)) hR.neg
  have hM : Memo (fun v => cannonade S t μ K (U v)) 0 := (u.spot.cross (Memo.raw _ _)).twice (u'.cross hX)
  have hm : Memo (fun v => militia S t μ K (U v)) 0 := hM.spot.cross hM
  have hl := Memo.twice (memo_damage (helmets _ _ _) (F:=fun x => burnJoint S t p R K (V x) (U x))
    (hw.earn w t (V:=fun z => V z.1) hF (Army.comp (w:=Prod.fst) (g:=V) hv contDiffAt_fst) hp)) hm
  have hZ := ((hw.ribbons w t hF).mul (hQ.ribbons w t he).inv).logL (show ribbon S t (F 0)*(ribbon S t (P 0))⁻¹=1 by rw [show F 0=P 0 from atire_zero K (U 0),mul_inv_cancel])
  let Q := fun v => ribbon S t (dress K (U v))
  have hQ : Army Q 0 := (sport_thaw H hu he).ribbons w t he
  have hd : Memo (fun v => damageC S t K (V v) (U v)) 0 := memo_damage _ (F:=fun v => inure S (V v) (Q v)) (bent V Q hv hQ)
  have ht : Memo (fun v => quota S t K (U v)) 0 := memo_rate _ _ (F:=fun v => worn S t K (U v)) hZ
  have hw' : Memo (fun z => flare p R (U z).1) 0 := memo_damage _ (F:=fun z => burn p R (U z).1) (blaze_fire (fun z => (U z).1) p R hp hu.1 he)
  have hy := (Memo.raw (rearM G c f) (0:X))
  exact ⟨hm,hl,((hy.spot.cross hw' |>.cross hy).twice (ht.spot.cross hd |>.cross ht)).twice hm⟩
end calculus
end YM.Stationary
end

/-! # Root tree tangent determinant. Counting bases. At tree field: each
trunk link is one and its child vertex contributes ±1 on the link slot at
same height. Compute triangular permutation also for empty Free / lie slots.
-/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix Finset Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

variable (F : Forest S.ratio)

def paintLink (e : Edge (Site f)) (i : G.ColorIndex) : Lines G f 1 := (e.1,coord e.2,i)
lemma edge_pair {p q : Edge (Site f)} {i j : G.ColorIndex} : paintLink p i=paintLink q j ↔ p=q ∧ i=j := by cases p; cases q; simp [paintLink,coord_iff,and_assoc]

-- rooted guard column maps to row(s) in tree or coarse frame
abbrev Rangers (G : Gauge) := (Lines G f 0) ⊕ (Key F G)
instance : DecidableEq (Rangers F G) := fun x y => instDecidableEqSum x y

def draftRoster (i : Lines G f 0) : Bodies G c f :=
    if h : leaf S.ratio i.1 then Sum.inl (paintLink ((Work.F05.pinEquiv F) ⟨i.1,h⟩).val i.2.2)
    else Sum.inr (S.ratio.parent i.1,vac,i.2.2)
def musterRoster : Rangers F G → Bodies G c f := Sum.elim (draftRoster F) (fun i => .inl (paintLink i.1.val i.2))
private lemma roster_match (i : Lines G f 0) (j : Key F G) : draftRoster F i≠.inl (paintLink j.1.val j.2) := by
  rw [draftRoster]; split
  next h =>
    intro he; exact j.1.property (((edge_pair.mp (Sum.inl.inj he)).1) ▸ ((Work.F05.pinEquiv F) ⟨i.1,h⟩).property)
  simp

def march (G : Gauge) : Rangers F G ≃ Bodies G c f := Equiv.ofBijective (musterRoster F) (by
  constructor
  · rintro (i|i) (j|j) h
    · simp only [musterRoster,Sum.elim_inl,draftRoster] at h
      rcases i with ⟨i,t,a⟩; rcases j with ⟨j,r,b⟩; rw [vac_only t, vac_only r]
      split at h <;> (rename_i ht; split at h <;> rename_i hr)
      · obtain ⟨hi,hj⟩ := edge_pair.mp (Sum.inl.inj h)
        have he : i=j := congrArg Subtype.val ((Work.F05.pinEquiv F).injective (Subtype.ext hi)); rw [he,show a=b from hj]
      · cases h
      · cases h
      obtain ⟨hx,hj⟩ := (Prod.mk.inj (Sum.inr.inj h)); have hb : a=b := congr_arg Prod.snd hj
      have hi : i=j := (Classical.not_not.mp ht).trans ((congr_arg _ hx).trans (Classical.not_not.mp hr).symm); rw [hi,hb]
    · exact False.elim (roster_match F i j h)
    · exact False.elim (roster_match F j i h.symm)
    exact congr_arg _ (Prod.ext (Subtype.ext ((edge_pair.mp (Sum.inl.inj h)).1)) (edge_pair.mp (Sum.inl.inj h)).2)
  rintro (⟨x,i,j⟩|⟨x,i,j⟩)
  · obtain ⟨i,rfl⟩ := axisEquiv.surjective i
    by_cases he : (x,i) ∈ F.trunks
    · obtain ⟨⟨y,hy⟩,hh⟩ := (Work.F05.pinEquiv F).surjective ⟨(x,i),he⟩
      exact ⟨.inl (y,vac,j),by simp only [musterRoster,Sum.elim_inl,draftRoster,dif_pos hy,hh]; rfl⟩
    exact ⟨.inr (⟨(x,i),he⟩,j),rfl⟩
  exact ⟨.inl (S.ratio.embed x,vac,j), by rw [vac_only i]; simp [musterRoster,draftRoster, Tree.leaf,Ratio.embed_parent]⟩)
lemma march_leaf (x : Site f) (h : leaf S.ratio x) (k : G.ColorIndex) : march F G (.inl (x,vac,k))=.inl (paintLink ((F.up x).used x) k) := by rw [show march F G _=draftRoster F _ from rfl,draftRoster,dif_pos (by exact h)]; rfl
lemma march_root (x : Site f) (h : ¬leaf S.ratio x) (k : G.ColorIndex) : march F G (.inl (x,vac,k))=.inr (S.ratio.parent x,vac,k) := by rw [show march F G _=draftRoster F _ from rfl,draftRoster,dif_neg (by exact h)]

def pad : AxisChart G F →L[ℝ] Link G f := edgeColor.symm.toContinuousLinearMap ∘L ContinuousLinearMap.pi fun e : Edge (Site f) =>
    if h : e∈ F.trunks then 0 else ContinuousLinearMap.proj (⟨e,h⟩:F.Free)
lemma pad_free (x : AxisChart G F) (i : F.Free) : edgeColor (pad F x) i=x i := by simp [pad,i.property]
lemma pad_trunk (x : AxisChart G F) (i : ↥F.trunks) : edgeColor (pad F x) i=0 := by simp [pad, i.property]

def rangers (G : Gauge) := billsM (Work.F05.countingBasis F G) (helmets G c f) ((pad F).prod 0)

-- columns concatenate transport plus slice
section columns
variable {ι κ l m : Type}
def paste_sides {R : Type} (A : Matrix l ι R) (B : Matrix l κ R) : Matrix l (ι⊕κ) R := of fun i j => Sum.elim (A i) (B i) j

/-- strictly lower block triangular except diagonal in each block. -/
lemma grouped_det [Fintype ι] [DecidableEq ι] (M : Funds ι) (H : ι → ℕ)
    (h : ∀ i j, M i j ≠ 0 → i=j ∨ H j < H i) : M.det = ∏ i,M i i := by
  rw [Matrix.det_apply,sum_eq_single 1]
  · simp
  · intro b _ hb; suffices he : (∏ i, M (b i) i)=0 by rw [he]; simp
    by_contra hn
    have ht (i) := h (b i) i (fun he => hn (prod_eq_zero (mem_univ i) he))
    obtain ⟨i,hi⟩ : ∃ i, b i ≠ i := by by_contra! hk; exact hb (Equiv.ext hk)
    have hs : ∑ j,H j < ∑ j,H (b j) := sum_lt_sum (fun i _ => (ht i).elim (fun he => by rw [he]) (fun he => he.le)) ⟨i,mem_univ _,(ht i).resolve_left hi⟩
    rw [Equiv.sum_comp b] at hs; exact hs.false
  simp
end columns

def pawns (V : Config G c) (x : AxisChart G F) : Funds (Rangers F G) :=
    (paste_sides (stood S (abode S F V x)) (rangers F G)).submatrix (march F G) id

lemma rangers_fee (p : AxisChart G F) (i) : cash (Work.F05.countingBasis F G) p i=p i.1 i.2 := by simp [cash,Work.F05.countingBasis]
lemma helmets_link (x : Vault G c f) (i j) : (cash (helmets G c f) x) (.inl (paintLink i j))=edgeColor x.1 i j := by unfold helmets; rw [cash_prod_left,cash_pocket]; rfl
lemma helmets_site (x : Vault G c f) (i j) : (cash (helmets G c f) x) (.inr (i,vac,j))=gaugeColor x.2 i j := by unfold helmets; rw [cash_prod_right,cash_pocket]; rfl
lemma pin_color (x : BaseSites G f) (i j) : gaugeColor x i j=x (i,vac,j) := rfl

lemma commandment (V : Config G c) (y : AxisChart G F) : (pawns F V y).det^2=1 := by
  let M := pawns F V y
  let U := abode S F V y
  let L := M.toBlocks₁₁
  have he (x : Site f) (k : G.ColorIndex) (h : ¬ leaf S.ratio x) (i : Lines G f 0) :
      L (x,vac,k) i= -(pocket (Lines G f 0) i (x,vac,k)) := by
    let p : BaseSites G f := pocket (Lines G f 0) i
    change stood S U (march F G (.inl (x,vac,k))) i = _
    rw [march_root F x h k,stood,bill_def,helmets_site,(soldier_mounted S U p).2]
    change (-G.adjoint 1 _ : G.Color) k = _
    rw [G.adjoint_one, ← (show x=S.ratio.embed (S.ratio.parent x) from Classical.not_not.mp h)]
    rfl
  have hp (x : Site f) (k : G.ColorIndex) (h : leaf S.ratio x) (i : Lines G f 0) :
      L (x,vac,k) i=(if (F.up x).neg then (-1:ℝ) else 1)* (pocket _ i (x,vac,k) - pocket _ i (x+(F.up x).vec,vac,k)) := by
    let p : BaseSites G f := pocket (Lines G f 0) i
    change stood S U (march F G (.inl (x,vac,k))) i = _
    rw [march_leaf F x h k,stood,bill_def,helmets_link,(soldier_mounted S U p).1,cant_at,
      show U.1 ((F.up x).used x)=1 from F.on_tree _ (⟨_, (F.trunk_mem_iff _).2 ⟨x,h,rfl⟩⟩),G.adjoint_one]
    simp only [PiLp.sub_apply, pin_color]; cases hv : (F.up x).neg <;> simp [p,Step.used,Step.vec,hv,← sub_eq_add_neg]
  have hT : L.det^2=1 := by
    let H := fun i : Lines G f 0 => F.height i.1
    rw [grouped_det L H]; swap
    · rintro ⟨x,b,k⟩ i hi; rw [vac_only b] at hi ⊢
      by_cases h : leaf S.ratio x
      · rw [hp x k h,Pi.basisFun_apply] at hi; simp only [Pi.single_apply] at hi
        by_cases hh : (x,vac,k)=i
        · exact Or.inl hh
        right; rw [if_neg hh] at hi
        by_cases h' : (x+(F.up x).vec,vac,k)=i
        · rw [← h']; exact F.rise x h
        simp [h'] at hi
      left; by_contra hv; rw [he x k h] at hi; simp [hv] at hi
    rw [← prod_pow]; convert Finset.prod_const_one (s:=univ (α:=Lines G f 0)) using 1
    refine Finset.prod_congr rfl ?_; rintro ⟨x,b,k⟩ _
    rw [vac_only b]; by_cases hh : leaf S.ratio x
    · have hn : (x+(F.up x).vec : Site f)≠x := fun hi => by have he:=F.rise x hh; rw [hi] at he; exact he.false
      have hne : (x+(F.up x).vec,vac,k) ≠ (x,vac,k) := fun h => hn (congr_arg Prod.fst h)
      rw [hp x k hh]; rw [Pi.basisFun_apply,Pi.single_eq_same,Pi.single_eq_of_ne hne]
      cases (F.up x).neg <;> norm_num
    rw [he x k hh]; simp
  have h : M=fromBlocks L (0:Matrix (Lines G f 0) _ _) M.toBlocks₂₁ (1:Funds (Key F G)) := by
    ext (i|i) (j|j)
    · rfl
    · rcases i with ⟨x,b,k⟩; rw [vac_only b]
      change rangers F G (march F G (.inl (x,vac,k))) j=0
      by_cases hh : leaf S.ratio x
      · rw [march_leaf F x hh,rangers,bill_def,helmets_link]; change edgeColor (pad F _) _ k=_
        rw [show edgeColor (pad F _) _ (k)=(0:G.Color) k from congrArg (fun c : G.Color => c k) (pad_trunk F _ (⟨(F.up x).used x,(F.trunk_mem_iff _).2 ⟨x,hh,rfl⟩⟩))]; rfl
      rw [march_root F x hh,rangers,bill_def,helmets_site]; simp
    · rfl
    change rangers F G (.inl (paintLink i.1.val i.2)) j=(1:Funds (Key F G)) i j
    rw [rangers,bill_def,helmets_link]; change edgeColor (pad F _) i.1.val i.2=_
    rw [pad_free, ← rangers_fee F]; rw [cash_works,Basis.repr_self]; simp [Matrix.one_apply,Finsupp.single_apply,eq_comm]
  change M.det^2=1; rw [h,det_fromBlocks_zero₁₂,det_one,mul_one]; exact hT
end YM.Stationary
end

/-! # Factorization of the determinant. The gauge-fixing contact is
exactly cancelled in this normalization. Multiplies by actual Γ determinant (even without invertibility),
real μ. Slice determinant still left-Haar increment. -/
noncomputable section
namespace YM.Stationary
open Function Lattice RG Wilson Exterior Precision Bloch Laurent Filter Tree Matrix Finset Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

section factor
variable {ι κ j n : Type} [Fintype ι] [Fintype κ] [Fintype j] [Fintype n]

omit [Fintype j] [Fintype ι] [Fintype κ] in
lemma sideProd (X : Matrix j n ℝ) (A : Matrix n ι ℝ) (B : Matrix n κ ℝ) : X*paste_sides A B=paste_sides (X*A) (X*B) := by ext i (j|j) <;> rfl
omit [Fintype ι] [Fintype κ] in
lemma squarePad (U A : Matrix j ι ℝ) (V B : Matrix j κ ℝ) :
    (paste_sides U V)ᵀ*paste_sides A B=fromBlocks (Uᵀ*A) (Uᵀ*B) (Vᵀ*A) (Vᵀ*B) := by ext (i|i) (j|j) <;> rfl

omit [Fintype ι] [Fintype κ] in
lemma pit (H : Funds j) (G : Matrix j ι ℝ) (P : Matrix j κ ℝ) (h : Hᵀ=H) (u : H*G=0) :
    (paste_sides G P)ᵀ*H*paste_sides G P=fromBlocks 0 0 0 (Pᵀ*H*P) := by
  have e : Gᵀ*H=0 := by rw [← transpose_transpose (Gᵀ * H),transpose_mul,h,transpose_transpose,u,transpose_zero]
  rw [Matrix.mul_assoc, sideProd H,squarePad,u]; simp only [Matrix.mul_zero,← Matrix.mul_assoc, e,Matrix.zero_mul]

variable [DecidableEq ι] [DecidableEq κ] [DecidableEq j]
omit [DecidableEq j] in
lemma chargeRoot (H : Funds j) (G : Matrix j ι ℝ) (L : Matrix ι j ℝ) (P : Matrix j κ ℝ) (h : Hᵀ=H) (u : H*G=0)
    (A : Funds ι) (hw : L*G=A) :
    ((paste_sides G P)ᵀ*(H+Lᵀ*L)*paste_sides G P).det=A.det^2 * (Pᵀ*H*P).det := by
  let B := L*P
  let C := Pᵀ*H*P
  let V : Funds (ι⊕κ) := fromBlocks A B 0 1
  have hv : Vᵀ*fromBlocks 1 0 0 C*V = (paste_sides G P)ᵀ*(H+Lᵀ*L)*paste_sides G P := by
    rw [Matrix.mul_add, Matrix.add_mul, pit H G P h u]; rw [← Matrix.mul_assoc (paste_sides G P)ᵀ Lᵀ,← transpose_mul, Matrix.mul_assoc (L*paste_sides G P)ᵀ L, sideProd L, squarePad, hw]
    unfold V; rw [fromBlocks_transpose, fromBlocks_multiply,fromBlocks_multiply]
    ext (i|i) (j|j) <;> simp [B,C,add_comm]
  rw [← hv,det_mul,det_mul,det_transpose]
  simp only [V,det_fromBlocks_zero₂₁,det_one]; unfold C; ring

lemma medals_product (H : Funds j) (C : Matrix j ι ℝ) (e : ι ≃ j) (hu : (C.submatrix e id).det ^ 2 = 1) :
    (Cᵀ*H*C).det=H.det := by
  let B := C.submatrix e id
  let A := H.submatrix e e
  have he : Cᵀ*H*C=Bᵀ*A*B := by
    suffices hv : Bᵀ*A=(Cᵀ*H).submatrix id e by rw [hv]; ext i k; exact (Equiv.sum_comp e _).symm
    ext i k; exact Equiv.sum_comp e (fun x => Cᵀ i x*H x (e k))
  rw [he,det_mul,det_mul,det_transpose, show A.det=H.det from det_submatrix_equiv_self e H, mul_right_comm, ← sq, show B.det ^2 =1 from hu,one_mul]
end factor

-- Counting eigenvalue charge ON ROOTED SLICE. No absolute determinant here.
theorem root_determines (F : Forest S.ratio) {μ σ A Λ : ℝ} {p : Clip} {R : PathData G} (V : Config G c) (x : AxisChart G F)
    (t : S.Choices) (h : S.patch.Branches S.kernel G) (hu : R.Bounds p σ A Λ) :
    let W := abode S F V x
    let H := damage (helmets G c f) (canon S t p R V W) 0
    Shell S t p R V W → Explosives S t 1 W →
    (medals S t p R μ 1 V W).det = (grenade μ W.1).det^2 * ((rangers F G)ᵀ*H*rangers F G).det := by
  intro W H hW hp
  let L := cannonade S t μ 1 W
  let Gm := stood S W
  have he : medals S t p R μ 1 V W=H+Lᵀ*L := by rw [medals,cannon_law]; rfl
  rw [he]; exact (medals_product _ (paste_sides Gm (rangers F G)) (march F G) (commandment F V x)).symm.trans
    (chargeRoot H Gm L _ (damage_symm _ hW.1) (honors S W h hu t hW) _ (count_ammo S t μ h hp))
end YM.Stationary
end
