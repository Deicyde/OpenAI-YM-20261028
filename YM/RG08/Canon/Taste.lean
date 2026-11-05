import YM.RG08.Canon.Mound
/-! # Extract common field-independent coefficient in centered expansion.
Thermal loop includes tree Jacobian AND tree determinant. Mean changes with y.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {F : Forest S.ratio} {p : Clip} {R : PathData G} {σ K Λ : ℝ} {ρ : fieldDir G c 1 → AxisChart G F}
variable {η:ℝ} (v:Stationary.Link G c) {t:S.Choices} {D : ChartRatio G} {L : fieldDir G c 1 → (AxisChart G F)≃L[ℝ] AxisChart G F}
local notation "U" => AxisChart G F
local notation "X" => (U) × ℝ
local notation "Γ" => fieldDir G c 1
variable {V:ℕ→Config G f→ℝ} (h : Salvo t F R p ρ η L)
local notation "Θ" => lance v h
variable {Q : Pot G 2} {W : Air G} (hp : ∀ i,Caper Q W 2 i (V i)) (hr : Cask p R f Q W)
local notation "T" => morsel v h V
local notation "K_" => sublet v D h
local notation "P[" a "," b "," x "]" => fun t:ℝ=> PertExtension.Series.Radial.projection a b t (plates G F.Free x)
include hp hr
lemma mambo (x:X) : Fit 3 (fun t:ℝ=> (T) (t•x)) (fun t:ℝ=> starsP v h (t•x)) := by
  let u (t:ℝ):= (t•x).2^2*loop R (Θ (t•x))
  have hz:= stencil_price v h (loop R) hr.looped
  let f' (t:ℝ) := loop R (Θ (t•x)); have hx : f' 0=0 := by unfold f'; rw [zero_smul,(gleam_color v h).2,(cask_open p R hr).2]
  have hA: ContDiffAt ℝ ω f' 0:= (show ContDiffAt ℝ ω (loop R ∘ (Θ)) ((0:ℝ)•x) from by simpa using hz).comp (f:=fun t:ℝ=>t•x) _ (contDiffAt_id.smul contDiffAt_const)
  have he : Bill 3 u:= bill_mul (k:=2) (by
    simp only [Prod.smul_snd,smul_eq_mul,mul_pow]; exact bill_mul (ruler 2 2 le_rfl) (bill_const _)) (priced1 hA hx)
  refine ((manta v h hp hr x).lower (by decide : 3≤5)).join ?_; let I:=fun t:ℝ=>starsP v h (t•x)
  change Fit _ (I+u) I; unfold Fit; rw [add_sub_cancel_left]; exact he
lemma expulse : YM.PertExtension.Series.Radial.Stationary (T) ∧ ∃ δ>0,∀ u:X,δ*‖u‖^2≤ jet (T) 2 u := by
  obtain ⟨hw,δ,hd,H⟩:= calm (schools v h)
  have hc : ContDiffAt ℝ ∞ T 0:= (mundane v h hp hr).of_le le_top
  have ht j x (hj:j≤2) : jet (T) j x=jet (starsP v h) j x:= aspiredV (mambo v h hp hr x) (directions hc _) (directions ((schools v h).regular.of_le le_top) _) hj
  refine ⟨⟨hc,?_,fun u=>?_⟩,δ,hd,fun i=>?_⟩
  · exact (jet_zero T 0).symm.trans ((ht 0 0 (by decide)).trans ((jet_zero _ _).trans hw.2))
  · rw [ht 1 u (by decide)]; exact hw.3 _
  rw [ht 2 i le_rfl]; exact H _

omit hp hr in
private lemma spaniet (x:U) : Bill 0 (fun t:ℝ=> starsP v h (t•(x,(1:ℝ)))/t^2) := by
  let A:= jet (tested F t p R 0) 2 x+1^ (2:ℕ)
  have he:= (passive_two (schools v h) x 1).shorten (n:=1) (k:=2)
  have hA := Fit.join he (Fit.supply (eventually_pos.mono (p:=fun t:ℝ=> 0<t) (q:=fun t:ℝ=>(t^2*A)/t^2=A) fun t h=> by field_simp) 1)
  exact hA.havePay (bill_const (R:=ℝ) A) (by decide)

lemma chalk (hd : R.Bounds p σ K Λ)(hS : LocalRatio D)(x : U) : Fit 3 P[K_,T,x] P[tinted v D h,starsP v h,x] := by
  let a:=plates G F.Free x; let I (t:ℝ):= t • a
  let Y (t:ℝ):= (T) (I t)/t^2; let g (t:ℝ):= loop R (Θ (I t)); let f':=fun t:ℝ=>starsP v h (I t)/t^2
  have he : (I 0)=0:=zero_smul ..; have hx : ContDiffAt ℝ ω I 0:= contDiffAt_id.smul contDiffAt_const
  have hu : Fit 3 Y (f'+g) := ((manta v h hp hr a).shorten (k:=2) (n:=3)).join (Fit.supply ?_ _)
  · have H : Bill 0 g:= life_price (((show ContDiffAt ℝ ω g 0 from (he.symm ▸ gleam_ink v h hd).comp (f:=I) _ hx).continuousAt).mono_left nhdsWithin_le_nhds)
    have hA := hu.negate.elevate (bill_neg (bill_add (spaniet v h x) H))
    let K t:= K_ (I t)
    have hL:Bill 0 K:= life_price (((show ContDiffAt ℝ ω K 0 from (he.symm ▸ gleam_start v h hd hS).comp (f:=I) _ hx).continuousAt).mono_left nhdsWithin_le_nhds)
    refine (Fit.supply (g:=K*(Real.exp ∘ (-Y))) (Eventually.of_forall fun t=> by
       dsimp only [Pi.mul_apply,Pi.neg_apply,Function.comp_apply]; rw [PertExtension.Series.Radial.projection_eq]; unfold K Y I; rw [neg_div]) _).join ((by
         exact hA.right (k:=0) hL : Fit 3 (K * (Real.exp ∘ (-Y))) (K * (Real.exp ∘ (-(f'+g))))).join (Fit.supply ?_ _))
    apply Eventually.of_forall; intro t
    dsimp only [Pi.mul_apply,Pi.add_apply,Pi.neg_apply, Function.comp_apply,K,f',g,I,a,tinted,sublet]; rw [neg_add_rev,Real.exp_add, PertExtension.Series.Radial.projection_eq, ← _root_.mul_assoc, neg_div]
  filter_upwards [eventually_pos] with t ht
  have hh : (I t).2=t:= by simp [I,a,plates]
  change _=f' t+g t; unfold f' g at *; change (_+(I t).2^2*_)/t^2= _; rw [hh]; field_simp
  rfl

lemma compare_shore (hd : R.Bounds p σ K Λ) (hS : LocalRatio D) (i:ℕ)(hi:i≤2) :
    moment (hold G F.Free) (sublet v D h) (T) i=moment (hold G F.Free) (sublet 0 D h) (morsel 0 h V) i := by
  let A:= tinted v D h; let B:= tinted 0 D h
  apply both_moments G F.Free (expulse v h hp hr).2 (expulse 0 h hp hr).2 (expulse v h hp hr).1 (expulse 0 h hp hr).1 (gleam_start v h hd hS) (gleam_start 0 h hd hS) _ i hi
  intro x; let f':=starsP v h; let g:=starsP 0 h
  have he x : A (x,0)=B (x,0) ∧ f' (x,0)=g (x,0):= tint_rayEq v h x
  have hC := (cask_open _ _ hr).2
  exact ((chalk v h hp hr hd hS x).pair (chalk v h hp hr hd hS (-x))).join (Fit.join (pas_agree (schools v h) (schools 0 h) (tint_starts v h hd hS) (tint_starts 0 h hd hS) (tint_lands v h hS hC) (tint_lands 0 h hS hC) (Eventually.of_forall fun x=> (he x).2) (Eventually.of_forall fun x=> (he x).1) x) ((chalk 0 h hp hr hd hS x).turn.pair (chalk 0 h hp hr hd hS (-x)).turn))
end YM.RG08.Canon
