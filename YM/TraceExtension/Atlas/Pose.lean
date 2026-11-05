import YM.TraceExtension.Atlas.Knit
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge}{C:Family G}
local notation "F₀"=> Bel C.book
open LoomX
variable {H:(Bel C.book).Hierarchy} (h:G.Simple)
section
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][NormedSpace ℝ E][IsScalarTower ℝ ℂ E]
variable (bar:E→ₛₗ[starRingEnd ℂ] E) (sw:Signed→Module.End ℂ E)
private lemma cotton [FiniteDimensional ℂ E] [CompleteSpace E][FiniteDimensional ℝ E](P:Bi E) (W: Submodule ℝ (Mat E)) (hw:(1:Mat E)∈ W)(hp:∀ x y:W,x.val*y.val∈W) (H:Bijective P)(hr:∀ x:W,∀ i j,P (x.val i) j=P i (x.val j))(B: ℕ→Bi E)
    (h:∀ i v, Tendsto (fun j=>B j i v) atTop (𝓝 (P i v))) (X:ℕ→W)(hX:∀ i a b, B i a b=P ((X i).val a) b):
    ∃ X:ℕ→Mat E, Tendsto X atTop (𝓝 1) ∧ ∀ᶠ i in atTop, X i∈W∧ IsUnit (X i) ∧ ∀ a b:E, B i a b= P (X i a) (X i b):=by
    let O:W:=⟨1,hw⟩; have ht:Tendsto (fun i=> (X i).val) atTop (𝓝 1):=by
       let U:= (LinearEquiv.ofBijective P.toLinearMap H)
       apply Work.A05.clm_convergence; intro v
       have he(i):Tendsto (fun j=> P ((X j).val v) i) atTop (𝓝 (P v i)):=by simp_rw [← hX];exact h v i
       have hf:= U.symm.toLinearMap.continuous_of_finiteDimensional; have hp:= hf.continuousAt.tendsto (x:=U v) |>.comp (Work.A05.clm_convergence _ _ he)
       change Tendsto (U.symm ∘ fun j=> U ((X j).val v)) atTop (𝓝 (U.symm (U v))) at hp; rw[U.symm_apply_apply] at hp; exact hp.congr (fun i=> U.symm_apply_apply _)
    obtain ⟨g,hg,hy⟩:= bridgeO W hw hp X (tendsto_subtype_rng.mpr ht)
    refine ⟨fun i=> (g i).val,continuous_subtype_val.continuousAt.tendsto.comp hg,?_⟩
    filter_upwards [hy] with i hi; refine ⟨(g i).property,hi.2,?_⟩
    intro a b; rw[hX,← hi.1]; exact hr (g i) _ _
lemma vin [FiniteDimensional ℂ E][CompleteSpace E] (B:Bi E)(P:ℕ→Bi E)
    (f:ℕ→Mat E)(hf:Tendsto f atTop (𝓝 1))(hQ: ∀ᶠ i in atTop, f i∈Wool bar sw∧ IsUnit (f i) ∧ ∀ a b:E, P i a b=B (f i a) (f i b)):∃ U:ℕ→ (E≃ₗ[ℂ] E), Tendsto (fun i=> LinearMap.toContinuousLinearMap (U i).toLinearMap) atTop (𝓝 1) ∧ ∀ᶠ i in atTop, LinearMap.toContinuousLinearMap (U i).toLinearMap∈ Wool bar sw∧ ∀ v w, P i (U i v) (U i w)=B v w:=by
    classical
    let V(i):=if h:IsUnit (f i) then (Spin.unit_shape _ h).choose else LinearEquiv.refl ℂ E; let U(i):=(V i).symm
    have hh(i)(hi:IsUnit (f i))(x):V i x=f i x:=by unfold V;rw[dif_pos hi]; exact LinearMap.congr_fun (unit_shape (f i) hi).choose_spec x
    -- invert square.I
    let Y(i):= LinearMap.toContinuousLinearMap ((U i).toLinearMap)
    have hx:Tendsto (fun i => Ring.inverse (f i)) atTop (𝓝 1):=by
         let hv:=NormedRing.inverse_continuousAt (1: (Mat E)ˣ); simpa only [Units.val_one,Ring.inverse_one] using! hv.tendsto.comp hf
    have hg(i)(hi:IsUnit (f i)): Ring.inverse (f i)= Y i:=by
       apply hi.mul_right_inj.mp; rw [Ring.mul_inverse_cancel _ hi];ext1 x; change x=f i (V i|>.symm x); rw[← hh i hi,LinearEquiv.apply_symm_apply]
    refine ⟨U,hx.congr' (hQ.mono (fun i hi=> hg i hi.2.1)),?_⟩; filter_upwards [hQ] with i ⟨hi,hu,hE⟩; let p:= V i; let Q(x):=f i x; have he(v): f i (p.symm v)=v:=by rw[← hh i hu, LinearEquiv.apply_symm_apply]
    constructor
    · obtain ⟨hv,ht⟩:=hi
      refine ⟨fun x=> p.injective ?_, fun s x=> p.injective ?_⟩
      · change p (p.symm _)=p (bar (p.symm x)); rw [p.apply_symm_apply,hh i hu,hv, he]
      change p (p.symm _)=p (sw s (p.symm x));rw [p.apply_symm_apply,hh i hu,ht,he]
    intro x y; change P i (p.symm x) (p.symm y)=_; rw[hE,he,he]

end
include h
set_option maxHeartbeats 700000 in
lemma roadway (P:ℕ→laceC H)(hp:∀ v w,Tendsto (fun i=>(P i).val v w) atTop (𝓝 ((scannerX H 1).val v w))):∃ U:ℕ→ Active (Bel C.book)≃ₗ[ℂ] Active (Bel C.book), Tendsto (fun i=> LinearMap.toContinuousLinearMap (U i).toLinearMap) atTop (𝓝 1) ∧ ∀ᶠ i in atTop, LinearMap.toContinuousLinearMap (U i).toLinearMap∈ Threads H ∧ LiftB (U i|>.toLinearMap) (P i).val=(scannerX H 1).val:=by
    let B:=scannerX H 1; choose X hX using fun i=> solveT h (P i)
    obtain ⟨f,hf,hQ⟩:= cotton (E:=↥(Active (Bel C.book))) B.val (Threads H) th_one (fun x y=>th_prod x.property y.property) (loom_bij h) (weave_self h B) (fun i=> (P i).val) hp X hX
    unfold Threads at hQ ⊢
    obtain ⟨U,hU,h⟩:= vin (E:=↥(Active (F₀))) (starA H) (swingA H) B.val (fun i=>(P i).val) f hf hQ
    refine ⟨U,hU,h.mono fun i hi=> ⟨hi.1,?_⟩⟩; ext1 x;ext1 y; exact hi.2 x y
end YM.Trace.Pilot
