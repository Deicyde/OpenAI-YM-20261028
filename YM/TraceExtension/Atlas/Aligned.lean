import YM.TraceExtension.Atlas.Group
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction OS OS.Ground Spec MeasureTheory Wilson
open RG Terrace MergeProof.East Next.Rank Next.Rank.East Next.UVStress Further.CorrectedLift Climb
open Analysis TraceExtension Boundary Over Org Work.A05 Table
open scoped Topology BigOperators InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {C: Family G}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book} {F:Final C f S}
variable {H:(Cells.standard C).Hierarchy}{J:Scaling S}{V:∀ i,Vane C i}
variable {Z:Terrace.Arch C}
local notation "F₀"=> Bel C.book
open Measure
attribute [local instance] Work.A15.compact_ortho
local instance : MeasurableSpace Ortho := borel Ortho
local instance : BorelSpace Ortho := ⟨rfl⟩
section
variable {G:Gauge}{L:Register G}{S:Table L}{E : Type*}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]
lemma circle_cont {R : Rotation S} {H:S.RealSpin}(h:Spin.Port R H){d:ℕ}(U:E≃ₗ[ℂ] S.Field d): Continuous (circle h U):=by
   apply continuous_iff_continuousAt.mpr; intro x
   apply (show Tendsto (⇑(circle h U)) (𝓝 x) _ from Dash.fit_plane (fun v=> ((circle h U) v).toLinearMap) _ ?_)
   intro i; exact (U.symm.toLinearMap.continuous_of_finiteDimensional.comp (h.spin d (U i))).continuousAt.tendsto
variable [CompleteSpace E][NormedSpace ℝ E][IsScalarTower ℝ ℂ E]
lemma mean_fixed (f g:Ortho→* (E→L[ℂ] E))(hf:Continuous f)(hg:Continuous g)(x:E)(hx:∀ v,f v x=x)(hy:∀ v,g v x=x): meanO f g x=x:=by
    rw[meanO_value _ _ hf hg]; simp_all only [ContinuousLinearMap.mul_apply]; simp
lemma mean_maps (f g:Ortho→* (E→L[ℂ] E))(hf:Continuous f)(hg:Continuous g)(P:E→L[ℝ] E)(h:∀ (v:Ortho) x,f v (P x)=P (f v x))(h':∀ (v:Ortho) x,g v (P x)=P (g v x))(x:E): (meanO f g) (P x)=P ((meanO f g) x):=by
    rw[meanO_value _ _ hf hg,meanO_value _ _ hf hg, ← P.integral_comp_comm]
    · simp only [ContinuousLinearMap.mul_apply,h,h']
    exact ((hf.mul (hg.comp continuous_inv)).clm_apply continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end
section
variable (h:G.Simple)(h₁:Scribe f J V Z F.sector 𝓛 F.room.kernel H)
open Spin
include h h₁
-- all d eventual, at each d align. can force unit once d≤4.Mark.
structure AlignO {T:Table C.book}(Y: Spec.Algebra T)(h₀:T.RealSpin)(H: (Cells.standard C).Hierarchy)(d : ℕ)(U:change T d) : Prop where
    real : ∀ x:(Bel C.book).Field d, U ((Bel C.book).conj H.spin _ x)=T.conj h₀ d (U x)
    unit : U ((Bel C.book).unit d)=T.unit d
    axis : ∀ i x,U ((turns C).act d i x)=Y.turns.act d i (U x)

def actMove(d:ℕ)(A B:change S d): ((Bel C.book).Field d) ≃ₗ[ℂ] ((Bel C.book).Field d) := B.trans A.symm
abbrev moveV(d:ℕ)(A B:change S d): Mat ((Bel C.book).Field d):= LinearMap.toContinuousLinearMap (actMove d (S:=S) A B).toLinearMap
lemma alignsO (d:ℕ): ∃ U:ℕ→change S d, Tendsto (fun k=> moveV (S:=S) d (J.U k d) (U k)) atTop (𝓝 1) ∧ ∀ᶠ i in atTop, AlignO F.sector F.room.kernel.spin H _ (U i):=by
    let E:= (Bel C.book).Field d; let w':= LinearEquiv.refl ℂ ((Bel C.book).Field d); let w:=circle (compass (H:=H) h) w'; let t(i):= circle (compassF F) (J.U i d); let y(i):=meanO (t i) w;
    have hu:Tendsto y atTop (𝓝 1):= eventualMeanO t (fun i=>circle_cont _ _) w (circle_cont _ _) (acts_tends h h₁ d)
    let P(i:ℕ):= IsUnit (y i)
    let σ(i):= if h:P i then (unit_shape _ h).choose else LinearEquiv.refl ℂ E; let U(i):= (σ i).trans (J.U i d)
    have hv(i)(ht:P i)(v):σ i v=y i v:=by
       unfold σ; rw[dif_pos ht]; exact LinearMap.congr_fun (unit_shape _ ht).choose_spec _
    have hh:= hu.eventually (Units.isOpen.mem_nhds isUnit_one)
    refine ⟨U,hu.congr' ?_,?_⟩
    · filter_upwards [hh] with i hi; ext1 x; change y i x=(J.U i d).symm ((J.U i d) (σ i x)); rw [LinearEquiv.symm_apply_apply,hv _ hi]
    filter_upwards [hh,h₁.monorail.units d] with i hi ht
    have hz(v):U i v= J.U i d (y i v):= congr_arg _ (hv i hi v)
    have hx(v z): F.sector.turns.act d v (J.U i d z)=J.U i d (t i v z):=((J.U i d).apply_symm_apply _).symm
    have hp:= flips ht.1; let F':= F.room.kernel.spin; let L:= Bel C.book
    constructor
    · let q := LinearMap.toContinuousLinearMap (StressFlux.conjQ (d:=d) H.spin); have he(s x): t i s (q x)=q (t i s x):=by
           let S':=F.sector.turns; change (J.U i d).symm (S'.act d s (J.U i d (L.conj H.spin d x)))=L.conj H.spin d ((J.U i d).symm _); rw[ht.1.stars,← F.phase.transport.spots.real,hp.stars];rfl
      have ha(s x):w s (q x)=q (w s x):=((compass (H:=H) h).real d s x).symm
      intro x; rw [hz,hz]; change J.U i d (y i (q x))= _; rw [show y i (q x)=q (y i x) from mean_maps (t i) w (circle_cont _ _) (circle_cont _ _) q he ha x]; exact ht.1.stars ..
    · let v:=L.unit d; apply (hz _).trans; have he(s): t i s v=v:= (J.U i d).injective (by rw [← hx, ht.2]; exact F.phase.transport.spots.identity ..)
      have hj:y i v=v:= mean_fixed (t i) w (circle_cont _ _) (circle_cont _ _) v he (fun i=> (baseRights (H:=H) h).identity d i)
      rw [hj]; exact ht.2
    intro s x; rw [hz,hz,hx]; exact congr_arg (J.U i d) ((congr_arg (fun f : Mat E=> f x) (underO (t i) w (circle_cont _ _) (circle_cont _ _) s)).symm)
end
end YM.Trace.Pilot
