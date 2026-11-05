import YM.TraceExtension.Pith.Probe
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pith
open Function Filter Set Extraction Ward Climb Spec Over Pilot Table Analysis Maxwell StressFlux Work Work.A05 MeasureTheory Next.UVStress Next.Rank Spin Work.A01
open scoped Topology BigOperators InnerProductSpace Classical ContDiff
variable {G:Gauge}{C:Family G}{p:Extraction.Order}{n:ℕ}
variable {S:Table C.book}(H:S.Hierarchy)(V:(Bel C.book).Hierarchy){P:ℝ→change S 4}
local notation "F₀" => Bel C.book
include H V
local instance (n:ℕ) : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
lemma stripes (hP:∀ m:ℕ,∀ᶠ r in trail, chores r (P r) m)(a:Axis)(Y:(Bel C.book).Field 4)(v:Fin n→(Bel C.book).Field 4)(x:Points (n+1))(hx:x∈conf (n+1)):
    Tendsto (fun t=> pron a (P t Y) (P t ∘ v) x t) trail (𝓝 (pron a Y v x 1)):=by
    let f(q):= (F₀).classMoment F₀ (fun _=>4) q (Fin.cons (α:=fun _: Fin (n+1)=>_) Y v); let u:=Fin.cons (α:=fun _:Fin (n+1)=> (Bel C.book).Field 4) Y v
    let g(t:ℝ)(q:Points (n+1)):=S.classMoment S _ (t • q) (P t∘u)
    have hf : Tendsto (fun t=>iteratedFDeriv ℝ 1 (g t) x) trail (𝓝 (iteratedFDeriv ℝ 1 f x)):=by
        apply Metric.tendsto_nhds.mpr; intro ε he; filter_upwards[jets H V P hP u 1 {x} isCompact_singleton (singleton_subset_iff.mpr hx) ε he] with k hk; rw [dist_eq_norm]; exact hk x (mem_singleton _)
    let D:= Points.direction (0:Fin (n+1)) a
    have hs:Continuous (fun T : (Points (n+1))[×1]→L[ℝ]ℂ => T (fun _=>D)):= by fun_prop
    have hp:= hs.continuousAt.tendsto.comp hf
    simp only [Function.comp_def,iteratedFDeriv_one_apply (𝕜:=ℝ)] at hp
    unfold pron; simp_rw [show ∀ t, Fin.cons (α:=fun _:Fin (n+1)=>S.Field 4) (P t Y) (P t ∘ v)=P t ∘ u from fun t=> funext (Fin.forall_fin_succ.mpr ⟨rfl,fun _=> rfl⟩),one_smul]; exact hp

omit H V in
def say (x:Points (n+1))(χ:E4→ℝ) (a:Axis) (w:(Bel C.book).Stress) (b:Axis)(Y:(Bel C.book).Field 4)(v:Fin n→(Bel C.book).Field 4)(t : ℝ)(P:change S 4): ℂ :=
    -∫ y, sheet t χ a (fun _=>1) x (Fin.cons ⟨4,P (w a b)⟩ (Fin.cons ⟨4,P Y⟩ (fun j=>⟨4,P (v j)⟩))) y
-- pure F eval
omit H V in
def said (x:Points (n+1))(χ:E4→ℝ)(a:Axis)(w:(Bel C.book).Stress)(b:Axis)(Y:(Bel C.book).Field 4)(v:Fin n→(Bel C.book).Field 4): ℂ :=
    -∫ y, sheet 1 χ a (fun _=>1) x (Fin.cons ⟨4,w a b⟩ (Fin.cons ⟨4,Y⟩ (fun j=>⟨4,v j⟩))) y
lemma steps (hP:∀ m:ℕ,∀ᶠ r in trail, chores r (P r) m)(x:Points (n+1))(hx:x∈conf (n+1)){χ:E4→ℝ}(hc:Window x χ)(a:Axis)(w:(Bel C.book).Stress)(b:Axis)(Y:(Bel C.book).Field 4)(v:Fin n→(Bel C.book).Field 4):
    Tendsto (fun t=> say x χ a w b Y v t (P t)) trail (𝓝 (said x χ a w b Y v)):=by
    let χ₀:= Work.A05.weight χ a fun _=>1; let T :=∫ y,‖χ₀ y‖; have hT: 0 ≤ T:= integral_nonneg fun _=>norm_nonneg _; let X:=tsupport (fderiv ℝ χ); let L(y:E4):= Points.cons y x; have hL:Continuous L:=by
       have hp:Continuous (fun y:E4=> Fin.cons (α:=fun _ : Fin (n+2) => E4) y x.ofLp):= continuous_pi fun k=> Fin.cases (by simp; exact continuous_id) (fun _=> by simp; exact continuous_const) k
       exact (PiLp.continuousLinearEquiv 2 ℝ _).symm.continuous.comp hp
    have hu :IsCompact (L '' X):= IsCompact.image (show IsCompact _ from hc.2.1.fderiv ℝ) hL
    let u:= Fin.cons (α:=fun _:Fin (n+2)=> (Bel C.book).Field 4) (w a b) (Fin.cons (α:=fun _:Fin (n+1)=>_) Y v)
    let h(y):= (F₀).classMoment F₀ (fun _=>4) y u; let g(t:ℝ)(y:Points (n+2)):= S.classMoment S _ (t•y) (P t ∘ u)
    let v0:= Fin.cons (α:=fun _:Fin (n+2) => (Bel C.book).Tag) ⟨4,w a b⟩ (Fin.cons ⟨4,Y⟩ (fun i=> ⟨4,v i⟩)); let Q(t:ℝ):=Fin.cons (α:=fun _:Fin (n+2) => S.Tag) ⟨4,P t (w a b)⟩ (Fin.cons ⟨4,P t Y⟩ (fun i=>⟨4,P t (v i)⟩))
    have hh:v0=(fun i=>(⟨4,u i⟩:(Bel C.book).Tag)):= funext (Fin.forall_fin_succ.mpr ⟨rfl, Fin.forall_fin_succ.mpr ⟨rfl,fun i=> rfl⟩⟩)
    have hq(t):Q t=(fun i=>(⟨4,P t (u i)⟩:S.Tag)):=funext (Fin.forall_fin_succ.mpr ⟨rfl, Fin.forall_fin_succ.mpr ⟨rfl,fun i=> rfl⟩⟩)
    let f(t:ℝ):= sheet t χ a (fun _=>1) x (Q t); let F:=sheet 1 χ a (fun _=>1) x v0
    unfold say said; apply Tendsto.neg; apply Metric.tendsto_nhds.mpr; intro ε he; let δ:= ε/(T+1); have hD:0 < δ:=by unfold δ; positivity
    have hI : L '' X ⊆ conf _:=by rintro _ ⟨y,hy,rfl⟩; exact window_cons_conf hx hc hy
    filter_upwards[self_mem_nhdsWithin, jets H V P hP u 0 _ hu hI _ hD] with t hp hJ
    let G:= f t; have hp:0<t:= hp; have hv:= integrable_sheet hp x hx H.smooth (Q t) hc a (show Continuous (fun _ : E4=>(1:ℝ)) from continuous_const); have hz:= integrable_sheet one_pos x hx V.smooth v0 hc a (show Continuous (fun _ : E4=>(1:ℝ)) from continuous_const)
    have he(y): ‖G y-F y‖ ≤ ‖χ₀ y‖*δ:=by
       by_cases hd:y∈X
       · unfold G f F sheet; rw[hq,hh, one_smul,← mul_sub,norm_mul]; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _); change ‖g t (L y)- h (L y)‖ ≤ δ
         have hm : iteratedFDeriv ℝ 0 (g t) (L y)-iteratedFDeriv ℝ 0 h (L y) = iteratedFDeriv ℝ 0 (fun y=> g t y-h y) (L y):=by ext1 z;simp
         rw[← (show ‖iteratedFDeriv ℝ 0 (fun y=>g t y-h y) (L y)‖=‖g t (L y)-h (L y)‖ from norm_iteratedFDeriv_zero ..),← hm]; exact (hJ (L y) ⟨y,hd,rfl⟩).le
       unfold G f F sheet χ₀ Work.A05.weight D; rw [image_eq_zero_of_notMem_tsupport hd]; simp
    change dist (∫ y,G y) (∫ y,F y)<ε; rw [dist_eq_norm,← integral_sub hv hz];
    calc _ ≤ ∫ y, ‖χ₀ y‖*δ:= norm_integral_le_of_norm_le ((integrable_weight hc.1 hc.2.1 a continuous_const).norm.mul_const _) (ae_of_all _ he)
         _ = T*δ:= integral_mul_const ..
         _ < (T+1)*δ:= mul_lt_mul_of_pos_right (lt_add_one _) hD
         _ = ε:=by unfold δ; field_simp
end YM.Trace.Pith
