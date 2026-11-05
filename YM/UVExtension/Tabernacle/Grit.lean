import YM.UVExtension.Tabernacle.Knots

/-! # Read transfer and analytic height closed-submodule test. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Tabernacle
open Function Set Filter Metric Lattice RG Precision Wilson Ovens
open Progress.DirectedRecipe Whirl Push Push.AbsoluteSums
open AnalyticBridge VerifiedReset Lamppost Concert BoundedContinuousFunction
open Oriel Oriel.Charted Complex Guild
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators Classical

variable {X Y:Type}
lemma silk (P:Meter.{0,0,0} X Y){u : ℝ}{x : Arbor→ P.Slot}(ht:0≤u)(H:Atlas P lever x (fun _=>u)):
    ∃ F: Lamppost.Mark→ Chime P,Bumps lever.span F ∧ (∀ z∈lever.span, ‖F z‖≤ u) ∧ (∀ i,F (lever.call i)=vibe P (x i)) := by
    let F (z:Lamppost.Mark) : Chime P:= if h:z∈lever.span then
            ofNormedAddCommGroupDiscrete (fun i=> Meter.Finger.issue P i (H.f z)) u (fun i=> P.spare (H.bounds z h) i) else 0
    have hF (z)(h:z∈lever.span)(i): F z i=Meter.Finger.issue P i (H.f z):=by unfold F; rw [dif_pos h]; rfl
    have hk z (h:z∈lever.span) i : ‖F z i‖≤u:=by rw [hF z h]; exact P.spare (H.bounds z h) i
    refine ⟨F,canal (M:=u) (fun i Z g hs he ht=> ?_) hk ht, fun z h=> (BoundedContinuousFunction.norm_le ht).2 (hk z h), fun i=> ?_⟩
    · exact (P.pollen H.pulse i Z g hs he ht).congr (fun z hz=> hF _ (he hz) i)
    have h (v:P.Finger) := P.income v (w:=x i) (fun j k=> (H.exacts i j k).symm)
    have H' : P.MeasureP (x i) u:= by apply P.clips_real; intro t; rw [← Complex.norm_real,h,← hF _ (lever.within _)]; exact hk _ (lever.within _) _
    exact DFunLike.ext _ _ fun t=> by rw [puts P ⟨u,H'⟩,h,hF _ (lever.within _)]
section S
variable [NormedAddCommGroup X] [NormedSpace ℂ X] (P:Submodule ℂ X) (h:IsClosed (P:Set X))
    {f:ℂ→P}{U:Set ℂ}(he:IsOpen U)
include h he
private lemma changes (ht : DifferentiableOn ℂ (fun x=> (f x:P).val) U): DifferentiableOn ℂ f U:=by
    intro z hz
    have hx := ht.differentiableAt (he.mem_nhds hz); let g z:=(f z:P).val
    have hV : Tendsto (slope g z) (𝓝[≠] z) (𝓝 (deriv g z)):= hasDerivAt_iff_tendsto_slope.mp hx.hasDerivAt
    have hp : deriv g z∈ P:= h.mem_of_tendsto hV (Eventually.of_forall (fun v=> (slope f z v).property))
    apply HasDerivAt.differentiableAt (f':= (⟨_, hp⟩:P)) _ |>.differentiableWithinAt
    exact hasDerivAt_iff_tendsto_slope.mpr (tendsto_subtype_rng.mpr hV)
end S
section box
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (P:Submodule ℂ X) (h:IsClosed (P:Set X))
    {F:Lamppost.Mark→X}{ε:ℝ}(hv:∀ z∈lever.span, ‖F z‖ ≤ ε)(hp:Bumps lever.span F)
include h hp hv
lemma enclose (d:Arbor→P)(he:∀ i, F (lever.call i)=(d i:P).val):∃ f:Lamppost.Mark→P,Bumps lever.span f ∧ (∀ z∈ lever.span, ‖f z‖ ≤ ε)∧∀ i, f (lever.call i)=d i:=by
  let f z:= if H:F z∈ P then (⟨F z,H⟩:P) else 0
  have hh : Husk (fun f:Unit→X=> f ()∈ P):=⟨P.zero_mem,fun _ _ hx hy=> P.add_mem hx hy,fun t _ H=> P.smul_mem t H,fun he ht=> h.mem_of_tendsto (ht ()) he⟩
  have hz(z)(h':z∈lever.span):(f z:P).val=F z:= by
    have hX(d:AxisK→ℝ)(hd:∀ i,|d i| <realcap): F (hoist d)∈P:=by rw [show F (hoist d)=_ from he ⟨d,hd⟩]; exact Subtype.coe_prop _
    have hM := Lamppost.regatta (c:=fun _:AxisK=>0) (fun _=> ball (0:ℝ) realcap) (fun _=> ball_mem_nhds _ (by norm_num [realcap])) (fun i v h=> mem_ball_zero_iff.mpr ((Complex.norm_real v).trans_lt ((mem_ball_zero_iff.mp h).trans (by norm_num [realcap,capK]: realcap<capK)))) (fun _=> isOpen_ball) (fun _=> (convex_ball (0:ℂ) _).isPreconnected) (fun z i=> F z) hh (fun _=> hp) (fun a ha=>hX a fun i=> mem_ball_zero_iff.mp (ha i)) z h'
    unfold f; rw [dif_pos (show F z∈ P from hM)]
  refine ⟨f, fun S g ht h' H=>?_,fun z h=> show ‖(f z:P).val‖≤ _ from (hz z h ▸ hv z h), fun i=> Subtype.ext ((hz _ (lever.within _)).trans (he i))⟩
  exact changes P h ht ((hp S g ht h' H).congr (fun i hi=>hz (g i) (h' hi)))
end box
end YM.UVExtension.Tabernacle
namespace YM.UVExtension.Tabernacle
open Function Set Filter Metric Lattice RG Precision Wilson Ovens
open Progress.DirectedRecipe Whirl Push Push.AbsoluteSums
open AnalyticBridge VerifiedReset Lamppost Concert BoundedContinuousFunction
open Oriel Oriel.Charted Complex Guild
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators Classical
variable {G:Gauge}{n:Side}(p:BudgetPoint)(d:Tabernacle.Charm G p n)
    (σ τ ε:ℝ) (q:Arbor→ d.Shed p)
lemma heading (h:0<σ)(ht:0<τ)(hp:0≤ ε) (H:Nonempty (Atlas (ChimeE G p n) lever (sheetE p ∘ (fun i=>(q i).val)) (fun _=>ε*σ)))
    (F:Nonempty (Atlas (ChimeK G p n) lever (sheetK p ∘ (fun i=>(q i).val)) (fun _=> ε*τ))): ∃ f:Mark→ d.Hall σ τ, Bumps lever.span f ∧ (∀ z∈lever.span, ‖f z‖≤ ε) ∧ ∀ i, f (lever.call i)=d.embed σ τ (q i):=by
   obtain ⟨A,ha,hA,hA'⟩:= silk (ChimeE G p n) (mul_nonneg hp h.le) (Classical.choice H)
   obtain ⟨B,hb,hB,hB'⟩:= silk (ChimeK G p n) (mul_nonneg hp ht.le) (Classical.choice F)
   let g z:= ((↑σ:ℂ)⁻¹ • A z,(↑τ:ℂ)⁻¹ • B z)
   refine enclose (F:=g) (Tabernacle.Box (d.hue p σ τ)) isClosed_closure ?_ ?_ _ ?_
   · intro z hz; unfold g; rw [Prod.norm_def]; dsimp only; rw [norm_smul,norm_smul,norm_inv,norm_real,norm_inv,norm_real,Real.norm_of_nonneg h.le,Real.norm_of_nonneg ht.le]; exact max_le ((inv_mul_le_iff₀ h).2 ((hA _ hz).trans_eq (mul_comm ..))) ((inv_mul_le_iff₀ ht).2 ((hB _ hz).trans_eq (mul_comm ..))) -- change only
   · exact fun Z v h hp he=> ((ha Z v h hp he).const_smul ((↑σ:ℂ)⁻¹)).prodMk ((hb Z v h hp he).const_smul ((↑τ:ℂ)⁻¹))
   intro i; unfold g; rw [hA',hB', ← ofReal_inv, ← ofReal_inv,rsmul,rsmul]; rfl

section usingBeta
-- 4 joint input columns; when mass for u normalized tiny. process real hV price via old (5 coords) receipt.
noncomputable def phase (v : Fin 4→ℝ)(u:Plot₀): Lamppost.Mark := fun i=> Option.elim' (∑ j,u j*(v j:ℂ)) u i
lemma phaseD (v:Fin 4→ℝ): Differentiable ℂ (phase v):=by
  apply differentiable_pi.mpr; rintro (_|i)
  · change Differentiable ℂ (fun t:Plot₀=> ∑ i:Fin 4,t i*(v i:ℂ)); fun_prop
  change Differentiable ℂ (fun t:Plot₀=> t i); fun_prop
lemma course (v:Fin 4→ℝ)(he :∀ i,|v i|≤1) : MapsTo (phase v) shieldB lever.span:= by
   intro z hz; have h(i): ‖z i‖<3:= mem_ball_zero_iff.mp (Lamppost.within.mp hz i)
   refine Lamppost.within.mpr (fun i=> ?_); rcases i with (_|i)
   · refine mem_ball_zero_iff.mpr ?_; change ‖∑ j:Fin 4,z j*(v j:ℂ)‖< _; apply lt_of_le_of_lt (norm_sum_le ..); refine lt_of_le_of_lt (Finset.sum_le_sum (g:=fun _=>3) (fun i _=>?_)) (by norm_num [capK]); rw [norm_mul,norm_real]; exact (mul_le_of_le_one_right (norm_nonneg _) (he i)).trans (h i).le
   exact mem_ball_zero_iff.mpr ((h i).trans (by norm_num [capK]))
noncomputable def Rhue (v:Fin 4→ℝ)(u:Fin 4→ℝ) (hv:∀ i,|v i|≤1) (hz:∀ i, |u i|<radiusU): Arbor:= ⟨fun i=>Option.elim' (∑ j,u j*v j) u i, by
   rintro (_|i); swap; · exact (hz i).trans (by norm_num [realcap,radiusU])
   apply lt_of_le_of_lt (Finset.abs_sum_le_sum_abs ..); refine lt_of_le_of_lt (Finset.sum_le_sum (g:=fun _=> radiusU) (fun i _=>?_)) (by norm_num [realcap,radiusU]); rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) (hv i)).trans (hz i).le⟩
lemma loves (v:Fin 4→ℝ)(u:Fin 4→ℝ)(hv:∀ i,|v i|≤1) (hz:∀ i, |u i|<radiusU) : lever.call (Rhue v u hv hz)=phase v (hoist u):= by funext i; rcases i with (_|i); change ((↑(∑ j,u j*v j):ℂ))=∑ j,(u j:ℂ)*(v j:ℂ); push_cast; rfl; rfl
lemma reed {X V : Type}[AddCommGroup V][Module ℝ V] [NormedAddCommGroup X][NormedSpace ℂ X] {u : (ℝ × V)→X}{e:ℝ}(W:Fin 4→ℝ × V)(v:Arbor→X)
    (F:Lamppost.Mark→ X)(he:Bumps lever.span F)(hp:∀ z∈lever.span, ‖F z‖ ≤ e)(h:∀ i,F (lever.call i)=v i)(hw : ∀ i,|(W i).1|≤1)
    (ht:∀ (x:Fin 4→ℝ) (hx:∀ i,|x i|<radiusU),v (Rhue _ x hw hx)=u (tick W x)): Nonempty (Reel u e W):=by
   let t:=fun i=>(W i).1; have hs:= course t hw
   refine ⟨⟨F∘phase t,fun T f h hp hq=>?_ ,fun z hz=> hp _ (hs hz),fun x hx=>?_⟩⟩
   · exact he _ _ h (hs.comp hp) ((phaseD _).comp_differentiableOn hq)
   exact (congr_arg F (loves t x hw hx)|>.symm).trans ((h _).trans (ht _ hx))
end usingBeta
end YM.UVExtension.Tabernacle
