import YM.TraceExtension.Link.Rad

/-!
# The position X-coupling diagnostic E carried into the selected phase

Not needed to earn qstress or `meterQ`. This strengthens the interpretation of
the link on the same fields at this order: the E diagnostic in those measuring
fields on the actual selected phase (or any such Final) has that same leading
Peano coefficient. We don't assert agreement between selected and unselected
on E to a higher rate. Can't take derivatives of pointwise asymptotics: here
we'll use convexity on the positive axis from the positive spectral measure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Link
open Set Filter Function Extraction Spec Table Climb Maxwell UVNext.FreeStress
open Ward Boundary Mink MeasureTheory Measure Spin Over Pilot TraceExtension Verse Pith
open scoped Topology BigOperators InnerProductSpace ContDiff Classical
variable {G:Gauge}{C:Family G}{X:Extraction.Order}{S:Table C.book}(F:Final C X S)(h:G.Simple)
local notation "F₀" => Bel C.book

lemma convex_heat (c:ℝ)(hp:0<c): ConvexOn ℝ (Ioi 0) (fun x=> (euclidean F (c*x)).re):=by
   obtain ⟨μ,hμ,-⟩:= traceSpectrum_exists F
   let f(x:ℝ)(p:E4):=Real.exp (-(c*x)*time p)
   have he(x:ℝ)(hx:x∈ Ioi 0): (euclidean F (c*x)).re= ∫ p, f x p ∂μ:=by
       have hx:0<c*x:= mul_pos hp hx
       rw [Wick.heat_value _ hx hμ, integral_complex_ofReal];rfl
   have hh(x:ℝ)(hx:x∈ Ioi 0): Integrable (f x) μ:=by
       haveI:= hμ.damped_mass (c*x) (mul_pos hp hx)
       have hp':Integrable (fun _ : E4 => (1:ℝ)) (OS.Semigroup.transform timeAxis (c*x) μ):= integrable_const _
       apply Integrable.congr ((integrable_withDensity_iff_integrable_smul (OS.Semigroup.measurable ..)).1 hp')
       exact ae_of_all _ (fun i=> by change Real.exp _ * 1=_; rw[mul_one]; rfl)
   constructor
   · exact convex_Ioi 0
   intro x hx y hy a b ha hb hs; let z:=a • x+b • y
   have ht:z∈ Ioi 0:=(convex_Ioi (0:ℝ)) hx hy ha hb hs
   change (euclidean F _).re ≤ a • (euclidean F _).re+b • (euclidean F _).re
   rw [he _ ht,he x hx,he y hy,← integral_smul,← integral_smul,← integral_add (f:=fun p=> a • f x p) (g:=fun p=>b • f y p) ((hh x hx).smul a) ((hh y hy).smul b)]
   apply integral_mono (hh _ ht) (((hh x hx).smul a).add ((hh y hy).smul b)); intro p; change f z p ≤ a • f x p + b • f y p; unfold f
   rw [show -(c*z)* time p=a • (-(c*x)* time p)+b • (-(c*y)*time p) by unfold z; simp only [smul_eq_mul]; ring]
   exact convexOn_exp.2 (mem_univ _) (mem_univ _) ha hb hs

private lemma slope_limit {U:ℝ→ℝ→ℝ}{V:ℝ→ℝ}{d':ℝ→ℝ}{d:ℝ}
    (he: ∀ x:ℝ, 0<x→ Tendsto (fun s=> U s x) trail (𝓝 (V x)))
    (hk: HasDerivAt V d 1) (hc:∀ᶠ s in trail,ConvexOn ℝ (Ioi 0) (U s))
    (hu:∀ᶠ s in trail,HasDerivAt (U s) (d' s) 1): Tendsto d' trail (𝓝 d):=by
    obtain ⟨hp,ht⟩:= hasDerivAt_iff_tendsto_slope_left_right.mp hk
    have hx(t:ℝ)(hz:0<t): Tendsto (fun s=> slope (U s) 1 t) trail (𝓝 (slope V 1 t)):= ((he t hz).sub (he 1 zero_lt_one)).const_smul ((t-1)⁻¹)
    apply tendsto_order.mpr; constructor
    · intro a ha; obtain ⟨x,hX,H,hA⟩:= ((show ∀ᶠ x:ℝ in 𝓝[<] 1,0 < x from (lt_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds).and ((show ∀ᶠ x:ℝ in 𝓝[<] 1,x < 1 from self_mem_nhdsWithin).and (hp.eventually (lt_mem_nhds ha)))).exists
      filter_upwards [hc,hu,(hx x hX).eventually (lt_mem_nhds hA)] with s hS hU hF; apply lt_of_lt_of_le hF; rw [slope_comm]; exact hS.slope_le_of_hasDerivAt hX (show (0:ℝ)<1 from zero_lt_one) H hU
    intro a ha; obtain ⟨x,H,hA⟩:= ((show ∀ᶠ x:ℝ in 𝓝[>] 1,1 < x from self_mem_nhdsWithin).and (ht.eventually (gt_mem_nhds ha))).exists;
    filter_upwards [hc,hu,(hx x (zero_lt_one.trans H)).eventually (gt_mem_nhds hA)] with s hS hU hF; apply lt_of_le_of_lt _ hF; exact hS.le_slope_of_hasDerivAt (show (0:ℝ)<1 from zero_lt_one) (show 0<x from zero_lt_one.trans H) H hU

private lemma twice (x:Points 2)(v:S.Field 4)(t:ℝ) : S.classMoment (selected F) (fun _=>4) x (fun _=> t • v)= t^(2:ℕ) • S.classMoment (selected F) (fun _=>4) x (fun _=>v):=by
   let P(t:ℂ):Fin 2→ℂ:=fun _=>t
   rw [show (fun _:Fin 2=> t • v)=(fun i=>P (t:ℂ) i • v) from funext (fun _=>Complex.coe_smul ..),(S.classMoment (selected F) (fun _=>4) x).map_smul_univ]; simp only[P,Finset.prod_const,Finset.card_univ,Fintype.card_fin, ← Complex.ofReal_pow,Complex.real_smul];rfl

def onset (p:S.Field 4)(s x:ℝ): ℝ:= (S.classMoment (selected F) (fun _=>4) (s • (x • sail)) (fun _=>p)).re

def pronY (F:Final C X S)(a:Axis)(p q:S.Field 4)(r:ℝ)(x:Points 2): ℂ := Points.gradient 0 a (fun y=> S.classMoment (selected F) (fun _=>4) (r • y) ![p,q]) x
local instance : ContinuousSMul ℝ (Points 2):=IsBoundedSMul.continuousSMul
set_option maxHeartbeats 800000 in
private lemma scales {s:ℝ}(hp:0<s)(q:S.Field 4): HasDerivAt (onset F q s) (pronY F timeAxis q q s sail).re 1 :=by
   let g(p:Points 2):= S.classMoment (selected F) (fun _=>4) (s • p) ![q,q]; let L:ℝ→L[ℝ] Points 2:=LinearMap.toContinuousLinearMap (LinearMap.toSpanSingleton ℝ _ sail); have he:L 1=sail:=one_smul ℝ sail
   have hz:HasDerivAt L sail 1:= he ▸ L.hasFDerivAt.hasDerivAt
   have hh:= (S.class_smooth _ (selected_hierarchy F).smooth
       (fun i:Fin 2=>(⟨4,(![q,q]) i⟩:S.Tag))).contDiffAt ((conf_open _).mem_nhds (sail_on hp))
   have ht:DifferentiableAt ℝ g sail:= (hh.comp sail (contDiffAt_id.const_smul s)).differentiableAt (by simp)
   have ht : DifferentiableAt ℝ g (L 1):=he ▸ ht
   have hv:HasDerivAt (g ∘ L) (pronY F timeAxis q q s sail) 1:=by
      have hp:= ht.hasFDerivAt.comp_hasDerivAt 1 hz; rw[he] at hp;exact hp
   apply (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 1 hv).congr_of_eventuallyEq ; apply Eventually.of_forall;intro x; unfold onset;rw [show (fun _ :Fin 2=>q) = ![q,q] from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)];rfl

include h
lemma convex_scalar (g f:ℝ→ℝ)(P:ℝ→change S 4)(hp:Coupling G g)(ht:TendC F P f):
    ∀ᶠ s in trail,ConvexOn ℝ (Ioi 0) (onset F (P s (stepField C)) s):=by
   filter_upwards [center_eq F P f ht,(logfit F h _ _ _ hp ht).eventually_ne (show (-1:ℝ)≠0 by norm_num),self_mem_nhdsWithin] with s hS hs he; have he:0<s:= he
   let v:=P s (stepField C); let w:=centerIn S (selected F) v; let B:=((4*f s)^2)⁻¹*s^8; let U:=((euclideanVEV S (selected F) v)^2).re; have hv:0 ≤ B:=by unfold B; positivity
   have hz:4*f s≠0:= (mul_ne_zero_iff.mp hs).2
   refine (((convex_heat F s he).smul hv).add (convexOn_const (c:=U) (convex_Ioi 0))).congr ?_
   intro i hi; have hI:0 < i:= hi; let u:=s • (i • sail); have hh:Verse.width u=s*i:=by simp[Verse.width,u,sail,Points.direction,norm_smul,abs_of_pos hI,abs_of_pos he]
   have hq:u∈conf 2:=Work.A05.smul_conf he (sail_on hI); let p:=S.classMoment (selected F) (fun _:Fin 2=>4) u
   have hA: p (fun _=>w)= B • euclidean F (s*i):=by
      rw[← hh, ← axis_shape F u hq, show B=((4*f s)^2)⁻¹*(s^4)^2 by unfold B;ring, mul_smul, ← twice, hS,twice,smul_smul,inv_mul_cancel₀ (pow_ne_zero _ hz),one_smul]
   change B • (euclidean F (s*i)).re+U=(p (fun _=>v)).re; unfold p; rw[center_formula F hq,Complex.add_re,hA]; simp[Complex.real_smul,U]

lemma selected_B (g f:ℝ→ℝ)(P:ℝ→change S 4)(H:(Bel C.book).Hierarchy)(hp:Coupling G g)(ht:TendC F P f)(he:EuclideanAsymptotic F (award G)):
   Tendsto (fun s=> (pronY F timeAxis (P s (stepField C)) (P s (stepField C)) s sail).re) trail (𝓝 (datum C).re):=by
   let U(s:ℝ):= onset F (P s (stepField C)) s
   let V(x:ℝ):= ((F₀).classMoment (F₀) (fun _:Fin 2=>4) (x • sail) (fun _=>stepField C)).re
   apply slope_limit (U:=U) (V:=V) _ _ (convex_scalar F h _ _ _ hp ht)
   · exact (show ∀ᶠ s in trail,0<s from self_mem_nhdsWithin).mono fun i hi=> scales F hi _
   · intro x hx; exact Complex.continuous_re.continuousAt.tendsto.comp (uncentered_scalar F h _ _ _ hp ht he (x • sail) (sail_on hx))
   let k:= 3*(G.lieDim:ℝ)/Real.pi^4
   have he:(datum C).re=k*(-8):=by rw [show datum C=_ from sails_peak H]; rfl
   rw [he]; have ht:= ((hasDerivAt_id' (1:ℝ)).pow 8).inv (by simp); norm_num at ht
   refine (ht.const_mul k).congr_of_eventuallyEq ((lt_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).mono fun x hx=> ?_)
   unfold V; rw [show (F₀).classMoment (F₀) (fun _:Fin 2=>4) (x • sail) (fun _=>stepField C)= _ from Pith.sails_val C x hx];rfl

omit h
def eSelected (P:ℝ→change S 4)(s:ℝ):ℂ := let v:=P s (stepField C)
    ∑ i, pronY F i (P s (standard4 C i timeAxis)) v s sail

local notation "D"=> F.sector.derivatives

private def frontal (F:Final C X S){d:ℕ} (v:S.Field 4)(t:Points 2): S.Field d→ₗ[ℂ] ℂ:=
   let k: Fin 2→ℕ:= ![d,4]
   (S.classMoment (selected F) k t).toLinearMap (Fin.cons (α:=fun i:Fin 2=> S.Field (k i)) 0 (Fin.cons (α:=fun i:Fin 1=> S.Field (k i.succ)) v (fun i=>Fin.elim0 i))) 0
private lemma frontal_y (x:Points 2)(p:S.Field 4){d:ℕ}(q:S.Field d):
    frontal F p x q= S.useAt (selected F) x ![⟨d,q⟩,⟨4,p⟩]:=by
   let k:=(![d,4]:Fin 2→ℕ);let v:= (![⟨d,q⟩,⟨4,p⟩]:Fin 2→ S.Tag); unfold Table.useAt
   have he:(fun i=>(v i).1)=k:=funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)
   let g:=Fin.cons (α:=fun i:Fin 2=> S.Field (k i)) q (Fin.cons (α:=fun i:Fin 1=> S.Field (k i.succ)) p (fun i=>Fin.elim0 i))
   unfold frontal
   change S.classMoment (selected F) k x (Function.update _ 0 q) = S.classMoment (selected F) _ x _
   trans S.classMoment (selected F) k x g
   · congr 1; exact funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)
   have ht:v= fun i=>⟨k i,g i⟩:=funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)
   change _= S.useAt (selected F) x v
   rw[ht];rfl
private lemma derives {s:ℝ}(hp:0<s)(p q:S.Field 4)(a:Axis):
    pronY F a p q s sail = (s:ℂ)* frontal F q (s • sail) (F.sector.derivatives.deriv 4 a p):=by
   let f(x:Points 2):= S.useAt (selected F) x (![⟨4,p⟩,⟨4,q⟩]:Fin 2→ S.Tag); let u:=s • sail; let U:Points 2→L[ℝ] Points 2:= s • ContinuousLinearMap.id ℝ _
   have he: HasFDerivAt (f ∘ U) ((fderiv ℝ f u).comp U) sail:= HasFDerivAt.comp sail (show HasFDerivAt f (fderiv ℝ f u) (U sail) from
       (((S.class_smooth _ (selected_hierarchy F).smooth _).contDiffAt ((conf_open _).mem_nhds (sail_on hp))).differentiableAt (by simp)).hasFDerivAt) U.hasFDerivAt
   unfold pronY
   have hY:(fun y=> S.classMoment (selected F) (fun _=>4) (s • y) ![p,q])=f ∘ U:=by
       funext y; unfold f
       rw[show (![⟨4,p⟩,⟨4,q⟩] :Fin 2→S.Tag)= fun i=>⟨4,(![p,q]) i⟩ from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)]
       rfl
   rw[hY,frontal_y]
   have hp':S.useAt (selected F) u ![⟨4+1,(D).deriv 4 a p⟩,⟨4,q⟩]=Points.gradient 0 a f u:= (F.phase.phase.calculus F.α.atPoint).kernels 4 a p (sail_on hp) _
   rw[hp']; unfold Points.gradient Analysis.D; rw[he.fderiv]; let v:=Points.direction (0:Fin 2) a
   change fderiv ℝ f u (s • v)= (s:ℂ)* _
   rw[map_smul]; exact Complex.real_smul ..
lemma selected_position (P:ℝ→change S 4)(f a e:ℝ→ℝ)
    (ht:∀ᶠ s in trail,Measures F s (P s) (a s) (f s) (e s))
    (hc:∀ᶠ s in trail, P s ((Bel C.book).unit 4)=S.unit 4):
    ∀ᶠ s in trail,a s • eSelected F P s + f s • (pronY F timeAxis (P s (stepField C)) (P s (stepField C)) s sail)=0 :=by
   filter_upwards [ht,hc,self_mem_nhdsWithin] with s ht hc hx; have hp: 0<s:= hx
   let y:=P s (stepField C); let z:=s • sail; let U(i):=P s (standard4 C i timeAxis); let R(f:S.Stress):=∑ i, (D).deriv 4 i (f i timeAxis)
   have hA (w t:S.Stress): R (w+t)=R w+R t:=by unfold R; simp only [Pi.add_apply,map_add, Finset.sum_add_distrib]
   have hF (c:ℝ) (w:S.Stress): R (c • w)=c • R w:=by unfold R; rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun i _=> (((D).deriv 4 i).restrictScalars ℝ).map_smul ..)
   have hh (q:(Bel C.book).Field 4): R (Pith.post (C:=C) (P s) (Pith.erase (C:=C) q))=(D).deriv 4 timeAxis (P s q):=by
      unfold R; rw [Finset.sum_eq_single timeAxis]; simp [Pith.post,Pith.erase]
      intro i _ he; simp only [Pith.post,Pith.erase,if_neg he,map_zero]
      simp
   have hB : R F.sector.energy=0:= F.phase.transport.conserved.divergence _
   have hc':R (Pith.post (C:=C) (P s) (Pith.erase (C:=C) (F₀|>.unit 4)))=0:=by rw[hh,hc]; exact (D).unit_drop F.room.kernel.laws F.phase.transport.derivatives F.room.kernel.smooth _ _
   have he:= congrArg R (ht.codes F); rw[hF,hB,smul_zero,hA,hA,hF,hF,hF,hc',smul_zero,add_zero,hh] at he
   unfold eSelected
   dsimp only; let V:=frontal F (d:=5) y z
   change a s • (∑ i:Axis, pronY F i (U i) y s sail)+f s • pronY F timeAxis y y s sail=0
   let r:= s
   simp_rw [derives F hp]
   rw[← Finset.mul_sum,← mul_smul_comm, ← mul_smul_comm,← mul_add];
   apply mul_eq_zero_of_right
   let j:= R (Pith.post (C:=C) (P s) (standard4 C)); rw[← _root_.map_sum]; change a s • V j+f s • V ((D).deriv 4 timeAxis y)=0
   let V':=V.restrictScalars ℝ; change a s • V' j + _=0; rw [← V'.map_smul]; change _ + f s • V' ((D).deriv _ _ _)=_; rw[← V'.map_smul, ← map_add,he.symm,map_zero]
include h
lemma e_position_check (g f a e:ℝ→ℝ)(P:ℝ→change S 4)(H:(Bel C.book).Hierarchy)
    (hp:Coupling G g)(hv:TendC F P f)(hE:EuclideanAsymptotic F (award G))
    (ht:∀ᶠ s in trail,Measures F s (P s) (a s) (f s) (e s))
    (ha:Tendsto a trail (𝓝 1)) (hc:∀ᶠ s in trail, P s ((Bel C.book).unit 4)=S.unit 4):
    Tendsto (fun s=> (eSelected F P s).re/g s^2) trail (𝓝 (Sundial.bauble C)):=by
   have hB:= selected_B F h g f P H hp hv hE
   have he:= (hv.measures _ hp).neg; rw[← force_b] at he
   have hT:= (he.mul hB).div ha one_ne_zero; rw[div_one] at hT; refine hT.congr' ?_
   filter_upwards [selected_position F P f a e ht hc,hp.positive,ha.eventually_ne one_ne_zero] with s hs hG hz
   have h:= congrArg Complex.re hs; simp only [Complex.add_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero, Complex.zero_re] at h
   change -(f s/g s^2)* (pronY F _ _ _ _ _).re/a s= _; field_simp; linarith
end YM.Trace.Link
