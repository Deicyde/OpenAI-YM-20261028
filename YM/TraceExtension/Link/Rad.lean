import YM.TraceExtension.Agora

/-!
# Radial centered trace and same X-frame in the selected phase

Pointwise statements, *no* integration over collisions. `TendC` gives
reference-label equality modulo exact unit, not just equality of some
unselected correlations. This makes the centered label comparison in the
chosen vacuum and its leading Euclidean reading particularly transparent. We
include the VEV result since the positioning and E-coupling prescription use
unselected correlations while the interacting asymptotic uses the phase.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Link
open Set Filter Function Extraction Spec Table Climb Maxwell UVNext.FreeStress
open Spin Ward Boundary Over Pilot TraceExtension Verse
open scoped Topology BigOperators InnerProductSpace ContDiff Classical
variable {G:Gauge}{C:Family G}{X:Extraction.Order}{S:Table C.book}(F:Final C X S)(h:G.Simple)
local notation "F₀" => Bel C.book

private lemma vev_smul (x:S.Field 4)(a:ℝ):
    euclideanVEV S (selected F) (a • x) = a • euclideanVEV S (selected F) x:=by
  have hp: a • x=(a:ℂ) • x:= Complex.coe_smul ..
  rw [hp, vev_linear.map_smul]
  exact (Complex.real_smul ..).symm

lemma center_smul (v:S.Field 4)(a:ℝ):
    centerIn S (selected F) (a • v)= a • centerIn S (selected F) v:=by
  unfold centerIn; rw[smul_sub,vev_smul]
  congr 1
  rw[smul_assoc]
private lemma center_fixed : centerIn S (selected F) (center F)= center F:= by
   unfold centerIn
   rw[show euclideanVEV S (selected F) (center F)=0 from
      centerIn_vac (selected_respects _) (selected_hierarchy _) _]
   rw [zero_smul,sub_zero]
lemma center_eq (P:ℝ→change S 4)(f:ℝ→ℝ)(ht:TendC F P f):
    ∀ᶠ s in trail,s^(4:ℕ) • center F=(4*f s) • centerIn S (selected F) (P s (stepField C)):=by
   obtain ⟨v,hv⟩:= ht.centered
   filter_upwards [hv] with s hs
   conv_lhs=> arg 2; rw[← center_fixed F]
   rw [← center_smul,hs,← center_smul]
   unfold centerIn
   rw [vev_linear.map_add, vev_smul F (v • _), vev_linear.map_smul, vev_unit (selected_respects _) (selected_hierarchy _)]
   simp only [add_smul,smul_eq_mul,mul_one,smul_assoc]
   abel

private lemma clue_eq (r:ℝ): Zlog r⁻¹ = clue r:=by simp[Zlog]
lemma radial_length (t:ℝ)(hp:0<t){A:ℝ} (he:EuclideanAsymptotic F A):
    Tendsto (fun s=> clue s • euclidean F (s*t)) trail (𝓝 ((A/t^8:ℝ):ℂ)):=by
   have ht: Tendsto (fun s:ℝ=> s*t) trail trail:= by
      apply tendsto_nhdsWithin_iff.mpr; constructor
      · have hx:= (show Continuous (fun s:ℝ=> s*t) by fun_prop).tendsto 0
        simp only [zero_mul] at hx; exact hx.mono_left nhdsWithin_le_nhds
      exact (show ∀ᶠ s in trail,0<s from self_mem_nhdsWithin).mono fun s h=>mul_pos h hp
   have hx:= (zlog_shift t hp).comp (tendsto_inv_nhdsGT_zero (𝕜:=ℝ));
   have hz:= hx.smul (he.comp ht)
   rw [show ((A/t^8:ℝ):ℂ)= (t⁻¹)^8 • (A:ℂ) by rw[Complex.real_smul];push_cast;ring]
   refine hz.congr' ?_
   filter_upwards [ht.eventually (self_mem_nhdsWithin (a:=0) (s:=Ioi (0:ℝ))), ht.eventually ((gt_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds)] with i hI hU
   have hh: 0 < i*t:= hI; have he : Zlog (i*t)⁻¹≠0:= (Zlog_pos (by have hz : i*t < 1:= hU; rw[one_lt_inv₀ hh];exact hz)).ne'
   rw[clue_eq] at he
   change (Zlog i⁻¹/Zlog (i⁻¹/t)) • (clue (i*t) • _) = _
   rw [show i⁻¹/t=(i*t)⁻¹ by ring,clue_eq,clue_eq,smul_smul,div_mul_cancel₀ _ he]

lemma radial_shape (x:Points 2)(hx:x∈conf 2){A:ℝ}(he:EuclideanAsymptotic F A):
    Tendsto (fun s=> clue s • S.classMoment (selected F) (fun _=>4) (s • x) (fun _=>center F)) trail
       (𝓝 ((A/Verse.width x^8:ℝ):ℂ)):=by
   have hh : 0 < Verse.width x:= norm_pos_iff.mpr (sub_ne_zero.mpr ((show Injective x.ofLp from hx).ne (by decide)))
   apply (radial_length F (Verse.width x) hh he).congr'
   filter_upwards[self_mem_nhdsWithin] with t ht
   rw [axis_shape F (t • x) (Work.A05.smul_conf ht hx)]; unfold Verse.width
   rw [PiLp.smul_apply,PiLp.smul_apply,← smul_sub,norm_smul,Real.norm_of_nonneg (le_of_lt ht)]

private lemma twice (x:Points 2)(v:S.Field 4)(t:ℝ) : S.classMoment (selected F) (fun _=>4) x (fun _=> t • v)= t^(2:ℕ) • S.classMoment (selected F) (fun _=>4) x (fun _=>v):=by
   let P(t:ℂ):Fin 2→ℂ:=fun _=>t
   rw [show (fun _:Fin 2=> t • v)=(fun i=>P (t:ℂ) i • v) from funext (fun _=>Complex.coe_smul ..),(S.classMoment (selected F) (fun _=>4) x).map_smul_univ]; simp only[P,Finset.prod_const,Finset.card_univ,Fintype.card_fin, ← Complex.ofReal_pow,Complex.real_smul];rfl

include h
lemma logfit (g f:ℝ→ℝ)(P:ℝ→change S 4)(hp:Coupling G g)(ht:TendC F P f):
    Tendsto (fun s=> LogV s*(4*f s)) trail (𝓝 (-1)):=by
   have ha : Tendsto (fun s=> LogV s*(4*f s)) trail (𝓝 (4*d2 G/G.slopeConstant)):=by
      have hl := (hp.running.mul ((ht.measures _ hp).const_mul 4)); rw[← force_b,inv_mul_eq_div] at hl; apply hl.congr'
      filter_upwards [hp.positive] with i hi; field_simp
   have hA:4*d2 G/G.slopeConstant=-1:=by
      rw [force_b,beta_eq]; have h':b0 G≠0:=by unfold b0; have hh:=Gauge.casimir_pos h; positivity
      field_simp [(Gauge.casimir_pos h).ne'] ; ring
   rwa [← hA]
lemma centered_scalar (g f:ℝ→ℝ)(P:ℝ→change S 4)(hp:Coupling G g) (ht:TendC F P f)
    (he:EuclideanAsymptotic F (award G)) (x:Points 2)(hx:x∈conf 2):
    Tendsto (fun s=> S.classMoment (selected F) (fun _=>4) (s • x) (fun _=>centerIn S (selected F) (P s (stepField C))))
      trail (𝓝 ((F₀).classMoment (F₀) (fun _=>4) x (fun _=>stepField C))):=by
   have ha:=logfit F h g f P hp ht
   let T (s : ℝ):=LogV s*(4*f s); have hu:Tendsto (fun s=> ((T s)^2)⁻¹) trail (𝓝 1):=by simpa using (ha.pow (2:ℕ)).inv₀ (by norm_num)
   let U:=award G; let t:=Verse.width x
   have hQ: U=3*(G.lieDim:ℝ)/Real.pi^4:=by
      unfold U award; rw [force_b]; have hn: b0 G≠0:=by unfold b0; have h:=Gauge.casimir_pos h; positivity
      field_simp [(Gauge.casimir_pos h).ne'] ; ring
   have hh:(F₀).classMoment (F₀) (fun _=>4) x (fun _=>stepField C)=(↑(U/t^8):ℂ):=by
      rw [hQ, div_eq_mul_inv (3*_/_)]; exact wick_norm ((show Injective x.ofLp from hx).ne (by decide))
   have hS:= hu.smul (radial_shape F x hx he); rw[one_smul] at hS; rw[hh]; apply hS.congr'
   filter_upwards [ha.eventually_ne (show (-1:ℝ)≠0 by norm_num),center_eq F P f ht] with i hi hp
   have hx: T i≠0:= hi
   let v:=P i (stepField C); let y:=centerIn S (selected F) v
   have hV: clue i • S.classMoment (selected F) (fun _=>4) (i • x) (fun _=>center F) = (T i)^2 • S.classMoment (selected F) (fun _=>4) (i • x) (fun _=>y):=by
      rw [show clue i= (LogV i)^2*(i^4)^2 by unfold LogV; change i^8*(Real.log i⁻¹)^2= _; ring,mul_smul, ← twice]; simp only [hp]; unfold T; rw [twice]; simp only [v,y,mul_pow,mul_smul]
   rw[hV,smul_smul,inv_mul_cancel₀ (pow_ne_zero _ hx),one_smul]

omit h F in
private lemma logflat : Tendsto (fun t:ℝ=> LogV t*t^4) trail (𝓝 0):=by
   have hp:= (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (tendsto_inv_nhdsGT_zero (𝕜:=ℝ)))
   have hv:= (show Tendsto (fun t:ℝ=>t^3) trail (𝓝 0) from by
       simpa only [zero_pow (by decide : (3:ℕ) ≠0)] using ((show Tendsto (fun t:ℝ=>t) trail (𝓝 0) from nhdsWithin_le_nhds).pow 3))
   have ht:=hp.mul hv; rw[mul_zero] at ht; exact ht.congr fun i=>by change Real.log i⁻¹ / i⁻¹*i^3=_; unfold LogV;rw [div_eq_mul_inv,inv_inv];ring
lemma disappearing (g f:ℝ→ℝ)(P:ℝ→change S 4)(hp:Coupling G g)(ht:TendC F P f):
    Tendsto (fun s=> euclideanVEV S (selected F) (P s (stepField C))) trail (𝓝 0):=by
   have ha:=logfit F h g f P hp ht; obtain ⟨v,hv⟩:= ht.centered
   have hh:= (logflat.div ha (by norm_num)).smul (tendsto_const_nhds (x:=-v)); rw[zero_div,zero_smul] at hh
   refine hh.congr' ?_
   filter_upwards [ha.eventually_ne (show (-1:ℝ)≠0 by norm_num),hv] with i hi hx
   let T:=selected F; let y:=P i (stepField C)
   let w:=euclideanVEV S T y
   have he:= congr_arg (fun p:S.Field 4=> euclideanVEV S T p) hx
   change euclideanVEV S (selected F) _=euclideanVEV S (selected F) _ at he
   rw [vev_linear.map_add,vev_smul F, vev_smul F, vev_smul F,vev_linear.map_smul, vev_unit (selected_respects _) (selected_hierarchy _),smul_eq_mul,mul_one,show euclideanVEV S (selected F) (center F)=0 from centerIn_vac (selected_respects _) (selected_hierarchy _) _,smul_zero] at he
   apply smul_right_injective ℂ hi
   simp only [Pi.div_apply]
   rw [smul_smul,mul_div_cancel₀ _ hi,mul_smul,mul_smul]
   rw [eq_neg_of_add_eq_zero_left he.symm,smul_neg]

omit h in
lemma unit_front {x:Points 2}(hx:x∈conf 2)(p:S.Field 4) : S.classMoment (selected F) (fun _=>4) x ![S.unit 4,p]= euclideanVEV S (selected F) p:=by
    let f:Fin 1→ S.Tag:=fun _=>⟨4,p⟩
    let X:Fin 1→ C.book.Token:=fun _=>⟨4,S.representative 4 p⟩
    let v:Fin 2→S.Tag:= Fin.cons (α:=fun _:Fin 2=> S.Tag) ⟨4,S.unit 4⟩ f
    let P: Fin 2→ C.book.Token:= Fin.cons (α:=fun _:Fin 2=> C.book.Token) (C.book.one 4) X
    have he : v= S.classTokens ∘ P:= by
       funext i; fin_cases i
       · rfl
       change (⟨4,p⟩:S.Tag)= ⟨4,S.project 4 (S.representative 4 p)⟩; rw [S.rep]
    rw [← vev_coordinates (selected_hierarchy F).translations p (Points.tail x)]
    have hu:(fun i:Fin 2=> (⟨4,(![S.unit 4,p]) i⟩:S.Tag)) = v:=funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)
    change S.useAt (selected F) x (fun i=>⟨4,(![S.unit 4,p]) i⟩)=_
    rw[hu,he,S.at_project (selected F) (selected_hierarchy F).laws.toSymmetric (selected_respects _) hx]
    exact (selected_hierarchy F).laws.unital hx 4 X
omit h in
lemma unit_back {x:Points 2}(hx:x∈conf 2)(p:S.Field 4) : S.classMoment (selected F) (fun _=>4) x ![p,S.unit 4]= euclideanVEV S (selected F) p:=by
   let q:Equiv.Perm (Fin 2) := Equiv.swap 0 1
   let Y:= ![p,S.unit 4]
   let W(i:Fin 2): S.Tag :=⟨4,Y i⟩
   change S.useAt (selected F) x W=_
   rw [← S.class_perm _ (selected_hierarchy F).laws.toSymmetric q hx W,show W ∘ q= fun i=>(⟨4,(![S.unit 4,p]) i⟩:S.Tag) from ?_]
   exact unit_front F (Points.rearrange_in q hx) p
   funext i; fin_cases i <;> simp [W,Y,q]
omit h in
lemma center_formula {x:Points 2}(hx:x∈conf 2)(p:S.Field 4):
    S.classMoment (selected F) (fun _=>4) x (fun _=>p)=
      S.classMoment (selected F) (fun _=>4) x (fun _=>centerIn S (selected F) p) + (euclideanVEV S (selected F) p)^2 :=by
   let X:= S.classMoment (selected F) (fun _:Fin 2=>4) x; let c:= (euclideanVEV S (selected F) p); let b:= centerIn S (selected F) p; let y:= S.unit 4
   have ht:b+c • y=p:= sub_add_cancel ..
   have ha(i j:S.Field 4): X ![i,j]= X.toLinearMap ![0,j] 0 i:=by
       change _= X (update _ _ _); congr 1; exact funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)
   have hb(i j:S.Field 4): X ![i,j]= X.toLinearMap ![i,0] 1 j:=by
       change _= X (update _ _ _); congr 1; exact funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩)
   change X _=X _+ c^2
   rw [show (fun _:Fin 2=> p)= ![b+c • y,p] from funext (Fin.forall_fin_two.mpr ⟨ht.symm,rfl⟩),show (fun _:Fin 2=>centerIn S (selected F) p)= ![b,b] from funext (Fin.forall_fin_two.mpr ⟨rfl,rfl⟩), ha, map_add, map_smul,← ha,← ha,show X ![y,p]=c from unit_front F hx p]
   rw [show X ![b,p]= X ![b,b] from ?_];rw[smul_eq_mul,pow_two]
   rw[← ht,hb,map_add,map_smul,← hb,← hb, show X ![b,y]=0 from ?_, smul_zero,add_zero]; exact (unit_back F hx b).trans (centerIn_vac (selected_respects _) (selected_hierarchy _) _)
lemma uncentered_scalar (g f:ℝ→ℝ)(P:ℝ→change S 4)(hp:Coupling G g)(ht:TendC F P f)
    (he:EuclideanAsymptotic F (award G)) (x:Points 2)(hx:x∈conf 2):
    Tendsto (fun s=> S.classMoment (selected F) (fun _=>4) (s • x) (fun _=>P s (stepField C)))
      trail (𝓝 ((F₀).classMoment (F₀) (fun _=>4) x (fun _=>stepField C))):=by
   have hp:= (centered_scalar F h g f P hp ht he x hx).add ((disappearing F h g f P hp ht).pow 2)
   rw [zero_pow (by norm_num),add_zero] at hp
   exact hp.congr' ((show ∀ᶠ i:ℝ in trail,0 < i from self_mem_nhdsWithin).mono fun i hi=> (center_formula F (Work.A05.smul_conf hi hx) _).symm)
end YM.Trace.Link
