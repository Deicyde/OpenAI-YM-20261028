import YM.UVExtension.Fallow.Flax
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Fallow
open Finset Filter Function MeasureTheory Set Lattice Wilson RG Cells Extraction Push GridApprox Hearth
open Lease Dash Work.D03
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {S:Schedule}{s:Side}{G:Gauge}{C:Family G}{d N p n:ℕ}(H:Vintage.YM.Family.Makes C) (K:Extraction.Wcmain C)

def entry (F:Stem C p)(a:Axis): Stem C p:= fun i=> ((C.S.a i:ℂ)⁻¹) • (bloom (F i) (step a) - F i)
lemma pushed (F:Stem C p)(a:Axis)(o:Site (C.side N p)) : bloom (entry F a N) o= ( (C.S.a N:ℂ)⁻¹) • (bloom (F N) (o+step a) - bloom (F N) o):=by
    rw [add_comm o, literal]; rfl
lemma box_one (a:Axis): step a ∈ GridApprox.window (0:Site s) 1:=by
    refine ⟨(step a:Cover),box_test.mpr ⟨fun i=>?_,fun i=>?_⟩,?_⟩
    · by_cases he:a=i; · subst i; simp
      simp [he,step,Ne.symm he]
    · by_cases he:a=i; · subst i; simp
      simp [he,step,Ne.symm he]
    dsimp only; rw [add_zero,wrap_step]
lemma tending {F:Stem C p}(h:Pasted F) (a:Axis): Pasted (entry F a):=by
   obtain ⟨r,hr⟩:=h; refine ⟨1+r,?_⟩; filter_upwards [hr] with i hi; let v:Site (C.side i p):=step a; have hx:= translated_window v hi; rw [zero_add] at hx
   apply Interior.scale; apply Next.UVStress.minus (hx.enlarges (fun x hu=> window_add (box_one a) (show _ from hu))) (hi.enlarges (window_large (by omega)))
-- exact difference
lemma agenda (F:Stem C p) (he:Envelope (F N)) (a:Axis)(I:Shot C.book)(r: Fin I.n→Site (C.side N p)):
    lyric I (entry F a) N r= ( (C.S.a N:ℂ)⁻¹)*(lyric I F N (r+jump I.i a (A:=Per (C.side N p))) - lyric I F N r):=by
   rw [lyric_point,lyric_point,lyric_point,pushed]; let Z (U: Config G (C.side N p)):= ∏ i∈Finset.univ.erase I.i,C.seen (I.left i) (r i) U
   have hZ: Envelope Z:=Envelope.prodC _ _ fun i _=> Envelope.compactC (C.continuousO ..)
   have he(o:Site (C.side N p)): Integrable (fun U=> bloom (F N) o U * Z U) (law G (C.side N p) (C.beta N p)):=((he.comp_env (law_translate 0 _).measurable).mulC hZ).integrableC _
   have hw (U: Config G (C.side N p)) : (∏ i∈Finset.univ.erase I.i,C.seen (I.left i) ((r+jump I.i a (A:=Per (C.side N p))) i) U) = Z U:= Finset.prod_congr rfl fun i hi=>by rw [show (r+jump I.i a (A:=Per (C.side N p))) i = r i from by simp [jump,Finset.ne_of_mem_erase hi]]
   simp_rw [hw]; rw [show (r+jump I.i a (A:=Per (C.side N p))) I.i = r I.i+step a by simp [jump]]; unfold moment; rw [← integral_sub (he _) (he _), ←integral_const_mul]; refine integral_congr_ae ?_; filter_upwards with i; simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul]; unfold Z; ring

lemma insula (S:Schedule)(p n:ℕ): IsOpen (Extraction.Inside S p n):=by
    simp_rw [Extraction.Inside,setOf_forall]; exact isOpen_iInter_of_finite fun i=> isOpen_iInter_of_finite fun a=> (isOpen_lt continuous_const (show Continuous (fun x:Points n=> x i a) by fun_prop)).inter (isOpen_lt (show Continuous (fun x:Points n=> x i a) by fun_prop) continuous_const)
lemma no_wrap (S:Schedule)(p n:ℕ): IsOpen (Extraction.NoHit S p n):=by
    unfold Extraction.NoHit; simp_rw [setOf_forall]; apply isOpen_iInter_of_finite; intro i; apply isOpen_iInter_of_finite; intro j; apply isOpen_iInter_of_finite; intro he; rw [setOf_exists]; exact isOpen_iUnion fun a=> Extraction.not_tie_open S p i j a
section tests
variable (I:Dash.Shot C.book)(hz:suitable C.S p I.f)
include H K hz
lemma spend (F:Stem C p)(a:Axis)(h:Wealth C F): Spar (smear I (entry F a)):=by
   let W:=angle I F; let Z:= tsupport I.f
   have hp : Z ⊆ Extraction.NoHit C.S p I.n ∩ Inside C.S p I.n:= fun _ h=>⟨readable _ _ _ hz h, hz h⟩
   obtain ⟨Y,hY,hp,hX⟩:= exists_compact_between I.f.hasCompactSupport ((no_wrap _ _ _).inter (insula _ _ _)) hp
   obtain ⟨r,hr,hp'⟩:= I.f.hasCompactSupport.exists_thickening_subset_open isOpen_interior hp
   have hI (i): Wealth C (W i):=by
     by_cases he : i=I.i; · subst i; rw [show W _= _ from Function.update_self ..]; exact h
     rw [show W i= _ from (Function.update_of_ne he .. : update (fun j=> plant (I.left j) p) I.i F i= plant (I.left i) p)] -- arg order
     exact (thorC H K p (Spar.rating ((I.left i).2))).wealth
   obtain ⟨D,hD,hG⟩:=Fallow.cover H W Y hY (fun _ h=> (hX h).1) hI
   obtain ⟨t,ht,hA⟩:= Order.testSup (Dash.down I.f I.i a)
   refine ⟨(Extraction.length C.S p)^(4*I.n)*((1+t)*D),?_⟩
   filter_upwards [hG,h.1.blast,C.S.shrinks.eventually (gt_mem_nhds hr), uniform I.f I.i a C.S (by exact zero_lt_one)] with N hG hK hR hs
   let g := Points.direction I.i a; let c:=C.S.a N; have hu :0<c:= C.S.a_pos N; have hw : ∀ y∈Z,y+c • g∈Y:=by
      intro y hy; apply interior_subset (hp' (Metric.mem_thickening_iff.mpr ⟨y,hy,?_⟩)); rw [dist_eq_norm,add_sub_cancel_left,norm_smul, Real.norm_of_nonneg hu.le]; simpa [g,Points.direction] using hR
   let V:=fun t : Fin I.n→ Site (C.side N p)=> Order.cells C N p t; unfold smear; simp_rw [agenda F hK]; rw [pair_sum (fun u=>I.f (V u)) (lyric I F N)]
   apply Work.D03.period_cost
   intro r; let x:= V r; rw [Work.D03.physical _ _ _ _ hz (fun y hy=>(hX (hw _ hy)).2)]; by_cases he:x∈Y
   · rw [norm_mul]; have hh:= hG (lift ∘ r) he; unfold patch at hh; rw [wrapR] at hh; have hV: ‖( (c:ℂ)⁻¹)*(I.f (x-c • g)-I.f x)‖ ≤ 1+t:=by
        let f:=Dash.down I.f I.i a; let F:= Work.D03.residue I.f I.i a c x; have hz : F-f x=( (c:ℂ)⁻¹)*(I.f (x-c • g)-I.f x):=add_sub_cancel_right ..; rw [← hz]; exact (norm_sub_le ..).trans (add_le_add (hs _) (hA _))
     exact mul_le_mul hV hh (norm_nonneg _) (add_nonneg zero_le_one ht)
   have hp : I.f (x-c • g)=0:= by_contra fun h=> he (sub_add_cancel x (c • g) ▸ hw _ (subset_closure h))
   have hW:I.f x=0:= by_contra fun h=> he (interior_subset (‹_ ⊆ interior Y› (subset_closure h)))
   rw [hp,hW,sub_zero,mul_zero,zero_mul,norm_zero]; exact mul_nonneg (add_nonneg zero_le_one ht) hD
end tests
end YM.UVExtension.Fallow
