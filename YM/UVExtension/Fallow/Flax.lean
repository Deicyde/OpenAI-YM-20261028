import YM.UVExtension.Limits
import YM.UVExtension.Fallow.Harvest
import YM.Work.D03
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Fallow
open Finset Filter Function MeasureTheory Set Lattice Wilson RG Cells Extraction Push GridApprox Hearth
open Lease Dash
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {S:Schedule}{s:Side}{G:Gauge}{C:Family G}{d N p n:ℕ}(H:Vintage.YM.Family.Makes C) (K:Extraction.Wcmain C)

def thor (v:ℕ→ C.label d)(p:ℕ): Stem C p:= fun i=> C.O i p (d:=d) (v i) 0
def plant (x:C.book.Token)(p:ℕ):Stem C p:= thor (d:=x.fst) (fun _=>x.snd) p

def Spar {V:Type*}[Norm V](x:ℕ→V):= ∃ b:ℝ,∀ᶠ N in atTop,‖x N‖ ≤ b
namespace Spar
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V] {x:ℕ→V} {r:ℕ→ℂ}
lemma rating (w:V): Spar fun _=>w:=⟨_,Eventually.of_forall fun _=>le_refl _⟩
lemma sturdy (h:Arrives x): Spar x:=by obtain ⟨T,hT⟩:=h; exact ⟨‖T‖+1,hT.norm.eventually_le_const (by linarith only)⟩
lemma plus (h:Spar x){y:ℕ→V}(hp:Spar y): Spar (x+y):=by obtain ⟨b,hB⟩:=h; obtain ⟨c,hc⟩:=hp; exact ⟨b+c,(hB.and hc).mono fun i hi=> (norm_add_le ..).trans (add_le_add hi.1 hi.2)⟩
lemma times {s:ℕ→ℂ}(h:Spar r)(p:Spar s): Spar (r*s):=by obtain ⟨b,hB⟩:=h; obtain ⟨c,hc⟩:=p; exact ⟨b*c,(hB.and hc).mono (fun i hi=> (norm_mul (r i) (s i)).trans_le (mul_le_mul hi.1 hi.2 (norm_nonneg _) ((norm_nonneg _).trans hi.1)))⟩
lemma same {y:ℕ→V}(h:Spar x)(p:x =ᶠ[atTop] y): Spar y:=by obtain ⟨c,hc⟩:=h; exact ⟨c,(hc.and p).mono (fun i hi=> hi.2 ▸ hi.1)⟩
end Spar

include H
lemma thorP (v:ℕ→ C.label d): Pasted (thor v p):=⟨stencilRadius C d,Eventually.of_forall (fun i=> Vintage.YM.Push.GridApprox.candidate_fits C H i p d ((C.factory d i p).terminal.symm (v i)))⟩
include K
lemma thorC {v:ℕ→ C.label d}(p:ℕ) (h:Spar v): Crude C (thor v p):=by
   obtain ⟨D,hD⟩:=h; obtain ⟨b,hb,hK⟩:= K d (max D 1) 1 (one_pos.trans_le (le_max_right ..)) one_pos
   refine ⟨thorP H _,?_⟩; filter_upwards [eventually_ge_atTop (C.ref d)] with i hi
   refine ⟨b*C.S.a i ^ (-(d:ℝ)-1),?_⟩; filter_upwards [hK i hi,hD] with N hN ht hk; obtain ⟨k,hh,hY⟩:=hN p (v N) (ht.trans (le_max_left ..)); exact (hY 0).2
omit H K

lemma blossoms (v:ℕ→ C.label d)(p N:ℕ)(o:Site (C.side N p)): bloom (thor v p N) o=C.O N p (d:=d) (v N) o:=by funext U; unfold bloom thor; rw [Function.comp_apply,C.translation,zero_add]
lemma flor (v:ℕ→ C.label d)(a:ℕ→ℂ): thor (d:=d) (fun i=> a i • v i) p=fun i=> a i • thor v p i:=funext fun i=> (C.linearO i p d 0).map_smul (a i) (v i)
lemma flour (v w:ℕ→ C.label d): thor (v+w) p= thor v p+thor w p:= funext fun i=> (C.linearO i p d 0).map_add ..
lemma flour' (v w:ℕ→ C.label d): thor (v-w) p= thor v p-thor w p:= funext fun i=> ((C.linearO i p d 0).mk' _).map_sub ..

section shot
-- update in every regulator. cut-wise continuity on finite forms, no interpolation used
variable (I:Dash.Shot C.book)
def angle (F: Stem C p): Fin I.n→ Stem C p:= Function.update (fun i=> plant (I.left i) p) I.i F
def lyric (F:Stem C p)(N:ℕ)(r):= garden (angle I F) N r
def smear (F:Stem C p)(N:ℕ):= (C.S.a N:ℂ)^(4*I.n)* ∑ r,I.f (Order.cells C N p r)*lyric I F N r
lemma lyric_point (F: Stem C p) (r:Fin I.n→ Site (C.side N p)): lyric I F N r= moment (C.beta N p) (fun U=> bloom (F N) (r I.i) U* ∏ i∈Finset.univ.erase I.i,C.seen (I.left i) (r i) U):=by
    unfold lyric garden angle; congr 1; funext U; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ I.i), Function.update_self]; congr 1; refine Finset.prod_congr rfl (fun i hi=> ?_); rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),plant,blossoms]; rfl
lemma scanning (v:ℕ→ C.label d) : smear I (thor v p) N= I.scan d N p (v N):=by
    change _=Extraction.Order.smears C N p (I.record _) I.f; unfold Extraction.Order.smears smear; congr 1; refine Finset.sum_congr rfl fun i _=>?_ ; congr 1; rw [lyric_point,blossoms]; rw [Family.num]; unfold moment; refine integral_congr_ae ?_; filter_upwards with U; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ I.i), Shot.record, Function.update_self]; exact congr_arg (C.O N p (v N) _ U * ·) (Finset.prod_congr rfl fun j hj=> congr_arg (fun v=>C.seen v (i j) U) (Function.update_of_ne (Finset.ne_of_mem_erase hj) ..|>.symm))
lemma smear_w (F:Stem C p)(a:ℕ→ℂ): smear I (fun i=> a i • F i) N=a N*smear I F N:=by
    unfold smear; rw [mul_left_comm (a N), Finset.mul_sum _ _ (a N)]; congr 1; refine Finset.sum_congr rfl fun i _=> ?_; rw [mul_left_comm (a N) _ _, lyric_point, lyric_point]; congr 1; unfold bloom moment; simp_rw [Function.comp_apply, Pi.smul_apply,smul_eq_mul, mul_assoc, integral_const_mul]
lemma smear_sub (F V:Stem C p)(h:Pasted F)(hp:Pasted V): ∀ᶠ N in atTop,smear I (F-V) N=smear I F N-smear I V N:=by
    filter_upwards [h.blast,hp.blast] with N hn hV; unfold smear; rw [←mul_sub,←Finset.sum_sub_distrib]; congr 1; refine Finset.sum_congr rfl fun i _=> ?_; rw [←mul_sub,lyric_point,lyric_point,lyric_point]; congr 1; unfold moment
    let X U:= ∏ j∈Finset.univ.erase I.i,C.seen (I.left j) (i j) U; have hx:Envelope X:= Envelope.prodC _ _ fun k _=> Envelope.compactC (C.continuousO N p ..)
    let β:= C.beta N p
    have ha(F')(h:Envelope F'): Integrable (fun U=>bloom F' (i I.i) U* X U) (law G (C.side N p) β):= ((h.comp_env (law_translate 0 _).measurable).mulC hx).integrableC _
    rw [←integral_sub (ha _ hn) (ha _ hV)]; refine integral_congr_ae ?_; filter_upwards with U; exact sub_mul ..

variable (hz:suitable C.S p I.f)
lemma wrapR (N:ℕ)(r:Fin I.n→ Site (C.side N p)): wrap (C.side N p) ∘ lift ∘ r=r:=funext fun i=> wrap_lift _
include hz H K
lemma faded {F:Stem C p}(hp:Faded C F): Tendsto (smear I F) atTop (𝓝 0):=by
   let X:= angle I F; have he:X I.i=F:= Function.update_self ..
   have hx i: Crude C (X i):=by
      by_cases h:i= I.i; · subst i; rw [he]; exact hp.crude
      unfold X angle; rw [Function.update_of_ne h]; exact thorC H K _ (Spar.rating _)
   let V:=tsupport I.f; obtain ⟨c,hc,hV⟩:= Order.testSup I.f
   let y:= (Extraction.length C.S p)^(4*I.n); have hy : 0<y:=by unfold y Extraction.length; positivity
   rw [Metric.tendsto_nhds]; intro ε hε; let d:= ε/(2*y*(1+c)); have hd : 0<d:= div_pos hε (mul_pos (mul_pos zero_lt_two hy) (add_pos_of_pos_of_nonneg one_pos hc))
   filter_upwards [losing H X V I.f.hasCompactSupport (readable C.S p I.f hz) hx I.i (he.symm ▸ hp) d hd] with i hi
   rw [dist_zero_right]; refine lt_of_le_of_lt (b:=y*c*d) ?_ ?_ -- simplify
   · rw [mul_assoc]; refine (Work.D03.period_cost C.S _ (c*d) (fun t=>?_)) -- show
     rcases eq_or_ne (I.f (Order.cells C i p t)) 0 with h|h
     · rw [h,zero_mul,norm_zero]; exact mul_nonneg hc hd.le
     rw [norm_mul]; have ht:=hi (lift ∘ t) (show _ from subset_closure h); unfold patch at ht; rw [wrapR] at ht; exact mul_le_mul (hV _) ht (norm_nonneg _) hc
   have hq: (2*y*(1+c))*d= ε:=by unfold d; field_simp
   nlinarith only [hq,hy,hd,hc,mul_pos hy hd,hε]
omit K
lemma ghost {F:Stem C p}(hp:Cloud C F): ∀ᶠ N in atTop,smear I F N=0:=by
   let X:= angle I F; have he:X I.i=F:= Function.update_self ..
   have hx i: Pasted (X i):=by
      by_cases h:i= I.i; · subst i; rw [he]; exact hp.same
      unfold X angle; rw [Function.update_of_ne h]; exact thorP H _
   filter_upwards [fading X (tsupport I.f) I.f.hasCompactSupport (readable C.S p I.f hz) hx I.i (he.symm ▸ hp)] with i hi; unfold smear; rw [Finset.sum_eq_zero _ ,mul_zero]
   intro t _; rcases eq_or_ne (I.f (Order.cells C i p t)) 0 with h|h
   · rw [h,zero_mul]
   have ht:=hi (lift ∘ t) (show _ from subset_closure h); unfold patch at ht; rw [wrapR] at ht; rw [show lyric I F _ _=0 from ht,mul_zero]
end shot
end YM.UVExtension.Fallow
