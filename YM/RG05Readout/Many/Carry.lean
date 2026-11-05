import YM.RG05Readout.Many.Channel
/-!
# Labelled density aggregation

The license for grouping alternatives carries anchored receipts and evaluated
log/K modes without a copy-count penalty. Repercussions include retaining the
EXACT individual counterterm profiles per grouped marker for use on this same
Serve. Works on the constrained Census chosen step by step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Finset Filter MeasureTheory Set
open Marker MergeProof Accent Lattice RG Wilson Extra Multi
open Push GridApprox.Nil Ac Extra.Trajectories
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {V W I Y : Type*}[DecidableEq V][DecidableEq W]
variable {B:Census V}{C:Census W}{δ:V→W}(h:License C B δ) (a:V→ℂ)
variable {G:Gauge}{n:Side}{w:V→ℝ}{w':W→ℝ}
local notation "P"=> feed a h

theorem carries {F:Y→Poly B}{c:ℝ}(h1:Loci w F c)(hP:∀ i, w' (δ i)*‖a i‖ ≤ w i)(hw:∀ i,0 < w i)(hW:∀ i,0<w' i) : Loci w' (fun U=>(P) (F U)) c:=by
    obtain ⟨f,hf,h,hX⟩:= h1
    let g(x:B.Mode):=‖∏ i ∈ x.val,a i‖* f x
    have hg(x):0 ≤ g x:=mul_nonneg (norm_nonneg _) (hf _)
    let e(x:B.Mode)(y:C.Mode):= if ht:Lit C δ x.val then if y=ht.climb then g x else 0 else 0
    refine ⟨(fun p=>∑ i:B.Mode,e i p),fun i=> Finset.sum_nonneg (fun j _=> by unfold e; split; split; exact hg _; rfl; next=>rfl),?_,?_⟩
    · intro U y; rw [parts_of_feed]
      refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun x _=>?_)); unfold move e
      by_cases ht : Lit C δ x.val; by_cases hy:y=ht.climb
      · rw [dif_pos ht,dif_pos ht,Poly.part_send,if_pos hy,if_pos hy,norm_mul]; exact mul_le_mul_of_nonneg_left (h _ _) (norm_nonneg _)
      · rw [dif_pos ht,dif_pos ht,Poly.part_send,if_neg hy,if_neg hy,norm_zero]
      rw [dif_neg ht,dif_neg ht,Poly.part_nil,norm_zero]
    unfold wordsPrice at *; refine le_trans ?_ hX
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    refine sum_le_sum (fun x _=> ?_); unfold e; split
    next ht=>
     simp_rw [mul_ite,mul_zero]; rw [sum_ite_eq',if_pos (Finset.mem_univ _)] -- check
     unfold g; rw [← mul_assoc]
     apply mul_le_mul_of_nonneg_right _ (hf _)
     simp only [Poly.toll,norm_prod,Lit.climb]; rw [prod_image, ← Finset.prod_mul_distrib]; exact Finset.prod_le_prod (fun i _=> mul_nonneg (hW ..|>.le) (norm_nonneg _)) (fun i _=> hP i)
     exact ht.2
    next he=> simp only [mul_zero,sum_const_zero]; exact mul_nonneg (Poly.worth hw _).le (hf x)
variable {M:ℕ}{d e:ℝ}
lemma carry {F:I→Y→Poly B}{r:I→Support n} (he:Towed w r F M d e)(hP:∀ i,w' (δ i)*‖a i‖ ≤ w i)(hw:∀ i,0<w i)(hW:∀ i,0<w' i) : Towed w' r (fun i U=>(P) (F i U)) M d e:=
    let ⟨f,hf,hV,hZ⟩:=he; ⟨f,hf,hV,fun i=> carries h a (hZ i) hP hw hW⟩
variable {t:ℝ}{o:V→Site n}{q:W→Site n}
    {r:Support n}{F:Config G n→ Poly B}
lemma exact_borne (ht:o=q ∘ δ)(hb:Borne o r F t) : Borne q r (fun U=>(P) (F U)) t:=by
    refine ⟨fun U V h j=>congr_arg (fun p=> (feed a _) p) (hb.home U V h j),fun s U=> ?_,fun i=> ?_,fun U i hc=>?_⟩
    · exact congr_arg (fun p=>(P) p) (hb.turns s U)
    · simp_rw [parts_of_feed]; refine Finset.measurable_fun_sum _ (fun j _=>?_); unfold move
      split
      next g=> simp_rw [Poly.part_send]; split; exact (hb.me j).const_mul _; exact measurable_const
      next=> exact measurable_const
    rw [parts_of_feed]; refine sum_eq_zero (fun j _=> ?_); unfold move; split
    next hp=> rw [Poly.part_send]; split
              next he=> rw [hb.scope _ j ?_,mul_zero]
                        intro hb'; apply hc
                        intro v hv; rw [he] at hv; obtain ⟨v',hv',rfl⟩:=mem_image.mp hv; change q (δ v')∈r; rw [← Function.comp_apply (f:=q) (g:=δ), ← ht]; exact hb' hv' -- syntax
              next=> rfl
    next=> rfl
lemma carry_flow {x:Box n} (ht:o=q ∘ δ)(hX:Flow o x F t) : Flow q x (fun U=>(P) (F U)) t:= ⟨exact_borne h a ht hX.toBorne,fun U hU=> hX.permits U (fun H=> hU (H ▸ map_zero (P)))⟩ -- hU ▸ issue
lemma carry_burns (ht:o=q ∘ δ)(hX:Burns o r F t) : Burns q r (fun U=>(P) (F U)) t:= ⟨exact_borne h a ht hX.toBorne,fun U hU=>hX.permits U (fun H=> hU (H ▸ map_zero (P))),fun U=> (feed_quiet ..).trans (hX.sil U)⟩
lemma still_rises {p:Poly B}(he:rises p) : rises ((P) p):=by
    intro i h'; rw [parts_of_feed] at h'
    obtain ⟨u,_,hU⟩:= exists_ne_zero_of_sum_ne_zero h'
    unfold move at hU; split at hU
    next ha=>
     rw [Poly.part_send] at hU; split at hU
     next hp=> rw [hp,ha.keep_count]; exact he u (right_ne_zero_of_mul hU)
     next=> contradiction
    next=> exact False.elim (hU (Poly.part_nil i))

lemma carry_field (r : Box n→ Poly B)(v:Support n): (P) (Accent.field r v) = Accent.field (fun i=>(P) (r i)) v:=by
    unfold Accent.field; rw [map_sum]; refine sum_congr rfl (fun i _=> ?_); unfold grid; split; exact map_prod ..; exact map_zero _

section big
variable [Fintype V][Fintype W] {R:Rep G n}
lemma carry_play {F:Config G n→Poly B}{K:Box n→ Config G n→Poly B}(hr:∀ U,(F U).part B.quiet=0):
     (fun U=>(P) (play R B K F U))=play R C (fun i U=>(P) (K i U)) (fun U=>(P) (F U)):=by
    funext U; unfold play; rw [map_smul,map_mul, carry_field,YM.Multi.pass_map (P) _ (hr U) ((feed_quiet ..).trans (hr U))]
omit [Fintype V] [Fintype W] in
lemma carry_carton {S:Support n→ Config G n→ Poly B}{K:Box n→ Config G n→Poly B}(ht:o=q ∘ δ)(hr:Carton o S K t):
    Carton q (fun i U=>(P) (S i U)) (fun i U=>(P) (K i U)) t:=
    ⟨fun i=>⟨carry_burns h a ht (hr.exp i).1,fun U=>still_rises h a ((hr.exp i).2 U)⟩,fun i=>⟨carry_flow h a ht (hr.flag i).1,fun U=>still_rises h a ((hr.flag i).2 U)⟩⟩
-- require Prescribed singleton read at new marker via equation. Accept ANY singles evaluated. `play` distinction.
lemma carry_restore {Φ:V→ Config G n→ℂ}{κ:V→ Box n→ Config G n→ℂ}
    {Z:Support n→ Config G n→Poly B}{G':Box n→ Config G n→Poly B}
    (hp:Carton o Z G' R.p.threshold) (U: Config G n) :
       (P) (restore R Φ κ Z G' U)= restore R (fun i U' =>∑ j:V,if δ j=i then a j*Φ j U' else 0) (fun i p U'=>∑ j:V, if δ j=i then a j*κ j p U' else 0) (fun i U'=>(P) (Z i U')) (fun i U'=>(P) (G' i U')) U:=by
    unfold restore; let v:=(Mach B fun i=>Φ i U)+∑ i,Z i U
    have he:v.part B.quiet=0:=by unfold v; rw [Poly.part_plus,mute B _,Poly.part_sum]; simp only [show ∀ i,(Z i U).part B.quiet=0 from (fun i=>(hp.exp i).1.sil _),sum_const_zero,add_zero]
    rw [map_smul,map_mul,YM.Multi.pass_map (P) v he ((feed_quiet ..).trans he)] -- v defeq?
    unfold v; rw [map_add,feed_mach,map_sum, carry_field]
    simp only[map_add,feed_mach]; congr 3
    funext j; unfold Accent.bar; rw [show (P) (Poly.bead B _) = Poly.bead C _ from (P).commutes _]
lemma carry_served {Φ:V→ Config G n→ℂ}{κ:V→ Box n→ Config G n→ℂ}
    {Q:Config G n→Poly B}(ht:o=q ∘ δ) (hm:Served R Φ κ Q o w d e)(hP:∀ i,w' (δ i)*‖a i‖ ≤ w i)(hw:∀ i,0<w i)(hW:∀ i,0<w' i) :
    Served R (fun i U=>∑ j:V, if δ j=i then a j*Φ j U else 0) (fun i p U=>∑ j:V, if δ j=i then a j*κ j p U else 0) (fun U=>(P) (Q U)) q w' d e:=
    let ⟨_,_,hZ,hf,hE,hQ⟩:=hm; hQ ▸ ⟨_,_,carry_carton h a ht hZ,carry h a hf hP hw hW,carry h a hE hP hw hW,funext fun U=> carry_restore h a hZ U⟩ -- likely hQ orientation
end big
end YM.RG05Readout.Many
