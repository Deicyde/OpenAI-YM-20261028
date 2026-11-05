import YM.MultipleContact.Multi.Fuel
import YM.MultipleContact.Multi.Relax
/-! Margins around live paths for finite comparators. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
noncomputable section
namespace YM.MultipleContact.Joins
open Filter Set Function MeasureTheory Extraction Table Ward MergeProof Acme Ribbons Cells Next.UVStress Wilson Lattice Arbor
open Script Scene Bunching
open Accent Matching
open RG Bunching.Cord
open Drama ScheduleRow
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}
variable {b:ℕ}{n d:Fin b→ℕ} (V:∀i:Fin b,Fin (n i)→S.Tag) (D:∀i:Fin b,Detector S (d i)) (p:Fin b → Mode)
variable [hn:∀i,Inhabited (Fin (n i))]
lemma collar_pos {κ:ℝ}(hκ:0<κ):∃ a> (0:ℝ), 4*a < κ ∧ ∀ k:Fin b, ∀ e∈(D k).probes, ∀ i:Fin e.n,a< ‖e.point i.succ - e.point 0‖:=by
       choose δ hD hh using fun k=> detector_clearance (D k)
       have h : ∀ᶠ a:ℝ in 𝓝 (0:ℝ),4*a<κ ∧ ∀k:Fin b,a<δ k:= (((continuous_const (y:=(4:ℝ))).mul continuous_id|>.tendsto (x:=(0:ℝ))).eventually (gt_mem_nhds (show 4*(0:ℝ)<κ from by linarith)) |>.and (eventually_all.mpr fun k=>gt_mem_nhds (hD k)))
       obtain ⟨a,ha,h0,v⟩:=Eventually.exists ((show ∀ᶠ a:ℝ in 𝓝[>]0,0<a from self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)).and (h.filter_mono nhdsWithin_le_nhds))
       refine ⟨a,ha,h0,fun k e he i=> ((v _).trans (lt_mul_of_one_lt_left (hD k) one_lt_two)).trans_le (hh k e he i)⟩

variable {t:ℕ}
lemma band_inj {x:Fin t → E4}{t':Side}{r:ℝ}[Inhabited (Fin t)](h:Band t t' r x)(hr:0<r):Injective x:=fun i j hi=> Classical.byContradiction fun hij=> norm_pos_iff.mp ((div_pos hr (by norm_num : (0:ℝ)<16)).trans (h.2.1 i j hij)) (sub_eq_zero.mpr hi)
lemma band_of_near {x:Fin t → E4}{t':Side}{r:ℝ}[Inhabited (Fin t)](h:Near t t' r x)(hr:0<r):Band t t' r x:= ⟨h.1,fun i j hij=>(by linarith only [h.2.1 i j hij,hr]),fun i=>(h.2.2 i).trans_le (by gcongr; exact by norm_num)⟩
lemma band_avoids {k:Fin b}(L:Lattice.Side){ρ bnd:ℝ}{j:Axis}(s t:ℝ){plane:Fin (n k) → E4}{pt:Fin (n k)} (hb:Band (n k) L ρ (Cord.polar (pt,j) plane s t))(hbnd: ρ < bnd/(4*L.val))(hD:∀e∈(D k).probes,∀ l:Fin e.n,bnd< ‖e.point l.succ - e.point 0‖):∀e∈(D k).probes,∀i:Fin (n k),∀l:Fin e.n,moved (e.point 0) plane pt j s t i≠ e.point l.succ:=by
        intro e he i l ht
        have h:= hb.2.2 i; have hx : e.point l.succ = e.point 0 + Cord.polar (pt,j) plane s t i:= by rw [← ht]; unfold Cord.polar moved; simp only [streak,Ward.inc,mul_smul]
        specialize hD e he l; rw [hx,add_sub_cancel_left] at hD
        have hhx:= (lt_div_iff₀ (show (0:ℝ)<4*(L.val:ℝ) from mul_pos (by positivity) (by exact_mod_cast L.pos))).mp hbnd
        linarith

lemma cost_grid {ε κ:ℝ}{L:Side}(hA:Acme.Aroma C)(hT:Treasury C)(hF:CellHyp C F)(H:S.Hierarchy)(hm:F.PointLimits C S)(hc:C.Makes)(hε:0<ε)(hκ:0<κ):
       ∃ (K:ℝ)(t:Fin b →ℝ)(j:Fin b→ℕ→ℕ)(M:ℕ),0 < K ∧ (∀i:Fin b,1< t i ∧ Tendsto (j i) atTop atTop ∧ Tendsto (fun m:ℕ=>C.S.scale (j i m)/C.S.scale m) atTop (𝓝 (t i))) ∧
          ∀ (m:Fin b → ℕ)(r:Fin b→ℝ), (∀ i,M ≤ m i ∧ 0<r i ∧ tail C (r i) (m i))→ ∀z:Fin b→E4, Close z κ → ∀x:∀i:Fin b,Fin (n i) → E4,(∀i,p i≠.fused→Band (n i) L (r i) (x i)) → (∀i,p i=.signed →∀ a,Placed (n i) (C.S.a (j i (m i))) (x i) a) → ∀u:∀i:Fin b,S.Field (d i),(∀i:Fin b,p i=.fused→‖u i‖≤1)→
         ‖evaluation S (planted p V D z u x)‖ ≤ K*due V D p r ε:=by
        let v(i a):= expose (V i a); obtain ⟨K,t,j,k,M,hK,hJ,ht,H⟩:=engineering (v:=v) D hA hT hF H hm hc L hε hκ p
        refine ⟨K,t,j,M,hK,ht,fun m r hm z hz x hx hp u hu=>?_⟩
        have h:=H m r hm z (fun i j hij=> hJ.trans_le (hz i j hij)) x hx hp _ hu
        convert h using 1
        · have he(i):V i=S.classTokens ∘ v i:=by funext a; unfold v; rw [comp_apply,expose,classTokens]; exact (congr_arg (fun t:S.Field (V i a).1=>(⟨(V i a).1,t⟩:S.Tag)) (S.rep ..)).symm
          simp_rw [planted,he] -- simp maybe loops, he rewrite V to expression includes v defeq!
        congr 1
        apply Finset.prod_congr rfl
        intro i _; unfold weight scaleMap; cases hp:p i <;> first | rfl | simp only [Real.rpow_zero]
end YM.MultipleContact.Joins
