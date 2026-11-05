import YM.MultipleContact.Multi.Dues

/-! Decoding one signed branch at a time, under polynomial-template limits on their common cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.MultipleContact.ScheduleRow
open Filter Set Function MeasureTheory Extraction Table Ward MergeProof Ribbons Cells Next.UVStress Wilson Lattice Arbor
open Script Scene Bunching
open Accent Matching
open RG Bunching.Cord
open Drama
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable {b:ℕ}{n d: Fin b → ℕ}
variable [∀i,Inhabited (Fin (n i))]{v:∀i:Fin b,Fin (n i) → C.book.Token}
variable (D : ∀ i:Fin b,Detector S (d i))
variable (hA:Acme.Aroma C)(hT:Treasury C){ε:ℝ}
variable (hF:CellHyp C F)(H:S.Hierarchy)(hm:F.PointLimits C S)(hc:C.Makes)
variable (lamp:Lattice.Side)
variable {M J : ℕ}{m j:Fin b→ℕ}{g:Fin b→Mode}{A:Fin b→ℝ}{B:ℝ}{ρ:Fin b→ℝ}
variable {xe:∀i:Fin b,Fin (n i)→ E4}
variable (hsa:∀i:Fin b,g i ≠ .fused → ‖(0:ℂ)‖≤1)
variable (hPortion:∀i:Fin b,Portion C F (d i) (v i) J (m i) (j i) lamp ε (A i))
variable (hTail:∀i:Fin b,tail C (ρ i) (m i)) (h0:∀i,0 < ρ i)
variable (hBand:∀i:Fin b,g i ≠ .fused → Band (n i) lamp (ρ i) (xe i)) (hPlaced:∀i:Fin b,g i=.signed→∀ k:Fin (n i)×Axis,Placed _ (C.S.a (j i)) (xe i) k)
-- layout constants (only detector-alone budget here)
variable (hJ:M ≤ J) (hfit:∀ k:Fin b,∀ e:(D k).probes,((e.val.n+1:ℕ):ℝ)*(6*C.S.a J)< C.S.a M)
variable (hfar:∀ k:Fin b,∀ e:(D k).probes,Drama.far (C.S.a M) e.val.point.ofLp)
variable (hBudget:∀ k:Fin b,∀ e:(D k).probes,∀ i:Fin e.val.n,Wage F C (Drama.Unit C ((e.val.letter i).2)) J B)
variable {x:Π i:Fin b,Fin (n i) → Cover}{u:Π i:Fin b,ℕ×ℕ → C.book.Ref (d i)}
variable {fl:Filter (ℕ×ℕ)}[hN:fl.NeBot]
include hPortion hTail hBand h0 hc H hm hJ hfit hfar hBudget
lemma closed_raw (k:Fin b)(hsk:g k=.signed){y:C.book.Ref (d k)}
        (hf:fl ≤ F.fuse)(hr:(xe k)=C.S.gridPoint (j k) ∘ (x k))(hX: ∀ a:Axis,Injective (fun s:Fin (n k)=>xe k s a))
        (hW:Wage F C (Loss C (j:=j k) (x k) (v k) (charge (v k) (d k) (m k)) (u k)) J (A k)) (hv:Tendsto (u k) fl (𝓝 y))
        (e:(D k).probes):
           ‖((charge (v k) (d k) (m k):ℝ):ℂ) • raw S (S.classTokens∘v k) (points (xe k)) e.val - response S _ e.val (S.project _ y)‖ ≤ (A k)*(B^e.val.n):=by
       let x':=xe k; let V':=S.classTokens∘v k
       have hu (i:Fin (n k)):= (hPortion k).small (ρ k) (h0 k) (hTail k) _ (hBand k (hsk.symm ▸ (by decide))) i
       have hx(i:Fin (n k)): ‖xe k i‖ ≤ C.S.a M:= (a_mono C.S hJ).trans' (by nlinarith only [hu i,norm_nonneg (xe k i)])
       have hv':Injective (xe k):=fun a b h=> hX 0 (congr_arg (fun y:E4=>y 0) h)
       have hj: joint e.val (points (xe k))∈conf _:=joint_clear e.val (δ:=4*C.S.a M) (fun i=>?_) _ (fun i=>?_) hv'
       · rw [← strict_packet S H.laws.toSymmetric e.val V' x' hj,← prospect_cost S H.laws.toSymmetric e.val,← map_smul,← map_sub]
         rw [← smul_mul_assoc,← sub_mul]
         simpa using! probe_ticket (A:=A k) hN hW e.val (fun _=>B) (hBudget k e) hr hX hx H hm hv hf hJ (hfit k e) (hfar k e) hc
       · -- hfar argument order
         rw [norm_sub_rev]; exact (hfar k e 0 i.succ (Fin.succ_ne_zero i).symm).le
       exact (hx i).trans_lt (by linarith only [C.S.a_pos M])

set_option maxRecDepth 50000
omit hPortion hTail hBand h0 hc H hm hJ hfit hfar hBudget
lemma decode_hold (D : ∀ i:Fin b,Detector S (d i)) (B:ℝ):
       ∃K> (0:ℝ),∀ k:Fin b,∀ V:Fin (n k) → S.Tag,∀ Y: Fin (n k) → E4,∀ y:S.Field (d k), ∀ c:ℝ,∀ A> (0:ℝ),(∀e:(D k).probes, ‖(c:ℂ) • raw S V (points Y) e.val-response S (d k) e.val y‖ ≤ A*(B^e.val.n))→
           ‖c • (D k).apply V (points Y) - y‖ ≤ K*A:=by
       let P' := Sigma fun i:Fin b=>(D i).probes; let κ(s:P'):=B^s.snd.val.n
       obtain ⟨B',hB''⟩:=Finite.bddAbove_range κ
       let f i:=LinearMap.toContinuousLinearMap (D i).decode
       obtain ⟨Z',hZ⟩:=Finite.bddAbove_range (fun i=> ‖f i‖)
       have hB'':∀i:P',κ i≤ max 1 B':=fun i=> (le_trans (hB'' (mem_range_self _)) (le_max_right ..))
       refine ⟨max 1 B'*max 1 Z',by have hb:(1:ℝ)>0:=zero_lt_one; positivity,?_⟩
       intro k V Y y c A hA hr
       let μ(e:(D k).probes):= raw S V (points Y) e.val; let τ(e:(D k).probes):=response S (d k) e.val y
       have hx:= (LinearMap.toContinuousLinearMap ((D k).decode)).le_opNorm ((c:ℂ) • μ-τ)
       change ‖(D k).decode ((c:ℂ) • μ-τ)‖ ≤ ‖f k‖*_ at hx; rw [map_sub,map_smul,(D k).fixes y] at hx
       have he := hx.trans (mul_le_mul (hZ (mem_range_self k)|>.trans (le_max_right 1 _)) ((pi_norm_le_iff_of_nonneg (by have h:=le_max_left 1 B'; positivity : 0≤A*max 1 B')).mpr (fun i=>by change ‖(c:ℂ) • μ i-τ i‖ ≤_;exact (hr i).trans (mul_le_mul_of_nonneg_left (hB'' ⟨k,i⟩) hA.le))) (norm_nonneg _) (show (0:ℝ) ≤ max 1 Z' from zero_le_one.trans (le_max_left ..)) )|>.trans_eq (show _ = max 1 B'*max 1 Z'*A by ring)
       exact he
end YM.MultipleContact.ScheduleRow
