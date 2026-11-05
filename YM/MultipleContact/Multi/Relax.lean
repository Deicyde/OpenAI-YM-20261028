import YM.MultipleContact.Multi.Store
/-! Throwing away just the cancellation in one branch in a path derivative estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
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
variable {P:DiffPlan S}(hA:Acme.Aroma C)(hT:Treasury C)(hc:CellHyp C F)(hM:F.PointLimits C S)(H:S.Hierarchy)(hP:P.Derivatives S)(hC:C.Makes)
variable {X:S.Rotation}(hX:X.Oriented S)(hG:G.Simple)
variable {t:ℕ}{k:Fin b} (h:Store S t) (N:Lattice.Side)(hk:p k=.signed)(hb:(Finset.univ.filter fun i=>p i=.signed).card ≤ t+1) (κ ε:ℝ)(hs:0<κ)(hε:0<ε)
include hP hA hT hc hM H hC hG hX h hk hb hs hε
lemma weaker :∃ (A r:ℝ),0<A ∧ 0<r ∧ ∀ z:Fin b → E4, Close z κ → ∀ρ:Fin b → ℝ, (∀i,0<ρ i ∧ ρ i < r)→ ∀ y:∀i:Fin b,Fin (n i) → E4,(∀i:Fin b,p i ≠.fused → Cord.Band (n i) N (ρ i) (y i)) →∀w:∀i:Fin b,S.Field (d i),(∀i:Fin b,p i=.fused→‖w i‖≤1)→
     ‖evaluation S (planted p V D z w y)‖ ≤ A*due V D (update p k .raw) ρ ε:=by
       let q := update p k .raw; let s:=update p k .fused
       have hCard (c:Mode)(hi:c≠.signed): (Finset.univ.filter (fun i=>update p k c i=.signed)).card ≤ t:=by have hh:= card_mask _ _ hk _ hi; omega
       obtain ⟨A,R,hA',hR,h'⟩:=banded V D q h N (hCard .raw (by decide)) κ ε hs hε
       obtain ⟨B,R',hB,hR',H₁⟩:=banded V D s h N (hCard .fused (by decide)) κ ε hs hε
       obtain ⟨E,r,he,hr,H₂⟩:=apply_cost (D:=D k) (V:=V k) hA hT hc hM H hP hC hX hG hε N -- ensure let
       refine ⟨A+E*B,min r (min R R'),add_pos hA' (mul_pos he hB),lt_min hr (lt_min hR hR'),fun z hz ρ hρ y hy v hV' => ?_⟩
       have hxL (i:Fin b):0< ρ i ∧ ρ i < min R R':=⟨(hρ i).1, (hρ i).2.trans_le (min_le_right ..)⟩
       have hx:=h' z hz ρ (fun i=>⟨(hρ i).1,(hxL i).2.trans_le (min_le_left ..)⟩) y (fun i hi=>by
              by_cases he:i=k
              · exact hy _ ((he.symm ▸ hk).symm ▸ (by decide))
              exact hy _ ((show q i=p i from update_of_ne he ..) ▸ hi)) (update v k (v k)) (fun i hi=>by
              by_cases he:i=k
              · rw [he] at hi; simp only [q,update_self] at hi; exact Mode.noConfusion hi
              simp only [q,update_of_ne he] at hi ⊢
              exact hV' i hi)
       let φ := (D k).apply (V k) (points (y k))
       let f(z' : Fin b→ E4)(q':Fin b→Mode)(u:S.Field (d k)):= evaluation S (planted q' V D z' (update v k u) y)
       let α':= rest V D p k z v y
       have hbase: evaluation S (planted p V D z v y) = f z q (v k) - f z s φ:=by
          let G (r:Mode)(w:S.Field (d k)):= planted (update p k r) V D z (update v k w) y
          unfold f q s
          conv_lhs =>
             rw [show p=update p k .signed from (by rw [← hk,update_eq_self]), show v=update v k (v k) from update_eq_self ..|>.symm]
          rw [← map_sub]
          apply congr_arg (evaluation S)
          rw [split_product V D p,split_product V D p,split_product V D p, scaledBranch]; unfold scaledBranch; rw [one_smul, Complex.ofReal_one,one_smul]; exact sub_mul ..
       have hConfig(i:Fin b)(hi:s i ≠ .fused):Band (n i) N (ρ i) (y i):=by
           have he:i≠k:=fun h=>hi (h.symm ▸ (by simp [s])); exact hy _ ((show s i = p i from update_of_ne he ..) ▸ hi)
       have hS(u:S.Field (d k))(hh:‖u‖ ≤ 1): ‖f z s u‖ ≤ B*due V D s ρ ε:= H₁ z hz ρ (fun i=>⟨(hρ i).1,(hxL i).2.trans_le (min_le_right ..)⟩) y hConfig (update v k u) fun i hi=>by
              by_cases he:i=k
              · subst i; rw [update_self]; exact hh
              change update p k .fused i=_ at hi; rw [update_of_ne he] at hi ⊢; exact hV' i hi -- fix
       have hse (u:S.Field (d k))(c:ℂ):f z s (c • u)=c • (f z s u):=by
           unfold f s; simp_rw [split_product]; change evaluation S ((insertion S (z k) (c • u))*_)=c • evaluation S ((insertion S (z k) u)*_);unfold insertion; exact Scene.inline_smul S H.laws.toSymmetric _ _ _ _
       have hAbs : ‖φ‖ ≤ E*((ρ k)^(-(massOf (V k):ℝ)-ε)):= (H₂ (ρ k) (hρ k).1 ((hρ k).2.trans_le (min_le_left ..)) _ (hy k (hk.symm ▸ (by decide))))
       have hhφ : ‖f z s φ‖ ≤ ‖φ‖*(B*due V D s ρ ε):=by
          by_cases h':φ=0
          · rw [h', show f z s (_: S.Field (d k))=(0:ℂ) from (by simpa using hse (0 : S.Field (d k)) 0) ]; simp
          let α:= ((‖φ‖:ℂ))⁻¹ • φ
          have hxα: ‖α‖ ≤ 1:= by rw [show ‖α‖=‖((↑‖φ‖:ℂ))⁻¹‖*‖φ‖ from norm_smul _ _, norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ (norm_ne_zero_iff.mpr h')]
          have hwα: (↑‖φ‖:ℂ) • α = φ:=by unfold α; rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast norm_ne_zero_iff.mpr h'),one_smul]
          change ‖f z s φ‖≤ ‖φ‖ *(B * due V D s ρ ε)
          have hnorm: ‖(↑‖φ‖:ℂ) • f z s α‖=‖φ‖ * ‖f z s α‖:=by rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
          rw [← hse,hwα] at hnorm; rw [hnorm]; exact mul_le_mul_of_nonneg_left (hS _ hxα) (norm_nonneg _)
       rw [hbase]
       calc ‖f z q _- _‖ ≤ _:=norm_sub_le ..
            _ ≤ A * due V D q ρ ε + E * ((ρ k)^(-(massOf (V k):ℝ)-ε)) * (B * due V D s ρ ε) := add_le_add hx (hhφ.trans (mul_le_mul_of_nonneg_right hAbs (show 0 ≤ _ from mul_nonneg hB.le (weight_pos V D s _ (fun i=>(hρ i).1) |>.le))))
            _ = (A+E*B)*due V D _ _ _ := by
                have hu:=weight_split V D q (k:=k) (show q k=.raw from update_self ..) ρ ε
                change A*due V D q ρ ε + _ = (A+E*B)*(due V D q ρ ε) -- change syntax
                unfold q at hu; rw [update_idem] at hu
                rw [show due V D q ρ ε= _ from hu];unfold s;ring
end YM.MultipleContact.Joins
