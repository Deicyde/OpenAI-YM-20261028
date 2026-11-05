import YM.MergeProof.West.Dink
import YM.Next.RANK.Zephyr
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open MeasureTheory Cells Edition Filter
variable {G:Gauge}{N n p k q i l j d D m u:ℕ} {C:Family G}{x:Points m} {ξ:Purse} {R:Lead G C.S p} {c:Course C N p k}{P:(i:ℕ)→ Rep G (C.side i p)}{s:ℝ}{Ψ:AtlasData G C.S p}
variable {V:Fin m→poly (Chamber G C.S k p)} (F:Ceremony ξ c P R Ψ)(H:Kith (A:=C.path.levels) V x ξ)
    (Q:Caff (G:=G) ξ (clim C.path.levels k) (k-middle C.path.levels ξ.band k) u m)

include Q F H
lemma festival (v:modes (Fin m)):
   let A:=C.path.levels;let s:=clim A k; let h:=before A ξ.band k; let f:= vista R V h v; let f':= vista (track Ψ) V h v
   (f-f').totalDegree≤ degrFt ξ m ∧ coin (f-f') ≤ blame ξ s m:=by
  intro A s h f f'
  let r:=rentFt ξ s m; let b:=middle A ξ.band k
  have hR:=topica H Q le_rfl h (fun j hj hm=> (F.probes.steps _ hj hm).pay) v
  have hX:=topica H Q (R:=track Ψ) le_rfl h (fun j hj hm=> (F.probes.steps _ hj hm).cut) v
  have he u : coin (heads R V h u - heads (track Ψ) V h u) ≤ r*knox s*ξ.sends s:=by
     let q:=hike ξ.L (m*ξ.taylor) (k-b)
     obtain ⟨hp,hU⟩:= works H u; have h:= diminish R _ h ξ.loan (Real.exp_pos _|>.le) (track Ψ) F.probes.steps hU
     refine le_trans h (mul_le_mul_of_nonneg_right (mul_le_mul ?_ F.grant.races.family (Nat.cast_nonneg (α:=ℝ) (k-b)) ((rent_buy ..).trans' (by norm_num))) (Real.exp_pos _).le)
     apply mul_le_mul hp Q.hikes (ample ξ.L _ _ ξ.loan) (pow_nonneg (Real.exp_pos _).le _)
  have hv: 1≤r:= rent_buy ..; have hs₁ : 1 ≤ knox s:=knock _; have hf : 0 < ξ.sends s:=Real.exp_pos _; have hb:0≤r*knox s*ξ.sends s:=by positivity
  refine ⟨?_,(pursesC (yolk _ v) _ _ r _ hv hb (fun i=> (metopia H Q le_rfl h (R:=R) (fun j hj hm=> (F.probes.steps _ hj hm).pay) _).1) (fun i=> (metopia H Q le_rfl h (R:=track Ψ) (fun j hj hm=> (F.probes.steps _ hj hm).cut) _).1) he).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=> penny _ _ (zero_le_one.trans hv)) (mem_univ v)) hb)⟩
  rw [sub_eq_add_neg,show -f'=(-1:ℂ)•f' by simp]; exact (totalDegree_add ..).trans (max_le hR.2 ((totalDegree_smul_le ..).trans hX.2))

variable (he:Fit C.path.levels ξ.band k x)
include he
lemma e_facade (j U)
    (hU : Healthy (P (middle C.path.levels ξ.band k)).p.threshold (Peak.route C.path.levels ξ.band k p ξ.era.coast.Q (walls (clim C.path.levels (middle C.path.levels ξ.band k))) j) U) :
    let A := C.path.levels
    let ℓ:=middle A ξ.band k
    let y:= Perch.bill (-3/2) (clim A k)
    let Ŵ:= tapestry H Q (before ..) (le_refl ℓ) F.sens c
    ∃ g : Chamber G A.S ℓ p→ℝ, Wind A g (fraction m ξ.taylor (clim A k)) ∧ ∀ z : PatchPt x ξ.band A p ξ.horizon (before ..),
      ‖(Ŵ (j,z)).value U - (Array.reorient (Ship.yard C ξ.band c.allow p) j (t_cum (track Ψ) V (before A ξ.band k) g)).part (tag z.val).val‖ ≤ y:= by
  intro A ℓ y W; let l:ℓ≤ k:= before ..; let T:=Ship.yard C ξ.band c.allow p;let ZQ:=T.hand j
  let u:= (watches C ξ.band p c.allow ℓ (le_refl _) j U); let P':=(P ℓ).p; let g:= anneals C c ℓ
  let s:=clim A k; let t:=clim A ℓ; let Vθ:= fraction m ξ.taylor s
  have hy':=F.grant.court ℓ (Station.wider ..) l
  let b:= ξ.era.coast.Q; let B:=b*walls t; have hB : 2*(B+1) < (C.side ℓ p).val:= F.sens.canvas.suite ℓ le_rfl l
  let o: Site (C.side ℓ p) := 0; let z₁:= spreadC C ξ.band p (Station.wider A ξ.band k) j
  have hp:Spindle.patch B z₁= swath (T.omega j) z₁ (Spindle.patch B o) := by
    unfold Spindle.patch; rw [swath_iffHalo,swath,image_singleton]; simp only [affine,o,Signed.act_zero,zero_add]
  have hQ:Healthy P'.threshold (Spindle.patch B o) u:= by
    apply (s_healthy (T.omega j) z₁ ..).2; rw [←hp]; exact hU
  have hg:= warmth C c (l.trans c.allow); let X':= afloat o u g B
  let D:= F.birth ℓ (le_refl ℓ) l
  have hτ: P'.threshold/g ≤ torque t:= D.2.2
  have hx u': |X' u'|≤ Vθ:= by
    refine (stream o u g hB hQ hg P'.threshold_pos.le u').trans (le_trans ?_ (Q.awaken.mark t hy'))
    calc
      _ = 16*↑B*(P'.threshold/g):= by ring
      _ ≤ _:= mul_le_mul_of_nonneg_left hτ (show 0≤16*(B:ℝ) by positivity)
  have hx' i: |X' i| ≤ knox s:= (hx _).trans Q.awaken.amplitude
  have hM : 1≤ knox s:= Glimmer.costed _ _ zero_le_one
  refine ⟨X',⟨hx, shuttered B g u o⟩,fun z=>?_⟩
  let f:= vista R V l z.val.val; let f':= vista (track Ψ) V l z.val.val
  let p₀:=kiosk g o u
  let i:= core A x ξ.band p l (Head z.val); have hi:i=o:= Station.at_stop he ..
  have hh: ((W (j,z)).value U)=dot ZQ (text (rigid p₀) f):= by
    change dot _ (text (rigid (kiosk g i u)) f)= _; rw [hi]
  have hP:= topica H Q (R:=R) le_rfl l (fun j hj hk=> (F.probes.steps _ hj hk).pay) z.val.val
  have hz:coin f≤ quotaFt ξ s m:= hP.1
  have ha t(tH : t∈f.vars) : separation o t.1+2≤ B := by rw [← hi]; exact West.n_earby x ξ.band l z.val t (West.housing H Q le_rfl l F.sens z.val|>.2 t tH) F.sens.canvas
  have hs q (w:q∈f.vars) : |rigid p₀ q| ≤ knox s:= by
    refine (rigidHelm p₀ q).trans ((dotSize (f:=fromBead G q) g hg u hQ hB (ha q w)).trans (le_trans (hτ.trans (F.grant.spend.lots t hy')) ?_)); exact F.grant.spend.inside.trans (sub_le_self _ zero_le_one)
  have hf q (w:q∈f.vars) : |rigid p₀ q-X' q| ≤ ξ.sends s:= by
    apply (competed o u g hB hQ hg P'.threshold_pos.le q (ha q w)).trans; apply le_trans _ (Q.awaken.peak t hy')
    have hv : Paint.phase t=P'.threshold:= D.2.1.symm
    change 6*G.colorScale*(4*B*_)^2/g ≤ 6*G.colorScale*(4*B)^2*Paint.phase t*torque t
    rw [hv]; calc
      _ = 6*G.colorScale*(4*B)^2*P'.threshold*(P'.threshold/g):= by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hτ (by have := G.colorScale_pos; have := P'.threshold_pos; positivity)
  have hc : ‖text (rigid p₀) f-text X' f‖ ≤ defect (knox s) (ξ.sends s) (quotaFt ξ s m) (degrFt ξ m):= (spot_trial _ _ _ hP.2 hM hs (fun i _=> hx' i) (Real.exp_pos _).le hf).trans (mul_le_mul_of_nonneg_right hz (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hM) _)) (Real.exp_pos _).le))
  let f'' := f-f'; obtain ⟨hd,hL⟩:=festival F H Q z.val.val
  have hV:‖text X' f-text X' f'‖≤ blame ξ s m* Common.priced (knox s) (degrFt ξ m):= by
    apply le_trans _ (le_trans (view_v X' f'' hd hM (fun i _=> hx' i)) (mul_le_mul_of_nonneg_right hL (zero_le_one.trans (priced_up _ hM)))); exact le_of_eq (congr_arg norm (map_sub (aeval _) f f').symm)
  let W':= t_cum (track Ψ) V l X'
  have he:(Array.reorient T j W').part (tag z.val).val=dot ZQ (text X' f'):= by
    have ht: (Array.reorient T j W').part (tag z.val).val=dot ZQ (W'.part (tag z.val).val):= by dsimp only [Array.reorient,ZQ,Edition.dot]; split_ifs <;> rfl
    rw [ht]; rfl
  rw [hh,show _ = _ from he,dot_equal]; apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans; exact (add_le_add hc hV).trans ((add_comm ..).trans_le Q.hiatus)
end YM.Next.Rank.Tapes.West
