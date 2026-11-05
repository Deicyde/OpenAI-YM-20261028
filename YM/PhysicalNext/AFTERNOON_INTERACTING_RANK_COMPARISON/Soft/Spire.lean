import YM.Next.MULTISOURCE.Journey
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Tapestry
/-!
# Checkout façade (`Next/RANK` argument with Soft)

Part not depending on c: can apply on shadow. And using the representation
at k: explicitly have equality there for reusing that proof.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Next.Rank Next.Rank.Tapes
open Function MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation EntryWord
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}
variable {C : Family G} {i k l j m p q d D a N : ℕ} {R : Lead G C.S p}
variable {c : Course C N p k} {ξ : Purse}
variable {P : (i : ℕ) → Rep G (C.side i p)} {X : AtlasData G C.S p}
variable (F : Nylon c P X R ξ)

variable (O : StampDuty C k N p d ξ.taylor (P k) ξ.era.coast.Q X)
variable {x : Points m} (H : Corridor C.path.levels ξ.band ξ k) (he : Fit C.path.levels ξ.band k x)
variable (v : Fin m→ C.label d) (Z : ∀ i, coin (O.W (v i))≤ ξ.principal (clim C.path.levels k))

include H F Z
lemma v_occasion (x : Points m) (i : pennant m) :
    let h:= before C.path.levels ξ.band k
    let p₀:= jacketPol (F:=R) (s:=ξ.band) x v O h i
    let v':= jacketPol (F:=track X) (s:=ξ.band) x v O h i
    let u:= p₀-v'
    u.totalDegree ≤ 2*ξ.taylor ∧ coin u ≤ fault (clim C.path.levels k) ξ:= by
  obtain ⟨P',g,hg,hP⟩:= F.backing
  have ht (Q:RG.Rep G (C.side k p)) (he : P' k=Q) (O : StampDuty C k N p d ξ.taylor Q ξ.era.coast.Q X)
      (H₀ : ∀ i,coin (O.W (v i))≤ξ.principal (clim C.path.levels k)) :
      let h:= before C.path.levels ξ.band k; let p₀:= jacketPol (F:=R) (s:=ξ.band) x v O h i
      let v':= jacketPol (F:=track X) (s:=ξ.band) x v O h i; let u:=p₀-v'; u.totalDegree≤ 2*ξ.taylor∧coin u ≤ fault (clim C.path.levels k) ξ:=by
    subst Q; exact occasion hg O H v H₀ x i
  exact ht _ hP O Z
include he
lemma v_façade (hn : m ≤ 2) (ht : Awakening ξ (clim C.path.levels k) m (G:=G)) (j U)
    (hU : Healthy (P (middle C.path.levels ξ.band k)).p.threshold (Peak.route C.path.levels ξ.band k p ξ.era.coast.Q (walls (clim C.path.levels (middle C.path.levels ξ.band k))) j) U) :
    let A := C.path.levels
    let ℓ:=middle A ξ.band k
    let y:= Perch.bill (-3/2) (clim A k)
    let Ŵ:= mimics x v O F.paths c.allow (before ..) (le_refl ℓ) (anneals C c ℓ)
    ∃ g : Chamber G A.S ℓ p→ℝ, Wind A g (fraction m ξ.taylor (clim A k)) ∧ ∀ z : Index x ξ.band A p ξ.horizon (before ..),
      ‖(Ŵ (j,z)).value U - (Array.reorient (Ship.yard C ξ.band c.allow p) j (Cumulus X (Station.choose A ξ.band k x) (before A ξ.band k) O.heater v g)).part (tale z.val).val‖ ≤ y:= by
  intro A ℓ y W; let l:ℓ≤ k:= before ..; let T:=Ship.yard C ξ.band c.allow p;let Q:=T.hand j
  let u:= (watches C ξ.band p c.allow ℓ (le_refl _) j U); let P':=(P ℓ).p; let g:= anneals C c ℓ
  let s:=clim A k; let t:=clim A ℓ; let V:= fraction m ξ.taylor s
  have hy':=H.court ℓ (Station.wider ..) l
  let b:= ξ.era.coast.Q; let B:=b*walls t; have hB : 2*(B+1) < (C.side ℓ p).val:= F.paths.canvas.suite ℓ le_rfl l
  let o: Site (C.side ℓ p) := 0; let z₁:= spreadC C ξ.band p (Station.wider A ξ.band k) j
  have hp:Spindle.patch B z₁= swath (T.omega j) z₁ (Spindle.patch B o) := by
    unfold Spindle.patch; rw [swath_iffHalo,swath,image_singleton]; simp only [affine,o,Signed.act_zero,zero_add]
  have hQ:Healthy P'.threshold (Spindle.patch B o) u:= by
    apply (s_healthy (T.omega j) z₁ ..).2; rw [←hp]; exact hU
  have hg:= warmth C c (l.trans c.allow); let X':= afloat o u g B
  let D:= F.fixture (le_refl ℓ) l
  have hτ: P'.threshold/g ≤ torque t:= Novice.small (l.trans c.allow) D
  have hx u': |X' u'|≤ V:= by
    refine (stream o u g hB hQ hg P'.threshold_pos.le u').trans (le_trans ?_ (ht.mark t hy'))
    calc
      _ = 16*↑B*(P'.threshold/g):= by ring
      _ ≤ _:= mul_le_mul_of_nonneg_left hτ (show 0≤16*(B:ℝ) by positivity)
  have hx' i: |X' i| ≤ knox s:= (hx _).trans ht.amplitude
  have hM : 1≤ knox s:= Glimmer.costed _ _ zero_le_one
  refine ⟨X',⟨hx, shuttered B g u o⟩,fun z=>?_⟩
  let f:= jacketPol (s:=ξ.band) (F:=R) x v O l z.val; let f':= jacketPol (s:=ξ.band) (F:=track X) x v O l z.val
  let p₀:=kiosk g o u
  let i:= core A x ξ.band p l (headMark z.val); have hi:i=o:= Station.at_stop he ..
  have hh: ((W (j,z)).value U)=dot Q (text (rigid p₀) f):= by
    change dot _ (text (rigid (kiosk g i u)) f)= _; rw [hi]
  have hP := vertex_cap X R O H v F.probes Z ℓ l x le_rfl z.val
  have hz : coin f ≤ ξ.double s := by
    rcases z with ⟨z|z,hz⟩; exacts [hP.1.trans (ξ.ledger_lo _),hP.1]
  have ha t(tH : t∈f.vars) : separation o t.1+2≤ B := by rw [← hi]; exact Tapes.nearby x ξ.band l z.val t (premise x v O F.paths l le_rfl z.val|>.2 t tH) F.paths.canvas
  have hs q (w:q∈f.vars) : |rigid p₀ q| ≤ knox s:= by
    refine (rigidHelm p₀ q).trans ((dotSize (f:=fromBead G q) g hg u hQ hB (ha q w)).trans (le_trans (hτ.trans (H.spend.lots t hy')) ?_)); exact H.spend.inside.trans (sub_le_self _ zero_le_one)
  have hf q (w:q∈f.vars) : |rigid p₀ q-X' q| ≤ ξ.sends s:= by
    apply (competed o u g hB hQ hg P'.threshold_pos.le q (ha q w)).trans; apply le_trans _ (ht.peak t hy')
    have hv : Paint.phase t=P'.threshold:= D.threshold.symm
    change 6*G.colorScale*(4*B*_)^2/g ≤ 6*G.colorScale*(4*B)^2*Paint.phase t*torque t
    rw [hv]; calc
      _ = 6*G.colorScale*(4*B)^2*P'.threshold*(P'.threshold/g):= by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hτ (by have := G.colorScale_pos; have := P'.threshold_pos; positivity)
  have hc : ‖text (rigid p₀) f-text X' f‖ ≤ defect (knox s) (ξ.sends s) (ξ.double s) (2*ξ.taylor):= (spot_trial _ _ _ hP.2 hM hs (fun i _=> hx' i) (Real.exp_pos _).le hf).trans (mul_le_mul_of_nonneg_right hz (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hM) _)) (Real.exp_pos _).le))
  let f'' := f-f'; obtain ⟨hd,hL⟩:=v_occasion F O H v Z x z.val
  have hV:‖text X' f-text X' f'‖≤ fault s ξ* Common.priced (knox s) (2*ξ.taylor):= by
    apply le_trans _ (le_trans (view_v X' f'' hd hM (fun i _=> hx' i)) (mul_le_mul_of_nonneg_right hL (zero_le_one.trans (priced_up _ hM)))); exact le_of_eq (congr_arg norm (map_sub (aeval _) f f').symm)
  let W':= Cumulus X (Station.choose A ξ.band k x) (before A ξ.band k) O.heater v X'
  have he:(Array.reorient T j W').part (tale z.val).val=dot Q (text X' f'):= by
    have ht: (Array.reorient T j W').part (tale z.val).val=dot Q (W'.part (tale z.val).val):= by dsimp only [Array.reorient,Q,Edition.dot]; split_ifs <;> rfl
    rw [ht]; exact congr_arg _ (notices (F:=O) v _ hn _ F.invariant X' _)
  rw [hh,show _ = _ from he,dot_equal]; apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans; exact (add_le_add hc hV).trans ((add_comm ..).trans_le ht.value)
end YM.PhysicalNext.InteractingRank.Soft
