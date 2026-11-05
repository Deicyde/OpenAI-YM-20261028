import YM.RG12.Shadows.Park
/-! Inverting at Media only. Determinant continuity costs through true Hessian.
 Serious distinction with Solver Quota Holder on physical Y axes versus
these analytic-over-compact-law inversion column estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Shadows
open Set Metric Filter Function Lattice Matrix ConnectedActivityE6 ConnectedActivityE6.Blaze Tablet PhysicalNext.Repeat.Prism
open scoped ContDiff Topology BigOperators Classical
variable {R:Haze}{E J:ℕ→Type}[∀ i,Fintype (J i)][∀ i,DecidableEq (J i)][∀ i, NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)]
def hands (J:ℕ→Type)[∀ i,Fintype (J i)](i:ℕ):ℝ:= ↑(Fintype.card (J i))
structure Ibis (R:Haze)(B:Gram J E):Prop where
  gain : Sleeve R 0 1 2 (gaze B)
  backlog : Keeps R 0 _ (birth (dusk B))
  sane : ∀ᶠ i:ℕ in atTop,(B i 0).PosDef
variable (A:Anthem 2) -- exact specialized
namespace Ibis
variable {C D: Gram J E}(H:Ibis R C)
abbrev wake (R:Haze)(C:Gram J E):Gram J E:= fun i y=> C i ((light R i)⁻¹ • y)
-- base logs positive. Price algebra assuming Breeze
include H
lemma existsH : ∃ w,Charges R 0 w ∧ (∀ i,0≤w i) ∧∀ᶠ i:ℕ in atTop,Holds (wake R C i) 0 (w i) 2:=by
  obtain ⟨v,hv,he,hg⟩:= Call.nonneg (scaled H.gain)
  obtain ⟨F,hF,hB⟩:= H.backlog; refine ⟨_,hv.add hF.absolute,fun i=>add_nonneg (he i) (abs_nonneg _),?_⟩
  filter_upwards [hg,hB,H.sane] with i ha hb ht; unfold wake
  refine ⟨fun j k=> (ha (j,k)).climb (le_add_of_nonneg_right (abs_nonneg (F i))) le_rfl,fun j k=> ?_,?_⟩
  · simp only [smul_zero]; exact (hb (j,k)).trans ((le_abs_self _).trans (le_add_of_nonneg_left (he _)))
  simpa only [smul_zero] using! ht
variable (hN: Charges R 0 (hands J))
include hN
lemma turned:Sleeve R 0 1 2 (gaze (dusk C)):=by
  obtain ⟨v,hv,he,hg⟩:= H.existsH; refine unscaled ⟨_,Charges.banner_charge hN hv 2,?_⟩
  filter_upwards [hg] with i hg j; exact broken (fun _: J i=> (0:Site 1)) hg le_rfl (he _) j.1 j.2
abbrev toll (C: Gram J E):Drift (fun _=>Unit) E:= fun i _ y=>Real.log ((C i y).det/(C i 0).det)
include A in
lemma shelters:Sleeve R 0 1 2 (toll C):=by
   obtain ⟨v,hv,he,hg⟩:= H.existsH; refine unscaled ⟨_, Charges.reck_charged hN hv A,?_⟩
   filter_upwards [hg] with i hg j; simpa only [flick, toll,wake, smul_zero] using wagers hg (N:=hands J i) le_rfl (he _) A
omit hN in
lemma base : ∃ w,Charges R 0 w∧(∀ i,0≤w i)∧∀ᶠ i:ℕ in atTop,Holds (fun _:ℝ=> C i 0) 0 (w i) 2:=by
   obtain ⟨w,ha,he,hb⟩:=H.existsH; refine ⟨_,ha,he,hb.mono ?_⟩
   intro i hi; refine ⟨fun j k=> (Brush.certified zero_le_one _).climb ?_ le_rfl,fun j k=> by simpa only [wake,smul_zero] using! hi.back j k,by simpa only [wake,smul_zero] using! hi.sane⟩
   simpa only [wake,smul_zero] using! (hi.liable j k).bound
-- compact and relative comparison flags against same R
structure Shift (B C: Gram J E):Prop where
   base : Keeps R 2 _ (fun i (k:Circle J i)=> C i 0 k.1 k.2-B i 0 k.1 k.2)
def ratioLog (B C: Gram J E):ℕ→ℝ:= fun i=> Real.log ((B i 0).det/(C i 0).det)
include A
lemma baseShift (K:Ibis R D)(S:Shift (R:=R) C D): Keeps R 2 _ (birth (dusk C)-birth (dusk D))∧Charges R 2 (ratioLog C D):=by
   obtain ⟨X,ha,hA,H⟩:=H.base
   obtain ⟨Y,hb,hB,G⟩:=K.base
   obtain ⟨W,hC,hD⟩:=S.base
   let v i:=X i+Y i; have hv: Charges R 0 v:=ha.add hb; have he (i):0≤v i:=add_nonneg (hA _) (hB _)
   obtain ⟨hQ,hK,hU⟩:= Charges.costes (n:=2) hN hv hC.absolute
   have hh := A.plus
   have he0 (B:ℕ→ℝ)(h:Charges R 2 B)(r:ℝ)(hr:0<r):∀ᶠ i:ℕ in atTop,B i ≤ r:=(h.tend0 (by norm_num)).eventually (ge_mem_nhds hr)
   let Gx i:= gear |W i| (v i) (hands J i) 2; let Gy i:= sail |W i| (v i) (hands J i) 2; let Gz i:=revs |W i| (v i) (hands J i) 2
   have hf : ∀ᶠ i:ℕ in atTop, (∀ (j:Circle J i), |birth (dusk C) i j-birth (dusk D) i j| ≤ Gz i)∧|ratioLog C D i| ≤ A.logE*Gy i:=by
     filter_upwards [H,G,hD,he0 _ hQ 1 zero_lt_one,he0 _ hK (1/2) (by norm_num)] with i ha hb hc hk ht
     let A' (_:ℝ):= C i 0; let B' (_:ℝ):=D i 0
     have hp:Holds A' 0 (v i) 2:= PhysicalNext.Repeat.Brim.widening ha (le_add_of_nonneg_right (hB i)); have hx:Holds B' 0 (v i) 2:= PhysicalNext.Repeat.Brim.widening hb (le_add_of_nonneg_left (hA i))
     have he' (j k:J i): Brush 2 |W i| 1 (fun x:ℝ=> (B'-A') x j k) (0:ℝ):= (Brush.certified zero_le_one (D i 0 j k - C i 0 j k) (x:=(0:ℝ)) (k:=2)).climb ((hc (j,k)).trans (le_abs_self _)) le_rfl
     exact ⟨fun j=> (inback hp hx he' le_rfl (abs_nonneg _) (he i) (fun _=> (0:Site 1)) j.1 j.2).bound,(A.treat ℝ _ _ _ (bays (D:=|W i|) hx he' le_rfl (abs_nonneg _) (he i) (fun _=> (0:Site 1)) hk) ht).bound⟩
   exact ⟨⟨_,hU,hf.mono fun i hi j=> hi.1 _⟩,(hK.left A.logE).move (hf.mono fun _ hi=>hi.2)⟩
end Ibis
end YM.RG12.Shadows
