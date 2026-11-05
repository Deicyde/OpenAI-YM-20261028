import YM.RG08.Lyt.Axis
/-! # Primitive projection gaps and STABLE Root norms before any estimate at Rho -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Lyt
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries
open scoped BigOperators Topology Real ContDiff Classical
open Wings Summit
variable {X:Chain}{G:Gauge}{D d k t n τ s E e i j r:ℕ}{w':ℝ}{T:Labels.Frame G d}{H:SectionData T}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{hp:1/2≤w'}{hD:d+1 ≤ D}{h:Hol G}{M:Signals P Q E τ h H hp hD}{ν:G.ColorIndex}{D':ChartRatio G}{S:Prism G X.kernel g Q E}
variable {I J:Type}{u:I→Windows}{w:J→ShoreP u}{v:Wall w 1→ Wings u 1}
variable (he:Tights M S ν D' u)
include he
local notation "Ⓨ"=> wallY X
variable (hv:∀ i,(v i).toLaunch=i.world.toLaunch)
include hv
lemma arms_w : Weighed (wallY X) (menu X ∘ v):= by
    unfold menu Function.comp; simp_rw [hv]; exact Wall.invested X
lemma crops_w : Weighed Ⓨ (fun i:Wall w 1=> ((X.S.block i.i).val:ℝ)) := (Wall.invested X).sway (Wall.plusOne X) (he.hc.M.crop.transfer (fun i:Wall w 1=>i.world.toLaunch))
lemma anchor_v : Bucks τ E (wallY X) (fun i=> chop X (1/4) (v i)) (fun i=> ώ M (v i).i) (fun i=>M.vi (X.J (v i).i)) (fun i=> ώ M ((v i).i+1)) (fun i=> heights X ν D' (v i)) (fun i=> heights X ν D' (v i).wingR) := bucks_here he.operator _ (arms_w he hv) (Wall.plusOne X)
variable {δ : Wall w 1→ℝ}
-- Ward A_tr Replacement: reserved widths and ζ same. prices include indicated geometric post (silk). credit may repeat
lemma path_paid (Z:∀ i:Wall w 1, Cross (X.S.block (v i).i) (Candles G) (Loc G 1))(hZ:SafeRow (wallY X) 1 Z (fun i=> ώ M (v i).i)) (hu:r ≤ τ+E)(V:Wall w 1→EnvelopeU D w' G j)
    (hb:Tin (wallY X) δ V (fun i=> ώ M ((v i).i+1))) :
    Tin Ⓨ δ (fun i=> ((↑(X.S.block (v i).i).val:ℝ)^d *((Fintype.card (Site (X.S.block (v i).i)):ℝ))⁻¹) • ∑ b:Site (X.S.block (v i).i),rue b (Z i) (V i) r) (fun i=>ώ M (v i).i) := by
  obtain ⟨C,hC,H⟩:= hZ; obtain ⟨D,hV,Y⟩:=hb.serves
  let a i:= ώ M ((v i).i+1) / (τ+E+1:ℕ); let P i:= Real.exp (4*ώ M (v i).i); let Q i:= Real.exp ((r:ℝ)*a i)
  have h i : ώ M i ≤ 1:= by have he:=tick_t M (X.J i); exact (he.1.trans he.2).trans (min_le_right ..)
  let w':Wall w 1→ℝ:=wallY X
  have he' : Weighed w' P := (Weighed.constant w' (Real.exp_pos 4|>.le)).mono (fun i=> (Real.exp_pos _).le) (fun i=>Real.exp_monotone (mul_le_of_le_one_right (by norm_num) (h _)))
  have hh : Weighed w' Q:= (Weighed.constant w' (Real.exp_pos r|>.le)).mono (fun _=>(Real.exp_pos _).le) (fun i=>Real.exp_monotone (mul_le_of_le_one_right (Nat.cast_nonneg r) ((div_le_self (M.pos _).le (by norm_cast; omega)).trans (h _))))
  have hb i (b) := amber (l:=(v i).toLaunch) (Z i) b he.he (C:=C i) (by simpa using H i) (hC.positive i) hu (Y i)
  have hy:= (anchor_v he hv).crop
  refine ⟨_, (hy.powers d).times ((((he'.times (Weighed.constant w' (Nat.cast_nonneg (Fintype.card (Loc G 1))))).times hC).powers r).times ((hh.times (Weighed.constant _ (silkSale_pos G j r))).times hV)), fun i=> Ink.raise (Ink.scale (Ink.additions (f:=fun b:Site (X.S.block (v i).i)=>rue b (Z i) (V i) r) (fun b _=>hb i b) (fun b=>(ling_pos _ _).le)) _) (le_of_eq ?_)⟩
  simp only [sum_const,card_univ,nsmul_eq_mul,Pi.mul_apply]; let Q' := Fintype.card (Site (X.S.block (v i).i)); have ht:0<Q':=Fintype.card_pos
  rw [Real.norm_of_nonneg (by positivity)]; unfold P Q a; field_simp
lemma spine_rt (Z:∀ i:Wall w 1, Cross (X.S.block (v i).i) (Candles G) (Loc G 1))(hz: SafeRow Ⓨ 1 Z (fun i=>ώ M (v i).i)) (V:Wall w 1→BoardU D w' G)(ht:r≤ τ+E)(hx:r≤k+e)
    (hp:∀ i< e,∀ j,Tin Ⓨ δ (fun b=> V b i j) (fun i=>ώ M ((v i).i+1))) :
    Tin Ⓨ δ (fun i=>curse k (k+e-r) r d (V i) (Z i)) (fun i=>ώ M (v i).i) := by
  let A j i:= moreU k (k+e-r) (V i) j
  have h j (hj:j<r): Tin Ⓨ δ (A j) (fun i=>ώ M ((v i).i+1)):= by
    unfold A moreU; split; next h=> apply hp; omega
    next h=> exact Tin.zero
  let W j i:= ((↑(X.S.block (v i).i).val:ℝ)^d *((Fintype.card (Site (X.S.block (v i).i)):ℝ))⁻¹) • ∑ b:Site (X.S.block (v i).i),rue b (Z i) (A j i) r
  rw [show (fun i=>curse k (k+e-r) r d (V i) (Z i))=(fun i=> ∑ j∈ range r,W j i) from funext fun i=> by unfold curse; rw [sum_comm, Finset.smul_sum]]
  exact Tin.additions _ (Wall.plusOne X) fun j hj=> path_paid he hv Z hz ht _ (h j (mem_range.mp hj))
lemma ward_p (F:Wall w 1→BoardU D w' G)(hQ:∀ i,Marvel t (F i))(hh:t≤τ)(h:j≤E)(ht:r ≤ t+j)(hx:∀ i<j,∀ r,Tin Ⓨ δ (fun j=> F j i r) (fun i=>ώ M ((v i).i+1))):
   Tin Ⓨ δ (fun i=> aboard d (heights X ν D' (v i)).tree (F i j r)- aboard d (babyQ G X (v i)) (F i j r)) (fun i=>ώ M (v i).i):= by
   -- need walkerF
   obtain ⟨Z,hZ,_,_,HZ⟩:= walkerF (k:=0) he w v hv
   rw [show (fun i=> _- aboard d (babyQ G X (v i)) (F i j r))= -(fun i=>curse t (t+j-r) r d (F i) (Z i)) from funext fun i=>?_]; · exact Tin.neg (spine_rt he hv Z hZ F (by omega) ht hx)
   rw [abroad (hQ i) hp (he.fair _|>.odds) (babyW _) (he.fair _|>.ct) (by apply hZ.status; exact fun _=>M.pos _) (HZ i),if_pos ht,Pi.neg_apply]; exact sub_sub_cancel_left ..
lemma edge_path {U:EnvelopeU D w' G r}{A : ℝ}(i:Wall w 1)(hP:Polished U)(hA:Abates U (d+1))(hr:r≤τ+E)(hh:Quire.Lit U (ώ M (i.i+1)) A): Quire.Lit (aboard d (babyQ G X (v i)) U) (ώ M i.i) (A*gain X.S (1/2) i.i (i.i+1)):= by
   have hz:(v i).i=i.i:= congr_arg Launch.i (hv i)
   have hV : Quire.Lit U (ώ M ((v i).i+1)) A:= hz.symm ▸ hh
   have ht:= he.he.stepCap (v i).up.toLaunch
   let F:= X.flight (v i).N (v i).i; have hG:= he.he.order (v i).toLaunch
   let P:= (v i).i; have hR:= M.pros (X.J P) (X.J (P+1)) F (X.adm P) ht hG r hr U hP hA A hV -- i orientation probe
   rw [show ώ M i.i= ώ M (v i).i from congr_arg (ώ M) hz.symm, show gain X.S (1/2) i.i (i.i+1) = gain X.S (1/2) (v i).i ((v i).i+1) from hz.symm ▸ rfl]; rw [gain_succ_half]; apply Ink.raise hR
   rw [mul_one_div]; apply div_le_self (div_nonneg hV.nonneg (Real.sqrt_nonneg _)) (expQ_pos _ (zero_le_one.trans (M.admits ..)))
end YM.RG08.Lyt
