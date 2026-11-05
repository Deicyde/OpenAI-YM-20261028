import YM.RG12.Shadows.Lateral
import YM.RG12.Shadows.Climb
/-! The law oracle pays square-loop suppression on tilted mirrors. Sign
 purchases *real germ only* both laws can be posed on aperture. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Shadows
open Set Metric Filter Function Lattice Matrix ConnectedActivityE6 ConnectedActivityE6.Blaze Tablet PhysicalNext.Repeat.Prism Next.SectorChange Next AnalyticBridge.LocalGaussianLaws
open scoped ContDiff Topology BigOperators Classical
variable {R:Haze}{E J I:ℕ→Type}[∀ i,Fintype (J i)][∀ i,DecidableEq (J i)][∀ i, NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)]
namespace Ibis
open Call
abbrev Cell:= fun _:ℕ=> Unit
abbrev backGauge (C:Gram J E):Gram J E:= fun i y=> C i (-y)
abbrev bell (C D: Gram J E): Drift Cell E:= fun i _ y=> Real.log ((C i 0).det/(D i y).det)
abbrev bell' (C D: Gram J E): Drift Cell E:= fun i j y=> bell C D i j (-y)
variable {C D:Gram J E}(H : Ibis R C)(K:Ibis R D)(h:Shift (R:=R) C D)(hN:Charges R 0 (hands J))
include H K h hN
lemma rowT : Tilts R 2 0 true (gaze (dusk C)) (gaze (dusk (backGauge C))) (gaze (dusk D)) (gaze (dusk (backGauge D))):=by
  obtain ⟨A⟩:=anthems 2; have H0:= (baseShift A H hN K h).1
  have hC:=H.turned hN; have hD:= K.turned hN; have hh:=hD.sub hC
  have hi:Sleeve R 2 1 2 (gaze (dusk D)-gaze (dusk C)):= by
    refine ⟨hh.smooth,Keeps.assures H0 ?_, hh.first,hh.second⟩
    refine Eventually.of_forall (fun i a=>?_); dsimp [normJ]; rw [norm_iteratedFDeriv_zero,abs_of_nonneg (norm_nonneg _),Real.norm_eq_abs]; exact (abs_sub_comm _ _).le
  apply ledge (p:=0)
  · simpa only [zero_add] using! hC.mono le_rfl le_rfl one_le_two
  simpa only [zero_add] using! hi
lemma bellT :Tilts R 2 0 true (bell C C) (bell' C C) (bell C D) (bell' C D):=by
  obtain ⟨A⟩:=anthems 2; have H0:= (baseShift A H hN K h).2; have H1:= H0.norm
  let M:Drift Cell E:= fun i _ _=> ratioLog C D i
  have hK:= click (Call.up H0 (I:=Cell) (E:=E)) -- no n arg of click
  have hC:=shelters A H hN; have hD:= shelters A K hN -- order?
  let T:= toll C; let Q:=toll D
  have hz:Sleeve R 0 1 2 ((-1:ℝ) • T):=by simpa only [Pi.smul_apply,add_zero] using! hC.scales (Charges.frozen (-1) R)
  have hX:=hK.mono (v:=0) (w:=1) (z:=2) (by norm_num) (by norm_num) le_rfl
  have hb:=hX.sub hD
  have hl: bell C C=(-1:ℝ) • T:=by
    ext i j x; change Real.log _= -1*_ ; unfold T toll; rw [show (C i 0).det/(C i x).det=((C i x).det/(C i 0).det)⁻¹ by simp,Real.log_inv]; ring
  have hg: Sleeve R 0 1 2 (bell C D):=by
    change Sleeve R _ _ _ (M-toll D) at hb; apply hb.congr
    filter_upwards [H.sane,K.sane,K.gain.smooth] with i H K D' j
    have hf := ((ConnectedActivityE6.Blaze.determinant (A:=D i) (fun j k=>D' (j,k))).continuousAt (lt_mem_nhds K.det_pos)) -- B?
    filter_upwards [hf] with y hy
    change Real.log _ = Real.log _ - Real.log _; have hh:=H.det_pos; have ht:=K.det_pos
    rw [Real.log_div hh.ne' hy.ne',Real.log_div hh.ne' ht.ne',Real.log_div hy.ne' ht.ne']; abel
  have hd:=hg.sub (hl.symm ▸ hz)
  have hj:Sleeve R 2 1 2 (bell C D-bell C C):=by
    refine ⟨hd.smooth,Flares.mk H1 ?_, hd.first,hd.second⟩
    filter_upwards [H.sane] with i hv j; have he:=hv.det_pos; dsimp [normJ]; rw [norm_iteratedFDeriv_zero]; change ‖Real.log _-Real.log _‖≤_; rw [div_self he.ne',Real.log_one,sub_zero]; exact le_rfl
  exact ledge (p:=0) (by rw [hl,zero_add]; exact hz.mono le_rfl le_rfl one_le_two) (by simpa only [zero_add] using! hj)
end Ibis
abbrev Trail (J E:ℕ→Type):= ∀ i:ℕ,E i→Gaussian.Vec (J i)
abbrev tip (f:Trail J E):Drift J E:= fun i j x=> f i x j
def dial (C:Gram J E)(Y Y':Trail J E): Drift Ibis.Cell E:= fun i _ x=> dotProduct (Y i x) ((C i x).mulVec (Y' i x))
omit [∀ i,DecidableEq (J i)] in
lemma dialT {R:Haze}{A B C D:Gram J E}{Y W Z X y w z x:Trail J E} (H:Tilts R 2 0 false (tip Y) (tip W) (tip Z) (tip X)) (K:Tilts R 2 0 true (gaze A) (gaze B) (gaze C) (gaze D))(L:Tilts R 2 0 false (tip y) (tip w) (tip z) (tip x))(hN:Charges R 0 (hands J)) :
    Tilts R 2 0 true (dial A Y y) (dial B W w) (dial C Z z) (dial D X x):=by
  let L':= L.reindex (fun (_:ℕ) i=> i.2) (I':=Circle J)
  have hf := (K.times L').total (fun (_:ℕ) l j=> (l,j)) (I':=J) hN
  simp only [zero_add,fit] at hf
  have hg:= (H.times hf).total (fun (_:ℕ)(_ : Unit) j=>j) (I':=Ibis.Cell) hN; simp only [zero_add,fit] at hg; exact hg
variable {C D:Gram J E}(H:Ibis R C)(K:Ibis R D)(hk:Ibis.Shift (R:=R) C D)(hN:Charges R 0 (hands J)) (z:∀ i, Gaussian.Vec (J i))(hz: Keeps R 0 J (fun i j=>z i j)) {Y6 Y9 W6 W9:Trail J E}(hf:Tilts R 2 0 false (tip Y6) (tip W6) (tip Y9) (tip W9))
def rapid (C D: Gram J E)(z:∀ i,Gaussian.Vec (J i))(Y:Trail J E): Drift Ibis.Cell E:= fun i _ x=> Density.replace (D i x) (C i 0) (Y i x-z i) (z i)
include H K hk hN z hz hf
lemma blend (hb:∀ᶠ i:ℕ in atTop,Y6 i 0=z i ∧ W6 i 0= -z i)
     (he:∀ᶠ i:ℕ in atTop,∀ᶠ x in 𝓝 (0:E i),(C i x).PosDef∧ (D i x).PosDef):
     Tilts R 2 0 true (rapid C C z Y6) (rapid C (Ibis.backGauge C) (-z) W6) (rapid C D z Y9) (rapid C (Ibis.backGauge D) (-z) W9):=by
   let B:= (dusk C); let A:=dusk D
   let v:Trail J E:= fun i _=>z i; let w:Gram J E:= fun i _=>(C i 0)⁻¹
   have ht:Call R 2 0 (tip v):=Call.flat hz
   have hz':Call R 2 0 (gaze w):=Call.flat H.backlog
   have hw0:= Tilts.noCast (Touch.welcomed hz'); have hv0:= Tilts.noCast (Touch.antipode ht)
   have ha:= dialT hv0 hw0 hv0 hN; have hf':=dialT hf (H.rowT K hk hN) hf hN
   have hg:= (((H.bellT K hk hN).adds (ha.subs hf')).coat (1/2))
   let J':= (1/2:ℝ) • (Ibis.bell C C+(dial w v v-dial B Y6 Y6))
   let v': Trail J E:= fun i _=>-z i
   let L:= (1/2:ℝ) • (Ibis.bell C (Ibis.backGauge C)+(dial w v' v'-dial (dusk (Ibis.backGauge C)) W6 W6))
   have hbH : Call.Marks J' 0 ∧ Call.Marks L 0:=by
     suffices h : ∀ᶠ i:ℕ in atTop,∀ j:Ibis.Cell i,J' i j 0=0∧L i j 0=0 from ⟨h.mono fun i ha j=> by rw [(ha j).1,abs_zero],h.mono fun i ha j=> by rw [(ha j).2,abs_zero]⟩
     filter_upwards [hb,H.sane] with i hf hW j; have hh:=hW.det_pos.ne'; simp [Ibis.bell,Ibis.backGauge,J',L,dial,hf.1,hf.2,v,w,v',B,dusk,hh]
   have hr:= hg.exp hbH.1 (hh:=hbH.2)
   have hh {J:ℕ→Type}[∀ i,Fintype (J i)][∀ i,DecidableEq (J i)] (i:ℕ)(B:Gaussian.Table (J i))(ζ: Gaussian.Vec (J i)) (Y':Gaussian.Vec (J i)) -- edit
       (D₀:Gaussian.Table (J i))(hx:B.PosDef)(hy:D₀.PosDef):
       Density.replace B D₀ (Y'-ζ) ζ = Real.exp ((1/2:ℝ)*(Real.log (D₀.det/B.det)+(Gaussian.force D₀ ζ-Gaussian.force B Y'))):=by
       rw [Density.replace, Density.chip_income _ _ hx hy,← Real.exp_add,Density.spice,add_sub_cancel]; congr 1; ring
   -- germ congruence on Tilts
   obtain ⟨un,vn⟩:=hr -- rename
   have hE:∀ᶠ i:ℕ in atTop,∀ᶠ x in 𝓝 (0:E i), (C i 0).PosDef ∧(C i x).PosDef∧ (D i x).PosDef∧ (C i (-x)).PosDef∧(D i (-x)).PosDef:=by
     filter_upwards [he,H.sane] with i he hp; filter_upwards [he, (by simpa only [neg_zero] using (show Tendsto (fun x:E i=> -x) (𝓝 0) (𝓝 (-0)) from continuous_neg.tendsto (0:E i)) : Tendsto (fun x:E i=> -x) (𝓝 0) (𝓝 0)).eventually he] with x ha hb using ⟨hp,ha.1,ha.2,hb⟩
   constructor <;> constructor
   · apply un.origin.fakes; filter_upwards [hE] with i ha j; filter_upwards [ha] with x hx; exact hh i _ _ _ _ hx.2.1 hx.1
   · apply un.listens.fakes; filter_upwards [hE] with i ha j; filter_upwards [ha] with x hx; change Density.replace _ _ _ _-_*Density.replace _ _ _ _=_; rw [hh _ _ _ _ _ hx.2.1 hx.1,hh _ _ _ _ _ hx.2.2.2.1 hx.1]; rfl
   · apply vn.origin.fakes; filter_upwards [hE] with i ha j; filter_upwards [ha] with x hx; change Density.replace _ _ _ _-Density.replace _ _ _ _=_; rw [hh _ _ _ _ _ hx.2.2.1 hx.1,hh _ _ _ _ _ hx.2.1 hx.1]; rfl
   apply vn.listens.fakes; filter_upwards [hE] with i ha j; filter_upwards [ha] with x hx; change Density.replace _ _ _ _-Density.replace _ _ _ _-_* (Density.replace _ _ _ _-Density.replace _ _ _ _)= _; rw [hh _ _ _ _ _ hx.2.2.1 hx.1,hh _ _ _ _ _ hx.2.1 hx.1,hh _ _ _ _ _ hx.2.2.2.2 hx.1,hh _ _ _ _ _ hx.2.2.2.1 hx.1]; rfl
end YM.RG12.Shadows
