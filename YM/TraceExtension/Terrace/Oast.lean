import YM.TraceExtension.Terrace.Cabin
import YM.ProofPorts.GRID_REAL_MODELS_ESTIMATES_20261012.Author
import YM.MergeProof.Maid
import YM.MergeProof.South.Block
import YM.MergeProof.South.Lens

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open GridApprox.Joint GridApprox
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V} {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
variable (L:C.label d)(X:Extra.Histories.Music (C.labels.level d) C.path N p) (Y:(C.labels.level d).Index→ C.label d)
local notation "ζ!"=> ζ d
variable (h:Scrim C W u ψ φ δ ζ r D){b:C.label d}{Z:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}{g:ℕ→ℝ} {Q:ℝ}
    (J:ℕ) (K:Stock.Tabs C.path.levels)
def stockX (d k N p:ℕ)(v:C.label d):= 2*(C.labels.level d).coeffSize (Next.Rank.Price.columns C d k N p v)
def allowanceC (d k:ℕ):= ‖alto C.path k d‖*(1+(C.path.levels.params k).columns)
include H
lemma dialsP (hK:ℓ ≤ k)(hN:k≤N)(hX:(s!).entries=(X.draft C.path).inits)(hh:Sung (Y!) T N p C.params W ℓ X)(he:∀ i: (F).Index,(F).coeffSize (Size.axis F i-(X.tone k).index (Y i)) ≤ (1:ℝ)/4) :∃ t:C.label d,L=∑ i,t i • ((s!).terminal (Y i))∧ (F).coeffSize t ≤ stockX C d k N p L:=by
   let I:=s!; let J:= (X.tone k).index; let V:= (F).Coeff; let A:(F).Coeff →ₗ[ℂ] (F).Coeff:=
      { toFun:=fun v=> ∑ i,v i • J (Y i)
        map_add':=fun v w=>by simp [add_smul,Finset.sum_add_distrib]
        map_smul':=fun v w=> by simp [Finset.smul_sum,mul_smul] }
   have h(v:V): (F).coeffSize v ≤ 2*(F).coeffSize (A v):=by
      have hp: v-A v=∑ i,v i • (Size.axis F i-J (Y i)):=by simp_rw [smul_sub,Finset.sum_sub_distrib, show ∑ i,v i • Size.axis F i=v from GridApprox.coeff_sum C v]; rfl
      have hx: (F).coeffSize (v-A v) ≤ (F).coeffSize v / 4:=by
         rw [hp]; refine (Size.finite F _ _).trans (le_trans (Finset.sum_le_sum fun i _=> show (F).coeffSize _≤ ‖v i‖*(1/4) from ?_) ?_)
         · rw [Size.smul]; exact mul_le_mul_of_nonneg_left (he i) (norm_nonneg _)
         rw [←Finset.sum_mul]; unfold Labels.Frame.coeffSize; linarith only
      linarith only [Work.G08.size_triangle F v (A v),hx,Work.G08.size_nonneg F v]
   have hI : Injective A := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x e=> by apply Work.G08.size_separates; simpa [e,Labels.Frame.coeffSize] using h x)
   let t:= I.terminal.symm L; obtain ⟨v,hv⟩:= LinearMap.injective_iff_surjective.mp hI (J t); refine ⟨v,?_,?_⟩
   · have hh': ∑ i,v i • Y i=t:= J.injective (by rw [map_sum]; simp_rw [map_smul]; exact hv); have hl : I.terminal t=L:=I.terminal.apply_symm_apply L; nth_rw 1 [← hl]; rw [← hh',map_sum]; simp_rw [map_smul]; rfl
   have hc: (I.entries k t).x=J t:=by
      rw [show I.entries=(X.draft C.path).inits from hX]; exact (hh.earned k hK hN).currents t
   have hz:= Work.D01.back_budget C H L hK hN (p:=p)
   change (F).coeffSize (I.entries k t).x ≤ _ at hz
   have hQ:=h v; rw [hv] at hQ; unfold stockX Price.columns; dsimp only; change _≤2* (F).coeffSize (I.entries k t).x; rw[hc];exact hQ
lemma allowanceC_non (v:(F).Index)(hK:C.ref d ≤ k)(hp:k≤N)(U:Config G (C.side k p)): ‖lens C N k p d (Size.axis (F) v) U‖ ≤ allowanceC C d k:=by
   let L:= Size.axis (F) v; let I:= Extra.Histories.primary (0:Site (C.side k p)) L; let Q:= C.path.rep N p k; let k':= C.path.levels.params k; let x:= k'.columns; have hx : Q.p=C.path.levels.budget k:= (H.wilson.represents N p k hp).vac
   have hv:=hull (C.localSection d) Q 0 I U (by rw[hx]; exact H.priced d k p hK 0) (k:=1) (primary_rem L (zero_lt_one)) (le_refl _) (show 0 ≤ x from zero_le_one.trans k'.columns_ge); rw [add_zero,show I.x= L from rfl, show (F).coeffSize L=1 from Size.size_axis ..,mul_one] at hv
   unfold lens; rw[norm_mul]; exact mul_le_mul_of_nonneg_left hv (norm_nonneg _)

include h K
lemma repast (hV : Stock.Tabs.opens C.path.levels 1 J m)(hK : ℓ ≤ m)(hk : m≤k)(hw:0<w)(hc:GridApprox.room C.path.levels J k (lensScope C d))(ht:w*‖alto T m d‖*(4*(1+(T|>.levels.params k).columns)/gainChart T k m) ≤ ζ d m/2) (hN : k<N )(hv:J ≤ N)(hf:∀ (v:C.label d), Interior ((center C.S p hv 0).chamber 0) (C.O N p v 0)) : ∃ B:Config G (C.side k p)→ℂ,let Qx:= center C.S p hv 0; Interior (GridApprox.window 0 (lensScope C d)) B∧ (∀ U, ‖B U‖ ≤ stockX C d k N p L * allowanceC C d k) ∧ Interior (Qx.chamber 0) (backTo C.path N p hN.le B)∧Qx.rootTest (C.beta N p) (backTo C.path N p hN.le B - C.O N p L 0) ≤ stockX C d k N p L * (stakes C J m/w):=by
   let A:= allowanceC C d k; have hA:0≤A:=by unfold A allowanceC; positivity[(C.path.levels.params k).columns_ge];
   have hw':0 ≤ stakes C J m/w:=div_nonneg (Real.exp_pos _).le hw.le
   obtain ⟨X,hX,hL,hC,hQ⟩:= (h.costs.aim d N p ((hK.trans hk).trans hN.le)).lyrics
   let R':= C.factory d N p; let c:= (C.path.levels.params k).columns; let H0:= center C.S p hv 0
   have he(i):= embrace C N k m p d H w (Size.axis F i) X h 1 (4*(1+c)) hK hk hN.le hL hC (Size.size_axis F i).le (by rw [mul_one]) zero_lt_one hw ht
   choose Z g b' hb' using he
   obtain ⟨v,hv',hM⟩:=dialsP C N k p d H L X b' (hK.trans hk) hN.le hX hL (fun i=>(hb' i).bias)
   let Y i:= lens C N k p d (Size.axis F i); let n:=lensScope C d
   let Z' i:= backTo T N p hN.le (Y i); let B:= ∑ i,v i • Y i
   have hY(i): Interior (GridApprox.window 0 n) (Y i):= visible C N k p d _ H hN.le
   have hZ(i): Interior (H0.chamber 0) (Z' i):=by
      let t:=hV.1.trans hk; let i':=(anchor C.S p t) 0; have he:i'=0:= (C.S.toDepth t p).root.map_zero
      have hx : Interior (GridApprox.window (anchor C.S p t 0) n) (Y i):=by rw [show anchor C.S p t 0=0 from he]; exact hY i
      exact (backTo_local T N p t hN.le 0 n hx).enlarges (room_fits p C.path.levels n t hN.le hc _)
   let f i:= C.O N p (R'.terminal (b' i)) 0
   have hz(i): H0.rootTest (C.beta N p) (Z' i-f i) ≤ stakes C J m/w:= quakes C N k m p d H w (Size.axis F i) X h J K hN hK hk hw (hb' i) hL hC hQ hV _ hc (hY i)
   have hS:=seamless H N p
   have he : backTo T N p hN.le B=∑ i,v i • Z' i := ProofPorts.GridRealModelsEstimates20261012.backTo_linSum N p hN.le Y v (fun i=>cylinder_env (hY i))
   refine ⟨B,ProofPorts.GridRealModelsEstimates20261012.interior_sum _ _ (fun i _=> (hY i).scale _),fun U=> ?_,he.symm ▸ (Next.UVStress.root_sum H0 (C.beta N p) univ Z' (fun i=>v i) (fun i _=>hZ i) hS).1,?_⟩
   · unfold B; rw [Finset.sum_apply]; apply (norm_sum_le ..).trans
     refine le_trans (Finset.sum_le_sum fun i _=> (show ‖(v i • Y i) U‖ ≤ ‖v i‖*A from ?_)) ?_
     · simp only [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (allowanceC_non C N k p d H i (hK.trans hk) hN.le U) (norm_nonneg _)
     rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hM hA
   rw [he,show C.O N p L 0=∑ i,v i • f i from by
         rw [hv']; let A₀:= (C.linearO N p d 0).mk' _; change A₀ (∑ i,v i • _)=_; rw [map_sum]; simp_rw [map_smul]; rfl, show (∑ i,v i • Z' i)-(∑ i,v i • f i)=∑ i, v i • (Z' i-f i) from by simp_rw [smul_sub,Finset.sum_sub_distrib]]
   refine (Next.UVStress.root_sum H0 (C.beta N p) univ (fun i=>Z' i - f i) (fun i=>v i) (fun i _=> Next.UVStress.minus (hZ i) (hf _)) hS|>.2).trans ?_
   refine le_trans (Finset.sum_le_sum (fun i _=> mul_le_mul_of_nonneg_left (hz i) (norm_nonneg (v i)))) ?_; rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hM hw'
end YM.MergeProof.Accent
