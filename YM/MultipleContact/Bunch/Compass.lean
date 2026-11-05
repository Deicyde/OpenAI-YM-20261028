import YM.MultipleContact.Bunch.Box
import YM.MultipleContact.Bunch.Economics
import YM.MultipleContact.Bunch.Himalaya
import YM.MultipleContact.Matching.Broad
import YM.MultipleContact.Sharp
import YM.MergeProof.North.Burrough
import YM.MergeProof.North.Lauder
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Bunching
open YM.MultipleContact.Matching
variable {α:Type}[Fintype α][DecidableEq α][Inhabited α]
open YM.MergeProof YM.MergeProof.Ribbons
open Function Filter Lattice RG MeasureTheory Asymptotics Finset Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G)(D d h:ℕ)
set_option quotPrecheck false
local notation "P"=>C.path.levels
local notation "Q"=>C.S.scale
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
variable {r:ℕ→ℕ}{D':∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
open Accent Source Extra.Histories
variable (V: C.label d) (T:C.label 4) {u ψ:ℕ→ℝ}{W:Worth} (hG:G.Simple)(hW:Scrim C W u ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r D')
variable (hV:Velour C (renal C.path.levels) r D')(p k:ℕ)(L:Stock.Tabs C.path.levels)(hx:Stock.Tabs.opens C.path.levels 1 p k)
def Stage (C:Family G)(d:α→ℕ)(lamp:Side)(a:ℝ)(γ:ℝ) (t:ℝ)(j:ℕ→ℕ) (p k D:ℕ)(w:ℝ):Prop:= 0<w∧1<t ∧ 0 < -a*(1-t) ∧ -a*(1-t) ≤ 1/32 ∧ -a*(1-t) ≤ γ ∧ Tendsto j atTop atTop ∧ Tendsto (fun i:ℕ=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 t) ∧ ∃ E:ℕ→ℝ, Note C.S E (-D+ -a*(1-t) + D) ∧ ∀ (v:∀s:α,C.label (d s)) (hx:∀s,(C.labels.level (d s)).coeffSize (v s) ≤w)(F:Extraction.Order), ∀ᶠ i in atTop, (Box C p (j i) i D d (totalDeg d-(D:ℝ)) v F lamp (lista C D i*(2*E i)) (2*(stakes C p k / pitts C i)))
structure Treasury (C:Family G):Prop where
  fees' : ∀(α:Type)[_h:Fintype α][_d:DecidableEq α][_i:Inhabited α](d:α→ℕ)(lamp:Lattice.Side)(D p k:ℕ),∀ γ:ℝ,0<γ→Stock.Tabs.opens C.path.levels 1 p k→C.ref D ≤ k →∀ w> (0:ℝ),let a:ℝ:= ((totalDeg d:ℕ):ℝ)+4*(Fintype.card α:ℝ); ∃ (t:ℝ)(j:ℕ→ℕ),Stage C d lamp a γ t j p k D w
variable (hY:Money C.path.levels)
variable (hBH:Broader C (renal C.path.levels) r D')
include hY
include hW hG L hV hBH
lemma prices_at (ht:Created C)(h:C.Makes): Treasury C:=by
   refine ⟨fun α _ _ _ d lamp D p k γ hγ hx hK w hw=>?_⟩
   obtain ⟨χ,hχ,hV',σt,hσ⟩:= procure C D hBH
   let a:ℝ:= ((totalDeg d:ℕ):ℝ)+4*(Fintype.card α:ℝ); let g:= min ((1:ℝ)/64) γ; let t:=1+g/a; have ha:0<a:=by have ht:=Fintype.card_pos (α:=α); unfold a; positivity
   have hg: 0 < g:= lt_min (by norm_num) hγ
   have hg':-(a*(1-t)) = g:=by unfold t; field_simp; ring
   have he:1<t:=lt_add_of_pos_right _ (by positivity); have ht':a*(1-t) > -(1/32):=by linarith only [hg',show g ≤ (1:ℝ)/64 from min_le_left ..]; -- replace
   obtain ⟨j,hj,hh,hT⟩:= trapeze C.S t he C.path.levels.fits.mesh; refine ⟨t,j,hw,he,by rw [neg_mul,hg']; exact hg,by rw [neg_mul,hg']; exact (min_le_left ..).trans (by norm_num),by rw [neg_mul,hg']; exact min_le_right ..,hj,hT,?_⟩
   let S:= C.path.levels; let L₁:= S.S
   let q:ℝ:= totalDeg d - D
   have hp:(D:ℝ)+q=totalDeg d:=by dsimp [q]; ring
   let A (i:ℕ)(s:α):= expenditure C (j i) i d q s w
   let Z'(i:ℕ):= basket S (lamp*C.S.block i) (j i) (i+1) (renal S) (near S) ((packet (α:=α) (renal S)) (i+1)) (A i)
   let c(i:ℕ):=1+(S.params i).columns
   let e (i:ℕ):= 4*(c i)*(2*((C.S.a (i+1))^D*(bling S i*(4*(1/Z' i)))))
   have hz: Note C.S c 0:= (Note.notes C.S 1 zero_lt_one).extra (fuNote C)
   have hf:= banket C hG
   have haD:= (Note.note_a C.S).scales C.path.levels.fits.mesh |>.powerN D
   have hρ:= rhythm' C d D q hG t hT hj hV hY hp hw lamp
   have hE: Note C.S e (-(D:ℝ) + -a*(1-t)+D):= by
       have h₀:=Note.notes S.S 4 (by norm_num); let hρ:= (Note.notes C.S 1 one_pos).splits hρ; exact (((h₀.mills hz).mills ((Note.notes C.S 2 two_pos).mills (haD.mills (hf.mills (h₀.mills hρ))))).swapP (by unfold a; ring))
   refine ⟨e,hE,fun v hW' F=>?_⟩
   filter_upwards [fees' C d D q hG t hT hj hV hY hp hw lamp hW k hK ht', installation C hG hV lamp p,eventually_ge_atTop k,eventually_all.mpr (fun i:α=>hj.eventually_ge_atTop (C.ref (d i))), hh,Push.GridApprox.plenty C.path.levels p (lensScope C D)] with i ⟨⟨he,hp⟩,hϑ⟩ ⟨hM,hL⟩ hN hK' hj' hU
   exact bunch_box C p k (j i) i D d q v hx.1 hN hj' F h ht hW lamp w _ _ _ _ hW' hw (Real.exp_pos _) L hx hK hK' hM (packet (α:=α) (renal _)) (bling _) hV' (hσ α) (adjusted C D hV' hχ) (hK.trans hN) rfl rfl hU (by push_cast at hL; exact hL) hp he (le_refl _) hϑ
end YM.MultipleContact.Bunching
