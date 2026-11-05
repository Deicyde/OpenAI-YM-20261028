import YM.MultipleContact.Matching.Broad
import YM.MultipleContact.Sharp
import YM.MergeProof.North.Burrough
import YM.MergeProof.North.Lauder
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Matching
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
variable (V: C.label d) (T:C.label 4) (hp:D+h=d+4) {u ψ:ℕ→ℝ}{W:Worth} (hG:G.Simple)(hW:Scrim C W u ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r D')
variable (hV:Velour C (renal C.path.levels) r D')(p k:ℕ)(L:Stock.Tabs C.path.levels)(hx:Stock.Tabs.opens C.path.levels 1 p k)
def Statement (C:Family G)(d l:ℕ)(a:ℝ)(γ:ℝ) (t:ℝ)(j:ℕ→ℕ) (p k D:ℕ)(w:ℝ):Prop:= 0<w∧1<t ∧ 0 < -a*(1-t) ∧ -a*(1-t) ≤ 1/32 ∧ -a*(1-t) ≤ γ ∧ Tendsto j atTop atTop ∧ Tendsto (fun i:ℕ=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 t) ∧ ∃ E:ℕ→ℝ, Note C.S E (-D+ -a*(1-t) + D) ∧ ∀ (v:C.label d)(y:C.label l) (hx:(C.labels.level d).coeffSize v ≤w)(hy:(C.labels.level l).coeffSize y ≤w)(F:Extraction.Order), ∀ᶠ i in atTop, (Box C p (j i) i D d l (d+l-(D:ℝ)) v y F (lista C D i*(2*E i)) (2*(stakes C p k / pitts C i)))
structure Matching (C:Family G):Prop where
  fees' : ∀ d l D p k:ℕ,∀ γ:ℝ,0<γ→Stock.Tabs.opens C.path.levels 1 p k→C.ref D ≤ k →∀ w> (0:ℝ),let a:ℝ:= (d:ℝ)+l+8; ∃ (t:ℝ)(j:ℕ→ℕ),Statement C d l a γ t j p k D w
variable (hY:Money C.path.levels)
include hY
include hW hG L hV
lemma amounts (ht:Created C)(h:C.Makes): Matching C:=by
   refine ⟨fun d l D p k γ hγ hx hK w hw=>?_⟩
   obtain ⟨χ,h'⟩:= hV.mother
   let a:ℝ:= (d:ℝ)+l+8; let g:= min ((1:ℝ)/64) γ; let t:=1+g/a; have ha:0<a:=by unfold a; positivity
   have hg: 0 < g:= lt_min (by norm_num) hγ
   have hg':-(a*(1-t)) = g:=by unfold t; field_simp; ring
   have he:1<t:=lt_add_of_pos_right _ (by positivity); have ht':a*(1-t) > -(1/32):=by linarith only [hg',show g ≤ (1:ℝ)/64 from min_le_left ..]; -- replace
   obtain ⟨j,hj,hh,hT⟩:= trapeze C.S t he C.path.levels.fits.mesh; refine ⟨t,j,hw,he,by rw [neg_mul,hg']; exact hg,by rw [neg_mul,hg']; exact (min_le_left ..).trans (by norm_num),by rw [neg_mul,hg']; exact min_le_right ..,hj,hT,?_⟩
   let S:= C.path.levels; let L₁:= S.S
   let q:= (d:ℝ)+l-D
   have hp:(D:ℝ)+q=(d:ℝ)+l:=by dsimp [q]; ring
   let A (i:ℕ):= sums C (j i) i d l q w w
   let Z'(i:ℕ):= wend S (C.S.block i) (j i) (i+1) (renal S) (near S) (renal S (i+1)) (A i)
   let c(i:ℕ):=1+(S.params i).columns
   let e (i:ℕ):= 4*(c i)*(2*((C.S.a (i+1))^D*(bling S i*(4*(1/Z' i)))))
   have hz: Note C.S c 0:= (Note.notes C.S 1 zero_lt_one).extra (fuNote C)
   have hf:= banket C hG
   have haD:= (Note.note_a C.S).scales C.path.levels.fits.mesh |>.powerN D
   have hρ:= rhythm C D d l q hG t hT hj hV hY hw hw hp
   have hE: Note C.S e (-(D:ℝ) + -a*(1-t)+D):= by
       have h₀:=Note.notes S.S 4 (by norm_num); let hρ:= (Note.notes C.S 1 one_pos).splits hρ; exact (((h₀.mills hz).mills ((Note.notes C.S 2 two_pos).mills (haD.mills (hf.mills (h₀.mills hρ))))).swapP (by unfold a; ring))
   refine ⟨e,hE,fun v y hW' hW₁ F=>?_⟩
   filter_upwards [fees C D d l q hG t hT hj hV hY hw hw hp hW k hK ht', setup C hG hV p,eventually_ge_atTop k,hj.eventually_ge_atTop (C.ref d), hj.eventually_ge_atTop (C.ref l), hh,Push.GridApprox.plenty C.path.levels p (lensScope C D)] with i ⟨⟨he,hp⟩,hϑ⟩ ⟨hM,hL⟩ hN hK' hI hj' hU
   exact corner C p k (j i) i D d l q v y hx.1 hN hj' F h ht hW w w _ _ _ _ hW' hW₁ hw hw (Real.exp_pos _) L hx hK hK' hI hM (renal _) (bling _) (h' D) (hK.trans hN) rfl rfl hU (by push_cast at hL; exact hL) hp he (le_refl _) hϑ
end YM.MultipleContact.Matching
