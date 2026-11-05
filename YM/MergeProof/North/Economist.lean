import YM.MergeProof.North.Brim
import YM.MergeProof.North.Burrough
import YM.MergeProof.North.Lauder
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
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
structure Economics : Prop where
   fees : ∀ d D h:ℕ,D+h=d+4 → ∃ (t:ℝ)(j:ℕ→ℕ), 1<t∧ Tendsto j atTop atTop ∧ Tendsto (fun i:ℕ=>Q (j i)/Q i) atTop (𝓝 t) ∧ ∀ p k:ℕ,Stock.Tabs.opens C.path.levels 1 p k→C.ref D ≤ k →∀ (v:C.label d)(T:C.label 4)(F:Extraction.Order), ∀ᶠ i in atTop, ShellNode C p (j i) i D d h v T F (2*(stakes C p k / pitts C i))
include hW hG L hV
lemma laurelE (ht:Created C)(h:C.Makes): Economics C:=by
   obtain ⟨χ,h'⟩:= hV.mother
   constructor; intro d D l hp
   let a:ℝ:= (d:ℝ)+4+8; let t:=1+1/(64*a); have ha:0<a:=by unfold a; positivity
   have he:1<t:=lt_add_of_pos_right _ (by positivity); have ht':a*(1-t) > -(1/32):=by rw [show a*(1-t)= -(1/64) by unfold t; field_simp; ring]; norm_num
   obtain ⟨j,hj,hh,hT⟩:= trapeze C.S t he C.path.levels.fits.mesh; refine ⟨t,j,he,hj,hT,fun p k hx hK v y F=>?_⟩
   let b:=max 1 ((C.labels.level 4).coeffSize y); let w:= max 1 ((C.labels.level d).coeffSize v)
   have hb:0<b:=zero_lt_one.trans_le (le_max_left ..); have hw:0<w:=zero_lt_one.trans_le (le_max_left ..)
   filter_upwards [pricey C D d l hG t hT hj hV hb hw hp hW k hK ht', lightness C hG hV p,eventually_ge_atTop k,hj.eventually_ge_atTop (C.ref d), hj.eventually_ge_atTop (C.ref 4), hh,Push.GridApprox.plenty C.path.levels p (lensScope C D)] with i ⟨⟨he,hp⟩,hϑ⟩ ⟨hM,hL⟩ hN hK' hI hj' hU
   exact bricks C p k (j i) i D d l v y hx.1 hN hj' F h ht hW b w _ _ _ _ (le_max_right ..) (le_max_right ..) hw hb (Real.exp_pos _) L hx hK hK' hI hM (renal _) (bling _) (h' D) (hK.trans hN) rfl rfl hU (by push_cast at hL; exact hL) hp he (le_refl _) hϑ
omit hW L
lemma fugacious : Note C.S (fun i=> fuga (P) (i+1)) (-1):= (fuchsia C hG hV).scales C.path.levels.fits.mesh -- remove hW etc
end YM.MergeProof.Ribbons
