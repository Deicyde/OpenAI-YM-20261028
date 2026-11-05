import YM.MultipleContact.Matching.Delay
import YM.MultipleContact.Matching.Trade
import YM.MergeProof.North.Burrough
import YM.MergeProof.North.Wicker
import YM.Progress.CLASSICAL_KIN_RECURSION.Weir
import YM.Push.LOOP_COEFFICIENT.Block.Explain
import YM.Push.LOOP_COEFFICIENT.Fine.Budgets
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Matching
open YM.MergeProof YM.MergeProof.Ribbons
open Function Filter Lattice RG MeasureTheory Asymptotics Finset Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G)(D d l:ℕ)(h:ℝ){x:ℝ} {j : ℕ→ℕ}
set_option quotPrecheck false
local notation "P"=>C.path.levels
local notation "Q"=>C.S.scale
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
local notation "J"=> C.path.levels.budget
local notation "H"=> C.path.levels.clock.hatBeta
variable (hG:G.Simple)(t:ℝ) (hT:Tendsto (fun i=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 t)) (hj:Tendsto j atTop atTop) -- notation binder
variable {r:ℕ→ℕ}{D':∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (hV:Velour C (renal C.path.levels) r D')
variable (hY:Money C.path.levels){b a:ℝ}(hb:0<b)(ha:0<a)(hp:(D:ℝ)+h=(d:ℝ)+l)
local notation "F"=> fun i=> fuga C.path.levels (i+1)
local notation "A"=> fun (i:ℕ)=> sums C (j i) i d l h b a
local notation "Z'"=> fun (i:ℕ)=> wend C.path.levels (C.S.block i) (j i) (i+1) δ η (δ (i+1)) ((A) i)
local notation "N"=>Note C.S
local notation "M"=> (((d:ℝ)+l+8)*(1-t))
open Accent
include hj hT hV hG hY
open YM.PhysicalNext YM.PhysicalNext.Repeat Ribbons
omit hj hT hV
lemma amount :N (fun i=>Real.exp (((J (i+1)).supportExponent+1/2)*↑((2*extra C.path.levels (C.S.block i) (i+1)+1)^4:ℕ))) 0 := by
    refine ⟨fun _=> Real.exp_pos _, squeeze_zero' ?_ ?_ (banket C hG|>.pitch)⟩ -- change below
    · filter_upwards; intro i; simp only [Real.log_exp]; exact div_nonneg (mul_nonneg (by linarith [(J (i+1)).exponent_pos]) (Nat.cast_nonneg _)) (Shoot.scale_nn (C.path.levels) i)
    filter_upwards; intro i; rw [Real.log_exp,bling,Real.log_exp]; exact div_le_div_of_nonneg_right (hY i) (Shoot.scale_nn _ _)
include hj hT
lemma priceEach {w:ℕ→Bool→ℝ}(v:Bool)(hw:N (fun i=>w i v) x): N (fun i=> wicket C.path.levels (C.S.block i) (j i) (i+1) δ η (δ (i+1)) (w i) v) (x+4*(1-t)):=by
   have hh:C.S.Gentle:=C.path.levels.fits.mesh; obtain ⟨hs,he⟩:= mintN C hG
   have hF:=Note.note_a C.S; have hx:= ((hs.relay j hj hT).mills ((he.relay j hj hT).mills hw)).splits (Note.notes C.S 16 (by norm_num)); have hb := ((hF.relay j hj hT).splits ((hF.scales hh).scales hh)).powerN 4 -- ratio
   exact (((hs.scales hh|>.mills ((hs.scales hh).mills (hx.mills hb))).splits (amount C hG hY)).swapP (by push_cast; ring))
include D hp ha hb hV
lemma rhythm : Note C.S Z' (-D + M) :=by
   have hg:= plumN C d hG a ha|>.relay j hj hT; have he:= ((plumN C l hG b hb).relay j hj hT).splits (((fuchsia C hG hV).scales C.path.levels.fits.mesh).powr h); unfold wend
   apply ((priceEach _ hG _ hT hj hY (w:=A) false (by exact hg)).mills (priceEach _ hG _ hT hj hY (w:=A) true (by exact he))).swapP
   have hi:(d:ℝ)+l-h=D:=by linarith
   push_cast; rw [←hi]; ring
local notation "Ne"=> N
variable {u ψ:ℕ→ℝ}{W:Worth}
variable (hW:Scrim C W u ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r D')
local notation "X"=>bling C.path.levels
local notation "c"=>pitts C
local notation "e"=> fun i=> 4*(1+(C.path.levels.params i).columns)*(2*(C.S.a (i+1)^D*(X i*(4*(1/((Z') i))))))
include hj hT hV hG hY hW hb ha hp
lemma fees (k:ℕ)(hK:C.ref D ≤ k)(he: -(1/32)< M) : ∀ᶠ i in atTop, (0<(Z') i ∧ march (fun _:Unit=>(c) i) η k i () ≤ δ i * (((Z') i)/(16*X i)))∧ 32*(1+(C.path.levels.params i).columns)* (c) i * ‖alto C.path k D‖*((e) i/gainChart C.path i k) ≤ fly C.path.levels D k/2:=by
   let S:= C.S; have ht:Ne (c) (1/32):= Note.bell_exp S _; have hx:= rhythm C D d l h hG t hT hj hV hY hb ha hp; have hy:= Note.note_a S; have hf:= banket C hG
   let q:= fly C.path.levels D k; have hq:0<q:= hW.grows _ _ hK
   have hr:= (Note.notes S 16 (by norm_num)).mills hf; have hI:= (mintN C hG).1.mills (hx.splits hr)
   let v i:= 1+(C.path.levels.params i).columns
   let w:= ‖alto C.path k D‖; have hw:0 < w:=by unfold w; rw [alto_norm]; exact inv_pos.mpr (pow_pos (C.S.a_pos _) _)
   have hz: Ne v 0:= (Note.notes C.S 1 zero_lt_one).extra (fuNote C)
   have hc:= ((Note.notes C.S 32 (by norm_num)).mills hz).mills ht|>.mills (Note.notes _ w hw)
   have haD:= (Note.note_a S).scales C.path.levels.fits.mesh |>.powerN D
   have hE: Ne e (-M):= by
       have h₀:=Note.notes S 4 (by norm_num); exact (((h₀.mills hz).mills ((Note.notes S 2 two_pos).mills (haD.mills (hf.mills (h₀.mills ((Note.notes S 1 one_pos).splits hx)))))).swapP (by ring))
   have hF:Ne (fun i=>gainChart C.path i k) (1/8):=by
       let r:ℝ:=Real.exp ((1/8:ℝ)*Q k)
       have hv:= (Note.bell_exp S (1/8)).splits (Note.notes S r (Real.exp_pos _))
       unfold gainChart; simp_rw [mul_sub,Real.exp_sub]; exact hv.swapP (sub_zero _)
   have hH:= (hc.mills (hE.splits hF)).outweigh (Note.notes C.S (q/2) (half_pos hq)) (by linarith)
   let u i:= ((c) i)* (S.a i/S.a k)^(D+1)*(1/q)
   have hJ:= (ht.mills ((hy.splits (Note.notes S _ (S.a_pos k))).powerN (D+1))).mills (Note.notes S (1/q) (by positivity)); have hh:=hJ.outweigh hI (by push_cast; linarith)
   filter_upwards [eventually_ge_atTop k,hH,hh] with i hi hk hh
   have hU := seeing C D hW (ht.pos i) i k hK hi
   refine ⟨⟨hx.pos _,hU.trans (le_trans ?_ hh)⟩,hk⟩
   apply mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (fly_le C i D) hq.le) (mul_nonneg ((ht.pos i).le) (pow_nonneg (div_nonneg (S.a_pos i|>.le) (S.a_pos k|>.le)) _))
omit hj hT hY hW hb ha hp D
omit hG hV in
lemma stepar (a:Levels G) : Note a.S (fun i=>(↑(a.S.block i).val:ℝ)) 0 :=by
    have ht:=Note.note_a a.S
    convert ht.splits (ht.scales a.fits.mesh) using 1
    · ext i; rw [a.S.a_step]; field_simp [(a.S.a_pos i).ne']
    exact (sub_self (-(1:ℝ))).symm
lemma setup (p:ℕ):∀ᶠ i in atTop, 32*(topZone C.path.levels (C.S.block i) (i+1)) ≤ C.S.a p ∧ C.S.a (i+1)*((((J (i+1)).B^2+1+2*patch C.path.levels (C.S.block i) (i+1)):ℕ):ℝ)≤ C.S.a p:=by
   have hz:C.S.Gentle:=C.path.levels.fits.mesh
   have hh:= (Note.notes C.S (C.S.a p) (C.S.a_pos p)); refine ((Note.notes C.S 32 (by norm_num)|>.mills ((stepar C.path.levels).mills ((fuchsia C hG hV).scales hz))).outweigh hh (by norm_num)).and ?_
   have hv: Ne (fun i=> ((((J (i+1)).B)^2+1+2*patch C.path.levels (C.S.block i) (i+1):ℕ):ℝ)) 0:=by
       unfold patch extra; push_cast; have he:Ne (fun i=> (((J (i+1)).B:ℝ))^2) 0:= ((briar C hG hV).scales hz|>.powerN 2).swapP (by norm_num); have hE:=((briar C hG hV).scales hz); have hv':= (((((Note.notes C.S 1024 (by norm_num)).mills (stepar C.path.levels)).mills hE).mills hE).swapP (by ring : 0+0+0+0=(0:ℝ))); exact (he.extra (Note.notes _ _ (by norm_num))).extra (((Note.notes C.S 2 two_pos).mills hv').swapP (by norm_num))
   exact ((Note.note_a C.S|>.scales hz).mills hv).outweigh hh (by norm_num)
end YM.MultipleContact.Matching
