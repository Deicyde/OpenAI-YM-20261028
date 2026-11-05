import YM.MergeProof.North.Economist
import YM.MergeProof.Noel

/-! Stronger spatial-error exponent from paying the replicated norm on a fixed
exterior cell with the full excess engineering degree. The hypotheses are stronger
materials from the *actual* construction before CLOSED. Not new smooth
approximating probability measures. Adapts the existing proof of `pricey`
with a changed marching budget, keeping the call to `quilled` as on inputs
without radial normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG MeasureTheory Asymptotics Finset Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open scoped Topology BigOperators Classical
structure Materials {G : Gauge} (C : Family G) : Prop where
  hG : G.Simple
  makes : C.Makes
  created : Created C
  opens : Stock.Tabs C.path.levels
  room : ∃ (r : ℕ → ℕ) (D : ∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p m.succ) (C.path.rep N p m))
    (u ψ:ℕ→ℝ) (W : Worth), Velour C (renal C.path.levels) r D ∧ Scrim C W u ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r D

variable {G:Gauge}(C:Family G)(D d h:ℕ){x:ℝ} {j : ℕ→ℕ}
set_option quotPrecheck false
local notation "P"=>C.path.levels
local notation "Q"=>C.S.scale
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
local notation "J"=> C.path.levels.budget
local notation "H"=> C.path.levels.clock.hatBeta
variable (hG:G.Simple)(t:ℝ) (hT:Tendsto (fun i=>C.S.scale (j i)/C.S.scale i) atTop (𝓝 t)) (hj:Tendsto j atTop atTop)
variable {r:ℕ→ℕ}{D':∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (hV:Velour C (renal C.path.levels) r D')
variable {b a:ℝ}(hb:0<b)(ha:0<a)
local notation "F0"=> fun i=> fuga C.path.levels (i+1)
local notation "A"=> fun (i:ℕ)=> whims C (j i) i d 0 b a
local notation "Z'"=> fun (i:ℕ)=> ventola C.path.levels (j i) (i+1) δ η (δ (i+1)) ((A) i)
local notation "Ne"=>Note C.S
local notation "M"=> (((d:ℝ)+4+8)*(1-t))
open Accent Source Extra.Histories
variable {u ψ:ℕ→ℝ}{W:Worth}
variable (hW:Scrim C W u ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r D')
local notation "X"=>bling C.path.levels
def posts (C:Family G)(d D i:ℕ):= Real.exp (((D:ℝ)-d-4+(1/32:ℝ))*C.S.scale i)
local notation "c"=>posts C d D
local notation "e"=> fun i=> 4*(1+(C.path.levels.params i).columns)*(2*(C.S.a (i+1)^D*(X i*(4*(1/((Z') i))))))
include hj hT hV hG hW hb ha D
lemma price_shift (k:ℕ)(hK:C.ref D ≤ k)(he: -(1/32)< M) : ∀ᶠ i in atTop, (0<(Z') i ∧ march (fun _:Unit=>(c) i) η k i () ≤ δ i * (((Z') i)/(16*X i)))∧ 32*(1+(C.path.levels.params i).columns)* (c) i * ‖alto C.path k D‖*((e) i/gainChart C.path i k) ≤ fly C.path.levels D k/2:=by
   let S:= C.S; have ht:Ne (c) ((D:ℝ)-d-4+1/32):= Note.bell_exp S _; have hx:= quilled C (d+4) d 0 hG t hT hj hV hb ha (add_zero _); have hy:= Note.note_a S; have hf:= banket C hG
   let q:= fly C.path.levels D k; have hq:0<q:= hW.grows _ _ hK
   have hr:= (Note.notes S 16 (by norm_num)).mills hf; have hI:= (mintN C hG).1.mills (hx.splits hr)
   let v i:= 1+(C.path.levels.params i).columns
   let w:= ‖alto C.path k D‖; have hw:0 < w:=by unfold w; rw [alto_norm]; exact inv_pos.mpr (pow_pos (C.S.a_pos _) _)
   have hz: Ne v 0:= (Note.notes C.S 1 zero_lt_one).extra (fuNote C)
   have hc:= ((Note.notes C.S 32 (by norm_num)).mills hz).mills ht|>.mills (Note.notes _ w hw)
   have haD:= (Note.note_a S).scales C.path.levels.fits.mesh |>.powerN D
   have hE: Ne e (-(D:ℝ)+d+4-M):= by
       have h₀:=Note.notes S 4 (by norm_num); exact (((h₀.mills hz).mills ((Note.notes S 2 two_pos).mills (haD.mills (hf.mills (h₀.mills ((Note.notes S 1 one_pos).splits hx)))))).swapP (by push_cast;ring))
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
omit D hj hT hV hG hW hb ha
/-- Available without changing the trials, through any requested output degree:
it is the normalization of two fixed inserted fields (one of weight four),
not a request for input estimates at unrealistically high total dimension. -/
lemma funded (s : Materials C) (d D : ℕ) : ∃ (t:ℝ)(j:ℕ→ℕ),
    1<t ∧ Tendsto j atTop atTop ∧ Tendsto (fun i : ℕ => Q (j i)/Q i) atTop (𝓝 t) ∧
    ∀ p k:ℕ, Stock.Tabs.opens (P) 1 p k→C.ref D ≤ k→∀ (v:C.label d)(B:C.label 4)(F:Extraction.Order),
      ∀ᶠ i in atTop, ShellNode C p (j i) i D d 0 v B F (2*(stakes C p k / (posts C d D i))) := by
  obtain ⟨r,D',u,x,W,hV,hW⟩ := s.room
  obtain ⟨χ,h'⟩:= hV.mother

  let a:ℝ:= (d:ℝ)+4+8; let t:=1+1/(64*a); have ha:0<a:=by unfold a; positivity
  have he:1<t:=lt_add_of_pos_right _ (by positivity); have ht':a*(1-t) > -(1/32):=by rw [show a*(1-t)= -(1/64) by unfold t; field_simp; ring]; norm_num
  obtain ⟨j,hj,hh,hT⟩:= trapeze C.S t he C.path.levels.fits.mesh; refine ⟨t,j,he,hj,hT,fun p k hx hK v y F=>?_⟩
  let b:=max 1 ((C.labels.level 4).coeffSize y); let w:= max 1 ((C.labels.level d).coeffSize v)
  have hb:0<b:=zero_lt_one.trans_le (le_max_left ..); have hw:0<w:=zero_lt_one.trans_le (le_max_left ..)
  filter_upwards [price_shift C D d s.hG t hT hj hV hb hw hW k hK ht', lightness C s.hG hV p,eventually_ge_atTop k,hj.eventually_ge_atTop (C.ref d), hj.eventually_ge_atTop (C.ref 4), hh,Push.GridApprox.plenty C.path.levels p (lensScope C D)] with i ⟨⟨he,hp⟩,hϑ⟩ ⟨hM,hL⟩ hN hK' hI hj' hU
  exact bricks C p k (j i) i D d 0 v y hx.1 hN hj' F s.makes s.created hW b w _ _ _ _ (le_max_right ..) (le_max_right ..) hw hb (Real.exp_pos _) s.opens hx hK hK' hI hM (renal _) (bling _) (h' D) (hK.trans hN) rfl rfl hU (by push_cast at hL; exact hL) hp he (le_refl _) hϑ
end YM.MergeProof.Ribbons
