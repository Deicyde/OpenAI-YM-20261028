import YM.MultipleContact.Matching.Costs
import YM.MultipleContact.Bunch.Sale
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Bunching
open Matching
open YM.MergeProof YM.MergeProof.Ribbons
open Function Filter Lattice RG MeasureTheory Asymptotics Finset Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open scoped Topology BigOperators Classical
variable {α: Type}[Fintype α][Inhabited α][DecidableEq α]
def totalDeg (d:α→ℕ):ℕ:=∑ s:α,d s
private lemma toll_match {G:Gauge}(Ain:Levels G)(L:Lattice.Side) (j i:ℕ)(δ φ:ℕ→ℝ)(η:ℝ)(a:Bool→ℝ)(b:Bool): Matching.wicket Ain L j i δ φ η a b =
 (η * (δ i * krill Ain.S j (i+1) (δ j*(φ j*a b)))) / Real.exp (((Ain.budget i).supportExponent+1/2)*↑((2*Matching.extra Ain L i+1)^4:ℕ)):=rfl
variable {G:Gauge}(C:Family G)(d:α→ℕ)(D:ℕ)(h:ℝ){x:ℝ} {j : ℕ→ℕ}
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
variable (hY:Money C.path.levels){w:ℝ}(htgt:(D:ℝ)+h=totalDeg d)(hw:0<w)
local notation "F"=> fun i=> fuga C.path.levels (i+1)
variable (lamp:Lattice.Side)
local notation "A"=> fun (i:ℕ)=> fun b=> expenditure C (j i) i d h b w
local notation "Z'"=> fun (i:ℕ)=> basket C.path.levels (lamp*C.S.block i) (j i) (i+1) δ η ((packet (α:=α) δ) (i+1)) ((A) i)
local notation "N"=>Note C.S
local notation "M"=> (((totalDeg d:ℝ)+4*(Fintype.card α))*(1-t))
open Accent
include hj hT hV hG hY

private lemma note_family {S:Schedule}(u:α→ℝ)(f:α→ℕ→ℝ)(he:∀s,Note S (f s) (u s)): Note S (fun i=> ∏ s:α,f s i) (∑s:α,u s):=by
   suffices hP:∀t:Finset α,Note S (fun i=> ∏ s∈t,f s i) (∑ s∈t,u s) by exact hP _
   intro t; induction t using Finset.induction with
   | empty=> simpa [Finset.prod_empty] using Note.notes S 1 one_pos
   | insert a b hb ih => simpa [Finset.prod_insert,Finset.sum_insert,hb] using (he a).mills ih
include hw d
lemma budget_cost : ∀s:α, N (fun i=> (A) i s) (-((d s:ℝ))*t+(if s=default then h else 0)):=by
   intro s
   have ht := plumN C (d s) hG w hw |>.relay j hj hT
   have he:= ((fuchsia C hG hV).scales C.path.levels.fits.mesh).powr h
   change N (fun i=> expenditure C (j i) i d h s w) _
   by_cases hx:s=default
   · convert ht.splits he using 1; ext; simp [expenditure,hx]; rw [if_pos hx]; ring
   convert ht using 1; ext; simp [expenditure,hx]; rw [if_neg hx]; simp
omit hw hT hj hV d in
lemma amount' :N (fun i=>Real.exp (((J (i+1)).supportExponent+1/2)*↑((2*Matching.extra C.path.levels (lamp*C.S.block i) (i+1)+1)^4:ℕ))) 0 := by
    let c(i:ℕ):= Matching.extra C.path.levels (C.S.block i) (i+1)
    let g (i:ℕ) := (J (i+1)).supportExponent+1/2
    let f(i:ℕ):ℝ:= Real.exp (g i*↑((2*c i+1)^4:ℕ))
    have ht: Note C.S f 0:= amount C hG hY
    have ht':Note C.S (fun i=> f i^(lamp.val^4)) 0:= (ht.powerN _).swapP (by simp)
    refine ⟨fun _=>Real.exp_pos _, squeeze_zero' ?_ ?_ ht'.pitch⟩
    · filter_upwards with i; simp only [Real.log_exp]; exact div_nonneg (mul_nonneg (by linarith [(J (i+1)).exponent_pos]) (Nat.cast_nonneg _)) (RG.Shoot.scale_nn (C.path.levels) i)
    filter_upwards with i; unfold f; simp only [Real.log_pow,Real.log_exp]; push_cast
    apply div_le_div_of_nonneg_right _ (RG.Shoot.scale_nn _ _)
    rw [show extra C.path.levels (lamp * C.S.block i) (i+1) = c i*lamp.val from ?_]; swap
    · unfold extra c; unfold Matching.extra
      rw [show (lamp * C.S.block i).val = lamp.val*(C.S.block i).val from rfl]; ring
    push_cast
    have hp:1≤ (lamp.val:ℝ):=by exact_mod_cast (show (1:ℕ)≤lamp.val from lamp.pos)
    have hg (i:ℕ):0≤g i:=by unfold g; linarith [(J (i+1)).exponent_pos]
    have he:(2*(↑(c i):ℝ)* lamp.val+1)^4≤ ((↑(lamp.val):ℝ)*(2*↑(c i)+1))^4:=by gcongr; rw [mul_add,mul_one]; linarith only [hp]
    change g i * _ ≤ _; nlinarith only [mul_le_mul_of_nonneg_left he (hg i)]
omit hV in
lemma gains (xs:ℕ→α→ℝ) (u:α →ℝ) (s:α)(hA:N (fun i=>xs i s) (u s)):N (fun i=> Matching.wicket C.path.levels (lamp*C.S.block i) (j i) (i+1) δ η ((packet (α:=α) δ) (i+1)) (fun _=>xs i s) false) (u s+4*(1-t)):=by
   have hh:C.S.Gentle:= C.path.levels.fits.mesh
   obtain ⟨hs,he⟩:= mintN C hG
   have hF:=Note.note_a C.S
   have hN:=((hs.relay j hj hT).mills ((he.relay j hj hT).mills hA)).splits (Note.notes _ 16 (by norm_num))
   have hD:=((hF.relay j hj hT).splits ((hF.scales hh).scales hh)).powerN 4
   have hb:= Note.notes C.S (Fintype.card α:ℝ) (by exact_mod_cast (Fintype.card_pos_iff.mpr (by infer_instance):0<Fintype.card α))
   have hval:= ((hs.scales hh|>.splits hb).mills ((hs.scales hh).mills (hN.mills hD))).splits (amount' C hG hY lamp)
   simp_rw [toll_match]; exact hval.swapP (by ring)

include htgt
lemma rhythm' : Note C.S Z' (-D + M) :=by
   let u(s:α):ℝ:= -((d s:ℝ))*t+(if s=default then h else 0)
   have hg:= budget_cost C d h hG t hT hj hV hY hw
   have hx(s:α):= gains (d:=d) C hG t hT hj hY hw lamp A u s (hg s)
   have hZ:= note_family C hG t hT hj hV hY (fun s=>u s+4*(1-t)) _ hx
   suffices he:(∑s:α,(u s+4*(1-t)))= -D + M by exact hZ.swapP he
   unfold totalDeg at *; push_cast at *
   simp only [u,Finset.sum_add_distrib,← Finset.sum_mul,Finset.sum_neg_distrib,Finset.sum_const]
   rw [Finset.sum_ite_eq' Finset.univ,if_pos (mem_univ (default:α)), Finset.card_univ]
   simp only [nsmul_eq_mul]
   linarith only [htgt]
local notation "Ne"=> N
variable {u ψ:ℕ→ℝ}{W:Worth}
variable (hW:Scrim C W u ψ (near C.path.levels) (renal C.path.levels) (fly C.path.levels) r D')
local notation "X"=>bling C.path.levels
local notation "c"=>pitts C
local notation "e"=> fun i=> 4*(1+(C.path.levels.params i).columns)*(2*(C.S.a (i+1)^D*(X i*(4*(1/((Z') i))))))
include hj hT hV hG hY hW htgt hw
lemma fees' (k:ℕ)(hK:C.ref D ≤ k)(he: -(1/32)< M) : ∀ᶠ i in atTop, (0<(Z') i ∧ march (fun _:Unit=>(c) i) η k i () ≤ δ i * (((Z') i)/(16*X i)))∧ 32*(1+(C.path.levels.params i).columns)* (c) i * ‖alto C.path k D‖*((e) i/gainChart C.path i k) ≤ fly C.path.levels D k/2:=by
   let S:= C.S; have ht:Ne (c) (1/32):= Note.bell_exp S _; have hx:= rhythm' C d D h hG t hT hj hV hY htgt hw lamp; have hy:= Note.note_a S; have hf:= banket C hG
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
omit hj hT hY hW htgt hw d D in
lemma installation (p:ℕ):∀ᶠ i in atTop, 32*(topZone C.path.levels (lamp*C.S.block i) (i+1)) ≤ C.S.a p ∧ C.S.a (i+1)*((((J (i+1)).B^2+1+2*Matching.patch C.path.levels (lamp*C.S.block i) (i+1)):ℕ):ℝ)≤ C.S.a p:=by
   have hz:C.S.Gentle:= C.path.levels.fits.mesh
   have hl:Note C.S (fun _=>(lamp.val:ℝ)) 0:= Note.notes _ _ (Nat.cast_pos.mpr lamp.pos)
   have hh:= Note.notes C.S (C.S.a p) (C.S.a_pos p)
   have hx:Note C.S (fun i=>topZone P (lamp*C.S.block i) (i+1)) (-1):=by
      simpa only [topZone,show ∀ i, (lamp*C.S.block i).val=lamp.val*(C.S.block i).val from (fun _=>rfl), Nat.cast_mul] using! ((hl.mills (stepar C.path.levels)).mills ((fuchsia C hG hV).scales hz) |>.swapP (by norm_num))
   have hM:=((Note.notes C.S 32 (by norm_num)).mills hx).outweigh hh (by norm_num)
   refine hM.and ?_
   have hv: Ne (fun i=> ((((J (i+1)).B)^2+1+2*Matching.patch C.path.levels (lamp*C.S.block i) (i+1):ℕ):ℝ)) 0:=by
       unfold Matching.patch extra; simp only [show ∀ i,(lamp*C.S.block i).val=lamp.val*(C.S.block i).val from (fun _=>rfl)] -- rw foreach occurrence okay binder
       push_cast
       have he:Ne (fun i=> (((J (i+1)).B:ℝ))^2) 0:= ((briar C hG hV).scales hz|>.powerN 2).swapP (by norm_num); have hE:=((briar C hG hV).scales hz); have hv':= (((((Note.notes C.S 1024 (by norm_num)).mills (hl.mills (stepar C.path.levels))).mills hE).mills hE).swapP (by ring : 0+(0+0)+0+0=(0:ℝ))); exact (he.extra (Note.notes _ _ (by norm_num))).extra (((Note.notes C.S 2 two_pos).mills hv').swapP (by norm_num))
   exact ((Note.note_a C.S|>.scales hz).mills hv).outweigh hh (by norm_num)
end YM.MultipleContact.Bunching
