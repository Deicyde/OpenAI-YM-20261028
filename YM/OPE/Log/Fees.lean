import YM.OPE.Log.Pricing
import YM.OPE.Log.Join
/-! # Terminal quote

Menus: view price/gain at ordinary exponential layer. Never use these
auxiliary bounds as the log budgets through their own equality-grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Function Set Filter Lattice RG Wilson MergeProof Accent Ribbons Source Overlay Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage ManyCopies Next.Rank
open scoped Topology BigOperators
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{ι:Type*}{I:Type}[Fintype I] {l:Filter ι}{T x y e w:ι→ℝ}{a b p₀ u : ℝ}
    {m j k:ι→ℕ} {W r D} (L:LogPackage C W r D)(hG:G.Simple) (i₀:I)
local notation "Y"=> C.path.levels
local notation "S'"=> C.path.levels.budget
local notation "α"=> C.path.S.a
local notation "Γ"=> C.path.levels.clock
local notation "β"=> C.path.levels.clock.hatBeta
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
local notation "τ"=> fly C.path.levels
variable (hT:Tendsto T l atTop)
include L hT
local notation "ν"=> Fintype.card I
lemma gatherStamp (u v: ι→ℝ) (hm:Height C.S l T m a)(hj: Height C.S l T j a) (t:ℕ)
     (hu:ValueStamp l T u) (hv: ValueStamp l T v) (hf: ValueStamp l T (fun i=>C.S.a (j i)/ C.S.a (m i))) : ValueStamp l T (fun i=> ManyCopies.initial C.path (renal C.path.levels) (near C.path.levels) (m i) (j i) (u i) (v i) t):= by
    have he:= (renalStamp hT hj).mul (nearStamp hT hj); have hz:= ValueStamp.const (a:=8) hT (by norm_num); have hx:= (he.div hz|>.pow hT t).mul hv
    have hh: ValueStamp l T (fun i=> C.S.a (j i)/C.S.a (m i+1)):= by
       apply (hf.mul (blockWallet L hT hm)).congr; filter_upwards with i; rw [Schedule.a_step]; ring_nf; rw [inv_inv] -- field_simp? a_scale cancel
    exact (hu.pow hT t).mul (((hh.pow hT (4*t)).mul ((hu.div hz).pow hT (t*(t-0)))).mul hx)

omit L
private lemma stomp (hk:Height C.S l T k b)(hm:Height C.S l T m a)(hu:b<a) (hp:RateIs l T x p₀)(hf:∀ᶠ i in l,march (fun _:Unit=>w i) (near C.path.levels) (k i) (m i) ()≤ w i*(α (m i)/α (k i))^1*(τ 0 (m i)/τ 0 (k i))) (hw:RateIs l T w u)(h:u<a-b+p₀) : ∀ᶠ i in l,march (fun _:Unit=>w i) (near C.path.levels) (k i) (m i) () ≤ renal C.path.levels (m i)*(x i/(16*β (m i+1))):=by -- β abbreviation doesn't carry param! ok?
    have hz:= (renalStamp hT hm).zeroCost hT; have hh := (betaStamp hT (hm.step (Y).fits.mesh)).zeroCost hT; have hX := hz.mul (hp.div ((RateIs.const (c:=16) hT (by norm_num)).mul hh)); have a0:= ((hw.mul ((hm.mesh.div hk.mesh).power 1)).mul (((flyStamp hT hm 0).zeroCost hT).div ((flyStamp hT hk 0).zeroCost hT))).pays hT
    filter_upwards [hf,hX.overtakes a0 hT (by push_cast; linarith)] with i hi hp using hi.trans hp.le
-- actual receipt (could use monotonicity against bling only eventually)
include L hG
lemma shortAfford (hk:Height C.S l T k b)(hm:Height C.S l T m a)(hu:b<a)(hp:RateIs l T x p₀)(d:ℕ)(he:RateIs l T e (-d*a-p₀))(hw:RateIs l T w u)(h:u<(d+1/8)*(a-b)+p₀): ∀ᶠ i in l,
    march (fun _:Unit=>w i) (near C.path.levels) (k i) (m i) () ≤ renal C.path.levels (m i)*(x i/(16*β (m i+1))) ∧
    32*(1+(C.path.levels.params (m i)).columns)*w i*‖alto C.path (k i) d‖*(e i/gainChart C.path (m i) (k i)) ≤ τ d (k i)/2:=by
    have hz:= (renalStamp hT hm).zeroCost hT; have hh:=(betaStamp hT (hm.step (Y).fits.mesh)).zeroCost hT; have hT':= hz.mul (hp.div ((RateIs.const (c:=16) hT (by norm_num)).mul hh)); have a0:= ((hw.mul ((hm.mesh.div hk.mesh).power (d+1))).mul (((flyStamp hT hm d).zeroCost hT).div ((flyStamp hT hk d).zeroCost hT))).pays hT; have hy:u-(d+1)*(a-b)<p₀ := by linarith only [hu,h]
    have hp':= terminalAfford hG L.toPackage hk hm hT hu hp d he hw h
    filter_upwards [hT'.overtakes a0 hT (by push_cast; linarith only [hy]),hp',hw.pos,hk.grows.eventually_ge_atTop (C.ref d),hk.earlier hu hT hm] with i hi hp ht hh he using ⟨(seeing C d L.system ht (m i) (k i) hh he.le).trans hi.le,hp.2⟩

omit hT L hG
-- multiply ManyCopies.initial envelope
lemma start_scale (u a v:ℝ)(i j k:ℕ): ManyCopies.initial C.path δ η i j u (a*v) k=a*ManyCopies.initial C.path δ η i j u v k:= by unfold ManyCopies.initial compensation; ring -- invented notation δ global
lemma obey_quota (d j N p:ℕ) (u:C.label d) : C.S.a j^d * Spindle.paid C d j N p u = Next.UVStress.quota C d j N p u:= by
    have hh:= C.S.a_pos j; unfold Spindle.paid Price.awake; rw [Extra.Histories.Size.smul, show ((C.S.a j:ℂ)^d)⁻¹=alto C.path j d from rfl, alto_norm]; change C.S.a j^d*((C.S.a j^d)⁻¹*_) = _; rw [← mul_assoc,mul_inv_cancel₀ (by positivity),one_mul]; rfl
local notation "b!"=> Cells.center
structure ShortPrice (C : Family G)(g o : ℝ)(Q : I→ℝ)(p:ℕ)(d:I→ℕ)(k m j:ℕ) : Prop where
    quote (N q:ℕ)(hn:j<N)(hu:k ≤ N) : ∀ (s:(i:I)→C.label (d i))(r:I→Site (C.side j q)), (∀ i,Next.UVStress.quota C (d i) j N q (s i) ≤ Q i) → (∀ i,loops C j q (r i) (m+1)=0) → Next.Rank.Edition.Spaced (C.path.levels.budget j).B r →
       let V:= Cells.center C.S q hu 0; let f (i:I):=C.O N q (s i) ((C.S.toDepth hn.le q).embed (r i)); (∀ i, Cells.Interior (V.chamber 0) (f i))→ (∀ z:C.label p, Cells.Interior (V.chamber 0) (C.O N q z 0)) →
       ∃ z:C.label p, let g': Config G (C.side N q)→ℂ:= (fun u=>∏ i,f i u)-C.O N q z 0;
       Next.UVStress.quota C p m N q z ≤ g ∧ Cells.Interior (V.chamber 0) g' ∧ V.rootTest (C.beta N q) g' ≤ o
    step : C.ref p ≤ m
local notation "β'"=> C.path.levels.clock.hatBeta
-- can't use bound variables α macros; errors.
variable (A:ι→I→ℝ)(d:I→ℕ)(t:ℕ)[DecidableEq I]
include hT L hG i₀
local notation "X" => (∑ i,d i:ℕ)
local notation "Y'" => ((t:ℝ)+1/16)*(a-b)-(X:ℝ)*a
set_option maxHeartbeats 400000 in
lemma cost_funding (hk:Height C.S l T k b)(hm:Height C.S l T m a)(hj: Height C.S l T j a) (ha:b<a)
    (ht:∀ᶠ i in l,m i+1<j i)(hp:ValueStamp l T (fun i=>C.S.a (j i)/ C.S.a (m i)))
    (h:C.Makes)(hA:∀ s,ValueStamp l T (fun i=>A i s)) :
    ∃ g o : ι→ℝ, ValueStamp l T g ∧ RateLE l T o (- (Y')) ∧ ∀ᶠ i in l, ShortPrice C (g i * (C.S.a (m i))^t/(C.S.a (j i))^(∑ i,d i)) (o i) (A i) t d (k i) (m i) (j i):=by
    let P:=Stock.Tabs.chosen C.path.levels 1 L.tabs ∘ k; have hP:Height C.S l T P b:= hk.stock L.tabs; have hf(i):= show Stock.Tabs.opens C.path.levels 1 (k i) (P i) from Stock.Tabs.opened ..
    let B:= Fintype.card I; have hB:0<B:= Fintype.card_pos_iff.mpr ⟨i₀⟩; let s (i):= solvency L B (j i)
    let y(i):= ∏ b,τ (d b) (j i)/A i b; let x(i):= C.S.a (j i)^(X); let u(i):= ManyCopies.initial C.path δ η (m i) (j i) (s i) (y i) B; let w(i s):=τ (d s) (j i)/A i s*C.S.a (j i)^(d s)
    have hu(i): (∏ s,w i s) = x i*y i :=by
       unfold w; rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum] -- name
       exact mul_comm ..
    have hz: ValueStamp l T u:= gatherStamp L hT s y hm hj B (solvency_stamp L hT hj hB) (ValueStamp.prod hT (fun i _=>(flyStamp hT hj (d i)).div (hA i))) hp
    let Z i:= ManyCopies.initial C.path δ η (m i) (j i) (s i) (∏ b,w i b) B; have hZ i:Z i=x i*u i:=by unfold Z; rw [hu]; exact start_scale ..
    have hX : RateIs l T Z (-X*a):=by simp_rw [Z,hu,start_scale]; exact ((hj.mesh.power X).mul (hz.zeroCost hT)).swap (by ring)
    let f i:= 4*(1+(C.path.levels.params (m i)).columns)*(2* ((C.S.a (m i+1))^t*((β' (m i+1))*(4*(1/Z i)))))
    let g i:= 4*(1+(C.path.levels.params (m i)).columns)*(2* (((((Y).S.block (m i)).val:ℝ)⁻¹)^t*((β' (m i+1))*(4*(1/u i)))))
    have hV : ValueStamp l T (fun i=> 1+(C.path.levels.params (m i)).columns):=by
       let x i:= (C.path.levels.params (m i)).columns; have h:(∀ i,0 ≤ x i):= fun i=> zero_le_one.trans ((Y).params _|>.columns_ge)
       exact ⟨Eventually.of_forall (fun i=>add_pos_of_pos_of_nonneg one_pos (h i)), (Wallet.const hT _).add hT (columnsWallet L hT hm), (ValueStamp.const hT one_pos).down.invLe (Eventually.of_forall fun _=>one_pos) (Eventually.of_forall fun i=>le_add_of_nonneg_right (h i))⟩
    have hg: ValueStamp l T g:=by
       have h₄:= ValueStamp.const hT (by norm_num : (0:ℝ)<4); exact (h₄.mul hV).mul ((ValueStamp.const hT zero_lt_two).mul (((blockWallet L hT hm).inv.pow hT t).mul ((betaStamp hT (hm.step (Y).fits.mesh)).mul (h₄.mul ((ValueStamp.const hT one_pos).div hz)))))
    have h_U i : f i=g i*C.S.a (m i)^t/x i:= by unfold f g; rw [hZ,Schedule.a_step]; simp only [div_eq_mul_inv,mul_inv_rev,mul_pow]; ring
    have he: RateIs l T f (-t*a - -X*a):=by
       apply (((hg.zeroCost hT).mul (hm.mesh.power t)).div (hj.mesh.power X)).swap (by ring)|>.congr; exact Eventually.of_forall fun i=>(h_U i).symm
    let q i:= Real.exp ((Y')*T i); have hh:=(RateIs.exp (Y') hT); have hW:= shortAfford L hG hT hP hm ha hX t he hh (by linarith only [ha]); let o i:=2*(stakes C (k i) (P i)/q i)
    obtain ⟨χ,hχ⟩:= L.lightCuts.mother
    refine ⟨fun i=>2*g i,o,(ValueStamp.const hT zero_lt_two).mul hg,?_,?_⟩
    · simp_rw [o,div_eq_mul_inv]; exact ((RateLE.const (2:ℝ) hT).mul ((stock_price L.tabs hG hk hT).mul (hh.inv.pays hT))).mono (by linarith only)
    have hb := briar C hG L.accounting; have hm':= hm.step (Y).fits.mesh; let r' i:=m i+1; have hW' := (((height0 hb hm').power 2).add (RateIs.const hT one_pos) hT).mul hm'.mesh
    have hh: ∀ᶠ i in l,∀ x : ℕ,r' i ≤ x → B ≤ r x:= hm'.grows.eventually ((eventually_ge_atTop ((eventually_atTop.mp (L.spare.eventually_ge_atTop B)).choose)).mono (fun x hx y hy=> (eventually_atTop.mp (L.spare.eventually_ge_atTop B)).choose_spec y (hx.trans hy)))
    filter_upwards [hp.profit,ht,hX.pos,hP.earlier ha hT hm,hk.grows.eventually_ge_atTop (C.ref t), height_room hk hm hT ha (lensScope C t), hk.mesh.overtakes (hW'.pays hT) hT (by simp; linarith),hW, hh,eventually_all.mpr (fun i=> (hA i).profit),eventually_all.mpr (fun x=>hj.grows.eventually_ge_atTop (C.ref (d x)))] with i hi ht hX hK hT' hr hU hW hh hA hd
    have hw (p:ℕ): ((S' (r' i)).B^2+1:ℕ) ≤ (C.S.toDepth (((hf i).1.trans hK.le).trans (Nat.le_succ (m i))) p).count.val := by
       let v:= C.S.toDepth (((hf i).1.trans hK.le).trans (m i|>.le_succ)) p; have hl: (((S' (r' i)).B:ℝ)^2+1) ≤ v.count.val:= le_of_mul_le_mul_right (hU.le.trans_eq ((C.S.embeds_scale v).symm.trans (mul_comm ..))) (C.S.a_pos (r' i))
       exact_mod_cast hl
    have hτ(s):0 < τ (d s) (j i):= inv_pos.mpr (pow_pos (zero_lt_one.trans ((Y).fits.delayed _)) _)
    rw [show 2*g i*C.S.a (m i)^t / C.S.a (j i)^(X)=2*f i by rw [h_U]; unfold x; ring]
    refine ⟨fun N p hn hm' v Ω he' hx hy hi hv=>?_,hT'.trans ((hf i).1.trans hK.le)⟩
    have he I : w i I * Spindle.paid C (d I) (j i) N p (v I) ≤ τ (d I) (j i):= by
       unfold w; rw [mul_assoc, obey_quota]; exact (mul_le_mul_of_nonneg_left (he' I) (div_pos (hτ I) (hA I)|>.le)).trans_eq (div_mul_cancel₀ _ (hA I|>.ne'))
    exact joins_light C N (m i) p t (k i) (P i) i₀ (q i) (w i) Ω (hf i).1 hK.le hn ht.le d v h L.system L.literal (hχ t) L.tabs (hf i) (hT'.trans (hf i).1) hd he (fun s=>mul_pos (div_pos (hτ s) (hA s)) (pow_pos (C.S.a_pos _) _)) hr hx (hw _) hy (solvency_pos L _ hB) (solvency_le L _ hB) (short L) ht (fun k _ hp=> ⟨solvency_anti L B hB hG hp.le,short_affords L k⟩) (fun k hk _=>hh k hk) _ (fun _=>rfl) hi hv hX le_rfl (Real.exp_pos _) hW.1 le_rfl hW.2
end YM.OPE.Log
