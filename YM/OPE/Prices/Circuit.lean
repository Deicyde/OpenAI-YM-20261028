import YM.OPE.Prices.Hall
import YM.OPE.Sweep.Camp
import YM.OPE.Replicas.Budget

/-!
# Subpower-price output on sweep
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Filter Function Set Lattice RG Wilson MergeProof Accent Ribbons Source Overlay
open Bid ManyCopies PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open scoped Topology BigOperators
variable {G:Gauge}{C:Family G}{ι κ : Type*}{I:Type}[Fintype I][DecidableEq I](i₀:I){l : Filter ι} {f : Filter κ} {T : ι→ℝ} {a b c : ℝ}
variable {m k j q:ι→ℕ}
variable (hG:G.Simple){W r D} (L: Package C W r D)
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "P'"=> C.path.levels.budget
local notation "Λ" => C.S.scale
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "τ" => fly C.path.levels
local notation "X" => bling C.path.levels

lemma Height.plumBudget (d:I→ℕ) (p:I→ℝ)(hp:∀ i,0<p i) (hb:Height C.S l T j b)(hT:Tendsto T l atTop) (hG:G.Simple) : RateIs l T (fun i=>∏ x,plumR C (d x) (p x) (j i)) (-b*(∑ x,d x:ℕ)) :=by
    refine (RateIs.prod (S:=Finset.univ) (fun x _=> Columns.rescale (plumN C (d x) hG (p x) (hp x)) hb.grows hb.pace) hT).swap ?_; push_cast; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=> by ring
lemma Height.gathered {u v:ι→ℝ}{x:ℝ} (hm:Height C.S l T m a)(hj:Height C.S l T j b)(hT:Tendsto T l atTop)(hu:RateIs l T u 0)(hv:RateIs l T v x)(hG:G.Simple)(d:ℕ) : RateIs l T (fun i=> ManyCopies.initial C.path δ η (m i) (j i) (u i) (v i) d) (x - 4*d*(b-a)):=by
    have hx:= RateIs.const (c:=8) hT (by norm_num); have hh:= ((height0 (mintN C hG|>.1) hj|>.mul (height0 (mintN C hG|>.2) hj)).div hx).power d; have hp:= (hm.step C.path.levels.fits.mesh).mesh
    unfold ManyCopies.initial compensation; exact ((hu.power d).mul ((((hj.mesh.div hp).power (4*d)).mul ((hu.div hx).power (d*(d-0)))).mul (hh.mul hv))).swap (by push_cast; ring)

def terminalCost (C:Family G)(d i:ℕ)(y:ℝ):ℝ:= 4*(1+(C.path.levels.params i).columns)*(2*(C.S.a (i+1)^d*(bling C.path.levels i*(4*(1/y)))))

variable {p x e w:ι→ℝ}{y z:ℝ}
lemma key_cost (hm:Height C.S l T m a)(hT:Tendsto T l atTop) (hx:RateIs l T x y) (hG:G.Simple)(d:ℕ) : RateIs l T (fun i=> terminalCost C d (m i) (x i)) (-d*a-y) :=by
    have hh:=height0 (fuNote C) hm; have ht:=RateIs.const hT one_pos; have hr:=RateIs.const (c:=4) hT (by norm_num); have hi:=hr.mul (ht.add hh hT)
    have hz:= height0 (banket C hG) hm; have hp:= (hm.step C.path.levels.fits.mesh).mesh; exact (hi.mul ((RateIs.const hT zero_lt_two).mul ((hp.power d).mul (hz.mul (hr.mul (ht.div hx)))))).swap (by rw [max_self]; ring)

include hG L
lemma terminalAfford (hk:Height C.S l T k b)(hm:Height C.S l T m a)(hT:Tendsto T l atTop)(hu:b<a) (hp:RateIs l T x y)(d:ℕ)(he:RateIs l T e (-d*a-y))(hw:RateIs l T w z)(h:z<(d+1/8)*(a-b)+y) : ∀ᶠ i in l,
    march (fun _:Unit=>w i) η (k i) (m i) () ≤ δ (m i)*(x i/(16*X (m i))) ∧
    32*(1+(C.path.levels.params (m i)).columns)*w i*‖alto C.path (k i) d‖*(e i/gainChart C.path (m i) (k i)) ≤ τ d (k i)/2:=by
    obtain ⟨hs,hη⟩:= mintN C hG; have hz:=height0 hs hm; obtain ⟨hG',hD⟩:= gainRate d hm hk
    have hx' := key_cost hm hT hp hG d
    have hB:= ((RateIs.const (c:=16) hT (by norm_num)).mul (height0 (banket C hG) hm)); have hZ:=hz.mul (hp.div hB)
    have hU:=flyRate hG hk d; have hW:= ((RateIs.const (c:=32) hT (by norm_num)).mul ((RateIs.const hT one_pos).add (height0 (fuNote C) hm) hT)).mul hw
    have hW':= (hw.mul ((hm.mesh.div hk.mesh).power (d+1))).mul ((flyRate hG hm d).div hU); have ha : z-(d+1)*(a-b)<y:= by linarith only [hu,h];
    filter_upwards [hZ.overtakes (hW'.pays hT) hT (by push_cast; linarith only [ha]), (hU.div (RateIs.const hT zero_lt_two)).overtakes (((hW.mul hD).mul (he.div hG')).pays hT) hT (by rw [max_self]; linarith), hk.grows.eventually_ge_atTop (C.ref d), hk.earlier hu hT hm, hw.pos] with i h₁ h₂ hk hm hb using
      ⟨(seeing C d L.system hb (m i) (k i) hk hm.le).trans h₁.le,h₂.le⟩

variable (h:C.Makes)(d:I→ℕ)(s: (i:I)→ C.label (d i))(t:ℕ)
structure PriceAt (C:Family G)(g o : ℝ)(n : ℕ) (d : I→ℕ)(s:(i:I)→ C.label (d i))(J m j:ℕ) : Prop where
    quote (N p:ℕ)(hn:j<N)(hm:J ≤ N) : ∀ (r:I→Site (C.side j p)), (∀ i,loops C j p (r i) (m+1)=0) → Next.Rank.Edition.Spaced (C.path.levels.budget j).B r →
       let V:= Cells.center C.S p hm 0; let f (i:I):=C.O N p (s i) ((C.S.toDepth hn.le p).embed (r i)); (∀ i, Cells.Interior (V.chamber 0) (f i))→ (∀ z:C.label n, Cells.Interior (V.chamber 0) (C.O N p z 0)) →
       ∃ z:C.label n, let g': Config G (C.side N p)→ℂ:= (fun u=>∏ i,f i u)-C.O N p z 0;
       Next.UVStress.quota C n m N p z ≤ g ∧ Cells.Interior (V.chamber 0) g' ∧ V.rootTest (C.beta N p) g' ≤ o
    live : J≤ m
    step : C.ref n ≤ m
    goes : m+1 ≤ j
local notation "Z'"=> ((∑ x,d x:ℕ):ℝ)*c +4*(Fintype.card I:ℝ)*(c-a)
local notation "X'"=> ((t:ℝ)+1/16)*(a-b)-(Z')
-- PriceAt along scales; with geometry paid elsewhere
include i₀ h
lemma funding (hk:Height C.S l T k b)(hm:Height C.S l T m a)(hj:Height C.S l T j c)(hT:Tendsto T l atTop)(he:b<a)(ht:a<c) (hΩ:∀ᶠ i in l, Push.GridApprox.room C.path.levels (k i) (m i) (lensScope C t)) :
    ∃ g o : ι→ℝ, RateIs l T g ((Z')-t*a) ∧ RateLE l T o (-(X')) ∧
       (∀ᶠ i in l,0<o i) ∧ ∀ᶠ i in l, PriceAt C (g i) (o i) t d s (k i) (m i) (j i):=by
    let P:= Stock.Tabs.chosen C.path.levels 1 L.tabs ∘ k; have hP:Height C.S l T P b:= hk.stock L.tabs
    have ha:∀ i,Stock.Tabs.opens C.path.levels 1 (k i) (P i):=fun i=>Stock.Tabs.opened ..
    let M:= Fintype.card I; have hM: 0 < M:= Fintype.card_pos_iff.mpr ⟨i₀⟩
    obtain ⟨y,hy,hF,hY⟩:= halls hG L.halos M hM
    obtain ⟨χ,hχ⟩:= L.productCuts.mother
    let B (i:I):= 1+(C.labels.level (d i)).coeffSize (s i); have hf i:0<B i:= add_pos_of_pos_of_nonneg one_pos (Work.G08.size_nonneg ..)
    let x i:= initial C.path δ η (m i) (j i) (y (j i)) (∏ p,plumR C (d p) (B p) (j i)) M
    have hx:RateIs l T x (-(Z')):= (Height.gathered hm hj hT (height0 hy hj) (Height.plumBudget d B hf hj hT hG) hG M).swap (by unfold M; ring)
    let e i:= terminalCost C t (m i) (x i); let g i:=2*e i; let z i:= Real.exp ((X')*T i); have hZ:=RateIs.exp (X') hT; have hg:= key_cost hm hT hx hG t; have hp:= terminalAfford hG L hP hm hT he hx t hg hZ (by linarith only [he]); let o i:=2*(stakes C (k i) (P i) / z i)
    refine ⟨g, o, ((RateIs.const hT zero_lt_two).mul hg).swap (by ring),?_ , Eventually.of_forall (fun i=>mul_pos zero_lt_two (div_pos (Real.exp_pos _) (Real.exp_pos _))),?_⟩
    · simp_rw [o,div_eq_mul_inv]; simpa only [zero_add] using! ((RateLE.const (2:ℝ) hT).mul ((stock_price L.tabs hG hk hT).mul (hZ.inv.pays hT)))
    have hb:=briar C hG L.accounting; have hm':= hm.step C.path.levels.fits.mesh; let S i:= m i+1; have hW' := (((height0 hb hm').power 2).add (RateIs.const hT one_pos) hT).mul hm'.mesh
    filter_upwards [hk.mesh.overtakes (hW'.pays hT) hT (by simp; linarith),hP.earlier he hT hm, hm'.earlier ht hT hj, hp, hx.pos, hΩ, hk.grows.eventually_ge_atTop (C.ref t), eventually_all.mpr (fun x=>hj.grows.eventually_ge_atTop (C.ref (d x)))] with i hψ hPi hS hp hx hr hK hd
    have hf'(p:ℕ): ((P' (S i)).B^2+1:ℕ) ≤ (C.S.toDepth (((ha i).1.trans hPi.le).trans (Nat.le_succ (m i))) p).count.val:= by
       let v:= C.S.toDepth (((ha i).1.trans hPi.le).trans (m i|>.le_succ)) p; have hl: ((P' (S i)).B:ℝ)^2+1 ≤ v.count.val:=by
          apply le_of_mul_le_mul_right _ (C.S.a_pos (S i)); exact hψ.le.trans_eq ((C.S.embeds_scale v).symm.trans (mul_comm ..))
       exact_mod_cast hl
    refine ⟨fun N p hn hz r he hw hi₀ hi₁=> ?_,(ha i).1.trans hPi.le,hK.trans ((ha i).1.trans hPi.le),hS.le⟩
    -- careful let V etc introduction reflexive
    exact joins C N (m i) p t (k i) (P i) i₀ (z i) (fun p=> plumR C (d p) (B p) (j i)) r (ha i).1 hPi.le hn hS.le d s h L.system L.literal (hχ t) L.tabs (ha i) (hK.trans (ha i).1) hd (fun p=>paid_new C N _ _ (d p) h (s p) (B p) (hf p) (le_add_of_nonneg_left zero_le_one) (hd p) hn) (fun p=>stockpit _ _ _ _ (hf p)) hr he (hf' _) hw (hy.pos (j i)) (hF (j i)) (fun q₀ hi hp=> hY (j i) q₀ hp.le) _ (fun _=>rfl) hi₀ hi₁ hx le_rfl (Real.exp_pos _)
      hp.1 le_rfl hp.2
end YM.OPE
