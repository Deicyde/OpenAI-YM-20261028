import YM.RG08.Redo.Pepper
/-! # C-promises, including stage-changing widths. Payment & use. -/
noncomputable section
namespace YM.RG08.Redo
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Rate.Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Camera Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open PhysicalNext PhysicalNext.Repeat Extraction Org Table Spec UVExtension MergeProof Next.Free Function Jetty Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks Sideshow April Yurt Filter
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
set_option autoImplicit false
variable {O X:Type}(G:Gauge)(K:KernelChoices)(P B:MapPrices){d D e k n j t l:ℕ}
local notation "T0"=> RG08.Supplies.stone
local notation "M"=>reef G K P B
local notation "N"=>snack G K P
local notation "V"=> Next.Foundations.hol G
local notation "C"=> cover G K P B
variable (R:Cup)
abbrev tool (i j l e n:ℕ)(hR:Note R i j)(hl:l≤R.d)(he:e≤R.k)(hn:n≤l+e):=April.cap ((Labels.frames G).level R.d) R.D R.k i j l e n V K (M R.E i) (M R.E j) (N i j).τ (C R i j hR).μ (N i j).V (C R i j hR).seat hl he hn
abbrev coin0 (i j l e n:ℕ)(hR:Note R i j)(hl:l≤R.d)(he:e≤R.k)(hn:n≤l+e):=April.post ((Labels.frames G).level R.d) R.D R.k i j l e n V K (M R.E i) (M R.E j) (N i j).τ (C R i j hR).μ (N i j).V (C R i j hR).seat hl he hn
lemma coins (hp:Note R j t)(hl:l≤R.d)(he:e≤R.k)(hn:n≤l+e):1≤tool G K P B R j t l e n hp hl he hn∧ Week (transitR n e l R.d R.k) (coin0 G K P B R j t l e n hp hl he hn):=by
 obtain ⟨h,hv,-⟩:= April.ledger (l:=l) (e:=e) (n:=n) (K:=K) ((Labels.frames G).level R.d) V (C R j t hp).seat hl he hn;exact ⟨h,hv⟩
def stock (i j l e n:ℕ)(hR:Note R i j)(hl:l≤R.d)(he:e≤R.k)(hn:n≤l+e):ℝ:=((coins G K P B R hR hl he hn).2).choose
lemma stock_use (hR:Note R j t)(hl:l≤R.d)(he:e≤R.k)(hn:n≤l+e):
 let a:= stock G K P B R j t l e n hR hl he hn
 let p:=coin0 G K P B R j t l e n hR hl he hn
 ;0 ≤ a ∧ ∀ x≥1,0≤p x ∧ p x≤a*x^(transitR n e l R.d R.k):=((coins G K P B R hR hl he hn).2).choose_spec

private lemma bounded {Z:Type}{A:ℕ}{w:Filter Z}[NeBot w][w.IsCountablyGenerated]{p:ℕ→Z→Prop}(h:∀ i ≤ A,∀ᶠ t in w,p i t):∀ᶠ t in w,∀ i ≤ A,p i t:=by
 induction A with
 | zero=>exact (h 0 (by omega)).mono (fun t ht i hi=> Nat.eq_zero_of_le_zero hi ▸ ht)
 | succ j ih=>exact ((ih fun _ hi=>h _ (hi.trans (Nat.le_succ _))).and (h (j+1) le_rfl)).mono (fun t ⟨ht,hj⟩ i hi=> by by_cases he:i=j+1; exact he ▸ hj; exact ht i (by omega))
private lemma beck {Z:Type}{w:Filter Z}[NeBot w][w.IsCountablyGenerated](j:ℕ)(p:Cup→ℕ→Z→Prop)(h:∀ R:Cup,∀ t:ℕ,t≤j→Note R j t→∀ᶠ x in w,p R t x):∀ᶠ x in w,∀ R:Cup,∀ t:ℕ,t≤j→Note R j t→p R t x:=by
 refine Filter.Eventually.mono (p:= fun x=> ∀ d:ℕ,d≤j→∀ D:ℕ,D≤j→∀ k:ℕ,k≤j→∀ t≤j,∀ (hp:d+1≤D),Note (⟨d,D,k,hp⟩:Cup) j t→p ⟨d,D,k,hp⟩ t x) ?_ ?_
 · apply bounded (fun d _=>bounded (fun D _=> bounded (fun k _=> bounded (fun t ht=>?_))))
   by_cases he:d+1≤D
   · by_cases hv: Note (⟨d,D,k,he⟩:Cup) j t; exact (h _ t ht hv).mono (fun x hx _ _=> hx)
     exact Filter.Eventually.of_forall fun _ _ hs=>False.elim (hv hs)
   exact Filter.Eventually.of_forall fun _ h _=>False.elim (he h)
 intro x hx a t ht hq;obtain ⟨d,D,k,hK⟩:=a
 have hd:=hq.demand.trans ht
 change 2*(D+k+1)≤j at hd;exact hx d (by omega) D (by omega) k (by omega) t ht hK hq

private lemma gate0 (j:ℕ):∃ x:ℕ,∀ (R:Cup)(t:ℕ)(h:Note R j t),(C R j t h).threshold ≤ x:=by
 apply Filter.Eventually.exists (f:=atTop) -- ℕ
 refine Filter.Eventually.mono (beck (w:=atTop) j (fun R t v=>∀ h,(C R j t h).threshold ≤ v) (fun R t _ h=>(eventually_ge_atTop ((C R j t h).threshold)).mono (fun _ ht _=>ht))) ?_
 intro x hx R t h; have hh:=h.neighbor; exact hx R t (by omega) h h

def rail (j:ℕ):ℕ:=(gate0 G K P B j).choose
lemma admit_cup (h:Note R j t):(C R j t h).threshold ≤ rail G K P B j:=(gate0 G K P B j).choose_spec .. -- maybe choose_spec not applied
structure Tab (T:Patch)(x:ℝ):Prop where
 title : 1 ≤ x
 costs : ∀ t≤T.J, (N T.J t).C T ≤ x
 -- inverse test width @ANY Haven with t=J_m, and E≤t≤j (need for x=j & incoming J=t). Fee distinguishes drive post over all positions; uniform exponent derived above!
 film:∀ p j:ℕ,p≤T.J→j≤T.J→ (M p j)⁻¹≤x
 est : ∀ R:Cup,∀ t:ℕ,∀ h:Note R T.J t,∀ l e n:ℕ,∀ (hl:l≤R.d)(he:e≤R.k)(hn:n≤l+e), stock G K P B R T.J t l e n h hl he hn ≤ x
  -- A-shell² gate from Length. lengths & width inverses register. -/
private lemma invoice (T:Patch):∃ x,Tab G K P B T x:=by
 have h:∀ᶠ x in (atTop:Filter ℝ), ∀ R:Cup,∀ t:ℕ,t≤T.J→ Note R T.J t → ∀ h: Note R T.J t,∀ l e n:ℕ,∀ (hl:l≤R.d)(he:e≤R.k)(hn:n≤l+e),stock G K P B R T.J t l e n h hl he hn ≤ x:=by
    refine beck T.J (fun R t x=> _) (fun R t ht h=>?_)
    have hx:∀ᶠ v in (atTop:Filter ℝ),∀ l≤R.d,∀ e ≤ R.k,∀ n≤l+e, ∀ (hl:l≤R.d)(he:e≤R.k)(hn:n≤l+e), stock G K P B R T.J t l e n h hl he hn ≤ v:=
           bounded (fun l hl=> bounded (fun e he=> bounded (fun n hn=> (eventually_ge_atTop (stock G K P B R T.J t l e n h hl he hn)).mono (fun _ hp _ _ _=>hp))))
    exact hx.mono (fun x hx _ l e n hl he hn=>hx _ hl _ he _ hn hl he hn)
 apply Eventually.exists (f:=atTop)
 filter_upwards [eventually_ge_atTop (1:ℝ),bounded (Z:=ℝ) (A:=T.J) (p:=fun t x=>(N T.J t).C T ≤ x) (fun t _=>eventually_ge_atTop _),bounded (Z:=ℝ) (A:=T.J) (p:=fun p x=>∀ t≤T.J,(M p t)⁻¹ ≤ x) (fun p _=>bounded (fun _ _=>eventually_ge_atTop _)),h] with x hx he hf hv
 exact ⟨hx,he,fun p j hp hj=>hf _ hp _ hj,fun R t h l e n=> hv R t (by have hs:=h.neighbor;omega) h h l e n⟩

def receipt (T:Patch):ℝ:=(invoice G K P B T).choose
lemma invoiced (T:Patch):Tab G K P B T (receipt G K P B T):=(invoice G K P B T).choose_spec
def after (f:ℕ→ℕ)(i:ℕ):=if h:∃ T:Patch,T.J=i∧T.L.val=f i then Real.exp (receipt G K P B h.choose) else 1 -- ≥1
-- α-compatible
variable {G P B K}
def OpenDoor (a:Levels G)(P B:MapPrices):Prop:=∀ m,rail G a.clock.kernel P B (a.clock.J (m+1)) ≤ (a.S.block m).val
def OpenBook (a:Levels G)(P B:MapPrices):Prop:=∀ m,receipt G a.clock.kernel P B (T0 a m) ≤ Real.log (a.clock.hatBeta m)
lemma paydays {a:Family G}{s:Supply.Sheet G}{P:MapPrices}(hK:∀ i, rail G s.kernel (Case.actualPay s P) B i ≤ (a.path.levels.clock.factor i).val)(hk:a.path.levels.clock.kernel = s.kernel)(he:∀ i,after G s.kernel (Case.actualPay s P) B (fun j=> (a.path.levels.clock.factor j).val) (a.path.levels.clock.J (i+1)) ≤ a.path.levels.clock.hatBeta i):OpenDoor a.path.levels (Case.actualPay s P) B ∧ OpenBook a.path.levels (Case.actualPay s P) B:=by
 constructor
 · intro i;rw [hk,←a.path.levels.fits.sameFactor];exact hK _
 intro i;rw [hk]; have hf:=he i; unfold after at hf
 let b:= a.path.levels;let g:= fun j=> (b.clock.factor j).val
 let j:=b.clock.J (i+1)
 have hx: ∃ T:Patch,T.J=j∧T.L.val=g j:= ⟨T0 b i,rfl, congrArg Subtype.val (b.fits.sameFactor i).symm⟩
 rw [dif_pos hx,show hx.choose=T0 b i from ?_] at hf
 · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hf
 have hm(P Q:Patch)(h:P.J=Q.J)(hP:P.L=Q.L):P=Q:=by cases P;cases Q;simp_all
 apply hm _ _ hx.choose_spec.1 (Subtype.ext (hx.choose_spec.2.trans (congrArg Subtype.val (b.fits.sameFactor _))))
end YM.RG08.Redo
