import YM.RG08.Run.Storm
/-!
# The joint derivative sector comparison on a segment. Both cutoff orientations.
Any size unit. On exact ages.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Pill Matrix PowerSeries
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I J : Type}{u : I→Windows}{w:J→ShoreP u}{X:Chain}{G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{R θ C:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{T':Aperture G P k E τ d D R}{p q:J→ℝ}
variable {L: Wall w 1→Wings u 1}{A B:Wall w 0→BoardU D R G}
lemma Crop.diff {V U: BoardU D R G}(h : Crop t U H F)(hp: Crop t V H F): Crop t (U-V) H F := by
    have he:= h.hU; have ht:= hp.hU; have hs:= h.paid; have hv:= hp.paid
    refine ⟨?_,?_,?_⟩
    · rw [sub_eq_add_neg, ← neg_one_smul ℝ]; exact choir_plus he (choir_weight ht _)
    · rw [sub_eq_add_neg,← neg_one_smul ℝ]; exact lank_add hs (lank_wt hv _)
    rw [audit_sub H he ht hs hv,h.spine,hp.spine,sub_self]
lemma tribes_ind (hm:e≤ E) (p:ℕ→ℕ→Prop) (he: ∀ i≤ E,∀ j, (∀ n s, awaits 1 i j n s→ p n s)→p i j) (hx:∀ i≤ E,∀ j,k+i<j→p i j): p e r:= by
    induction e using Nat.strong_induction_on generalizing r with
    | h e H=>
      by_cases hr:r ≤ k+e
      swap; exact hx _ hm _ (by omega)
      generalize hN : k+e-r=n; induction n using Nat.strong_induction_on generalizing r with
      | h n ih=>
        apply he e hm r; rintro i j (ha|⟨hv,hx'⟩)
        · exact H i ha (ha.le.trans hm)
        subst i; by_cases h:j≤k+e
        · apply ih _ _ h rfl; simp only [one_ne_zero,↓reduceIte] at hx'; omega
        exact hx _ hm _ (by omega)
lemma tribeAll (he:Tights T S ν D' u)(hz: Heirs T' u)(ht:Keeps A T ν D' L t) (hp:0≤p)(hk:e≤E)
    (hx:∀ i≤E,∀ r,Card k (fun i=>wallY X (Wall.tip w i)) p (fun j=> A (Wall.tip w j) i r) 1): Tribe T' H F p A (route A X ν D' L t d) e r := by
     refine tribes_ind (k:=t) hk _ (fun i hi r hv=> bondKeep he hz ht hi hp (hx i hi r) hv) (fun i hi r hv=> planned ht.caps hv (fun i=>(ht.zone i).hU) (fun i=>crest_u (he.fair _) h (ht.zone i.roof|>.hU)))
abbrev wallL:= Wall.world (b:=w) (n:=1)
abbrev wallR:= fun i:Wall w 1=> i.world.wingR
local notation "Ⓨ" => wallY X
local notation "Δ₁" => (fun t=>q (Wall.a (b:=w) (n:=1) t))
local notation "Υ" => Ye X ν D' T
local notation "▲" => heights (u:=u) X ν D'
local notation "Σ♭" => strideP X w
-- canonical cost with Wall recaptured
lemma oldEnough (he:Tights T S ν D' u)(hp:∀ t:Wall w 1,tiltP X t ≤ q t.a)(hk:e≤E) b r k: Drum k Ⓨ (fun i=>q i.a) 1 (fun i:Wall w 1=> Υ i.world.low b e r) (fun i=> Υ (wallR i).low b e r) 1 := by -- hp wrong n; use Wall1
   let y (i:Wall w 1):= menu X i.world; let p:= Wall.invested X (n:=1) (b:=w); have ht:= (Lens_pay he hk b r k).mold (fun i:Wall w 1=>i.world.low)
   refine ⟨ht.first.tax p (Wall.plusOne X),ht.second.tax p (Wall.plusOne X),?_⟩
   exact ((ht.funds.tax p (Wall.plusOne X)).raise (fun i=> mul_le_mul_of_nonneg_right ((Wall.loan X i).trans (hp i)) zero_le_one))
lemma stride_pay (t) : Δ₁ t * Σ♭ p t=Σ♭ (q*p) t:= by simp only [strideP,Pi.mul_apply,mul_assoc]
private lemma dipS (he:Tights T S ν D' u)(hz:Heirs T' u)(ht:Keeps A T ν D' wallL t)(hv:Keeps B T ν D' wallR t)(hp : 0≤p)(hx:∀ t:Wall w 1,tiltP X t ≤ q t.a) (hh:0≤q)(ho:e ≤ E)
    (hC: Card k (fun i=>wallY X (Wall.tip w i)) (q*p) (fun j=> (A-B) (Wall.tip w j) e r) 1)
    (hy:∀ i≤E,∀ r, Tribe T' H F p A (route A X ν D' wallL t d) i r)(hg:∀ i≤E,∀ r, Tribe T' H F p B (route B X ν D' wallR t d) i r)
    (hD:∀ j k,awaits 1 e r j k→Tribe T' H F (q*p) (A-B) (route A X ν D' wallL t d-route B X ν D' wallR t d) j k):
    Tribe T' H F (q*p) (A-B) (route A X ν D' wallL t d-route B X ν D' wallR t d) e r:= by
   let M:= route A X ν D' wallL t d; let N:=route B X ν D' wallR t d; let K:=M-N
   let P i:= A (Wall.roof i); let Q i:=B (Wall.roof i)
   have hp':0≤q*p:= fun i=>mul_nonneg (hh i) (hp i)
   have hH i: Marvel t (P i):= (ht.zone _).hU; have hH' i: Marvel t (Q i):= (hv.zone _).hU
   have hV i : Marvel t (M i):= crest_u (he.fair _) T'.paper (hH _); have hV' i:Marvel t (N i):= crest_u (he.fair _) T'.paper (hH' _)
   have hW i: Lank (M i):= crest_l (he.fair _) T'.paper (hH _) (ht.zone _|>.paid); have hW' i:Lank (N i):= crest_l (he.fair _) T'.paper (hH' _) (hv.zone _|>.paid)
   have hA i:Crop t ((A-B) i) H F:= (ht.zone i).diff (hv.zone i)
   have hK i: Marvel t (K i)∧ Lank (K i):= by unfold K; rw [Pi.sub_apply,sub_eq_add_neg,← neg_one_smul ℝ]; exact ⟨choir_plus (hV i) (choir_weight (hV' i) _),lank_add (hW i) (lank_wt (hW' _) _)⟩
   by_cases hn:r≤t+e; swap; · exact planned ht.caps (by omega) (fun i=>(hA i).hU) (fun i=>(hK i).1)
   let δ:= Δ₁; let Ψ : Wall w 1→ℝ:= Σ♭ p; let ξ : Wall w 1→ℝ:= Σ♭ (q*p); have Hξ: δ*Ψ=ξ:=funext (fun i=>stride_pay i)
   let S:= billsT he w (fun i=>show chop X (1/4) i.world ≤ δ i from (Wall.loan X i).trans (hx i)) k
   have hw(i:Wall w 1): (1:ℝ)/(X.S.block i.i).val ≤ 1:= by apply (div_le_one (by positivity)).2; exact_mod_cast (X.S.block _).property
   have Hψ : 0 ≤ Ψ:= fun i=> mul_nonneg (hp _) (gain_pos ..).le
   let C i:= fetchU (▲ (wallL i)) t d (P i) e r; let C' i:=fetchU (▲ (wallR i)) t d (Q i) e r
   have hU' (i k')(hi:i≤E)(h:Card k Ⓨ (Σ♭ (q*p)) (fun t=> (A-B) t i k') 1): Drum k Ⓨ δ Ψ (fun a=> P a i k') (fun a=> Q a i k') 1:= by
     refine ⟨((hy i hi k').cards).up S.pay hp,((hg i hi k').cards).up S.pay hp,?_⟩; rw [Hξ]; exact h.up S.pay hp'
   have hr' : Card k Ⓨ ξ (C-C') 1:= Hξ ▸ (foc_ear S hH hH' ht.caps T'.paper ho zero_le_one le_rfl (η:=1) hw Hψ (fun i j he=> hU' i j (by unfold awaits at he; omega) ((hD i j he).cards)) (d:=d)).funds -- may need r
   let R i:= aboard d (▲ (wallL i)).tree (P i e r); let R' i:= aboard d (▲ (wallR i)).tree (Q i e r)
   have hX(i): M i e r=R i+C i:= formula_bucks (he.fair _) (hH i) T'.paper d e r; have hZ(i):N i e r= R' i+C' i:= formula_bucks (he.fair _) (hH' i) T'.paper d e r
   have hY : (fun i=> K i e r)=(R-R')+(C-C'):= funext fun i=> by simp only [K, Pi.add_apply,Pi.sub_apply,hX,hZ]; abel
   refine season (L:=wallL) he hz ht.caps ho hn ht.wake hp' hA (fun i=>(hK _).1) (fun i=>(hK _).2) hC hD ?_ ?_ (fun h=>?_)
   · let W' i:= aboard d (▲ (wallL i)).tree (Q i e r); let V i:= aboard d (babyQ G X (wallL i)) ((P i-Q i) e r)
     have hD': Card k Ⓨ ξ (W'-R') 1:= Hξ ▸ (inlet S hH' hH' T'.paper zero_le_one le_rfl hw (Drum.home (((hg _ ho r).cards).up S.pay hp)) (d:=d) (r:=r) (e:=e)).funds
     have Ht : Card k Ⓨ ξ (R-W'-V) 1:= by
       have HA i: Marvel t (P i-Q i):= (hA i.roof).hU
       rw [show R-W'=(fun i=>aboard d (▲ (wallL i)).tree ((P i-Q i) e r)) from funext fun i=> Eq.symm (aboard_sub (he.fair (wallL i)).odds T'.paper (he.fair _|>.ct) ((hH i).hem _ _) ((hH' i).hem _ _) d)]
       exact dean he ht.wake HA hn (fun i hi j=> (((hD i j (Or.inl hi)).cards).up S.pay hp'))
     change Card k _ _ (fun i=> K i e r-_) _
     rw [show (fun i=> K i e r-_)= (W'-R')+(R-W'-V)+(C-C') from funext fun i=>?_]; · exact ((hD'.more Ht zero_le_one S.age).more hr' zero_le_one S.age)
     change K i e r-V i=_; rw [show K i e r= _ from congr_fun hY i]; simp only [Pi.add_apply,Pi.sub_apply]; abel
   · intro hq
     let F' (i: Wall w 1):= Υ (wallL i|>.low); let G' (i: Wall w 1):= Υ (wallR i|>.low); let X' i:= call H F (M i); let Y i:= call H F (N i)
     let T' i:= edgeBook (F' i) (X' i-Y i) e r; let U' i:= edgeBook (F' i-G' i) (Y i) e r
     have hY(i): X' i-Y i=call H F (K i) := by ext1 j; ext k; rw [Pi.sub_apply,map_sub]; change coeff _ (PowerSeries.mk _) - coeff _ (PowerSeries.mk _)= coeff _ (PowerSeries.mk _); rw [coeff_mk,coeff_mk,coeff_mk]; exact (congr_fun (congr_fun (audit_sub H (hV i) (hV' i) (hW i) (hW' i)) k) j).symm
     have Hu : Card k Ⓨ ξ T' 1:= by
        rw [show T' = (fun i=> edgeBook (F' i) (call H F (K i)) e r) from funext fun i=> by unfold T'; rw [hY i]]; rw [← mul_one ξ]; refine elig S.age zero_le_one (V:=F') (fun i hi b r=> (oldEnough he hx (hi.trans ho) b r k).first) (fun i=> (he.firs _).toBoards) (fun j b hb=> ?_)
        rcases hb with h|⟨h,hk⟩
        · exact (hD j _ (Or.inl h)).key b rfl
        subst j; rcases hk.eq_or_lt with h|h; · exact hq _ _ h.symm rfl b rfl
        exact (hD _ _ (Or.inr ⟨rfl,by simp only [one_ne_zero,↓reduceIte]; exact h⟩)).key b rfl
     have Hw : Card k Ⓨ ξ U' 1:= by
        rw [← Hξ,mul_comm]; apply elig S.age (V:=fun i=> F' i-G' i) S.rent (fun i hi b r=>?_ ) (fun i=> slate_minus (he.firs _|>.toBoards) (he.firs _|>.toBoards)) (fun j b hb=> (hg j (by omega) _).key b rfl)
        have H := (oldEnough he hx (hi.trans ho) b r k).funds; rw [mul_one] at H; exact H
     rw [show (fun i:Wall w 1=> (A - B) i.low e r - _)= -(U'+T') from funext fun i=>?_]; · exact (Hw.more Hu zero_le_one S.age).neg
     change (A i.low e r-B i.low e r)-(M i e r-N i e r) = -(U' i+T' i)
     rw [ht.rise i,hv.rise i]; unfold eject; change (M i e r-edgeBook (F' i) (X' i) e r) - (N i e r-edgeBook (G' i) (Y i) e r) - _ = _
     rw [← show edgeBook (F' i) (X' i) e r-edgeBook (G' i) (Y i) e r= U' i+T' i from congr_fun (congr_fun variance_b e) r]; abel
   change Card k _ ξ (fun i=> K i e r) _; rw [hY,←Hξ]; exact ((inlet S hH hH' T'.paper zero_le_one le_rfl hw (hU' e r ho h) (d:=d)).funds).more (Hξ.symm ▸ hr') zero_le_one S.age
theorem dip_all (he:Tights T S ν D' u)(hz:Heirs T' u)(ht:Keeps A T ν D' wallL t)(hv:Keeps B T ν D' wallR t)(hp : 0≤p)(hx:∀ t:Wall w 1,tiltP X t ≤ q t.a) (hh:0≤q)(ho:e ≤ E)
    (hC: ∀ i≤E,∀ r,Drum k (fun i=>wallY X (Wall.tip w i)) q p (fun j=> A (Wall.tip w j) i r) (fun j=>B (Wall.tip w j) i r) 1) :
    Tribe T' H F (q*p) (A-B) (route A X ν D' wallL t d-route B X ν D' wallR t d) e r ∧ Tribe T' H F p A (route A X ν D' wallL t d) e r ∧ Tribe T' H F p B (route B X ν D' wallR t d) e r := by
  have ha i (hi:i ≤ E) (r:ℕ):= tribeAll he hz ht hp hi (r:=r) fun i hi r=> (hC i hi r).first
  have hb i (hi:i ≤ E) (r:ℕ):= tribeAll he hz hv hp hi (r:=r) fun i hi r=> (hC i hi r).second -- hi typing
  refine ⟨tribes_ind (k:=t) ho _ (fun i hi r=>dipS he hz ht hv hp hx hh hi (hC i hi r|>.funds) ha hb) (fun i hi r hm=>planned ht.caps hm (fun i=>?_ ) (fun i=>?_)), ha e ho r,hb e ho r⟩ -- budgets
  · exact ((ht.zone i).diff (hv.zone i)).hU
  have he' := crest_u (he.fair (wallL i)) h ((ht.zone i.roof).hU) (d:=d)
  have hh := crest_u (he.fair (wallR i)) h ((hv.zone i.roof).hU) (d:=d)
  rw [Pi.sub_apply,sub_eq_add_neg,← neg_one_smul ℝ]; exact choir_plus he' (choir_weight hh _)
end YM.RG08.Run
