import YM.RG08.Run.Snow
/-!
# Strong ticket at projection-null column. Roots anchored cells; support cost POLY no loss of that chosen exponent.
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
variable {I J:Type}{u:I→Windows}{w:J→ ShoreP u} {X:Chain}{G:Gauge}{E e N r d τ D j t i k m l n kN o s :ℕ}{R θ C:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{T':Aperture G P k E τ d D R}
local notation "Ⓨ" => wallY X
local notation "Δ" => tiltP X
local notation "Υ" => Ye X ν D' T
local notation "Γ" => heights X ν D'
variable {L : Wall w 1→Wings u 1}{U:Wall w 0→ BoardU D R G}{p: J→ℝ}
structure Keeps (U:Wall w 0→BoardU D R G)(T:Signals P Q E τ H Ω h hD)(ν:G.ColorIndex)(D':ChartRatio G) (L:Wall w 1→Wings u 1)(t:ℕ) : Prop where
    wake i : (L i).toLaunch=i.world.toLaunch
    caps : t≤τ
    zone i : Crop t (U i) H F
    rise i : U i.low=eject H (Ye X ν D' T (L i).low) (Needle.push (heights X ν D' (L i)) t d (U i.roof)) -- notation T captures ambient T not new!
-- check
abbrev route (U:Wall w 0→BoardU D R G)(X:Chain)(ν:G.ColorIndex)(D':ChartRatio G)(L:Wall w 1→ Wings u 1)(t d:ℕ) (i:Wall w 1) := Needle.push (heights X ν D' (L i)) t d (U i.roof)
lemma lensCall (he: Tights T S ν D' u)(hp : ∀ i, (L i).toLaunch=i.world.toLaunch) k : LensP k E τ Ⓨ (fun i=>chop X (1/4) (L i)) (fun i=>T.vi (X.J (L i).i)) (fun i=> Γ (L i)) (fun i=> Γ (L i).wingR) := by
  let δ t:= chop X (1/4) (L t); let v t:= T.vi (X.J (L t).i); have hE: Weighed (wallY X (b:=w) (n:=1)) (fun t=> menu X (L t)):= by unfold Wings.menu; simp_rw [hp]; exact Wall.invested X
  let B:= he.operator
  have he(t):0< v t:=(B.ht (L t)).trans_le (bucks_v B (L t))
  have hT: Audience (wallY X (b:=w) (n:=1)):=Wall.plusOne X
  have hQ {α β: Wings u 1→Type}(P Q:∀ i,Row (α i) (β i))(h:RowBoth (menu X) (chop X (1/4)) P Q (fun i=> T.vi (X.J i.i))): RowBoth Ⓨ δ (fun i=>P (L i)) (fun i=>Q (L i)) v := by
      have hh {P : ∀ i,Row (α i) (β i)} {w' : Wings u 1→ℝ}(h : SafeRow (menu X) w' P (fun i=> T.vi (X.J i.i))): SafeRow Ⓨ (fun i=> w' (L i)) (fun i=>P (L i)) v:= ⟨_,hE.sway hT (h.choose_spec.1.transfer L),fun i=> h.choose_spec.2 _⟩
      exact ⟨hh h.fresh,hh h.again,hh h.moves⟩
  refine ⟨fun i=> B.faith _,fun i=>B.bond _,hT,hE.sway hT (B.crop.transfer L),hQ _ _ B.hessian,hQ _ _ B.meansT,fun e hx t ht r=>?_,fun e he=> leaseT (Summit.Lease.whirls (B.castG e he) L) hT hE le_rfl,he,utterBuy k ?_ (fun i=> B.hv _),fun i=>B.hs _⟩
  · have hh:= RG08.Both.mold (B.ribs e hx t ht r) L; exact ⟨hh.fresh.age hE hT,hh.again.age hE hT,hh.moves.age hE hT⟩
  apply Weighed.mono (hE.sway hT (‹Tights _ _ _ _ _›.he.costs.transfer (fun i=> (L i).toLaunch))) (fun i=> inv_nonneg.mpr (he i).le) (fun i=> inv_anti₀ (T.pos _) (tick_t T _|>.1))
lemma Lens_pay (he:Tights T S ν D' u)(hk:e≤E)(b:Letter F) r k : Drum k (menu X) (chop X (1/4)) 1 (fun i:Wings u 0=>Υ i b e r) (fun i=> Υ i.wingR b e r) 1 := by
   have hh:= yellow he hk b r
   have ht:= T.pos
   have hE : Weighed (menu X) (fun i:Wings u 0=>utter k (ώ T i.i)):= utterBuy k (he.he.costs.transfer Wings.toLaunch) (fun t=>(tick_t T _).1.trans ((tick_t T _).2.trans (min_le_right ..)))
   refine ⟨ofTin hh.one (fun _=>ht _) hE,ofTin hh.two (fun _=>ht _) hE,?_⟩; rw [mul_one]; exact ofTin hh.goes (fun _=>ht _) hE
private lemma fetchesT (he:Tights T S ν D' u)(hz:Heirs T' u)(ht:Keeps U T ν D' L t) (h:kN ≤ E)(hp:0≤p)
    (hv:∀ j k,awaits 1 kN r j k→ Tribe T' H F p U (route U X ν D' L t d) j k) :
    Card k Ⓨ (strideP X w p) (fun i:Wall w 1=>fetchU (Γ (L i)) t d (U i.roof) kN r) 1:= by
   let u':= lensCall he ht.wake k
   have hu i:= (ht.zone i).hU
   have hV : Weighed Ⓨ (fun i:Wall w 1=> ((X.S.block i.i).val:ℝ)):= by
       rw [show (fun i:Wall w 1=> ((X.S.block i.i).val:ℝ))=(fun i : Wall w 1 => ((X.S.block (L i).i).val:ℝ)) from funext fun i=> by rw [show (L i).i=i.i from congr_arg Launch.i (ht.wake i)]]; exact u'.pay
   refine (foc_ear (d:=d) u' (fun i=>hu i.roof) (fun i=>hu i.roof) ht.caps (by assumption) h (v:=1) zero_le_one le_rfl (η:=1) (fun i=> show _≤_ from one_div_le_one_div_of_le zero_lt_one (show 1≤((X.S.block (L i).i).val:ℝ) by exact_mod_cast (X.S.block _).property) |>.trans (by simp)) (ρ:=strideP X w p) (fun i=> mul_nonneg (hp _) (gain_pos ..).le) (fun i j h=> Drum.home ( (hv i j h|>.cards).up hV hp))).first
lemma bondKeep (he:Tights T S ν D' u)(hz:Heirs T' u)(ht:Keeps U T ν D' L t)(h:o≤E)(hp:0≤p)(h1 : Card k (fun j=>Ⓨ (Wall.tip w j)) p (fun i=> U (Wall.tip w i) o r) 1)
    (hv:∀ j k,awaits 1 o r j k→ Tribe T' H F p U (route U X ν D' L t d) j k) : Tribe T' H F p U (route U X ν D' L t d) o r := by -- simplify hp
    let P i:= route U X ν D' L t d i
    have hh i:= (ht.zone i).hU
    have hQ i: Marvel t (P i):= crest_u (he.fair _) T'.paper (hh _)
    by_cases hx:r ≤ t+o; swap; · exact planned ht.caps (by omega) hh hQ -- T'
    let u':= lensCall he ht.wake k
    have hV : Weighed Ⓨ (fun i:Wall w 1=> ((X.S.block i.i).val:ℝ)):= by
       rw [show (fun i:Wall w 1=> ((X.S.block i.i).val:ℝ))=(fun i:Wall w 1=> ((X.S.block (L i).i).val:ℝ)) from funext fun i=> by rw [show (L i).i=i.i from congr_arg Launch.i (ht.wake i)]]; exact u'.pay
    have hd:= fetchesT he hz ht h hp hv
    let X' i:= U (Wall.roof i) o r; let Y i:= fetchU (Γ (L i)) t d (U i.roof) o r
    let R i:= aboard d (Γ (L i)).tree (X' i); have hy i : P i o r=R i + Y i:= formula_bucks (he.fair _) (ht.zone i.roof|>.hU) T'.paper _ _ _
    refine season (L:=L) (U:=P) he hz ht.caps h hx ht.wake hp ht.zone hQ (fun i=>crest_l (he.fair _) T'.paper (hh _) (ht.zone _|>.paid)) h1 hv ?_ ?_ (fun g=>?_)
    · let W i:= aboard d (babyQ G X (L i)) (X' i)
      have hh : Card k Ⓨ (strideP X w p) (R-W) 1:= dean he ht.wake (m:=t) (U:=fun i:Wall w 1=> U i.roof) (fun i=>hh _) hx (fun j hj k=> ((hv j k (Or.inl hj)).cards.up hV hp))
      rw [show (fun i=> P i o r-_)= (R-W)+Y from funext fun i=>?_]; · exact hh.more hd zero_le_one u'.age
      simp only [hy,Pi.add_apply,Pi.sub_apply]; change R _+Y _-W _= _; abel
    · intro hM
      have hy (j) (hj:j≤o) b r: Card k Ⓨ 1 (fun i=> Υ (L i).low b j r) 1:= by
        refine ((Lens_pay he (hj.trans h) b r k).first.mold (fun i=> (L i).low)).tax ?_ u'.age
        have h (i:Wall w 1): menu X (L i).low= menu X i.world := by change Launch.farY X (L i).toLaunch=_; rw [ht.wake]
        simp_rw [h]; exact Wall.invested X
      let G i:= edgeBook (Υ (L i).low) (call H F (P i)) o r
      rw [show (fun i=> U i.low o r-P i o r)= -G from funext fun i=>?_]; swap
      · rw [ht.rise i]; change _= -(G i); exact sub_sub_cancel_left (P i o r) (G i)
      apply Card.neg; rw [← mul_one (strideP X w p (n:=1))]; exact elig u'.age zero_le_one hy (fun i=>(he.firs (L i|>.low)).toBoards) (fun j b hb=> by
         rcases hb with H|⟨hv',hh⟩
         · exact (hv j _ (Or.inl H)).key b rfl
         subst j; rcases hh.eq_or_lt with h|he
         · exact hM _ _ h.symm rfl b rfl
         exact (hv _ _ (Or.inr ⟨rfl,by simp only [one_ne_zero,↓reduceIte]; exact he⟩)).key b rfl)
    rw [show (fun i=>P i o r)= R+Y from funext hy]
    exact ((inlet (d:=d) u' (fun i=> (ht.zone i.roof).hU) (fun i=>(ht.zone i.roof).hU) T'.paper (v:=1) zero_le_one le_rfl (η:=1) (fun i=> by simp only [Pi.one_apply]; apply (div_le_one (by positivity)).2; exact_mod_cast (X.S.block _).property) (Drum.home (g.up hV hp))).first).more hd zero_le_one u'.age
end YM.RG08.Run
