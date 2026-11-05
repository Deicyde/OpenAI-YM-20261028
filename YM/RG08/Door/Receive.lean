import YM.RG08.Door.Lodge
/-!
# Canonical Wilson history on wing: deliver operator at clock i and gauge tree. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped BigOperators Topology Real
variable {X:Chain}{G:Gauge}{E e r d τ D N i k: ℕ}{R w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings
variable {I:Type}{u:I→Windows}
-- Canonical powers over y_i. stage demands for post white currencies added below.
structure Enabled (T:Signals P Q E τ H Ω h hD)(u:I→Windows) : Prop where
  fromJ l : d+2 ≤ X.J (u l).start
  order (i:Launch u) : T.gate (X.J (i.i+1)) ≤ (X.S.block i.i).val
  costs : Weighed (Launch.farY X (u:=u)) (fun i=>(T.wi (X.J i.i))⁻¹)
  inv : Weighed (Launch.farY X (u:=u)) (fun i=> T.cost (X.J (i.i+1)) (X.J i.i))

lemma Enabled.stepCap (ha:Enabled T u)(t:Launch u) : d+2 ≤ X.J t.i := (ha.fromJ _).trans ((monotone_nat_of_le_succ X.mono) t.geC)
lemma Enabled.stepV (ha:Enabled T u)(t:Launch u): T.vi (X.J t.i)≤ (X.S.block t.i).val*(T.wi (X.J (t.i+1))/((τ+E+1:ℕ):ℝ)) := T.pad _ _ (X.flight 0 t.i) (X.adm t.i) ((ha.stepCap t).trans (X.mono _)) (ha.order _)
lemma tick_t (T:Signals P Q E τ H Ω h hD)(j:ℕ): T.wi j ≤ T.vi j ∧ T.vi j ≤ ticketW Q j := by
  have hu := le_trans (show T.wi j ≤ snug .. • _ from ?_) (T.ores j)
  have hx := (T.pos j).trans_le hu
  have hk : 1≤ funding E (windows τ E):= Nat.succ_le_of_lt (by unfold funding; positivity)
  refine ⟨hu, le_trans ?_ (T.arcs j)⟩
  · simpa only [one_smul] using smul_le_smul_of_nonneg_right hk hx.le
  simpa only [one_smul] using smul_le_smul_of_nonneg_right (show 1≤ snug τ E (windows τ E) from snug_p) (T.pos j).le
lemma onward : rootsRatio X ν D' N (i+1) i= reform (slag X ν D' N i) := by
  unfold rootsRatio; rw [show spanR (i+1) i=0+1 by unfold spanR; split <;> omega, paths,paths,ratioLane,if_pos (by omega),show bright (i+1) i 0=i by unfold bright; split <;> omega]
  ext j; unfold glide Span
  rw [show PowerSeries.mk (fun j=>PowerSeries.coeff j (1:PowerSeries ℝ)) =1 from (by ext k; rw [PowerSeries.coeff_mk])]; simp 
lemma local_power (hc:Circuit S ν D' u)(hs:G.Simple)(hv:X.Wake G)(hm:LocalRatio D')(he:e≤E): Lease (menu X) (chop X (1/4)) (fun t:Wings u 1=> PowerSeries.coeff e (dance X ν D' t.N t.i).scale) (fun t=>PowerSeries.coeff e (dance X ν D' t.M t.i).scale):= by
  classical
  let A t:= slag X ν D' (t:Wings u 1).N t.i; let B t:= slag X ν D' (t:Wings u 1).M t.i
  simp only [dance,onward, afternoons,PowerSeries.coeff_expand,PowerSeries.coeff_mk]
  by_cases hx: 2 ∣ e
  · simp only [hx,↓reduceIte]; apply Lease.mat; swap; exact sh X
    intro i hi; exact Lease.reforming (f:=A) (g:=B) (k:=e/2) (sh X) (fun j hj=>grow_budget hc hv hm hs (by omega)) _ hi
  simp only [hx,↓reduceIte]; exact Lease.const ..

abbrev ώ (t : Signals P Q E τ H Ω h hD)(i:ℕ):= t.wi (X.J i)
abbrev heights (X:Chain)(ν:G.ColorIndex)(D':ChartRatio G)(t:Wings u 1) := dance X ν D' t.N t.i
private lemma wakes_f (hc:Circuit S ν D' u)(hs:G.Simple)(hv:X.Wake G)(hm:LocalRatio D')(j e b k:ℕ) {n:ℕ}(he:e≤E)(hk: RootStep n e k j b): let U i := ((heights X ν D' (i:Wings u 1)).song); let V i:= ((heights X ν D' (i:Wings u 1).wingR).song)
    Both (menu X) (chop X (1/4)) (fun i=>U i j b) (fun i=> V i j b) (fun i=>ticketW Q (X.J i.i)) := by
  intro U V
  obtain ⟨⟨ht,k',hx'⟩,hu⟩:=hk
  have hu' := (Wings.skater hc hs hv hm (e:=j) (by omega) b).top -- name
  have hh := Wings.bothUp hc hu'
  let L i:= luggage ν (X.patch (i:Wings u 1).i) D' X.kernel j b
  let v i:=ticketW Q (X.J (i:Wings u 1).i); have hL: Voucher (menu X) 1 L v := by
    refine ⟨_,(hc.M.post j (by omega) b (by omega)).transfer toLaunch,fun i=>?_⟩
    apply glow_less (tariff_yes ν _ _ _ _ _ (show v i≤1 from min_le_right ..)) le_rfl
    exact (by simp only [Pi.one_apply, mul_one,le_refl])
  have hz(i:Wings u 1): U i j b=L i-gemL _ (moon X ν D' i.up j b):= nuts ν (X.patch i.i) D' X.kernel _ _
  have hi(i:Wings u 1) : V i j b = L i-gemL _ (moon X ν D' i.up.wingR j b) := hz i.wingR
  rw [show (fun i=> U i j b)= _ from funext hz,show (fun i=> V i j b)= _ from funext hi]
  have H := gem_accrue b (L:=fun t:Wings u 1=>(X.patch t.i).L) (F:=fun v=> moon X ν D' v.up j b) (H:=fun t=>moon X ν D' t.up.wingR j b) (v:=v) (σ:=fun t:Wings u 1=> Tier S (t.i+1)) (y:=menu X) (hc.M.crop.transfer toLaunch) (sh X) (fun _=>(ticket_pos Q _).le) (fun _=> min_le_right ..) (fun _=> (S.positive _).le) (fun i=> le_trans (smul_le_smul_of_nonneg_right (show b+1≤E+3 by omega) (ticket_pos Q _).le) (hire hc i)) hh
  exact (Both.self hL).sub H (sh X)
lemma book_f (hE:Enabled T u)(hc:Circuit S ν D' u)(hs:G.Simple)(hv:X.Wake G)(hm:LocalRatio D'):
    Bucks τ E (menu X) (chop X (1/4)) (fun t:Wings u 1=>ώ T t.i) (fun t=>T.vi (X.J t.i)) (fun t=>ώ T (t.i+1)) (heights X ν D') (fun t=>heights X ν D' t.wingR) := by
  have hV : (fun i:Wings u 1=>T.vi (X.J i.i)) ≤ fun i=>ticketW Q (X.J i.i):=fun i=>(tick_t T _).2
  have ⟨hx,hy⟩:= gear_both hc hv
  refine ⟨fun i=>fairground X ν D' hv hm i.cut,fun i=> fairground X ν D' hv hm i.wingR.cut,sh X,hc.M.crop.transfer toLaunch,hV.trans (fun i=> min_le_right ..),fun i=> (gain_pos ..).le,fun i=> T.pos _,fun i=> (T.pos _).le,fun i=>?_,(fun t=> T.ores _),⟨hx.fresh.soften hV,hx.again.soften hV,hx.moves.soften hV⟩,⟨hy.fresh.soften hV,hy.again.soften hV,hy.moves.soften hV⟩,?_,fun k hk=>local_power hc hs hv hm hk⟩
  · exact (hE.stepV i.toLaunch).trans (mul_le_mul_of_nonneg_left (div_le_self (T.pos _).le (by exact_mod_cast (show 1 ≤ τ+E+1 by omega))) (by positivity))
  intro e he n hn k
  let P i:= (heights X ν D' (i:Wings u 1))
  let B i:= heights X ν D' (wingR (u:=u) i)
  have hP i:Fair (P i):= fairground X ν D' hv hm i.cut; have hB i:Fair (B i):=fairground X ν D' hv hm i.wingR.cut
  let U i:= ((heights X ν D' (i:Wings u 1)).song); let V i:= ((heights X ν D' (i:Wings u 1).wingR).song)
  have hw(t:Wings u 1) : 0≤T.vi (X.J t.i) := (T.pos _).le.trans (tick_t T _).1
  refine crypt (F:=U) (H:=V) (Q:=fun i=>veiled (P i).cv) (U:=fun i=>veiled (B i).cv) (sh X) (fun i=> (gain_pos ..).le) hw (fun i=>ticket_pos Q _) (veil_contract hx (fun _=>(gain_pos ..).le)) (fun i=>⟨(hP i).lived,(hP i).tune⟩) (fun i=>⟨(hB i).lived,(hB i).tune⟩) (fun _=>none) (fun i=>le_trans ?_ (T.arcs _)) ?_
  · exact smul_le_smul_of_nonneg_right (show funding e n ≤ funding E (windows τ E) by unfold funding; gcongr <;> omega) (hw i)
  intro j b hk; exact wakes_f hc hs hv hm j e b k (n:=n) he hk
end YM.RG08.Door
