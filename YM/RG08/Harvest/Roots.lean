import YM.RG08.Plot.Isle
/-!
# Closer stops. Age charges for full evaluated product before Π and any free pivots
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Harvest
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands Pill Wings PowerSeries Taste Plot Plot.High
open scoped BigOperators Topology Real ContDiff Classical
variable {I J M:Type} {u:I→Windows}{n k i:ℕ}{X:Chain}{G:Gauge}{E e r d τ D j t l N:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{A:Grotto G P k E τ}
variable {b:J→ Dial u}{p:List M}{a z:M→ℕ}{φ:M→J→ Profile D}{C B:J→ℝ}{q s:M→ J→ℝ}
-- define on older all. At stage above k candidate subset.
def Optic (P:Dial u)(n:ℕ) : Prop := (u P.a).start ≤ n ∧ n ≤ P.K
variable {W:J→ℕ}
def shineP (t:J)(h:∀ i,Optic (b i) (W i)): ShoreP u:=⟨⟨⟨⟨(b t).a, (b t).K, (b t).side⟩,(b t).N,(b t).M, (b t).main,(b t).ripe⟩,(b t).side,(b t).main⟩,W t,(h t).2,(h t).1⟩ -- W typo intro
variable (hp: ∀ i,Optic (b i) (W i)) -- W interpreted separately
local notation "☎" => fun i=> shineP i hp
def civic (hp:∀ i,Optic (b i) (W i)) : J→ ShoreP u:= fun i=>shineP i hp
lemma softer_one (i:Wall (civic hp) 0): fareP X (b i.a).K i.i =1:= by
  unfold fareP spanP; apply min_eq_left; rw [← Real.rpow_one (X.S.a _/X.S.a _),←gain_spacing]; apply Real.one_le_exp_iff.mpr; exact mul_nonneg_of_nonpos_of_nonpos (by norm_num) (sub_nonpos.mpr (age_scale_mono _ i.last))
lemma y_hatch (i:Wall (civic hp) n): Plot.tribute X b i.a ≤ wallY X i:= by
   apply le_max_right ..
lemma y_pay : Weighed (fun i=>(civic hp i).y X) (Plot.tribute X b) := by
   let v i:=(civic hp i).y X
   exact (show Weighed v v by simpa only [pow_one] using Weighed.power v (fun i=>city_one (civic hp i) X) 1).mono (fun i=> zero_le_one.trans (age_one (u _|>.pos) _ _)) (fun i=> y_hatch (n:=0) hp (Wall.tip (civic hp) i))
lemma rent_lo (X:Chain)(b:J→Dial u)(W:J→ℕ)(hp:∀ i,Optic (b i) (W i)) i : (civic hp i).rate X=payableD X b i:= by
    let P:=civic hp i; change gain _ (1/4) (max (b i).K (b i).K) _= _; simp only [max_self]; rfl
lemma roof_high (hp:∀ i,Optic (b i) (W i))(he : Tights T S ν D' u) (i:Wall (civic hp) 1): Fair (dance X ν D' (b i.a).N i.i) ∧ Fair (dance X ν D' (b i.a).M i.i):=⟨he.fair i.world,he.fair i.world.wingR⟩

-- at measurement center vertex
variable {U V: J→ M→ℕ→BoardU D R G}
variable (X ν D')
abbrev beacon (b:J→Dial u)(j:J): High b 0 := ⟨j,(b j).K,le_rfl,(b j).main⟩
def field_at (b:J→ Dial u)(U:J→ M→ℕ→BoardU D R G)(p:List M)(z a:M→ℕ)(φ:M→ J→Profile D) (x:J→E4) (i:J)(k:ℕ): Tale G:= waveProduct X ν D' (b i).K (b i).N (x i) p z a (fun j=>φ j i) (U i) k
def field_x (b:J→ Dial u)(U:J→ M→ℕ→BoardU D R G)(p:List M)(z a:M→ℕ)(φ:M→ J→Profile D)(x:J→E4)(i:J)(k:ℕ): Tale G:= Town.season (-arcT X (b i).K k (x i)) (field_at X ν D' b U p z a φ x i k)
variable {X ν D'}
local notation "Ω₁" => field_at X ν D'
local notation "ρ" => field_x X ν D'
section stage
variable [Fintype M]
lemma flare (he:Tights T S ν D' u)(hz:Fleece T b ν D' (k+(loadᵣ a p+l)) E p z a U V q)(hM:Mats p (Plot.tribute X b) C B s φ)(hm: loadᵣ z p ≤ τ)(hF:∀ i∈p,z i≤ τ)(hP:p.Nodup)(hd:∀ i,i∈p)(hv:Pines A u)(hE:e≤E)(h0:1≤l) (x:J→E4) : Drum k (Plot.tribute X b) (payableD X b) (accrues (q*s) p) (fun i=> ρ b U p z a φ x i (b i).K e r) (fun i=>ρ (rightT b) V p z a φ x i (b i).K e r) 1:= by
  have ht: material X ∘ (beacon b) = 1:= funext fun i=> by change X.S.a _ / X.S.a _ = (1:ℝ); apply div_self; exact (X.S.a_pos _).ne'
  have hY:= (gather he hz hM hm hF hP hd hv hE h0 x (r:=r)).mold (beacon b)
  convert hY using 1 <;> first | rfl| (funext i; first| exact Eq.symm (congr_fun ht i)| (change _=_/(material X (beacon b i))^(loadᵣ a p); rw [show material X (beacon b i)=1 from congr_fun ht i,one_pow,div_one]))
-- marchFull relation to o (finite). variation timing exact
lemma stone_f (hz:∀ i:J, Scenes X ν D' (b i).K (b i).N p z a (U i))(x:J→ E4)(i:J): Stone (loadᵣ z p) (Ω₁ b U p z a φ x i (b i).K) := by
    let V j:= cost_full (hz j) (k:=(b j).K) (i:=(b j).K) le_rfl ((b j).main) (x j) (fun k=>φ k j)
    unfold field_at; rw [serve (hz i) (le_refl _) ((b i).main)]; exact Stone.more (V i) (Stone.group _ _ (fun j hj=> dust_rides (hz i) (le_refl _) ((mem_Ico.mp hj).1) ((mem_Ico.mp hj).2)))
lemma dust_on (X:Chain)(ν:G.ColorIndex)(D':ChartRatio G)(hp:i ≤ k)(V:Tale G)(h:k ≤ l) : dustP X ν D' N l τ i V= dustP X ν D' N k τ i (dustP X ν D' N l τ k V) := by
  induction hp using Nat.decreasingInduction with
  | self=> rw [dust_top]
  | of_succ i hi ih=> nth_rw 1 [dust_step _ _ _ _ _ _ _ _ (hi.trans_le h)]; rw [dust_step _ _ _ _ _ _ _ _ hi,ih]
lemma dictum (hp:∀ i, Optic (b i) (W i))(he:Tights T S ν D' u)(hP:Fleece T b ν D' (k+(loadᵣ a p+l)) E p z a U V q) (hv:Pines A u)(hm:Mats p (Plot.tribute X b) C B s φ)(hy:loadᵣ z p ≤τ)(hZ:∀ i∈p,z i ≤ τ)(hH:p.Nodup)(hd:∀ i,i∈p)(h0:1≤l)(hE:e≤E)(x:J→E4) :
    Drum k (wallY X) (tiltP X) (badge (accrues (q*s) p)) (fun i:Wall (civic hp) 0=> field_x X ν D' b U p z a φ x i.a i.i e r) (fun i=> field_x X ν D' (rightT b) V p z a φ x i.a i.i e r) 1:= by
  let L:= civic hp; let E' j:= field_at X ν D' b U p z a φ x j (b j).K; let W' j:= field_at X ν D' (rightT b) V p z a φ x j (b j).K
  let y(t:Wall L 0) := scaleP X (fun j=> (b j).K) t
  have hr t : y t=1:= softer_one _ t; have hs:0 ≤ accrues (q*s) p := pow_pr (fun i hi j=>mul_nonneg (hP.hint i hi _) (hm.zero i hi _));
  have hH' := rowing (b:=fun j=>(b j).K) (w:=L) (U:=E') (V:=W') he hv (δ:=y) (stairsP X L (fun j=>(b j).K)) (fun i=> le_of_eq (rent_lo _ _ _ hp i.a)) (stone_f hP.main x) (stone_f (b:=rightT b) hP.side x) hy hs (fun i=> (gain_pos ..).le) (he':=fun i hi r=> ?_) e hE r (x:=x)
  · have hR (b:J→ Dial u)(U:J→ M→ℕ→ BoardU D R G)(j:J)(i)(hi:i≤ (b j).K): Ω₁ b U p z a φ x j i= dustP X ν D' (b j).N (b j).K (loadᵣ z p) i (Ω₁ b U p z a φ x j (b j).K):= dust_on _ _ _ hi _ (b j).main
    convert hH'.1 using 1
    all_goals first|rfl|(
      ext1 i
      first
      | exact rent_lo _ _ _ hp i.a
      | exact Eq.symm (hr i)
      | unfold field_x; rw [hR b U i.a i.i i.last]; rfl
      | unfold field_x; rw [hR (rightT b) V i.a i.i (show _≤ _ from i.last)]; rfl)
  have hM:= flare he hP hm hy hZ hH hd hv hi h0 x (r:=r); have hz:Audience (fun i=> (L i).y X):= fun i=> city_one _ _
  have hx: (fun t=> y (Wall.tip L t)) = 1:= funext fun t=> hr _; rw [hx]; exact ⟨hM.first.tax (y_pay hp) hz,hM.second.tax (y_pay hp) hz,hM.funds.tax (y_pay hp) hz⟩ -- orientation args
end stage
end YM.RG08.Harvest
