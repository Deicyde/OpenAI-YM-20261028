import YM.RG08.Door.Keys
/-!
# Bill within-sector joint recurrence. Theta-power ∆. Closure. Applies to single
strands of canonically projected H, absolute and variations separately with ONE path.
No auxiliary kernel charged per repeat from post-block horizon. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped BigOperators Topology Real
variable {X:Chain} {G:Gauge}{E e r d τ D j t i k m l :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings
variable {I:Type}{u:I→Windows}
-- oldF & variant.
def price_u (T:Signals P Q E τ H Ω h hD) (t:Launch u) := T.cost (X.J (t.i+1)) (X.J t.i)
def babyQ (G:Gauge) (X:Chain)(t:Wings u 1):= eff X.kernel (X.flight t.N t.i) G
def singSl (U:Session (Letter F)):=diagonalSl (hot U 0)
lemma foot_income (i:Wings u 1) {b:Letter F} (κ:Session (Letter F)) (hS:Enabled T u) {V: Letter F→ EnvelopeU D R G r} {R': Letter F→ EnvelopeU D R G r} (hk : ∀ j k:Letter F,‖singSl κ⁻¹ j k‖≤price_u T i.toLaunch)
    (hu: ∀ j:Letter F,slot j=slot b→ Quire.Lit (V j) (ώ T (i.i+1)) C)
    (he:∀ j:Letter F,slot j=slot b→Quire.Lit (R' j) (ώ T i.i) (C/Real.sqrt (X.S.block i.i).val / expQ F (price_u T i.toLaunch))) :
    Quire.Lit (footnote R' (singSl κ⁻¹) b univ) (ώ T i.i) (C*gain X.S (1/2) i.i (i.i+1)) := by
  rw [singSl,swap_coins (i:=slot b) (he:=rfl)]
  let p := univ.filter (fun i:Letter F=>slot i=slot b); let Q:= price_u T i.toLaunch; let a:= expQ F Q; let H:= Real.sqrt (X.S.block i.i).val
  have ht:0<H:= by unfold H; positivity
  have hC:0≤C:=(hu b rfl).nonneg
  have hh:0≤Q:= zero_le_one.trans (T.admits ..); have ha:0<a:= zero_lt_one.trans_le (expQ_pos F hh)
  apply Ink.raise (Ink.additions (s:=p) (g:=fun _=> Q*(C/H/a)) (f:=fun k=> singSl κ⁻¹ k b • R' k) (fun j hj=>Ink.raise (Ink.scale (he j (mem_filter.mp hj).2) _) (mul_le_mul_of_nonneg_right (hk j b) (div_nonneg (div_nonneg hC ht.le) ha.le))) (fun _=>(ling_pos _ _).le))
  rw [sum_const,nsmul_eq_mul,gain_succ_half,mul_one_div]
  calc
    _ ≤ a*(C/H/a):=by rw [←mul_assoc]; gcongr; exact le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_univ p)) hh) (le_add_of_nonneg_left zero_le_one)
    _ = _ := mul_div_cancel₀ _ ha.ne'

variable {V : Wings u 0→Letter F→EnvelopeU D R G r} {S' : Wings u 1→ Session (Letter F)}

theorem transferSl (he:θ ≤ 1/4)(hk: Enabled T u)
    (hh:∀ i:Wings u 1,Flash (X.S.block i.i) (S' i)) (hq:∀ i:Wings u 1, ∀ a b:Letter F,‖singSl (S' i)⁻¹ a b‖≤price_u T i.toLaunch)
    (hV: r≤ τ+E)(hA : ∀ i b, Abates (V i b) (d+1)) (hP:∀ i b, Polished (V i b))
    (hp:∀ b:Letter F,slot b=l→ Tin (fun i:Wings u 0=>menu X i.roof) 1 (fun i:Wings u 0=> V i.roof b) (fun i=>ώ T i.N))
    (ht : ∀ b:Letter F,slot b=l → Tin (menu X) (chop X θ) (fun i:Wings u 1=> footnote (V i.low) (singSl (S' i)) b univ - aboard d (babyQ G X i) (V i.up b)) (fun i=>ώ T i.i)) :
    ∀ b:Letter F, slot b=l → Tin (menu X) (chop X θ) (fun i:Wings u 0=> V i b) (fun i=>ώ T i.i) := by
  let a := univ.filter (fun i:Letter F=>slot i=l)
  have h1 : 0 ≤ (1:Wings u 0→ℝ):= fun _=> zero_le_one
  obtain ⟨C,hC,H₀⟩:= tin_pool (F:=fun t i=>V i.roof t) (q:=a) (δ:=1) h1 (fun i hi=>hp i (mem_filter.mp hi).2) fun i=> sh X _
  let R' i b:= aboard d (babyQ G X i) (V i.up b)
  let W (i:Wings u 1): Letter F→ EnvelopeU D R G r:=fun b=> footnote (V i.low) (singSl (S' i)) b univ-R' i b
  have hY i : V (low i)=fun b=> footnote (R' i) (singSl (S' i)⁻¹) b univ+ footnote (W i) (singSl (S' i)⁻¹) b univ:= by
    funext b; apply Eq.trans (consume (V i.low) _ (hh i) b).symm; conv_lhs=> arg 1; rw [show (fun j=> footnote (V i.low) (diagonalSl (hot (S' i) 0)) j univ)=R' i+W i from funext fun j=> (add_sub_cancel ..).symm]
    unfold footnote; simp_rw [Pi.add_apply,smul_add,sum_add_distrib]; rfl
  let Y b i:= footnote (W i) (singSl (S' i)⁻¹) b univ
  have hB b (hb:slot b=l): Tin (menu X) (chop X θ) (Y b) (fun i=>ώ T i.i):= by
    unfold Y singSl; simp_rw [fun i=> swap_coins (A:=hot (S' i)⁻¹ 0) (f:=W i) hb] -- unfold singSl
    refine Tin.additions _ (sh X) (f:=fun i j=> _) (fun i hi=> ?_) -- f
    refine Tin.scale (ht i (mem_filter.mp hi).2) ?_
    exact (hk.inv.transfer (toLaunch (u:=u) (k:=1))).mono (fun i=> norm_nonneg _) (fun v=> hq v i b)
  obtain ⟨B,hD,hU⟩:= tin_pool (F:=Y) (q:=a) (fun i=> (gain_pos ..).le) (fun i hi=> hB i (mem_filter.mp hi).2) (sh X)
  obtain ⟨K,p,hK,hk'⟩:=hC; obtain ⟨M,s,hM,hE⟩:=hD
  let A:=K+M; have hA':0≤A:= add_nonneg hK hM
  obtain ⟨D,hD,H⟩:=solve_bed θ he _ hA' (max p s)
  intro b hb
  refine ⟨_,(Weighed.constant (menu X) hD).times (Weighed.power (menu X) (Wings.sh X) (max p s)),fun i=>?_⟩
  let g (j:ℕ) (hV:(u i.b).start ≤ j)(hs:j ≤ i.N): Wings u 0 := {i with i:=j, geC:=hV,cut:=hs}
  let Q (j:ℕ) (p:ℝ) := ∀ c:Letter F,slot c=l→∀ h₁ h₂,Quire.Lit (V (g j h₁ h₂) c) (ώ T j) p
  refine (H X.S (u i.b).pos _ i.N (u i.b).k Q (i.geC.trans i.cut) ?_ ?_ ?_ i.i i.geC i.cut b hb i.geC i.cut)
  · intro i hi hv v hP t hx b hp h₁ h₂; exact Ink.raise (hP b hp h₁ h₂) hx
  · intro c hc hs hz
    apply Ink.raise (H₀ c (mem_filter.mpr ⟨mem_univ _,hc⟩) i); rw [Pi.one_apply,mul_one]; refine (hk' i).2.trans ?_; change K*(menu X i.roof)^p≤ A*(menu X i.roof)^(max p s); have hv:1≤menu X i.roof:= sh X _; have hh:K≤A:= le_add_of_nonneg_right hM; gcongr; exact le_max_left ..
  intro t h₁ h₂ v hv c hc ht' hz
  let a': Wings u 1 := ⟨⟨i.b,t,h₁⟩,i.N,i.M,h₂,i.side⟩
  let i':=a'.low
  have hg : g t ht' hz=i':= rfl
  rw [hg]; unfold i'
  rw [hY a']
  have hz':=foot_income a' (S' a') hk (V:=V a'.up) (R':=R' a') (b:=c) (hq a') (fun j hj=> hv j (hj.trans hc) a'.up.geC a'.up.cut) (fun j hj=> ?_)
  · refine Ink.raise (Ink.plus hz' (hU c (mem_filter.mpr ⟨mem_univ _,hc⟩) a') (fun _=>(ling_pos _ _).le)) (add_le_add_right ?_ _)
    apply mul_le_mul_of_nonneg_right _ (gain_pos ..).le; refine (hE a').2.trans ?_; change M*(menu X a')^s≤ A*(menu X a')^(max p s); have hu:M≤A:=le_add_of_nonneg_left hK; have he':1≤ menu X a':=sh X _; gcongr; exact le_max_right .. -- add_le...
  exact T.pros _ _ (X.flight a'.N a'.i) (X.adm _) ((hk.stepCap _).trans (X.mono _)) (hk.order _) r hV _ (hP _ _) (hA _ _) _ (hv _ (hj.trans hc) a'.up.geC a'.up.cut)
end YM.RG08.Door
