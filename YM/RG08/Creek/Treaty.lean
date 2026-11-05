import YM.RG08.Creek.Line
/-! # Organization of marker steps through partial budgets and cuts. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door
open Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset RG Bloch Conductor Staffer Reflect UVExt.Paths Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Wings High
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {X:Chain} {G:Gauge}{E e r d τ D j t f i k m n :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}
variable {P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1 ≤ D}{T:Signals P Q E τ H Ω h hD}
variable {I J Y:Type} [Fintype I][DecidableEq I]{u:Y→Windows}{a b:I→ℕ}{B: ℕ→ Side}{Z w':ℕ→ℝ}
section gear
-- supplement `ω`: even smaller as-needed, not depending on L
structure BrookW (T:Signals P Q E τ H Ω h hD)(u:Y→Windows)(I:Type)[Fintype I](w:ℕ→ℝ): Prop where
    irrigate (i:ℕ): 0<w i
    prior (i:ℕ): w i ≤ secretT T I i
    earth (i:Launch u): T.wi (X.J i.i)≤(X.S.block i.i).val*w (X.J (i.i+1))
    cost : Weighed (Launch.farY X) (fun i:Launch u=> (w (X.J i.i))⁻¹)
lemma secret_house (hk:Ripple T u I)(hp:Enabled T u) : BrookW T u I (secretT T I):=⟨secret_t _ _,fun _=>le_rfl,hk,wind_inv hp I⟩
lemma brook_gates {w:ℕ→ℝ}(hp:∀ i,0<w i) (K:ℕ→ℝ): ∃ L:ℕ→ℕ,∀ i j (f:Flight j i), L j ≤ f.L.val → K i ≤ f.L.val*w j:= by
   choose G hG using fun i j=> exists_nat_gt (K i/w j)
   refine ⟨fun j=>max (G j j) (G (j-1) j),fun i j f he=>?_⟩
   apply (div_le_iff₀ (hp j)).mp; refine (hG i j).le.trans (Nat.cast_le.mpr ?_); by_cases h:i=j; · subst j; exact (le_max_left ..).trans he
   dsimp only at he; rw [show j-1=i by have hv:=f.mono; have hp:=f.narrow;omega] at he; exact (le_max_right ..).trans he
lemma funds_rift (hp:Tights T S ν D' u)(hw:BrookW T u I Z)(a:I→ℕ): ∃ A:Wings u 1→ℝ, Weighed (menu X) A ∧ ∀ (i:Wings u 1)(F:Layouts I G D R)(p:Wax.Head I)(k:I→ℕ), Sense k F →(∀ t, vanes k t+E≤τ)→ Crease p →Fest (Z (X.J (i.i+1))) E 1 p F →Fest (2*Z (X.J i.i)) E (A i) p (creekT (heights X ν D' i) k (vaneW X a i.i) F):= by
   have he i:advanceFee I τ (2*Z i) (windows τ E) ≤ T.wi i:= (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hw.prior _) (by norm_num)) (by positivity : 0≤(parPort I τ:ℝ)^(windows τ E))).trans_eq (secret_b T I i)
   apply creek_univ hp.operator (fun i=> mul_pos (show (0:ℝ)<2 by norm_num) (hw.irrigate _)) (fun i=> (he _).trans (tick_t T _).1) _ (fun i=> (he _).trans (hw.earth i.toLaunch)) (wheel_cash hp a) h
   simp_rw [mul_inv_rev]; exact (hw.cost.transfer toLaunch).times (Weighed.constant _ (show 0≤(2:ℝ)⁻¹ by norm_num))
end gear
section formal
variable {p:J→ Dial u}
def ledgerR (P:∀ i:ℕ,StripU G (B i))(U:Layouts I G D R)(a b:I→ℕ)(n m:ℕ): Layouts I G D R:= if m<n then creekT (P m) a (fun i=>rallyW (B m) (b i)) (ledgerR P U a b n (m+1)) else U
termination_by n-m
abbrev ownerU (X:Chain)(ν:G.ColorIndex)(D':ChartRatio G)(b:J→Dial u)(V:J→ I→ℕ → BoardU D R G)(a w:I→ℕ)(x:J) := ledgerR (dance X ν D' (b x).N) (markZ (fun i=>V x i (b x).N)) a w (b x).N
structure Attract (ν:G.ColorIndex)(D':ChartRatio G)(X:Chain)(p:J→Dial u)(V:J→I→ℕ→BoardU D R G)(a b:I→ℕ) : Prop where
   leaf (s:High p 0)(i):Marvel (a i) (V s.z i s.i)
   roll (s:High p 1)(i): V s.z i s.i= Needle.push (heights X ν D' s.appr) (a i) (b i) (V s.z i (s.i+1))
-- U a unit for primary weights may smaller. use Pla*_PAY, horizon.
def Bureau (w:ℕ→ℝ)(E:ℕ)(A:Chain)(S: J→I→ℕ→ BoardU D R G)(p:J→ Dial u)(F:I→J→ℝ):Prop:= ∀ k≤E,∀ i j,Tin (High.glass A) (fun x:High p 0=>F i x.z) (fun x=>S x.z i x.i k j) (fun x=> w (A.J x.i))
variable {U:J→I→ℕ→BoardU D R G}
lemma owned_tv (hv: Attract ν D' X p U a b)(hC:∀ i:High p 1,Climate (heights X ν D' i.appr))(hk: 1/2≤R)(v:High p 0): Sense a (ownerU X ν D' p U a b v.z v.i) ∧ Harmon (ownerU X ν D' p U a b v.z v.i) (fun i=>U v.z i v.i):= by
   obtain ⟨s,k,he,h⟩:=v; dsimp only; let Z := ownerU X ν D' p U a b s
   change Sense a (Z _) ∧ Harmon (Z _) _
   rw [add_zero] at h; induction h using Nat.decreasingInduction with
   | self => unfold Z ownerU; rw [ledgerR,if_neg (lt_irrefl _)]; exact ⟨eyeSense (hv.leaf ⟨s,_,he,le_refl _⟩), harmony_initial _⟩
   | of_succ k hx ih=>
      let S: High p 1:= ⟨s,k,he,hx⟩; have hU(i): U s i k=_:= hv.roll S i
      obtain ⟨hh,ht⟩:=ih (he.trans (Nat.le_succ k))
      rw [show Z k=creekT (heights X ν D' S.appr) a (vaneW X b k) (Z (k+1)) by unfold Z ownerU; rw [ledgerR, if_pos hx]; rfl]
      refine ⟨creekS_w _ (hC S) hh hk _,?_⟩
      rw [show (fun i=> U s i k)=_ from funext hU]; exact civic_o (hC S) hh hk (hv.leaf S.upT) ht _
end formal
end YM.RG08.Creek
