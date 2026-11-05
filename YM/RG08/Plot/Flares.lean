import YM.RG08.Plot.Forest
/-!
# Cost geometry W⊕. Harvest $δ without moving the center between cutoffs
or changing Width set. `Dial` over same schedule of widths/costs per local.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Plot
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands Pill Wings
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I J M:Type} {u:I→Windows}{n k i:ℕ}{X:Chain}
structure Dial (u:I→Windows) where
   a:I
   N:ℕ
   M:ℕ
   side:(u a).start≤ (u a).k
   main:(u a).k≤ N
   ripe:N≤M
abbrev Dial.K (t: Dial u):=(u t.a).k
abbrev Dial.W (t:Dial u):=(u t.a).Z
abbrev Dial.fee (X:Chain)(t: Dial u):=age X.S t.W t.K t.K
variable {b:J→ Dial u}
def rightT (b:J→Dial u)(s:J): Dial u:= let p:= b s;{p with N:=p.M,main:=p.main.trans p.ripe,ripe:=le_rfl}
structure High (b:J→Dial u)(n:ℕ) where
   z:J
   i:ℕ
   heap:(b z).K ≤ i
   scope:i+n≤(b z).N
namespace High
def appr (w:High b n): Wings u n:= ⟨⟨(b w.z).a,w.i,(b w.z).side.trans w.heap⟩,(b w.z).N,(b w.z).M,w.scope,(b w.z).ripe⟩
abbrev K (s:High b n):= (b s.z).K
def roamP (s:High b 0): Roam u:= ⟨s.appr,(b s.z).side,(b s.z).main⟩
def upT (s:High b 1): High b 0 := ⟨s.z,s.i+1,s.heap.trans (Nat.le_succ _),s.scope⟩
def lowT (s:High b 1): High b 0:=⟨s.z,s.i,s.heap,(Nat.le_succ _).trans s.scope⟩
def waitP (s:High b 0): ShoreP u:=⟨s.roamP,s.K,s.heap,(b s.z).side⟩
abbrev glass (X:Chain)(s:High b n):= menu X s.appr
abbrev defect (X:Chain)(s:High b n):= chop X (1/4) s.appr
abbrev material (X:Chain)(s:High b n):= spanP X s.K s.i
lemma matL (X: Chain)(s:High b n): material X s = gain X.S 1 (b s.z).K s.i:= by rw [gain_spacing,Real.rpow_one]; rfl
lemma oneP (X:Chain): (material X (b:=b) (n:=n))≤1 := by intro i; rw [matL]; exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_nonneg.mpr (age_scale_mono X.S i.heap)))
lemma scale_u (X:Chain)(s:High b n): fareP X s.K s.i=material X s:= min_eq_right (oneP X s)
lemma glint (X:Chain)(b:J→Dial u)(n): Audience (glass (n:=n) (b:=b) X):= fun i=>sh X i.appr
lemma joust (X:Chain)(p:High b 0):p.waitP.rate X= defect X p:= by unfold ShoreP.rate; change gain _ _ (max p.i (b p.z).K) _=_; rw [max_eq_left p.heap]; rfl
lemma spend (X:Chain)(p:High b 0):p.waitP.y X=glass X p:= by
    unfold ShoreP.y; change max (2+_+|X.S.scale p.K - X.S.scale p.K|) (2+_+ |X.S.scale p.i-X.S.scale p.K|)=_; apply max_eq_right; rw [sub_self,abs_zero]; exact add_le_add (le_refl _) (abs_nonneg _)
lemma here_bill (X:Chain): Weighed (glass X (b:=b) (n:=n)) (fun i=> Dial.fee X (b i.z)):= ((show Weighed (glass X (b:=b) (n:=n)) (glass X) by simpa only [pow_one] using Weighed.power _ (glint X b n) 1).mono (fun i=>zero_le_one.trans (age_one (u _|>.pos) _ _)) (fun i=> add_le_add (le_refl _) (by rw [sub_self,abs_zero]; exact abs_nonneg _))) -- Z>0 need
end High
open High
variable {G:Gauge}{E e r d τ D t l:ℕ}{ν:G.ColorIndex}{F:Labels.Frame G d}{Ω:SectionData F}{H:Hol G}{D':ChartRatio G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}{R:ℝ}{h:1/2≤R}{hD:d+1≤D}{T:Signals P Q E τ H Ω h hD}
lemma kitchen (he:Tights T S ν D' u)(k:ℕ): LensP k E τ (menu X) (chop X (1/4)) (fun i:Wings u 1=>T.vi (X.J i.i)) (fun i=>heights X ν D' i) (fun i=>heights X ν D' i.wingR):= by
   let v:=he.operator; have hp i:=v.hv i
   have hh (i: Wings u 1): 0<T.vi (X.J i.i):=(T.pos _).trans_le (tick_t T _|>.1)
   refine ⟨v.faith,v.bond, sh X,v.crop,v.hessian,v.meansT,v.ribs,v.castG,hh,utterBuy k ?_ hp,fun i=>(gain_pos ..).le⟩
   refine (he.he.costs.transfer Wings.toLaunch).mono (fun i=> inv_nonneg.mpr (hh _).le) (fun i=> inv_anti₀ (T.pos _) (tick_t T _|>.1))
lemma age_take (he:Tights T S ν D' u): Weighed (glass X (b:=b) (n:=1)) (fun i=> (glass X i.upT)):= by
   -- geometric upper only step
   have hP: Weighed (glass X (b:=b) (n:=1)) (fun i:High b 1=> ((X.S.block i.i).val:ℝ)):= he.operator.crop.transfer appr
   have hx := (show Weighed (glass X (b:=b) (n:=1)) (glass X) by simpa only [pow_one] using Weighed.power _ (glint X b 1) 1).times hP
   apply hx.mono (fun i=>zero_le_one.trans (sh X _)) (fun i=> le_trans (age_larger (u (b i.z).a).pos i.K (S:=X.S) (i:=i.i) (Nat.le_succ i.i)) ?_)
   let L:=X.S.block i.i
   have he:=Real.add_one_le_exp (Real.log (L.val:ℝ)); rw [Real.exp_log (by positivity), add_comm] at he
   refine mul_le_mul_of_nonneg_left ?_ (zero_le_one.trans (age_one (u _|>.pos) i.K i.i)); rw [X.S.scale_succ _,add_sub_cancel_left]; exact he -- pos
lemma helms (hx:Tights T S ν D' u){v:J→ℝ}{U V:High b 0→Rooted (Voice D R) (Loc G 1) r}(hp:0≤v)(h:Drum k (glass X) (defect X) (fun i=>v i.z) U V 1) : Drum k (glass X) (defect X) (fun i:High b 1=>v i.z) (fun i=> U i.upT) (fun i=> V i.upT) 1:= by
   have hz: Audience (High.glass X (b:=b) (n:=1)):= High.glint X b 1
   have he := h.mold High.upT; refine ⟨he.first.tax (age_take hx) hz,he.second.tax (age_take hx) hz,?_⟩
   -- need nonneg v
   refine Card.lesser (z:=fun i:High b 1=> ((X.S.block i.i).val:ℝ)) (Card.raise (he.funds.tax (age_take hx) hz) ?_) (hx.operator.crop.transfer High.appr)
   intro i; simp only [Pi.mul_apply]; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (continued' X _ (by norm_num) i.appr) (hp i.z)
end YM.RG08.Plot
