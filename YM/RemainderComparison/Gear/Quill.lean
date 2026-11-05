import YM.RemainderComparison.Gear.Tapis
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Courants
/-!
# Price the Pad Jacobian without scaling β losses

 Uses exact same cuts/moments; stencil bounds and corona invoiced
 at this post L,j. Does not assert corresponding price for `.stream`
 (e.g., `Rate 0` fees on other vertices may be greater).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Frond
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows Mask Coat SliceRows.DataKernel Metric
open SectorMeasure Oriented Tags Progress.StationaryScenes Green Bid Coat Tree Control Window Census
open Brush Foramen Gate Scroll Vine Tablet RemainderComparison
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge}
-- Gauge fixed; valid p even where Z is void
attribute [local instance] Gauge.frobInner
lemma cushion (G : Gauge) (L : Side) (χ : Chi) {K : ℝ} (γ : ℝ) (j : ℕ) {v : ℝ→ℝ}
    (h : Gear G L (-(1/2)) v) : ∃ B : ℝ→ℝ, Gear G L (-(1/2)) B ∧ ∀ᶠ x in atTop,
    ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U:E→ G.El) (z:E), Brush j (royalty G) (v x) (G.mat ∘ U) z →
      let Z:=K*Pressure.fiery G x L
      Reliable G Z γ → Brush j (|B x|) 1 (fun i=>cutLog χ Z (U i)) z := by
  obtain ⟨J,d,he⟩:= cleanly G j 1 zero_lt_one
  obtain ⟨C,hC,hΘ⟩ := Brush.compact (k:=j) (f:=χ.read) (s:=Set.Icc 0 4) isCompact_Icc (fun _ _=> χ.smooth.contDiffAt.of_le
    (WithTop.coe_le_coe.mpr le_top))
  let m:= royalty G; let f x:= K*Pressure.fiery G x L; let D x:= (1+m)*v x
  let H x:= γ*(2*f x)+(j.factorial*J)*D x; let Y x:= (m*f x)⁻¹*((2*f x)*m+(m+m)*v x); let B x:=
    ((1:ℝ)* H x)*(1+((1+j.factorial*C)*((1+Y x*Y x)*(1+1))+1))^j
  have hp : 0 < m := zero_lt_one.trans_le (royalty_ge _)
  have hf : Gear G L (-(1/2)) f := Gear.flame.mul_left K
  have hd := h.mul_left (1+m)
  refine ⟨B,?_,?_⟩
  · have hr : Gear G L (-(1/2)) H := ((hf.mul_left 2).mul_left γ).add (hd.mul_left (j.factorial*J))
    have hh : Gear G L (1/2) (fun x=> (m*f x)⁻¹) := by
      have hk:= Gear.inverse (G:=G) (L:=L)
      simpa only [f,_root_.mul_inv_rev] using! (hk.mul_right K⁻¹).mul_right m⁻¹
    have hY : Reserve G L Y := (Gear.zero.mp (by convert hh.mul (((hf.mul_left 2).mul_right m).add (h.mul_left (m+m))) using 1; norm_num))
    let hx := Reserve.const (G:=G) (L:=L) (1:ℝ)
    have ha:= (Reserve.const (1+(j.factorial:ℝ)*C)).mul ((hx.add (hY.mul hY)).mul (Reserve.const (1+1)))
    simpa only [add_zero] using! ((hr.mul_left 1).mul (Gear.zero.mpr ((hx.add (ha.add hx)).pow j)))
  filter_upwards [((hf.mul_left 2).mul_right m).rate.below (by norm_num) _ he.pos,
    h.rate.below (by norm_num) 1 zero_lt_one, hd.rate.below (by norm_num) 1 zero_lt_one] with x hX hx ht E _ _ U z h Z hr
  have hp' : 0 < Z := hr.down
  have h₂ : v x ≤ 1 := (le_abs_self _).trans hx
  by_cases hi : G.chord (U z) ≤ 2*Z
  · let V i:= χ.innerShare Z (G.chord (U i))
    let P i:= G.plog (G.mat (U i))
    have hh : ‖G.mat (U z)-1‖ ≤ (2*f x)*m := (div_le_iff₀ hp).1 hi
    let Z' := m*Z; have ht' : 0<Z':=mul_pos hp hp'
    have hV:Brush j 1 ((1+j.factorial*C)*((1+Y x*Y x)*(1+1))) V z := by
      let F i:= G.mat (U i)-1
      have hg : ‖F z‖≤2*Z':= hh.trans_eq (by unfold Z' Z; unfold f; ring)
      have hF:= (plateauChi (f:=F) χ (shrinker (h.separating (a_oneB G 1 h.pos)) hh h₂) hΘ ht' hg)
      refine hF.shimmy (Eventually.of_forall fun z=>?_)
      unfold V F Gauge.chord; unfold Chi.innerShare Z' Z m royalty
      apply congrArg; ring
    have hX' : Brush j (H x) 1 P z := shrinker (h.pine (he.sound _ (hh.trans ((le_abs_self _).trans hX))))
      ((hr.cap _ hi).trans (mul_le_mul_of_nonneg_left hi hr.price.le)) ((le_abs_self _).trans ht)
    exact ((snaps hV hX').trim).climb (le_abs_self _) le_rfl
  refine Brush.zi ?_ (abs_nonneg _) zero_le_one
  have hz : ContinuousAt (fun y=> G.chord (U y)) z := ((h.smooth.continuousAt.sub_const _).norm.div_const _)
  filter_upwards [hz (lt_mem_nhds (lt_of_not_ge hi))] with y hy
  have hu : χ.innerShare Z (G.chord (U y))=0 := by
    by_contra H; exact (χ.chosen_lt _ _ hp' H).not_ge (show _<_ from hy).le
  rw [cutLog,hu,zero_smul]
set_option maxHeartbeats 400000 in
lemma quoin (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W : ℝ) (χ : Chi)
    (j : ℕ) {V : ℝ→ℝ} (h : Gear G L (-(1/2)) V) :
    ∃ X : ℝ→ℝ, Gear G L (-(1/2)) X ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L x S T→ ShellAccess S G x W K γ →
    ∀ (F : Forest S.ratio) (Y : Coat T F) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → Config G c) (z : E), Y.x=x → Y.width=K → Y.χ=χ → Mode U z j (V x) →
      let p i:= vary Y (U i); (p z).manifest → ∀ i, Brush j (|X x|) 1 (fun z=> stand (bar (p z) 0) i) z := by
  obtain ⟨A,hA,hX⟩:= cushion G L χ (K:=K) γ j h
  obtain ⟨C,hC,hq⟩:= bounded_stencils P D hD
  obtain ⟨e,he,hD⟩:= charters P L D hD j h
  let m:= royalty G; let f x:=m*(|A x| *m); let b x:= C*(m*(f x*m)); let d x:= 4*(radiusB x:ℝ)*(V x*royalty G)
  let H x:= b x*(1+(d x+(V x+1+V x)+d x))^j
  refine ⟨fun x=> ‖Coat.scale‖*(e x+H x),?_,?_⟩
  · have hf : Gear G L (-(1/2)) b := by unfold b f; exact ((((hA.absG.mul_right _).mul_left _).mul_right _).mul_left _).mul_left _
    have hs := Reserve.const (G:=G) (L:=L) (1:ℝ)
    have hz : Reserve G L V := Gear.zero.mp (h.weaken (by norm_num))
    have hj : Reserve G L d := ((Reserve.const _).mul Reserve.field).mul (hz.mul (Reserve.const _))
    exact (he.add (show Gear G L (-(1/2)) H from by
      simpa only [add_zero] using! (hf.mul (Gear.zero.mpr ((hs.add ((hj.add ((hz.add hs).add hz)).add hj)).pow j))))).mul_left _
  filter_upwards [hD,hX, room G P L] with x hX he hp c f S T hS hh ha F Y E _ _ U z hv hw ht hhV p hF i
  subst x
  let y := Y.x
  let X:=p z; let s:= i.fst.fst; let k:= i.fst.snd
  have hj (i:Bond f) : Brush j (|A Y.x|) 1 (fun z=> (vary Y (U z)).saved i) z:=by
    let Z := K*Pressure.fiery G Y.x L
    have hk : Reliable G Z γ := by unfold Z; rw [← hh.length_eq]; exact ha.log
    by_cases hi:i∈ F.trunks ∨ Y.Hot i
    · rw [show (fun z=> (vary Y (U z)).saved i)=(fun z:E=> (0:G.Color)) from funext fun z=> (if_pos hi)]
      exact Brush.zi EventuallyEq.rfl (abs_nonneg _) zero_le_one
    let W z := F.drape Y.Y i*(replica S.ratio (U z) i)⁻¹
    have hb: Brush j (royalty G) (V Y.x) (G.mat ∘ W) z := by
      have hh := offsetB (Blaze.reverse (f:=fun t=> replica S.ratio (U t) i) (Blaze.recopy S hhV.atLink i)) (F.drape Y.Y i) 1
      simpa only [mul_one] using! hh
    refine (he _ W _ hb hk).shimmy (Eventually.of_forall fun z=>?_); dsimp only; unfold Coat.saved
    rw [if_neg (show ¬(i∈F.trunks ∨ (vary Y (U z)).Hot i) from hi)]
    change cutLog Y.χ (Y.width*Y.t) _=_; rw [ht,hw]; unfold Coat.t; rw [hh.length_eq]; rfl
  have hx:=hp _ _ S T hh
  by_cases hg : Y.selected s (spot S k)
  swap; · apply Brush.zi _ (abs_nonneg _) zero_le_one; filter_upwards with z; unfold stand bar; rw [if_neg (show ¬(p z).selected i.1.1 (spot S i.1.2) from hg)]; rfl
  let G' (t:E) := strain (p t) s k 0
  have hG : Brush j (e y+H y) 1 G' z := by
    have hk := Blaze.turn hhV s
    apply (hX _ _ S T hS hh (choice s Y.k) k E (fun t=> pull s 0 (U t)) z hk (safe_hull X hF s k hg)).gathering
    rw [show (fun i=> orientedRow T (p i).R s k (p i).V ((p i).signal 0)) =
      (fun i=> straightened T Y.R (pull s 0 (U i)) (displacement s ((p i).saved) (replica S.ratio (U i))) k) from by
        funext i; simp only [Coat.signal, (p i).lens_zero, add_zero]; rfl]
    have ht i := displacement_pay (S:=S) (V:=fun i=> (p i).saved) s i _ _ hhV (hj (edge s i))
    have hn := royalty_ge G; have hm := hhV.pos
    exact ((hard_turn k hx (e:=royalty G *(|A Y.x| *royalty G)) (by positivity) (by exact (ht (0,0)).pos)
      (fun i _=> ht i) hk (hq c f S T hS hh.funds) hC.le).trim)
  have hh (z) : bar (p z) 0 i.1= Coat.scale • G' z := if_pos hg
  unfold stand; simp_rw [hh]; exact (colorEvaluated _ (hG.smul Coat.scale)).climb (le_abs_self _) le_rfl
lemma polyP (G:Gauge)(L:Side)(k m:ℕ)(C u:ℝ):Reserve G L (fun x=> Tablet.facePrice k (radiusB x) m C u):=by
  have ht:= Reserve.ball _ (Reserve.lag (G:=G) (L:=L) 1 2)
  simp only [one_mul] at ht; simp only [facePrice,Nat.cast_mul]
  exact (ht.mul (Reserve.const _)).mul (Reserve.const _)
lemma quartz (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W : ℝ) (χ : Chi) (j : ℕ) {η r Q : ℝ} (hT : Torch η r Q)
    {V : ℝ→ℝ} (h : Gear G L (-(1/2)) V) :
    ∃ b : ℝ→ℝ, Gear G L (-(1/2)) b ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L x S T→ ShellAccess S G x W K γ →
    ∀ (F : Forest S.ratio) (Y : Coat T F) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → Config G c) (z : E), Y.x=x → Y.width=K → Y.χ=χ → Mode U z j (V x) →
      let p i:= vary Y (U i); let X := p z
      X.manifest → Allow X.plate (along S) (tubularPrice G L) η r Q → ∀ i, Brush j (|b x|) 1 (fun y => voltage (p y) i) z := by
  obtain ⟨Z,hZ,Ha⟩:=bounded_stencils P D hD
  obtain ⟨M,hM,hp⟩:= quoin P L D hD K γ W χ j h
  let k:= carat D P L 0 Z; let m:= tubularPrice G L; let A:=k*k+1; let w:=payE η r Q m
  let b x:= kernelGrowth (radiusB x) G (V x); let g x:= k*|M x| *(1+(b x+1))^j
  let d x:= b x+b x; let l x:= facePrice j (radiusB x) m A w; let p x:=driftP j (d x)
  let f x:= (Fintype.card G.ColorIndex:ℝ) * ((l x*g x)*(1+(p x+1))^j)
  have hk:Gear G L 0 b:=Gear.ascend (jet_growth G L h.rate) (by norm_num)
  have hd : Gear G L 0 p:= (hk.add hk).mul_left _
  have hc := (Gear.zero.mpr (Reserve.const (G:=G) (L:=L) 1))
  have hh : Gear G L (-(1/2)) g := by
    simpa only [zero_mul,add_zero] using! ((hM.absG.mul_left k).mul ((hc.add (hk.add hc)).pow j))
  refine ⟨f,?_,?_⟩
  · simpa only [add_zero,zero_mul,zero_add] using!
      ((((Gear.zero.mpr (polyP G L j m A w)).mul hh).mul ((hc.add (hd.add hc)).pow j)).mul_left (Fintype.card G.ColorIndex))
  filter_upwards [hp,room G P L] with x Hx HZ c f' S T hS hY hF F Y E _ _ U z hx hy he hV V' X h hX i
  subst x; let x:= Y.x
  have hz:=Ha _ _ S T hS hY.funds
  have ht := replicaM Y D hS hY.length_eq (HZ _ _ _ _ hY) hV Z hZ hz (le_refl 0) P.top.width_pos
  have ha := plates Y D hS hY.length_eq (HZ _ _ _ _ hY) hV Z hZ hz (le_refl 0) P.top.width_pos
  have hL i : Brush j (g x) 1 (fun y=>leanB (V' y) i) z := (beam_vec ht.reverse
    (u:=fun y i=> stand (bar (V' y) 0) i) (abs_nonneg _) zero_le_one (Hx _ _ S T hS hY hF F Y E U z rfl hy he hV h) i).trim
  have hp : 0 ≤ g x := by dsimp only [g]; have hh : 0≤k:=ht.basis; have he : 0≤ b x:= ht.pos; positivity
  have hh:=padjets Y.shutter ha hX hT.prices.le
  have he (p) := (beam_vec hh.reverse hp zero_le_one (u:=fun i => leanB (V' i)) hL p).trim
  have hv : Brush j (f x) 1 (fun t=>voltage (V' t) i) z := tie G _ (mul_nonneg (mul_nonneg hh.basis hp) (pow_nonneg (add_nonneg zero_le_one (add_nonneg hh.pos zero_le_one)) j)) zero_le_one (fun p=> (he (i,p)).opposite)
  exact hv.climb (le_abs_self _) le_rfl
end YM.ConnectedActivityE6.Blaze.Frond
