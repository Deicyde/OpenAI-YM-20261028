import YM.Next.RANK.Radian.Signed


/-!
# Rank Kernel fee from unmarked geometry

For these epochs. No mixing different kernels at any N,p!

Do NOT claim `Seal` from other Rank detector estimates or endpoint contour.
Needs an unmarked metric Fourier symbol step theorem (at k using its *actual*
ancestors and harmonic) and its prep prices. We explicitly keep chart trimming as
domain choice of prudence. Could, for example, use a smooth partition of unity
relative to Native Brillouin zone (chart scaled to unit-period) (with sign conventions exactly in
symbol), but still must prove all rates. Supports any finite p by requiring F
possibly individually, exact matrix values at every corresponding torus point.
No needing analytic torus at infinite period. Vantage budget comes from level price.
No claiming realizing it. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric Beamer Lattice Prayer Finset
open Atlas Normal Perch Wall CellsInt Function RG Station 
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace
variable {H : Gauge}

structure Seal (A : Levels H)
    (k p d R : ℕ) (F : AtlasData H A.S p) (b : ℝ) : Prop where
  fiscal u v : (∀ i, shutter (looked (F.κ k) u v i)) ∧ (∀ j,shutter (fun z=>looked (F.κ k) u v z j))
  stamps (a T : Degree H) (h : a.degree=0) (hp : T.degree=0) : ∃ f : E4→ℂ,
    (∀ u v x y : Cover,(F.κ k).cov (body u (x,a.a,a.paint)) (body v (y,T.a,T.paint))= stepsP f (A.S.side k p) R (captured u v x y)) ∧
      Window f R (Perch.bill (1/4) (clim A k)) (2*d+6) b a T
-- Here asks partials through 2*d+6 in sense of Fréchet derivatives (punctured).

lemma commissioned (A : Levels H) (hG : H.Simple) (d R : ℕ) (h : 0 < R) {b : ℝ} (hb : 0<b) :
    ∀ᶠ k in atTop,∀ p F,Seal A k p d R F b→Wall.Model A d k p F:= by
  have ht :∀ᶠ k in atTop,∀ a T : Hub H (d+2) 0, ∀ f,
    let F:= parade a.val T.val f
    let C:= Perch.bill (1/2) (clim A k)
    Window f R (Perch.bill (1/4) (clim A k)) (2*d+6) b a.val T.val→ Integrable F ∧ Mist (F-HeatP b a.val T.val) (a.val.degree+T.val.degree) C ∧ Lip F R C:= by
    refine eventually_all.mpr fun a=> eventually_all.mpr fun T=>?_
    obtain ⟨c,hc,hx⟩:= intended R h a.val T.val hb (2*d+6) (by have hj:= a.property; have ht:= T.property; omega)
    filter_upwards [(Station.hat_rate A hG).eventually (Glimmer.transports (show (1/4:ℝ)< 1/2 by norm_num) c)] with i hi f F C H
    exact hx _ _ _ (Glimmer.costed _ _ (by norm_num)) H ((mul_comm ..).trans_le hi)
  refine (ht.and (commuting A hG d R hb)).mono ?_; intro k h p F Y
  apply h.2 p F; refine ⟨Y.fiscal,fun a b Ha Hb=>?_⟩
  obtain ⟨f,hx,HQ⟩:=Y.stamps (origin a) (origin b) rfl rfl
  let U (p : Degree H) (h : p.degree ≤ d-1) : Hub H (d+2) 0:= ⟨{p with point:=0},rfl,Nat.zero_le _,by dsimp;omega⟩
  have he : Window f R (Perch.bill (1/4) (clim A k)) _ _ (U a Ha).val (U b Hb).val:= ⟨HQ.nonneg,HQ.event,HQ.coast,HQ.meas,HQ.cast,HQ.crest⟩
  exact ⟨f,hx,h.1 (U a Ha) (U b Hb) f he⟩
-- expenditure after large_L chosen checks Height with pre-L multiplier.

def Weight (L M b a : ℝ):= 1≤M∧1<L∧0≤b∧0<a∧ 4*(b+2)*Real.log M ≤ a*Real.log L
lemma trains {L M b a} (h : Weight L M b a) (t : ℕ) : ∀ᶠ s in atTop,M^(Station.bump L b s)*(2:ℝ)^t≤ Perch.bill a s:= by
  obtain ⟨hv,hl,hb,ha,H⟩:=h
  have he:0 ≤ log M:= Real.log_nonneg hv; have hz:=Real.log_pos hl
  let p:= fun s=> ((Station.bump L b s):ℝ)
  filter_upwards [boil_rate.eventually_ge_atTop (4*log M/a), Glimmer.transports (show a/2<a by linarith) ((2:ℝ)^t)] with s hs hp
  let f:= Real.log L; let u:= boil s; have hU:0 ≤ u:= boil_pos _
  have hh:(↑(Station.bump L b s):ℝ) ≤ (b+2)*u/f+1:= by
    have he: Real.log ((YM.Vac.Numbers.P s)^b*(YM.Vac.Numbers.P s)^2)= (b+2)*u:= by unfold YM.Vac.Numbers.P; rw [Real.log_mul (by positivity) (by positivity),Real.log_rpow (Real.exp_pos _),Real.log_pow,Real.log_exp]; push_cast; unfold u boil y;ring
    unfold Station.bump Station.want;rw [he]; exact (Nat.ceil_lt_add_one (by exact div_nonneg (mul_nonneg (by linarith only [hb]) hU) hz.le)).le
  apply le_trans _ hp;rw [mul_comm]; apply mul_le_mul_of_nonneg_left _ (by positivity); rw [← show Real.exp (Real.log M)=M from Real.exp_log (by linarith), ← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr
  have hx : (b+2)*u/f*(Real.log M)≤a*u/4:= by rw [div_mul_eq_mul_div]; apply (div_le_iff₀ hz).2; nlinarith only [mul_le_mul_of_nonneg_right H hU]
  have hz := (div_le_iff₀ ha).1 hs
  apply le_trans (mul_le_mul_of_nonneg_right hh he); linarith only [hx,hz]
lemma gloss {D' n : ℕ} {R M b} (h : Weight R M b (Glimmer.fuel D' n/4)) d : ∀ᶠ s in atTop,M^(Station.bump R b s)*(2:ℝ)^d ≤ fraction n D' s:= trains h _
lemma enough_room {n m b} (M : ℝ) (h : 1≤M) (hh : 0≤b) : ∀ᶠ L in atTop, Weight L M b (Glimmer.fuel n m /4):= by
  let v:= Glimmer.fuel n m/4; have he:0 < v:= div_pos (Glimmer.fuel_real ..) (by norm_num)
  filter_upwards [eventually_gt_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop (4*(b+2)*Real.log M/v)] with L hL ht
  exact ⟨h,hL,hh,he,(mul_comm v (Real.log L)).trans_ge ((div_le_iff₀ he).1 ht)⟩
end YM.Next.Rank.Radian
