import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Epoch
import YM.TraceExtension.Prom.Hill.Cadence
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Ratchet
import YM.TraceExtension.Prom.Hill.ShapeS
import YM.TraceExtension.Prom.Hill.StagePass
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Port.Leading
import YM.TraceExtension.Prom.Port.Ribbon
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Epoch for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Rise Spindle Atlas WeightedGaussianMarginal45C.Issue.Cut
    AnalyticBridge.LocalGaussianLaws Work.F08 FreeResolvent Exterior
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge}

section calls

variable {C : Family G} (B : Binding C) (N i p : ℕ)

local notation "j" => C.path.levels.clock.J i

end calls

-- uniform width scheduling

-- post-L, after fixing K,T etc. Don't depend on sizes n

section proceeds
variable {C : Family G} (B : Binding C) (N i p : ℕ)

local notation "j" => C.path.levels.clock.J i

local notation "J" => C.path.levels.clock.J (i+1)
local notation "X" => stamp C.path.levels N p
local notation "x" => clim C.path.levels i
private lemma numericSky {a b c:ℝ}{m:Type*}[Fintype m]{H:Matrix m m ℝ} (h : Numeric H a b)(he:b ≤ c): Numeric H a c:= fun v=> ⟨(h v).1,(h v).2.trans (mul_le_mul_of_nonneg_right he (Finset.sum_nonneg (f:=fun i => v i*v i) fun i _=> mul_self_nonneg _))⟩
private lemma floorSky {a b d:ℝ} {n Q p} (h : Floor Q p n a b)(hv:b ≤ d): Floor Q p n a d:= { h with uniform:= ⟨numericSky h.uniform.1 hv,numericSky h.uniform.2 hv⟩ }

variable (h : i<N)
include h
lemma telescopeSky {ε d} (hp : Paying (C.path.levels.clock.op i p).patch (tell B i)
    (min (B.prices.α J) (B.prices.α j)) (B.prices.η J) (max (B.prices.Ω J) (B.prices.Ω j)) ε x)
    (hx : 0≤ε) (hd : capitalSky C.path.levels.clock.kernel B.prices (C.path.levels.clock.J (i+1)) (C.path.levels.clock.J i) ≤ d) :
    Awake (short B N p i) (track X i) d ε := by
  have he:= paths_budgetSky B (p:=p) h d hd
  let S:= C.path.levels.clock.op i p; let P:=S.patch
  refine ⟨he.1,he.2,hx,fun y=> ?_,fun y u=>?_⟩
  · let A:= (short B N p i).H y; let A':=(track X i).H y
    rw [show Normal.glyph A-Normal.glyph A'=Normal.glyph (A-A') from (map_sub ..).symm]
    exact (coin_pay _).trans ((high_rowsSky B h y).2.trans hp.movement)
  let H:= B.world.H N (i+1); let H':= B.world.H N i
  have hs : H.metric.strip (min (B.prices.α J) (B.prices.α j)) (max (B.prices.Ω J) (B.prices.Ω j)) := strip_mono (B.pays.rows N (i+1) h).2.1 (min_le_left ..) (le_max_left ..)
  have hc (n : Side) : Floor H (tell B i).top.clip n (B.prices.η J) (max (B.prices.Ω J) (B.prices.Ω j)) := by
    -- explicit transports of prices only
    exact floorSky (B.pays.all N (i+1) h n) (le_max_left ..)
  obtain ⟨Z,t,A,hT,ht,hA,hZ⟩:=hp.turns H hs hc
  unfold short Qrow; dsimp only
  split
  · rw [sub_self,norm_zero]; exact hx
  next hh' =>
    let Y:=takePaths (Current.dial P G) (Current.dial P G) (clim C.path.levels i)
    have hU : Figure G P (tell B i).bind t A H Z := hT
    have hv : laid G P S rfl (Y.draw Z) (toPAC y) (toPAC u)=0 := enough_room Y (C.side i p) (publish G P S rfl (toPAC y))
      (publish G P S rfl (toPAC u)) (lt_of_not_ge hh')
    have hB : 3 ≤ (C.side i p).val:= le_trans (show 3≤100*(C.path.levels.clock.coverSize i+1) by omega) (C.path.levels.fits.sizeT i p)
    rw [zero_sub,norm_neg,planner_Q B N i p h,Complex.norm_real]
    have hz := (hU.joints ht _ (path_flip _ (clim C.path.levels i)) S rfl).2 (toPAC y) (toPAC u)
    change |laid G P S rfl Z (toPAC y) (toPAC u) - laid G P S rfl (Y.draw Z) (toPAC y) (toPAC u)|≤_ at hz
    rw [hv,sub_zero,hU.transfer S rfl H' (C.path.levels.params i).clip (B.world.towers N i) rfl (B.prices.eta_pos _)
      (B.pays.all N i h.le (C.side i p)) (B.pays.crossings N i p h) (B.sized i p) hB] at hz
    exact hz.trans hZ
end proceeds

section earning
-- Storefront can be *asked for* with kernel + prepaid data, at post-L.
-- Keep the Tender and these requests in the parallel Wait purchase.
-- Include opportunity to use them at any p.
open Station Peak Finset
structure StorefrontSky (j l : ℕ) (K : KernelChoices) (M : ℕ → Stage) (B : MapPrices) (L : Side)
    (U : Purse) (s : ℝ) (G : Gauge) : Prop where
  vote : capitalSky K B j l ≤ U.L
  optics : (RankCovariance.prepared K).centers j ≤ LiftMark.tin s U.taylor
  earn (x : ℝ) (P : Patch) (h : P.J=j) (p : P.L=L) (hP : P.Branches K G) :
    x ∈ Set.Icc (s/2) s → 0 ≤ B.Ω j → Paying P (initials (G:=G) B M K j l) (min (B.α j) (B.α l)) (B.η j) (max (B.Ω j) (B.Ω l)) (U.sends s) x

variable {C : Family G} (B : Binding C) {N p k : ℕ} (ξ : Purse)
local notation "A" => C.path.levels
local notation "L" => ξ.band

lemma ordersSky (U : ∀ i,middleSky A ξ.band k ≤ i → i < k → StorefrontSky (C.path.levels.clock.J (i+1)) (C.path.levels.clock.J i) C.path.levels.clock.kernel C.path.levels.clock.stage B.prices (C.path.levels.clock.factor (C.path.levels.clock.J (i+1))) ξ (clim A k) G) (hf : optics A k ξ.taylor)
    (H : CorridorSky A ξ.band ξ k) (h' : roomTestSky A ξ.band k p ξ.horizon ξ.era.coast.Q)
    (c : Course C N p k) (V : (j : ℕ)→Rep G (C.side j p)) (h : ∀ i, Station.widthSky A ξ.band k ≤ i → ∀ a : i ≤ k, Perch.Candle c i (V i) (a.trans c.allow)) :
    MarketGrantSky c V (stamp A N p) (short B N p) ξ := by
  let R := short B N p
  have hh i (hl:middleSky A L k ≤ i) (ht:i<k):= exact_voice B i p (lt_of_lt_of_le ht c.allow)
  refine ⟨h,⟨h',fun i hl ht=>?_,hh⟩,⟨fun i hl ht=>?_,hh,fun i hl ht m i'=> ?_⟩,control_same A N k p _, producesInk ξ.taylor hf⟩
  · have hx:= lt_of_lt_of_le ht c.allow
    have hz := sufficient_rowsSky B hx
    exact support_rows B (lt_min (B.prices.alpha_pos _) (B.prices.alpha_pos _)) hz
  · let S:= C.path.levels.clock.op i p
    have he:=U i hl ht
    have ht' := lt_of_lt_of_le ht c.allow
    have hw:S.patch.L=C.path.levels.clock.factor (C.path.levels.clock.J (i+1)):= (C.path.levels.fits.sameFactor _).symm
    apply telescopeSky B N i p ht' _ (Real.exp_pos _).le he.vote
    exact he.earn _ S.patch rfl hw (C.path.levels.blocks ..).branches (H.court _ ((Station.widerSky ..).trans hl) ht.le) (minimum_price B N _ ht')
  rw [linear_write]
  simp only [H_at,← Complex.ofReal_mul, ← Complex.ofReal_sum,Complex.ofReal_re]

variable (M : C.Makes)
include M
open Paint
-- Expose survivors + paths. Offer a joint Retained choice; does NOT
-- provide the still-needed density expansion supported along these choices.
lemma earn_epochSky {w d} (g : LaunchSky C k ξ w d) (hN : k ≤ N)
    (h' : ∀ i,middleSky A ξ.band k ≤ i → i < k → StorefrontSky (C.path.levels.clock.J (i+1)) (C.path.levels.clock.J i) C.path.levels.clock.kernel C.path.levels.clock.stage B.prices (C.path.levels.clock.factor (C.path.levels.clock.J (i+1))) ξ (clim A k) G) (hf : optics A k ξ.taylor)
    (hs : ∀ j ≤ k, Station.widthSky A L k ≤ j → TableReady C j w (load ξ.era) ξ.era.coast.a)
    (hX : roomTestSky A L k p ξ.horizon ξ.era.coast.Q) :
    let c := keeping M p N k hN
    ∃ Y : (i : ℕ) → Rep G (C.side i p), survivors C N k p g.pane (Y k) ∧
      MarketGrantSky c Y (stamp A N p) (short B N p) ξ ∧ ∀ i (_ : Station.widthSky A L k ≤ i) (_ : i ≤ k),
        (Y i).path=(C.path.rep N p i).path ∧ (Y i).clip=(C.path.rep N p i).clip := by
  intro c
  letI (i : ℕ) : Nonempty (Rep G (C.side i p)) := ⟨C.path.rep N p i⟩
  -- choose ONE rewritten vacuum at each i
  choose! Y hY using fun (i) ht hh => parser C (ht.trans hN) M (hs i ht hh) p
  have ht := (Station.widerSky A L k).trans (Station.beforeSky ..)
  refine ⟨Y,hY k le_rfl ht,ordersSky B ξ h' hf g.coup hX c Y (fun i hv hx=> ?_),fun i hv he => ?_⟩
  · let c' := keeping M p N i (hx.trans hN)
    obtain hh := lights C (hx.trans hN) c' M _ (Y i) (hY i hx hv)
    exact ⟨⟨⟨hh.settle.tied.density,hh.settle.tied.coupling⟩, hh.settle.proper⟩,hh.budget,hh.threshold⟩
  obtain ⟨_,_,T,P,H,-⟩:= hY i he hv
  exact ⟨H.precise.1,H.precise.2.1⟩
end earning
end YM.PhysicalNext.InteractingRank
