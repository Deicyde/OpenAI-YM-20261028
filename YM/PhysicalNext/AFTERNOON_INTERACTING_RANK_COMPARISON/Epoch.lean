import YM.Extra.ITERATION_NO_LOSS.Mechanism
import YM.Next.RANK.Happen
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Ribbon


/-!
# MarketGrant

At one plateau stage J, path and entry bounds of Fair paid *pre*-L (`capital`);
approximation estimates paid POST-L. For all periods (the consumer will
establish roomTest etc., not by measuring rows at a different volume).
`earn_epoch` already supplies MarketGrant with a choice of Candle data
from regrouping only -- NOT a claim that the physical hypotheses later
needed on these same calls were purchased. We will also use `orders` with
(possibly) different candles *on the same path data and family*, but where
we've discharged the actual step comparison, e.g. with a restarted
E-style Course (β may change below k).
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

/-- Pre-cost, independent of L. -/
def initials (Z : MapPrices) (U : ℕ → Stage) (K : KernelChoices) (j i : ℕ) : Teller G :=
  ⟨K,U j, U i, j, Z.α j, Z.Ω j,Z.alpha_pos j⟩
variable {C : Family G} (B : Binding C) (N i p : ℕ)
local notation "x" => clim C.path.levels i
local notation "j" => C.path.levels.clock.J i

def tell := initials (G:=G) B.prices C.path.levels.clock.stage C.path.levels.clock.kernel (C.path.levels.clock.J (i+1)) j

/-- Tying all Paths to Binding. -/
def tunnel : Tube G (C.path.levels.clock.op i p) := ⟨B.world.towers N i,(C.path.rep N p (i+1)).path,
    (C.path.levels.params (i+1)).clip,(C.path.rep N p i).path,(C.path.levels.params i).clip⟩

theorem ships (M : C.Makes) (h : i<N) : (tell B i).Funds (C.path.levels.clock.op i p) (tunnel B N i p) := by
  let A:=C.path.levels
  have hh k (he : k≤N) : (C.path.rep N p k).path.Bounds (A.params k).clip (A.params k).width (A.params k).paths (A.clock.loopCap k) := by
    obtain hv:= M.wilson.represents N p k he
    rw [show (A.params k).clip=_ from hv.clip.symm]; exact hv.good.paths
  exact ⟨rfl,rfl,(A.blocks i p).branches,B.pays.costs N i h,rfl,rfl, ⟨_,_,hh (i+1) h,hh i h.le⟩,
    ⟨_,_,B.paths N (i+1) h p,B.paths N i h.le p,B.pays.stack N i p h⟩⟩

theorem knot (M : C.Makes) (h : i<N) :
    Lift.Booth (tell B i) (C.path.levels.clock.op i p) (tunnel B N i p) := by
  exact ⟨ships B N i p M h,B.world.H N (i+1),B.world.H N i,_,_,_,_,B.pays.all N _ h _,B.pays.all N _ h.le _,B.paths N _ h _,B.paths N _ h.le _,B.sworn _ _ h _,B.sworn _ _ h.le _,B.pays.crossings N i p h,B.pays.stack N i p h⟩

lemma minimum_price (H : i ≤ N) : 0 ≤ B.prices.Ω j := by
  let k := plaquette ⟨(0,1),by decide⟩
  have he := (B.pays.rows N i H).1 k k
  exact (tsum_nonneg he.1).trans he.2.2
end calls

-- uniform width scheduling
lemma long_pay (c : ℝ) (v : ℝ) (hv : 0<v) : ∀ᶠ s : ℝ in atTop,∀ t∈ Set.Icc (s/2) s,
    t^(-v) ≤ Perch.bill (-c) s := by
  -- $t ≥ s/2$; pay half exponent
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (2*Real.log 2), eventually_gt_atTop (1:ℝ), Paint.monitors c (v/2) (half_pos hv)] with s hs h he
  intro t ht; obtain ⟨ht,hx⟩:= ht
  have hz : 0<s:=zero_lt_one.trans h; have hp : 0<s/2:=half_pos hz
  apply (Real.rpow_le_rpow_of_nonpos hp ht (by linarith only [hv])).trans
  rw [Real.rpow_def_of_pos hp]; unfold Perch.bill; apply Real.exp_monotone
  rw [Real.log_div hz.ne' (by norm_num : (2:ℝ) ≠ 0)]; linarith only [he,mul_le_mul_of_nonneg_left hs hv.le]

-- post-L, after fixing K,T etc. Don't depend on sizes n
structure Paying (P : Patch) (Pt : Teller G) (s a M' : ℝ) (ε : ℝ) (x : ℝ) : Prop where
  movement : cheque (TypeFace 2) s (psiBudget M' / (P.L.val:ℝ)^2) x ≤ ε
  turns (H : Bed) : H.metric.strip s M' → (∀ n, Floor H Pt.top.clip n a M') →
    ∃ (Z : veilCut G P) (t A : ℝ), Figure G P Pt.bind t A H Z ∧ 0<t ∧ 0<A ∧ cheque (Current.dial P G) t A x ≤ ε

lemma confers (P : Patch) (Pt : Teller G) (h : P.Branches Pt.bind G)
    (s a M' : ℝ) (hs : 0<s) (ha : 0<a) (hM : 0≤M') (d : Purse) : ∀ᶠ t : ℝ in atTop,
    ∀ x∈ Set.Icc (t/2) t, Paying P Pt s a M' (d.sends t) x := by
  obtain ⟨u,A,hu,hA,H⟩:= summon G P Pt h s M' a ha hs hM
  let M:= psiBudget M' / (P.L.val:ℝ)^2
  have hm : 0≤ M:=div_nonneg (psiBudget_nn _ hM) (sq_nonneg _)
  have h1 := currency (TypeFace 2) s M 1 hs hm
  obtain ⟨B,hB⟩:= eventually_atTop.mp (h1.and (currency (Current.dial P G) u A 1 hu hA.le))
  filter_upwards [Perch.half.eventually_ge_atTop B,long_pay d.foil 1 zero_lt_one] with y hx hf
  intro t ht; obtain ⟨hβ,hγ⟩:= hB t (hx.trans ht.1); have hv:t^(-(1:ℝ))≤d.sends y:=hf t ht
  refine ⟨hβ.trans hv,fun Q hL hq=>?_⟩; obtain ⟨Z,hZ⟩:=H Q hL hq
  exact ⟨Z,u,A,hZ,hu,hA,hγ.trans hv⟩

section proceeds
variable {C : Family G} (B : Binding C) (N i p : ℕ)
local notation "x" => clim C.path.levels i
local notation "j" => C.path.levels.clock.J i
local notation "X" => stamp C.path.levels N p
variable (hh : C.path.levels.clock.J (i+1)= C.path.levels.clock.J i)
include hh
variable (h : i<N)
include h
lemma telescope {ε d} (hp : Paying (C.path.levels.clock.op i p).patch (tell B i)
    (B.prices.α j) (B.prices.η j) (B.prices.Ω j) ε x)
    (hx : 0≤ε) (hd : capital C.path.levels.clock.kernel B.prices (C.path.levels.clock.J i) ≤ d) :
    Awake (short B N p i) (track X i) d ε := by
  have he:= paths_budget B (p:=p) h hh d hd
  let S:= C.path.levels.clock.op i p; let P:=S.patch
  refine ⟨he.1,he.2,hx,fun y=> ?_,fun y u=>?_⟩
  · let A:= (short B N p i).H y; let A':=(track X i).H y
    rw [show Normal.glyph A-Normal.glyph A'=Normal.glyph (A-A') from (map_sub ..).symm]
    exact (coin_pay _).trans ((high_rows B h hh y).2.trans hp.movement)
  let H:= B.world.H N (i+1); let H':= B.world.H N i
  have hs : H.metric.strip (B.prices.α j) (B.prices.Ω j) := hh ▸ (B.pays.rows N (i+1) h).2.1
  have hc (n : Side) : Floor H (tell B i).top.clip n (B.prices.η j) (B.prices.Ω j) := by
    -- explicit transports of prices only
    rw [← hh]; exact B.pays.all N (i+1) h n
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
structure Storefront (j : ℕ) (K : KernelChoices) (M : ℕ → Stage) (B : MapPrices) (L : Side)
    (U : Purse) (s : ℝ) (G : Gauge) : Prop where
  vote : capital K B j ≤ U.L
  optics : (RankCovariance.prepared K).centers j ≤ LiftMark.tin s U.taylor
  earn (x : ℝ) (P : Patch) (h : P.J=j) (p : P.L=L) (hP : P.Branches K G) :
    x ∈ Set.Icc (s/2) s → 0 ≤ B.Ω j → Paying P (initials (G:=G) B M K j j) (B.α j) (B.η j) (B.Ω j) (U.sends s) x

lemma forecasts (j : ℕ) (K : KernelChoices) (M : ℕ → Stage) (B : MapPrices) (L : Side) (U : Purse) (G : Gauge)
    (hU : capital K B j ≤ U.L) : ∀ᶠ s in atTop, Storefront j K M B L U s G := by
  let E := (RankCovariance.prepared K).centers j
  have he:= (bill_lo (LiftMark.shade_pos U.taylor)).eventually_ge_atTop E
  by_cases ht : (∃ P : Patch, P.J=j ∧ P.L=L ∧ P.Branches K G) ∧ 0≤ B.Ω j
  swap
  · filter_upwards [he] with s hs; exact ⟨hU,hs,fun x P h v t _ hx=> (ht ⟨⟨P,h,v,t⟩,hx⟩).elim⟩
  obtain ⟨⟨P,h,v,t⟩,hp⟩:=ht
  filter_upwards [he,confers P (initials B M K j j) (G:=G) t (B.α j) (B.η j) (B.Ω j) (B.alpha_pos j) (B.eta_pos j) hp U] with s hs hy
  refine ⟨hU,hs,fun x V he hv h hx h' =>?_⟩; rw [show V=P from ?_]; exact hy x hx
  cases P; cases V; congr <;> simp_all

variable {C : Family G} (B : Binding C) {N p k : ℕ} (ξ : Purse)
local notation "A" => C.path.levels
local notation "L" => ξ.band

lemma orders (U : Storefront (C.path.levels.clock.J k) C.path.levels.clock.kernel C.path.levels.clock.stage B.prices (C.path.levels.clock.factor (C.path.levels.clock.J k)) ξ (clim A k) G)
    (H : Corridor A ξ.band ξ k) (h' : roomTest A ξ.band k p ξ.horizon ξ.era.coast.Q)
    (c : Course C N p k) (V : (j : ℕ)→Rep G (C.side j p)) (h : ∀ i, Station.width A ξ.band k ≤ i → ∀ a : i ≤ k, Perch.Candle c i (V i) (a.trans c.allow)) :
    MarketGrant c V (stamp A N p) (short B N p) ξ := by
  let R := short B N p
  have he i (hl:middle A L k ≤ i) (hg:i≤k) : C.path.levels.clock.J i=C.path.levels.clock.J k:= H.heft.plateau i ((Station.wider ..).trans hl) hg
  have hh i (hl:middle A L k ≤ i) (ht:i<k):= exact_voice B i p (lt_of_lt_of_le ht c.allow)
  refine ⟨h,⟨h',fun i hl ht=>?_,hh⟩,⟨fun i hl ht=>?_,hh,fun i hl ht m i'=> ?_⟩,control_same A N k p _, producesInk ξ.taylor U.optics⟩
  · have hx:= lt_of_lt_of_le ht c.allow
    have hz := sufficient_rows B hx ((he (i+1) (hl.trans (Nat.le_succ _)) ht).trans (he i hl ht.le).symm)
    exact support_rows B (B.prices.alpha_pos _) hz
  · let S:= C.path.levels.clock.op i p; let J:= C.path.levels.clock.J i
    have hx := he i hl ht.le; have hy := he (i+1) (hl.trans (Nat.le_succ _)) ht
    have ht' := lt_of_lt_of_le ht c.allow
    have hw:S.patch.L=C.path.levels.clock.factor (C.path.levels.clock.J k):= by rw [←hy]; exact (C.path.levels.fits.sameFactor _).symm
    apply telescope B N i p (hy.trans hx.symm) ht' _ (Real.exp_pos _).le (hx.symm ▸ U.vote)
    unfold tell; rw [hx,hy]
    exact U.earn _ S.patch hy hw (C.path.levels.blocks ..).branches (H.court _ ((Station.wider ..).trans hl) ht.le) (hx ▸ minimum_price B N i ht'.le)
  rw [linear_write]
  simp only [H_at,← Complex.ofReal_mul, ← Complex.ofReal_sum,Complex.ofReal_re]

variable (M : C.Makes)
include M
open Paint
-- Expose survivors + paths. Offer a joint Retained choice; does NOT
-- provide the still-needed density expansion supported along these choices.
lemma earn_epoch {w d} (g : Launch C k ξ w d) (hN : k ≤ N)
    (h' : Storefront (C.path.levels.clock.J k) C.path.levels.clock.kernel C.path.levels.clock.stage B.prices (C.path.levels.clock.factor (C.path.levels.clock.J k)) ξ (clim A k) G)
    (hs : ∀ j ≤ k, Station.width A L k ≤ j → TableReady C j w (load ξ.era) ξ.era.coast.a)
    (hX : roomTest A L k p ξ.horizon ξ.era.coast.Q) :
    let c := keeping M p N k hN
    ∃ Y : (i : ℕ) → Rep G (C.side i p), survivors C N k p g.pane (Y k) ∧
      MarketGrant c Y (stamp A N p) (short B N p) ξ ∧ ∀ i (_ : Station.width A L k ≤ i) (_ : i ≤ k),
        (Y i).path=(C.path.rep N p i).path ∧ (Y i).clip=(C.path.rep N p i).clip := by
  intro c
  letI (i : ℕ) : Nonempty (Rep G (C.side i p)) := ⟨C.path.rep N p i⟩
  -- choose ONE rewritten vacuum at each i
  choose! Y hY using fun (i) ht hh => parser C (ht.trans hN) M (hs i ht hh) p
  have ht := (Station.wider A L k).trans (Station.before ..)
  refine ⟨Y,hY k le_rfl ht,orders B ξ h' g.coup hX c Y (fun i hv hx=> ?_),fun i hv he => ?_⟩
  · let c' := keeping M p N i (hx.trans hN)
    obtain hh := lights C (hx.trans hN) c' M _ (Y i) (hY i hx hv)
    exact ⟨⟨⟨hh.settle.tied.density,hh.settle.tied.coupling⟩, hh.settle.proper⟩,hh.budget,hh.threshold⟩
  obtain ⟨_,_,T,P,H,-⟩:= hY i he hv
  exact ⟨H.precise.1,H.precise.2.1⟩
end earning
end YM.PhysicalNext.InteractingRank
