import YM.RG08.Taste.Bureau
/-!
# Spin for marked K marks through rank, and projection in a frame. Real coefficients, signed space-time directions including translations of base packets.
Do NOT impose turn on non-tree slice data. For those want inversion only; shown separately.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Spin
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Pivot Carrier
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ}{F:Labels.Frame G d}{H:Hol G} {c : Side}
section lift
variable (s: Signed)
lemma wingSize (a: Cover): size (s.act a)=size a := by
    unfold size; rw [← Equiv.sum_comp s.perm (fun i=> ((s.act a i):ℤ).natAbs)]; simp_rw [s.act_at]; exact Finset.sum_congr rfl fun i _=> by split <;> simp
lemma wingDot (a: Edge Cover): size (Film.up s a).1 ≤ size a.1+1:= by
    rw [Film.up]; dsimp only; rw [going_spec]; apply (size_add ..).trans; rw [wingSize]; refine Nat.add_le_add_left ?_ _; unfold Carrier.delay; split <;> simp [size,apply_ite Int.natAbs]
-- plenty release under Signed orientations. Need wrap_slide via Site on all even.
def loc_sig (z: Fare G):Fare G:= let j:=Film.up s (Vale.heap z); (j.1,coord j.2,z.2.2)
lemma bill_sig (z:Fare G): ‖bias s (Vale.heap z).2‖=1:= by unfold bias; split <;> simp -- Vale.heap collision
lemma heap_loc (z:Fare G) : Vale.heap (loc_sig s z)=Film.up s (Vale.heap z):= by unfold loc_sig Vale.heap; refine Prod.ext rfl ?_; exact axisEquiv.symm_apply_apply _
lemma slip_loc (z:Fare G)(c:Side)(A:Link G c): orderTurn s A (wrap c z.1,z.2) =bias s (Vale.heap z).2 * A (wrap c (loc_sig s z).1,(loc_sig s z).2) := by
    obtain ⟨x,i,k⟩:=z; obtain ⟨i,rfl⟩:=axisEquiv.surjective i
    rw [show orderTurn s A=flipCoords (G:=G) (m:=c) s ℝ A from rfl]; change flipCoords s ℝ _ (_, coord i,_) = bias s (Vale.heap ((x,coord i,k):Fare G)).2 * _
    rw [flip_price,show Vale.heap ((x,coord i,k):Fare G)=(x,i) from Prod.ext rfl (axisEquiv.symm_apply_apply i)]
    change _ = bias s i * A (wrap c (Film.up s (Vale.heap ((x,coord i,k):Fare G))).1,coord (Film.up s (Vale.heap ((x,coord i,k):Fare G))).2,k)
    rw [show Vale.heap ((x,coord i,k):Fare G)=(x,i) from Prod.ext rfl (axisEquiv.symm_apply_apply i)]
    unfold Film.up; dsimp only; rw [going_spec]; unfold bias Carrier.delay; split <;> simp [*,wrap_signed,sub_eq_add_neg]
private abbrev F' (z:Fare G)(d:ℕ) := screenR G d z ∘ Film.turnIn G d s
lemma shade_loc (H:Hol G)(z:Fare G)(d:ℕ) : F' s z d =ᶠ[𝓝 0] (bias s (Vale.heap z).2) • screenR G d (loc_sig s z) := by
    unfold F' screenR; rw [heap_loc]; filter_upwards [Film.shade H s (d:=d) (Vale.heap z)] with i hi; exact (congr_arg (scent z.2.2) hi).trans (map_smul ..)
private abbrev FlyS (i d:ℕ)(G:Gauge):= (orderTurn s) ∘ (studio G d (boards i))
set_option maxHeartbeats 450000 in
lemma plentiful (H:Hol G): Plenty (fun z=> F' s z d) boards (fun i=> FlyS s i d G) := by
    intro k x
    let P i:= studio G d (boards i); let K(z: Fare G):= bias s (Vale.heap z).2; let Y(z:Fare G):=loc_sig s z
    let R i:= iteratedFDeriv ℝ k (FlyS s i d G) 0 x
    let S i:= iteratedFDeriv ℝ k (P i) 0 x
    obtain ⟨hr,n,C,hC,H'⟩:= rotor G d k x
    have hh i: R i=orderTurn s (S i):= DFunLike.congr_fun ((orderTurn s).iteratedFDeriv_comp_left (begins_sm G d _) le_top) x
    refine ⟨fun z=>?_, n,C*2^n,mul_nonneg hC (by positivity),fun z i=>?_⟩
    · have hx:= (hr (loc_sig s z)).const_mul (bias s (Vale.heap z).2)
      have hv: ContDiffAt ℝ k (screenR G d (Y z)) 0:= by unfold screenR; apply ContDiffAt.of_le _ (show (k:WithTop ℕ∞) ≤ ω from le_top); exact ((scent _).contDiff.contDiffAt.comp _ (Film.lane_smooth ..))
      have hM: iteratedFDeriv ℝ k (F' s z d) 0 x=bias s (Vale.heap z).2 * iteratedFDeriv ℝ k (screenR G d (loc_sig s z)) 0 x := by
         exact (DFunLike.congr_fun (((shade_loc s H z d).iteratedFDeriv ℝ k).eq_of_nhds) x).trans (DFunLike.congr_fun (iteratedFDeriv_const_smul_apply (a:=bias s (Vale.heap z).2) hv) x)
      rw [hM]
      refine hx.congr' (Eventually.of_forall fun i=>?_)
      exact Eq.symm ((congr_fun (hh i) (wrap (boards i) z.1,z.2)).trans (slip_loc ..))
    change ‖R i (wrap _ z.1,z.2)‖≤_; rw [hh,slip_loc,norm_mul,bill_sig,one_mul]; apply (H' _ _).trans; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hC
    unfold dime Carrier.liftCost; rw [←mul_pow]; apply pow_le_pow_left₀ (by positivity) _ n; have hz : size (loc_sig s z).1 ≤ size z.1+1:=wingDot s _; have hw : 0≤ (size z.1:ℝ) := (by positivity); have hg : (↑(size (loc_sig s z).1):ℝ) ≤ size z.1+1:= (by exact_mod_cast hz); linarith
set_option maxHeartbeats 450000 in
lemma vault_sig (x:Fin j→Snap G d) (V: Shale (Loc G 1) r): vault V (fun z=> F' s z d) x=vault V (screenR G d) ((Film.turnIn G d s) ∘ x) := by
    refine sum_congr rfl fun i _=>?_ ; unfold Vale.penny; apply congr_arg ((i.length.factorial:ℝ)*·); apply congr_arg (wallet (grant i.length V)); funext j z
    have hg(k:ℕ): ContDiffAt ℝ k (screenR G d z) 0:= by unfold screenR; apply ContDiffAt.of_le _ (show (k:WithTop ℕ∞) ≤ ω from le_top); exact ((scent _).contDiff.contDiffAt.comp _ (Film.lane_smooth ..))
    exact DFunLike.congr_fun (Next.Foundations.jets_linear (Film.turnIn G d s) (hg (i.partSize j))) (x ∘ i.emb j)
lemma penny_sig (H:Hol G)(x: Fin j→Snap G d)(V W : Shale (Loc G 1) r)(he: Tidy V)(hp:Tidy W)(hv:Polished V)(hh:Polished W)(hP:∀ m:Side, rootSong V m 0= rootSong W m 0 ∘ orderTurn s):
   amount V d j x=amount W d j ((Film.turnIn G d s)∘x):= by
    rw [penny_amt hp hh, ← vault_sig]; refine tendsto_nhds_unique_of_eventuallyEq (movie he hv _) (plenish board_end hp hh (plentiful s H) (fun i=> (orderTurn s).contDiff.contDiffAt.comp _ (begins_sm ..)) (fun i=>by simp [FlyS,begins]) _) ?_; apply Eventually.of_forall; intro i; simp_rw [hP]; rfl
end lift
end YM.RG08.Spin
