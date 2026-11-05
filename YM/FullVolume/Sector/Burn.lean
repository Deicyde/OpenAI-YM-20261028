import YM.FullVolume.Sector.Crime
/-! Atom Ω. No kernel-sector shortcuts on the broad side. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R} -- implicit v
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
namespace Tune
variable (U:Tune H v δ)
-- continuation of raw labels. Reimburse Sales optional once.
local notation "Λ" => U.pole
local notation "t'"=> U.notes
local notation "B₀" => radiusB x₀
local notation "Q'" => stella Q
local notation "A'" => topStorm S.patch
variable {p:Lyre.Signal 0} {ν:ℝ}
local notation "g"=> Q.goal L x₀
abbrev plainP (p:Lyre.Signal 0) (ν:ℝ) := sheet U p ν (topStorm S.patch)
abbrev totalP (p:Lyre.Signal 0) (ν:ℝ) := sheet U p ν (H.alarms * topStorm S.patch)
local notation "g₀"=> plainP U p ν
local notation "g₁" => totalP U p ν
abbrev snaps (X:Coat T F) (p:Head S) (z:Air f G) (l:Finset ℕ) t:= X.vertex (U.notes t) Q.table W o.a l Q.halo (U.pole.flow t • z) p
variable (X:Coat T F)
lemma scout0 {f:ℝ→ℝ} {a b:ℝ} (h:Weigh 0 (0:ℝ) v a b (fun s _ => f s)) : Scout v f a:= by
  have h:= h.probes 0 (by simp) _ (Nat.zero_le 0); simp only [FullVolume.Ray.marked, iteratedDeriv_zero, Function.comp_apply,pow_zero,mul_one] at h; exact h
lemma risingP (i:ℝ) (hi:|i|≤6*v) (M:Directions G f) (l:Finset ℕ) (p:Stores S): X.Pack (U.notes i) Q.table l W o.a p M=X.Pack R Q.table l W o.a p M*(Λ).flow i^(Tune.count X p)*Real.exp ((Λ).sqcost i*(R.beta*(X.quoteNear p M+ X.far_bills p))):=by
  rw [risingMoon o.a W (U.seats i hi),Tune.melody U i hi, Tune.plot_rel U i hi]
  simp_rw [mul_assoc]; apply congr_arg
  have hp : 0< (Λ).flow i:=zero_lt_one.trans_le ((Λ).moves i hi).1
  rw [← Real.exp_log (pow_pos hp (Tune.count X p)), ← Real.exp_add,Real.log_pow]; apply congr_arg; unfold Fold.sqcost Tune.count; push_cast; ring
variable (h : Clear Q L μ ν x₀ v p)(hc:Lyre.Clarity H 0 C δ ν) (z:Air f G) (l:Finset ℕ) (hx:X.x=x₀) (hy:X.width=o.K) (hm:X.manifest)
local notation "u'"=> X.liftA R.beta z
include U
lemma fluent (i:LogIndex c f) : ∃ φ:ℝ→ℝ, Set.EqOn φ (fun t=> Coat.farLog X (U.notes t) o.a Q.table (U.pole.flow t • z) i) sun ∧ FullVolume.Ray.ink 2 φ:=by
  by_cases he : Alabaster.oldVac c f i
  · let q:=X.farLog R o.a Q.table z i; let p(s:ℝ):= if Alabaster.flips c f i then q*(Λ).flow s^2 else q
    refine ⟨p,fun t ht=> ?_,?_⟩
    · unfold p; dsimp only; have hh:= U.lay ht; rw [← U.pitch t hh,flitter o.a (U.seats t hh) _ _ _ _ he]; unfold q; split<;> ring
    unfold p; split
    · let hh:= FullVolume.Ray.ink.straight (Λ).peak (Λ).slope; simp_rw [pow_two]; exact (hh.docket hh).scale _
    exact FullVolume.Ray.ink.termC _
  unfold oldVac at he; push Not at he; obtain ⟨i,rfl⟩:= he
  obtain ⟨g',hg,hK⟩:= U.onto (X.input u') i
  let s:=X.enforce (2*o.a) u' (X.plaza (Raw.space T 0 X.B R (.inl i))); refine ⟨_,fun t ht=> ?_,FullVolume.Ray.ink.scale (-s) hK⟩
  have hf:= U.lay ht; dsimp only; rw [hg ht, ← U.pitch t hf]
  unfold farLog s; rw [lifting (U.seats _ hf)]; simp only [Sum.elim, Coat.inhale]; rw [← location (T:=T) (U.seats t hf)]; change - _ * _ = - (U.notes t).activities.regularOccurrence _ i _ * _; ring
lemma tiny (i:ℕ) : ∃ φ:ℝ→ℝ, Set.EqOn φ (fun t=> Coat.bag X (U.notes t) o.a (X.liftA (U.notes t).beta (U.pole.flow t • z)) i) sun ∧ FullVolume.Ray.ink 2 φ:=by
  let A:= X.enforce (2*o.a) u' (X.plaza (Raw.forcedFoot S.ratio 0 X.B R i)); obtain ⟨g',hg,hK⟩:= U.quote (X.input u') i; refine ⟨_,fun t ht=> ?_,FullVolume.Ray.ink.scale A hK⟩
  have hf:= U.lay ht; dsimp only; rw [hg ht, ← U.pitch t hf,lifting (U.seats _ hf)]
  unfold A bag; rw [pointed (U.seats t hf),mul_comm]
include hx hy hm
lemma priced_real {t:ℝ} (he:|t|≤6*v)(i:Head S): |U.snaps X i z l t|≤(U.beams _ he).fair i:= (U.beams t he).voice X hx hy hm _ _ _
include h hc
lemma sprawl (i:Head S): Scout v (U.snaps X i z l) (g₀ i):=by
  have hp:X.B=B₀:=congr_arg _ hx
  rcases i with i|i|i|i
  · unfold plainP sheet Mixed.costs; dsimp only [Sum.elim]; split
    next hz =>
      let u:= u'; let a:= R.beta*(X.quoteNear i u+X.far_bills i); let y:=X.Pack R Q.table l W o.a i u; let f:= Fold.jet (Λ) (fun _:ℝ=> y) (fun _=> a) (Tune.count X i)
      have hh(s:ℝ)(h:|s|≤6*v): ∀ x:ℝ,U.snaps X (Sum.inl i) z l s=f s x:= by
        intro x; unfold Tune.snaps; change (if Packets.connected S Q.halo X.B i then _ else 0)=_; rw [if_pos (hp.symm ▸ hz)]
        rw [← U.pitch s h,lifting (U.seats s h)]; exact risingP U X s h u l i
      let v':= R.beta
      let e:=steamP S (Q.costs L μ v' x₀ C) i
      have he : Weigh 0 (0:ℝ) v (FullVolume.Ray.Fold.charge 0 * (1+δ)^(Tune.count X i) * e) 1 f := Fold.scores contDiffAt_const contDiffAt_const (by unfold e steamP Packets.income; change 0≤1*_; positivity) zero_le_one (fun j=>?_)
      swap
      · let t:=v*(Λ).seat a j; have hf: |t|≤6*v:= U.away ..
        refine (Brush.certified (k:=0) zero_le_one (f t 0)).climb ?_ le_rfl
        rw [← hh t hf]; have he: (U.beams t hf).fair (Sum.inl i) = steamP S (Q.costs L μ (U.notes t).beta x₀ C) i:= if_pos hz; apply (Tune.priced_real U X z l hx hy hm hf (.inl i)).trans (he.trans_le ?_); unfold e steamP Packets.income; change 1*Real.exp _ ≤1*Real.exp _
        apply mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (sub_le_sub_left (Lyre.momentum (U:=U) («A'»:=C) t hf) _) (Nat.cast_nonneg _))) zero_le_one
      exact ((scout0 (f:=fun t=> f t 0) he).replace (fun s hs=> (hh s (U.lay hs) 0).symm)).enlarged (hc.pays F X i hx (Packets.shares_nonzero S _ _ hz))
    next hz =>
      refine ((Scout.still U.normed (0:ℝ)).enlarged (by simp)).replace (fun s hs=> (if_neg ?h).symm); exact fun h=> hz (hp ▸ h)
  · let q:= U.tipBag i
    refine scout0 (b:=1) (FullVolume.Ray.starpath (k:=2) Lyre.trio Lyre.in_trio U.normed (a:=q) (Finset.sum_nonneg fun j _=> U.tip_b i j) ?_ (fun y=> U.tiny X z i))
    intro j; refine (Brush.certified zero_le_one (U.snaps X (.inr (.inl i)) z l (Lyre.trio j).val)).climb ((Tune.priced_real U X z l hx hy hm (U.lay (Lyre.trio j).2) (.inr (.inl i))).trans ?_) le_rfl
    exact Finset.single_le_sum (fun z _=> U.tip_b i z) (mem_univ j)
  · let q:= U.tipLog i; let A t (x:ℝ):= farLog X (U.notes t) o.a Q.table (U.pole.flow t • z) i
    refine scout0 (p.emits ℝ 0 _ q 1 A U.normed ((U.pepper _).trans h.low) ((mul_le_mul_of_nonneg_left (U.pepper _) (mul_nonneg (zero_le_one.trans p.plus) (sq_nonneg _))).trans h.promise) (fun j=> ?_) (fun x=> fluent U X z i))
    exact (Brush.certified zero_le_one (U.snaps X (.inr (.inr (.inl i))) z l (Lyre.trio j).val)).climb ((Tune.priced_real U X z l hx hy hm (U.lay (Lyre.trio j).2) (.inr (.inr (.inl i)))).trans (Finset.single_le_sum (fun z _=> U.tip_l i z) (mem_univ j))) le_rfl
  let x:= X.detect u' W o.a R l i
  refine ((Scout.still U.normed x).enlarged (X.fires_at ..)).replace (fun i' h=>?_)
  unfold Tune.snaps; rw [← U.pitch i' (U.lay h)]; exact alarmLace _ _ (U.seats _ (U.lay h)) ..
end Tune
end YM.ConnectedActivityE6.Empire
