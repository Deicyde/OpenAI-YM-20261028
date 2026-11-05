import YM.RemainderComparison.Sagas.Home
/-! Currency at helpers. Log.Auth weights absorb R.P.En lengths. Ghost marker germs.Code. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Sagas
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler ThroughLaunch Bid Planned.JetPort
open YM.RemainderComparison.Aux Portal Herbal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{c f:Side}{L:Side}{α:Type*}{ι J:Type}
variable {p:BudgetPoint} (β:ℝ) {R:RG.Rep G f}
namespace Packet
variable {αP dθ t b η x B A:ℝ}{n k r m j:ℕ}
open Time WickReps
variable (P:ι→ Packet G f α)(Q:Packet G f α)
-- Material implementation.Me.Mask-only authentic TERM.Arr.Foot.Angle covariates. At PHY label exact sewing.M.A.Element gauge weigh.L budget rooted.Anal.Anal.Per
variable [Fintype J] {S:StepData c f}
open Lyric Typeface Marker Merge
variable (a:α)
lemma ready (hp:0 <R.beta)(he:(R.activities.reg j)= Q.postage)(h:R.activities.E j=0):∃ w:Portrait R α, w.wing= Lotus.Wing.logKey j ∧ w.weight=Q.eats R.beta R.p∧∀ a, (w.angle a).ingredient= RG.masked R.p.threshold Q.postage.support (Q.send R.beta a):=by
   have hq (a:α):∃ L:Lotus.Leaf R, L.turn=Lotus.Wing.logKey j∧ L.ingredient=RG.masked R.p.threshold Q.postage.support (Q.send R.beta a)∧ L.weight=Q.eats R.beta R.p:=by
      let P:= Q.send R.beta a; let X:= (R.activities.reg j).support; let t:=R.p.threshold; let T:= RG.masked t X P; let k:= Q.eats R.beta R.p
      obtain ⟨hx,hf⟩:= solo R.beta Q R.p a hp; have he : X=Q.postage.support:=congr_arg RG.RegularAddress.support he
      refine ⟨⟨Lotus.Wing.logKey j,T,?_,?_,h,k,?_,?_,masked_measurable _ _ _ (hx.borel)⟩,rfl,?_ ,rfl⟩
      · intro U V hh hv; have he' : Healthy t X U ↔ Healthy t X V:=by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,Finset.disjoint_iff_inter_eq_empty]; rw [show X∩flags t U=X∩flags t V from hv]
        unfold T; by_cases hi : Healthy t X U; · rw [masked_eq _ _ _ _ hi,masked_eq _ _ _ _ (he'.1 hi)]; exact hx.sites _ _ (he ▸ show _ from hh)
        rw [masked_ne _ _ _ _ hi,masked_ne _ _ _ _ (mt he'.2 hi)]
      · intro i h; exact Classical.byContradiction fun he => h (RG.masked_ne _ _ _ _ (show ¬ Healthy t X i from he)) -- args
      · intro i; unfold T; by_cases hi : Healthy t X i; · rw [masked_eq _ _ _ _ hi]; exact hf.2 _ (he ▸ hi) [] (by simp) (by simp)
        rw [masked_ne _ _ _ _ hi,norm_zero]; exact hf.1
      · intro v U; unfold T; by_cases hi: Healthy t X U; · rw [masked_eq _ _ _ _ (show Healthy t X (gauge v U) by simpa [Healthy] using hi), masked_eq _ _ _ _ hi]; exact hx.symmetry ..
        rw [masked_ne _ _ _ _ (show ¬ Healthy t X (gauge v U) by simpa [Healthy] using hi), masked_ne _ _ _ _ hi]
      change T = masked _ _ _; unfold T; rw [he]
   choose Z hA hf hK using hq; exact ⟨⟨Lotus.Wing.logKey j,Q.eats R.beta R.p,Z,hA,hK⟩,rfl,rfl,hf⟩

variable (M :ι→ Portrait R α) (l:ι→ℝ) (K:J→Site f)(Y:ι→Finset J)
-- Active source gloss. Already.Y.Forced gifts estimated at INPUT ROOT with weights p.Y.Sc pans, separately supplied.Base estimates retained and mask partners.
variable (V:Set ι)(D : Stage)
structure Parade (X:StepData c f) (b αP dθ η B A:ℝ) (x:ℝ)(r k n m:ℕ) : Prop where -- b X allowance
    priced i : 0≤ l i
    cash : 0≤ B∧0≤A
    roots i : (Y i).Nonempty ∧ ∀ a∈ Y i,K a ∈ ((M i).wing.support R)
    size : Extra.Multi.Occupancy (X.ratio.parent ∘ K) m
    paint i : i∈ V→∃ j, (M i).wing= Lotus.Wing.logKey j ∧ (P i).postage=(R.activities.reg j)
    ticket i : i∈ V→ (M i).weight ≤ (P i).eats R.beta R.p  -- computed via Ready, or other proof. no assumption adjoint perturbative estimate
    fares i : i∈V→ (P i).rank≤ k ∧ n ≤ (P i).grade
    shell i : i∈V →(coverNumber R.p.B (P i).postage.support:ℝ) ≤ αP+dθ*(P i).length
    vision i : i∈V →(P i).length< Pressure.Stores.till x→(P i).postage.support⊆ neighbors r ((P i).postage.site)
    anchors t : SumBudget (fun i=> if i∈V∧t∈Y i then l i*((P i).weight*Real.exp (η*(P i).length)) else 0) B
    forced i : i∉V → ∃ j,(M i).wing= Lotus.Wing.gasKey j
    cold t : SumBudget (fun i=> if i∉V ∧t∈Y i then l i*(M i).weight * Real.exp (b*coverNumber R.p.B ((M i).wing.support R)) else 0) A
variable (h:0< R.beta)(ht:Parade P M l K Y V S b αP dθ η B A x r k n m)(he:gStep R.beta≤1)(hq:Time.Same D R.p)
variable {ξ:ℝ}(hz:0<ξ)(hδ: t+b*dθ+ξ≤η)(hB:0≤b)
local notation "Z₁"=> Packet.music G D ξ b αP n k R.beta R.p.threshold
include ht h hz he hq hδ hB
lemma ships : let f' (i:ι):= if i∈ V then (P i).length else 0
              Nursery.Charters (x:=x) (S:=S) M a l f' r m t b (Z₁*B + A) :=by
   intro f'; let w :ι→ℝ:= Palette.wages (brand M a) l; have hℓ : 0 ≤ Z₁:= by have hg:= (Fare.gS _ h).1; unfold music; have hh:= R.p.threshold_pos; have hk:= tolls G D ξ k; positivity
   have hw(i): 0≤ w i:=mul_nonneg (ht.priced i) (Lotus.Leaf.profit (brand M a i))
   constructor
   · exact ht.priced
   · exact add_nonneg (mul_nonneg hℓ ht.cash.1) ht.cash.2
   · intro i j he; refine if_neg ?_; intro h; obtain ⟨j,h⟩:=ht.paint i h; exact False.elim (by have hh:= h.1; rw [he] at hh; contradiction) -- h shadow
   · intro i j he hv; have hi:i∈V:= Classical.byContradiction fun hi=>by obtain ⟨j,h⟩:= ht.forced i hi; rw [he] at h; contradiction
     obtain ⟨k,h,hv'⟩:= ht.paint i hi; obtain rfl:= Lotus.Wing.logKey.inj (he.symm.trans h); unfold f'; rw [if_pos hi]; apply Classical.byContradiction
     intro h; obtain ⟨a,ha,hN⟩:= hv; rw [← hv'] at ha hN; exact hN ((neighbors_mem ..).mp ((ht.vision i hi (by omega)) ha))
   refine ⟨J,inferInstance,K,Y,fun i hi=>?_,ht.size,fun o=>?_⟩
   · obtain ⟨v,hv⟩:= (ht.roots i).1; exact ⟨v,hv,(ht.roots i).2 v hv⟩
   apply budget_mono (Extra.Multi.Budget.plus (Cost.scale (ht.anchors o) Z₁ hℓ) (ht.cold o)) -- name edit
   · intro i; split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hw i) (Real.exp_pos _).le); exact le_rfl
   intro i; dsimp only; split
   next hp =>
     by_cases hP:i∈V; swap; · simp_rw [f',if_neg hP]; rw [if_pos (And.intro hP hp), if_neg (show ¬ (i∈V ∧ _) from fun h'=>hP h'.1)]; simp only [Nat.cast_zero,mul_zero,Real.exp_zero,mul_one,zero_add]; exact le_of_eq (mul_comm ..)
     obtain ⟨u,hu,hx⟩:= ht.paint i hP
     have hh:= @Packet.glow G _ α R.p R.beta (P i) ξ αP dθ t b η n k D hq h he hz (ht.fares _ hP).1 (ht.fares _ hP).2 hB (ht.shell _ hP) hδ
     rw [if_neg (show ¬ (i∉V ∧ _) from fun z=>z.1 hP),add_zero,if_pos (And.intro hP hp), show f' i=_ from if_pos (show i∈V from hP),show (Typeface.brand M a i).crest=(P i).postage.support from (by change (M i).wing.support _= _; rw [hx,hu]; rfl)]
     change _*(l i*(M i).weight*_ ) ≤ _
     apply le_trans ?_ ((mul_le_mul_of_nonneg_left hh (ht.priced i)).trans_eq (mul_left_comm ..))
     · calc _ ≤ Real.exp (b*coverNumber R.p.B (P i).postage.support) * (l i * (P i).eats R.beta R.p * Real.exp (t*(P i).length)) := by gcongr <;> first| exact ht.priced i| exact ht.ticket i hP
            _ = l i* ((P i).eats R.beta R.p*( Real.exp (t*(P i).length)*Real.exp (b* coverNumber R.p.B (P i).postage.support))) := by ring
   next hz=> exact (Extra.Multi.Budget.plus (Cost.scale (ht.anchors o) Z₁ hℓ) (ht.cold o)).1 i
end Packet
end YM.RemainderComparison.Sagas
