import YM.Extension.UV.WeightLimit
/-! Absolute row convergence (kinetic part seen by Potential) of the **actual** history.
What is uniform here is uniform for exponential rates strictly below one common fixed-level
reserve; not stated for Wilson interactions or scalar running betas. The kinetic matrix Suffices
is independent of period (though bounds are paid using all periods). -/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV.Linear
open Set Function Filter Lattice Laurent Exterior Bloch Metric Precision RG Next.Free Work.F08
open scoped Topology BigOperators
variable {G: Gauge} {A:Levels G}

def KrowSeries (R : Row (TypeFace 2) (TypeFace 2)):=composeRows (composeRows (transRows (cobound 1)) R) (cobound 1)

def Kseries (M : Horizon A) (m n : ℕ):=KrowSeries (M.H n m).metric

lemma Krow_acts (R : Row (TypeFace 2) (TypeFace 2)) (h:Whole R) (n: Side) : (KrowSeries R).acts n=Precision.K (R.acts n) := by
  have hg := Whole.boundary 1
  rw [KrowSeries,(Whole.prod hg.flipped h).acts hg n,Whole.acts hg.flipped h n,Work.F08.acts_trans,Precision.K]

-- remove lame lemma
lemma side_diverges (A:Schedule) (m:ℕ) : Tendsto (fun n=>(A.side m n).val) atTop atTop :=
  tendsto_atTop_mono (fun i => by change (A.period i).val ≤ _; rw [Schedule.side,PNat.mul_coe]; exact Nat.le_mul_of_pos_right _ (A.denominator m).property) (A.period_strict.tendsto_atTop)
lemma Kseries_stock (M:Horizon A) {P:MapPrices} (h:M.Suffices P) (m:ℕ) : ∃ σ C:ℝ,0<σ ∧ 0<C ∧ ∀ n ≥ m, (Kseries M m n).strip σ C := by
  have hM (n:{n:ℕ // m≤n}) := (h.rows n.val m n.2).2.1
  let R := fun n : {n // m≤n} => (M.H n.val m).metric
  have he : Stock (α:=fun _=>TypeFace 2) (β:=fun _=>TypeFace 2) (fun _=>1) R := by
    refine ⟨fun _=>zero_le_one,P.α (A.clock.J m), max 1 (P.Ω (A.clock.J m)),P.alpha_pos ..,zero_lt_one.trans_le (le_max_left ..),fun n a b=> (hM n a b).mono le_rfl (by simp)⟩
  have hi := Stock.constant (ι:={n//m≤n}) _ (Whole.boundary 1)
  obtain ⟨σ,C,hσ,hc,hE⟩ := ((hi.flipped.times he).times hi).uniform
  exact ⟨σ,C,hσ,hc,fun n hn=>by simpa [Kseries,KrowSeries,R] using (hE ⟨n,hn⟩) ⟩

lemma nativeK (M:Horizon A) {P:MapPrices} (hM:M.Suffices P) (h:SizeFloor A.clock.kernel.penalty A) (m:ℕ) : ∃ σ C, 0<σ ∧ 0<C ∧ ∃ V,
    (∀ a b x, ‖V a b x‖ ≤ C*weight (-σ) x) ∧ ∀ τ:ℝ, τ<σ → Weighted (Kseries M m) τ V := by
  obtain ⟨σ,C,hσ,hc,hR⟩:= Kseries_stock M hM m
  refine ⟨σ,C,hσ,hc,row_visible hσ hc.le (Eventually.mono (eventually_ge_atTop m) hR) (side_diverges A.S m) (fun l=> ?_)⟩
  obtain ⟨v,hv⟩:=K_tendsto M hM h m l
  apply Filter.Tendsto.cauchySeq (x:=v)
  apply (hv.congr' ?_)
  filter_upwards [eventually_ge_atTop m] with n hn
  unfold Kactual Kseries
  have hg := (hM.rows n m hn).2.1
  exact (Krow_acts _ ⟨_,_,P.alpha_pos _,hg⟩ _).symm
end YM.Extension.UV.Linear
