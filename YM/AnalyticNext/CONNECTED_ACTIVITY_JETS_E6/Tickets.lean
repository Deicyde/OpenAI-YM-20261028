import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.SalesRoot
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.UnifiedValue

/-!
# Counting FULL alphabets, summable and integral exchange

Per Macroscope with K and structural packets given. No periodic F tags
summed here except at later application. Includes infinite label spaces!
Summability not asserted on exponential until weighting Census. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets Presented LabelSum Sector Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A W γ μ C : ℝ} {L : Side} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}

/-- No repetition at the first molecule, before connectedness. -/
abbrev ListsAt (c f : Side) := Finset (WarningAt c f) × Finset (LogIndex c f)

def issue (Y : Finset (Stores S)) (l : Finset ℕ) (p : ListsAt c f) : Molecule S :=
    Finset.disjSum Y (Finset.disjSum l (Finset.disjSum p.2 p.1))

instance : Countable (ListsAt c f) := by
  unfold ListsAt
  let h (d : ℕ) : Countable (Ledger f d) := by unfold Ledger; letI : ∀ n, Countable (Bond f × Itinerary f (n+d)) := fun n => inferInstance; infer_instance
  letI := h 1; letI := h 2; letI := h 3
  haveI hu : Countable (ChainIndex f) := by unfold ChainIndex; infer_instance
  haveI ht : Countable (Raw.LogLetter c f) := by unfold Raw.LogLetter Raw.Trans Raw.Pairs; infer_instance
  haveI hp : Countable (LogIndex c f) := by haveI : Countable (Miniature c f) := Finite.to_countable; unfold LogIndex; infer_instance
  haveI hx : Countable (WarningAt c f) := Finite.to_countable; infer_instance

lemma budgets_arr (H : Cash W A μ L Q o C T R) : Summable H.opt := by
  let v := Reserves.tariff H.opt (ConnectedActivityE6.lengths T R) (fun _=>0) Q.ε
  have hz i : H.opt i ≤ v i := by
    apply le_mul_of_one_le_right (H.earns i) (Real.one_le_exp (by have := H.armed.extra i; have:=Q.usable; positivity))
  have he : ∀ i,H.opt i ≠ 0 → (H.birth i).Nonempty := by
    rintro (i|i|i) _
    · let F := (R.activities.forced i).support
      have hp : F.Nonempty := (R.activities.forced i).inventory_ne.mono (R.activities.forced i).inventory_sup
      obtain ⟨x,h⟩ := hp
      exact ⟨_,halo_subset _ _ (mem_image_of_mem _ (show x ∈ RG.inspected F from mem_union_left _ h))⟩
    · exact exChart ..
    exact ⟨_, crucial S i (radiusB A) Q.halo⟩
  have hi := H.fares.hit
  have ht : Ac.Hit H.birth (radiusB A) v Q.relative _ := hi
  have hk i (hf : v i≠0) : (H.birth i).Nonempty := he i (left_ne_zero_of_mul hf)
  have hp := AbsoluteSums.Product.everyone_ne H.birth _ (fun i=> (H.earns _).trans (hz i)) hk ht
  refine hp.2.1.of_nonneg_of_le (fun i=> H.earns i) fun i => ?_
  apply (hz _).trans
  apply le_mul_of_one_le_right ((H.earns i).trans (hz i)); apply Real.one_le_exp
  unfold Target.relative; have := Q.usable; have := Q.bound; have := Q.pos; positivity

variable (X : Coat T F) (k : Finset ℕ) {Y : Finset (Stores S)}

lemma luxury (H : Cash W X.x μ L Q o C T R) (hk : X.width=o.K) (hF : X.manifest) (h : Layout X.seeds Q.halo X.B Y)
    (z : Air f G) :
    HasSum (fun t : ListsAt c f => X.term R Q.table W o.a k Q.halo z (issue Y k t))
      (X.summedUp R Q.table W o.a z k Y) := by
  let u := X.liftA R.beta z
  let A := ∏ B∈Y, X.Pack R Q.table k W o.a B u
  let B := ∏ i∈k,X.bag R o.a u i
  let f' (t : Finset (WarningAt c f)) := ∏ i∈t,X.detect u W o.a R k i
  let C' := Real.exp (∑' j,X.farLog R o.a Q.table z j)
  have he := (expense_series H X rfl hk hF z).2.2
  have hZ (t : ListsAt c f) : X.term R Q.table W o.a k Q.halo z (issue Y k t)=
      f' t.1*(A*B)*(∏ i∈t.2,X.raiseAir R o.a Q.table z i) := by
    have ht l (hl : l∈Y) : X.vertex R Q.table W o.a k Q.halo z (.inl l) = X.Pack R Q.table k W o.a l u := if_pos (h.checkpoints _ hl)
    unfold Coat.term issue; simp only [prod_disjSum]
    rw [show (∏ i∈Y,X.vertex R Q.table W o.a k Q.halo z (.inl i))=A from prod_congr rfl ht]; unfold f'
    unfold B u; simp only [vertex,Sum.elim]; ring
  have hp : (∏ i : WarningAt c f,(1+X.detect u W o.a R k i))=∑ t,f' t := _root_.Finset.prod_one_add _
  convert Raw.finite_start (fun t : ListsAt c f => X.term R Q.table W o.a k Q.halo z (issue Y k t)) (fun i=> f' i*(A*B)*C') (fun i => (he.mul_left (f' i*(A*B))).congr_fun (fun j=> (hZ (i,j)))) using 1
  unfold Coat.summedUp
  dsimp only; rw [hp,← Finset.sum_mul, ← Finset.sum_mul]; unfold A B u C'; ring

lemma recede (H : Cash W X.x μ L Q o C T R) (hp : Layout X.seeds Q.halo X.B Y) (hf : X.manifest)
    (ht : X.width=o.K) : HasSum
      (fun l' => ∫ i, X.body R Q.table W o.a k Q.halo (issue Y k l') i ∂((F.order G).prod X.dice))
      (∫ i : F.Slice G × Air f G,(X.wrapY i.1).summedUp R Q.table W o.a i.2 k Y ∂((F.order G).prod X.dice)) := by
  let v l := X.body R Q.table W o.a k Q.halo (issue Y k l)
  let X' := (F.order G).prod X.dice
  have he : Summable (fun l => ∫ i, ‖v l i‖ ∂X') := by
    have hk := budgets_arr H
    have hx : Summable H.text := Summable.sum _ (hasSum_fintype _).summable hk
    have hy := summable_finsetProd_of_summable_nonneg H.positive hx
    apply Summable.of_nonneg_of_le (fun l => integral_nonneg fun _ => norm_nonneg _) (fun i => H.statements X rfl ht hf k _)
    apply hy.comp_injective; rintro ⟨i,j⟩ ⟨g,h⟩ e
    have ha (u) : blaze (issue Y k u)=u.1 := by simp only [blaze,issue,toRight_disjSum]
    have hh (u : ListsAt c f) : (issue Y k u).toRight.toRight.toLeft=u.2 := by simp only [issue,toLeft_disjSum,toRight_disjSum]
    exact Prod.ext (by rw [← ha (_, _),e,ha]) (by rw [← hh (_, _),e,hh])
  have hZ := hasSum_integral_of_summable_integral_norm (μ:=X') (F:=v) (fun i => H.integrated X rfl ht hf k _) he
  have hX i : (∑' j,v j i)=(X.wrapY i.1).summedUp R Q.table W o.a i.2 k Y := (luxury (X.wrapY i.1) k H ht hf hp i.2).tsum_eq
  simp_rw [hX] at hZ; exact hZ
end YM.ConnectedActivityE6
