import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Sprung
/-! # F-averaged restoration (port of Threshold/Fire/Siege, using integrated average and actual K support).
 Existing terms are single-F; they are not multiplicative across average! Use this version.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Cash
open PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees Multiple Letter OmitClusters
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C δ e : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side}
variable {k k' : Finset ℕ} {w v : Air f G}
variable {j b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable (H : Cash W α μ L Q o C T R) (χ : Chi) (V : Config G c)
variable (p : Renewed j a δ e H)

lemma poleIncome {A: Type} [Fintype A] [Nonempty A] (P : A→ℝ) (t : ℝ) (h : ∀ i,‖P i‖ ≤ t) : ‖Pond.likely P‖ ≤ t := by
  unfold likely; have hz : 0<(Fintype.card A:ℝ) := by positivity
  rw [norm_mul,Real.norm_of_nonneg (inv_pos.mpr hz).le]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (inv_pos.mpr hz).le).trans
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i (_:i∈univ)=> h i)) (inv_pos.mpr hz).le).trans_eq; rw [Finset.sum_const,card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ hz.ne']
lemma renew (n : ℕ) : (∀ i,‖H.entriesPool χ V i‖ ≤ H.thinPay n i) ∧ ∀ i,‖H.depositsPool χ V i‖ ≤ H.broadPay n i := by
  letI : Nonempty (Tree.Forest S.ratio) := Tree.select S.ratio S.patch.odd_side
  let X (r:Reserve S):= prism T α χ o.K V (Greenbelt.allot r); refine ⟨fun i=> ?_,fun i=> ?_⟩
  · exact poleIncome (fun r=> H.entries (X r) i) _ (fun r=> (H.errorPaid (X r) rfl rfl n).1 i)
  exact poleIncome (fun r=>H.deposits (X r) i) _ (fun r=> (H.errorPaid (X r) rfl rfl n).2 i)
def trainedPool (c : Clusters H.ThinP) := Gas.term H.seam (H.entriesPool χ V) c
include p
lemma first_logsPool : Ready H.smallAt (radiusB α) (fun i=> ‖H.entriesPool χ V i‖) (a+e) (Q.overture L μ α j) δ (1/2) := by
  obtain ⟨hv,hz,he',hc,hu,hm⟩ := p.shift
  exact ⟨hv,hz,he',hc,(fun _=> norm_nonneg _), Labels.raise_prices _ _ (fun _=> norm_nonneg _) hm (H.renew χ V j).1⟩

omit p
def homesteadPool := Gas.total H.seam (H.entriesPool χ V)
def lossesPool (A : Finset H.ThickP) := Gas.missing H.smallAt (H.tall A) (H.entriesPool χ V)
def siegePool (A : Finset H.ThickP) := H.bankedPool χ V A* H.homesteadPool χ V* Real.exp (-∑' i,H.lossesPool χ V A i)

variable (O : Tree.Forest S.ratio)
lemma coast_inPool : HasSum (fun i=> overhead (prism T α χ o.K V O) R Q.table * H.inletPool χ V i) (S.push R.beta R.eval V) := by

  let v : Finset (Molecule S) → ℝ := fun t=> overhead (prism T α χ o.K V O) R Q.table*festival T α χ o.K Q.table V R W o.a Q.halo t
  have hv : HasSum v _:= Greenbelt.organizes T α χ H V _ rfl rfl
  have hp z (hp : z∉Set.range H.binders) : v z=0 := by
    by_contra hy; apply hp
    have he j (hj : j∈z) : (H.unionP j).Nonempty := by
      have hn := right_ne_zero_of_mul hy; unfold Greenbelt.festival at hn; split at hn
      next hk => exact (H.resident χ V _ (fun h=> hn (prod_eq_zero hj (show H.spawn χ V j=0 from h)))).2.2.1
      exact (hn rfl).elim
    let X:= z.subtype fun i=> (H.unionP i).Nonempty ∧ (roster i).flags.Nonempty
    let Y:= z.subtype fun i=> (H.unionP i).Nonempty ∧ (roster i).flags=∅
    refine ⟨⟨X,Y⟩,?_⟩; unfold binders; ext i; change i∈H.stave X∪H.sword Y ↔ _; rw [mem_union]; constructor
    · rintro (hx|hx)
      all_goals obtain ⟨i,hi,hx⟩ := mem_map.mp hx; rw [← hx]; exact mem_subtype.mp hi
    intro hi; by_cases hp : (roster i).flags.Nonempty
    · exact Or.inl (show i∈H.stave X from mem_map_of_mem (Embedding.subtype _) (show (⟨i,he i hi,hp⟩:H.ThickP)∈X from mem_subtype.mpr hi))
    exact Or.inr (show i∈H.sword Y from mem_map_of_mem (Embedding.subtype _) (show (⟨i,he i hi,Finset.not_nonempty_iff_eq_empty.mp hp⟩:H.ThinP)∈Y from mem_subtype.mpr hi))
  have hx : HasSum (v∘ H.binders) _ := (H.bindInj.hasSum_iff hp).2 hv
  simp_rw [family_pool H χ V]; exact hx

include p
lemma threshold_logPool : Real.log (H.homesteadPool χ V)= logSum H.seam (H.entriesPool χ V) ∧
    Real.exp (logSum H.seam (H.entriesPool χ V))= H.homesteadPool χ V :=
  let h:=price_log H.seam (H.entriesPool χ V) H.hardH H.smallAt (radiusB α) H.testS (add_nonneg p.full p.post.le) (H.first_logsPool χ V p)
  ⟨h.2.2.2.2,h.2.2.1⟩

lemma rampartPool : HasSum (fun A => overhead (prism T α χ o.K V O) R Q.table * H.siegePool χ V A) (S.push R.beta R.eval V) := by
  have hh := H.coast_inPool χ V O
  have ha A := (price_log H.seam (H.ignoresPool χ V A) H.hardH H.smallAt (radiusB α) H.testS (add_nonneg p.full p.post.le)
    (show Ready _ _ _ _ (Q.overture L μ α j) δ (1/2) from ?_)).1.2.1.of_norm.hasSum
  swap
  · obtain ⟨hz,hv,hA,hD,hF,hY⟩:= H.first_logsPool χ V p
    exact (show Ready H.smallAt (radiusB α) (fun i=> ‖H.ignoresPool χ V A i‖) (a+e) _ _ _ from
      ⟨hz,hv,hA,hD,(fun _=>norm_nonneg _), Labels.raise_prices _ _ (fun _=> norm_nonneg _) hY (fun i=> by
        unfold ignoresPool Gas.cut; split
        · exact le_rfl
        rw [norm_zero]; exact norm_nonneg _)⟩)
  refine hh.prod_fiberwise fun A=> ?_
  have hz := (restores_log H.smallAt (H.tall A) (radiusB α) (H.entriesPool χ V) (fun i=>i.2.1) (add_nonneg p.full p.post.le)
    (H.first_logsPool χ V p)).1
  convert! (((ha A).mul_left (H.bankedPool χ V A)).mul_left (overhead (prism T α χ o.K V O) R Q.table)) using 2
  unfold siegePool; rw [mul_assoc]; exact congr_arg _ hz.symm

end YM.ConnectedActivityE6.Cash
