import YM.MergeProof.West.Bravo

-- following YM.Next.UV_STRESS.Ward with `annular_fieldA`
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Acme
open Filter Function Set MeasureTheory Analysis Extraction Table Ward Climb Work.A01
open YM.Next.UVStress
open scoped Topology ContDiff BigOperators
variable {G : Gauge}{n d D : ℕ}
variable {C : Family G} {S : Table C.book} {F : Extraction.Order} {V : DiffPlan S}

private lemma map_shell (v : S.Field d → S.Field D) (h : S.Hierarchy) (J : S.Stress) (U : E4 → E4)
    (hu : ∀ i : Axis,Continuous (fun y => U y i)) (hp : ∀ B (n : ℕ) (q : Fin n→S.Tag) (x : Points (n+1)), x∈conf _ →
      ∀ χ, Window x χ → flux J χ (fun y => U (y - x 0)) x q B = disc (Fin.cons ⟨D,v B⟩ q) x) :
    ∃ M : S.Field d →ₗ[ℂ] S.Field D, ∀ B,M B=v B := by
  have he (B) (n) (q : Fin n→S.Tag) (x) (ht : x∈conf (n+1)) (χ) (hw : Window x χ)
      (ho : ∀ i : Axis,Continuous (fun y => U (y-x 0) i)) :
      frontRead q x D (v B)=chargeField h.smooth J x ht hw (fun y => U (y-x 0)) ho q d B :=
    (front_eval ..).trans (hp B n q x ht χ hw).symm
  have hU (t : E4) (i : Axis) : Continuous (fun y => U (y-t) i) := (hu i).comp (continuous_id.sub continuous_const)
  refine ⟨⟨⟨v,?_⟩,?_⟩,fun B => rfl⟩
  · intro B D'; apply S.field_ext h.laws.toSymmetric
    intro n q x hx
    obtain ⟨χ,hχ⟩ := exists_window x hx
    simp_rw [← front_eval,map_add]; rw [he _ _ _ _ hx χ hχ (hU (x 0)), he _ _ _ _ hx χ hχ (hU (x 0)),
      he _ _ _ _ hx χ hχ (hU (x 0)), map_add]
  intro c B; change v (c • B) = c • v B
  apply S.field_ext h.laws.toSymmetric; intro n q x hx
  obtain ⟨χ,hχ⟩ := exists_window x hx
  simp_rw [← front_eval,map_smul]; rw [he _ _ _ _ hx χ hχ (hU (x 0)), he _ _ _ _ hx χ hχ (hU (x 0)),map_smul]

lemma shells_law (hC : C.Makes) (hs : Cells.CellHyp C F) (ho : F.PointLimits C S)
    (H : S.Hierarchy) (h : V.Derivatives S) (J : S.Stress) (hc : Conserved V H.spin J)
    (ht : Aroma C) :
    ∃ (p : Parts S) (Y : SpinRows S), StressLaws S J p Y := by
  choose X hX using fun d (i : Axis) v => annular_fieldA hC hs ho H h hc (d:=d) v (fun _ => basis i) (fun _ => contDiff_const)
    (killing_const _) 0 (fun _ _ _ => by simp) (d+1) rfl ht
  choose P hP using fun d i => map_shell (X d i) H J (fun _ => basis i) (fun _ => continuous_const) (hX d i)
  have hv (k : Ortho.Skew) (y : E4) (r : ℝ) : orbital k 0 (r • y)= r^1 • orbital k 0 y := by
    simp only [orbital,M4.move,sub_zero,map_smul,pow_one]
  choose Y hY using fun d k v => annular_fieldA hC hs ho H h hc (d:=d) v (orbital k 0)
    (smooth_orbital k 0) (killing_orbital k 0) 1 (fun y r _ => hv k y r) d rfl ht
  choose R hR using fun d k => map_shell (Y d k) H J (orbital k 0) (fun i => (smooth_orbital k 0 i).continuous) (hY d k)
  have hu {n} q k d B (x : Points (n+1)) (hx : x∈conf _) χ (hw : Window x χ) :
      frontRead q x d (R d k B)=chargeAngular H.smooth J x hx hw q B k := by
    rw [front_eval,hR]; exact (by
      simpa [orbital] using! (hY d k B n q x hx χ hw).symm)
  let T : SpinRows S := fun d => { toFun := R d
                                   map_add' := ?_, map_smul' := ?_ }
  · refine ⟨P,T,fun {n} {x} hx q {χ} w b d B => ?_,fun {n} {x} hx q {χ} w k d B => ?_⟩
    · rw [← flux_translation,hP]; exact hX d b B n q x hx _ w
    rw [← flux_spin,← front_eval]; exact (hu q k d B x hx _ w).symm
  · intro a b; apply LinearMap.ext; intro v
    apply S.field_ext H.laws.toSymmetric; intro n q x hx
    obtain ⟨χ,hχ⟩ := exists_window x hx
    change S.useAt S _ _ = S.useAt S x (Fin.cons ⟨d,R d a v+R d b v⟩ q)
    rw [← front_eval,← front_eval,map_add]; simp only [hu _ _ _ _ _ hx χ hχ,map_add]
  intro r k; apply LinearMap.ext; intro v; apply S.field_ext H.laws.toSymmetric; intro n q x hx
  obtain ⟨χ,hχ⟩ := exists_window x hx
  change S.useAt S _ _ = S.useAt S x (Fin.cons ⟨d,r • R d k v⟩ q)
  rw [← front_eval,← front_eval, show frontRead q x d (r • R d k v)=r • frontRead q x d (R d k v) from
    ((frontRead q x d).restrictScalars ℝ).map_smul .., hu q k d v _ hx χ hχ, hu q (r • k) d v _ hx χ hχ,map_smul]
end YM.MergeProof.Acme

